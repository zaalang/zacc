//
// lifetime.cpp
//
// Copyright (C) 2020-2022 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "lifetime.h"
#include "lower.h"
#include "diag.h"
#include <unordered_set>
#include <iostream>

using namespace std;

namespace
{
  enum State
  {
    ok,
    dangling,
    consumed,
    poisoned,
  };

  struct Context
  {
    Diag &diag;

    struct Storage
    {
      bool live = false;
      bool consumed = false;
      bool immune = false;
      bool poisoned = false;
      bool toxic = false;
      size_t borrowed = 0;
      unordered_set<MIR::local_t> depends_upon;
    };

    struct Thread
    {
      MIR::block_t block;
      vector<Storage> locals;

      Thread(MIR::block_t block, vector<Storage> locals)
        : block(block),
          locals(std::move(locals))
      {
      }
    };

    vector<Thread> threads;

    void add_thread(MIR::block_t block, vector<Storage> locals)
    {
      threads.push_back(Thread(block, std::move(locals)));
    }

    bool is_dangling(MIR::local_t arg, int depth = 5)
    {
      for(auto dep : threads[0].locals[arg].depends_upon)
      {
        if (depth != 0 && is_dangling(dep, depth - 1))
          return true;
      }

      return !threads[0].locals[arg].live;
    }

    bool is_consumed(MIR::local_t arg, int depth = 5)
    {
      for(auto dep : threads[0].locals[arg].depends_upon)
      {
        if (depth != 0 && is_consumed(dep, depth - 1))
          return true;
      }

      return threads[0].locals[arg].consumed;
    }

    bool is_poisoned(MIR::local_t arg, int depth = 5)
    {
      for(auto dep : threads[0].locals[arg].depends_upon)
      {
        if (depth != 0 && is_poisoned(dep, depth - 1))
          return true;
      }

      return threads[0].locals[arg].poisoned;
    }

    State state(MIR::local_t arg)
    {
      if (is_dangling(arg))
        return State::dangling;

      if (is_consumed(arg))
        return State::consumed;

      if (is_poisoned(arg))
        return State::poisoned;

      return State::ok;
    }

    TypeTable &typetable;

    Context(TypeTable &typetable, Diag &diag)
      : diag(diag),
        typetable(typetable)
    {
    }
  };

  struct Annotation
  {
    enum Type
    {
      unknown,

      consume,
      borrow,
      clone,
      depend,
      poison,
      assign,
      follow,
    };

    Type type = unknown;
    SourceLocation loc;
    std::string_view text;
  };

  string_view trim(string_view str, const char *characters = " \t\r\n")
  {
    auto i = str.find_first_not_of(characters);
    auto j = str.find_last_not_of(characters);

    if (i == string_view::npos || j == string_view::npos)
      return "";

    return str.substr(i, j-i+1);
  }

  //|///////////////////// parse ////////////////////////////////////////////
  Annotation parse(Context &ctx, string_view src, SourceLocation loc)
  {
    Annotation tok = {};

    if (src.substr(0, 7) == "consume")
    {
      tok.type = Annotation::consume;
      tok.text = trim(src.substr(8), "( \t)");
    }

    if (src.substr(0, 6) == "borrow")
    {
      tok.type = Annotation::borrow;
      tok.text = trim(src.substr(7), "( \t)");
    }

    if (src.substr(0, 5) == "clone")
    {
      tok.type = Annotation::clone;
      tok.text = trim(src.substr(6), "( \t)");
    }

    if (src.substr(0, 6) == "depend")
    {
      tok.type = Annotation::depend;
      tok.text = trim(src.substr(7), "( \t)");
    }

    if (src.substr(0, 6) == "poison")
    {
      tok.type = Annotation::poison;
      tok.text = trim(src.substr(7), "( \t)");
    }

    if (src.substr(0, 6) == "assign")
    {
      tok.type = Annotation::assign;
      tok.text = trim(src.substr(7), "( \t)");
    }

    if (src.substr(0, 6) == "follow")
    {
      tok.type = Annotation::follow;
      tok.text = trim(src.substr(7), "( \t)");
    }

    tok.loc = loc;

    return tok;
  }

  //|///////////////////// annotations //////////////////////////////////////
  vector<Annotation> annotations(Context &ctx, FunctionDecl *fn)
  {
    for(auto attr : fn->attributes)
    {
      auto attribute = decl_cast<AttributeDecl>(attr);

      if (attribute->name == "lifetime")
      {
        vector<Annotation> result;

        auto i = attribute->options.find_first_not_of(" \t", 1);

        while (i < attribute->options.length() - 1)
        {
          auto j = attribute->options.find_first_of("(", i);

          for(int indent = 0; j != string::npos; )
          {
            if (attribute->options[j] == '(')
              indent += 1;

            if (attribute->options[j] == ')')
              if (--indent <= 0)
                break;

            j += 1;
          }

          auto annotation = parse(ctx, string_view(attribute->options).substr(i, j - i + 1), SourceLocation { attribute->loc().lineno, attribute->loc().charpos + int(i) + 8 });

          result.push_back(annotation);

          i = attribute->options.find_first_not_of(" \t,", j + 1);
        }

        return result;
      }
    }

    return {};
  }

  //|///////////////////// has_consume //////////////////////////////////////
  bool has_consume(Context &ctx, FunctionDecl *fn, Decl *parm)
  {
    for(auto &annotation : annotations(ctx, fn))
    {
      if (annotation.type == Annotation::consume)
      {
        if (decl_cast<ParmVarDecl>(parm)->name == annotation.text)
          return true;
      }
    }

    return false;
  }

  //|///////////////////// has_poison ///////////////////////////////////////
  //bool has_poison(Context &ctx, FunctionDecl *fn, Decl *parm)
  //{
  //  for(auto &annotation : annotations(ctx, fn))
  //  {
  //    if (annotation.type == Annotation::poison)
  //    {
  //      if (decl_cast<ParmVarDecl>(parm)->name == annotation.text)
  //        return true;
  //    }
  //  }
  //
  //  return false;
  //}

  //|///////////////////// apply ////////////////////////////////////////////
  void apply(Context &ctx, MIR const &mir, Annotation const &annotation, MIR::local_t dst, FnSig const &callee, vector<MIR::local_t> const &args)
  {
    switch (annotation.type)
    {
      case Annotation::consume: {

        size_t arg = 0;
        for(auto &parm : callee.parameters())
        {
          if (decl_cast<ParmVarDecl>(parm)->name == annotation.text)
          {
            for(auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
              ctx.threads[0].locals[dep].consumed = true;

            break;
          }

          arg += 1;
        }

        if (arg == args.size())
        {
          ctx.diag.error("unknown consume parameter", callee.fn, annotation.loc);
        }

        break;
      }

      case Annotation::borrow: {

        size_t arg = 0;
        for(auto &parm : callee.parameters())
        {
          if (decl_cast<ParmVarDecl>(parm)->name == annotation.text)
          {
            for(auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
              ctx.threads[0].locals[dep].consumed = true;

            ctx.threads[0].locals[dst].borrowed = args[arg];

            break;
          }

          arg += 1;
        }

        if (arg == args.size())
        {
          ctx.diag.error("unknown consume parameter", callee.fn, annotation.loc);
        }

        break;
      }

      case Annotation::clone: {

        size_t arg = 0;
        for(auto &parm : callee.parameters())
        {
          if (decl_cast<ParmVarDecl>(parm)->name == annotation.text)
          {
            if (is_reference_type(decl_cast<ParmVarDecl>(parm)->type))
            {
              for(auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
                ctx.threads[0].locals[dst].depends_upon.insert(ctx.threads[0].locals[dep].depends_upon.begin(), ctx.threads[0].locals[dep].depends_upon.end());
            }
            else
            {
              ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[args[arg]].depends_upon;
            }

            break;
          }

          arg += 1;
        }

        if (arg == args.size())
        {
          ctx.diag.error("unknown clone parameter", callee.fn, annotation.loc);
        }

        break;
      }

      case Annotation::depend: {

        size_t arg = 0;
        for(auto &parm : callee.parameters())
        {
          if (decl_cast<ParmVarDecl>(parm)->name == annotation.text)
          {
            for(auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
              ctx.threads[0].locals[dst].depends_upon.insert(dep);

            break;
          }

          arg += 1;
        }

        if (arg == args.size())
        {
          ctx.diag.error("unknown depend parameter", callee.fn, annotation.loc);
        }

        break;
      }

      case Annotation::poison: {

        size_t arg = 0;
        for(auto &parm : callee.parameters())
        {
          if (decl_cast<ParmVarDecl>(parm)->name == annotation.text)
          {
            for(auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
            {
              ctx.threads[0].locals[dep].toxic = true;

              for(auto &local : ctx.threads[0].locals)
              {
                if (!local.live)
                  continue;

                if (local.immune)
                  continue;

                if (local.depends_upon.find(dep) != local.depends_upon.end())
                  local.poisoned = true;
              }
            }

            break;
          }

          arg += 1;
        }

        if (arg == args.size())
        {
          ctx.diag.error("unknown poison parameter", callee.fn, annotation.loc);
        }

        break;
      }

      case Annotation::assign: {

        auto lhs = trim(annotation.text.substr(0, annotation.text.find_first_of(',')));
        auto rhs = parse(ctx, trim(annotation.text.substr(annotation.text.find_first_of(',') + 1)), annotation.loc);

        size_t arg = 0;
        for(auto &parm : callee.parameters())
        {
          if (decl_cast<ParmVarDecl>(parm)->name == lhs)
          {
            for(auto dst : ctx.threads[0].locals[args[arg]].depends_upon)
            {
              ctx.threads[0].locals[dst].immune = false;
              ctx.threads[0].locals[dst].consumed = false;
              ctx.threads[0].locals[dst].poisoned = false;
              ctx.threads[0].locals[dst].toxic = false;
              ctx.threads[0].locals[dst].depends_upon.clear();

              apply(ctx, mir, rhs, dst, callee, args);
            }

            ctx.threads[0].locals[args[arg]].immune = false;
            ctx.threads[0].locals[args[arg]].poisoned = false;

            break;
          }

          arg += 1;
        }

        if (arg == args.size())
        {
          ctx.diag.error("unknown assign parameter", callee.fn, annotation.loc);
        }

        break;
      }

      case Annotation::follow: {

        auto lhs = trim(annotation.text.substr(0, annotation.text.find_first_of('.')));
        auto rhs = trim(annotation.text.substr(annotation.text.find_first_of('.') + 1));

        size_t arg = 0;
        for(auto &parm : callee.parameters())
        {
          if (decl_cast<ParmVarDecl>(parm)->name == lhs)
          {
            Annotation target;

            for(auto type = mir.locals[args[arg]].type; is_tag_type(type); )
            {
              auto tagtype = type_cast<TagType>(type);

              for(auto decl : tagtype->decls)
              {
                if (decl->kind() == Decl::Function && decl_cast<FunctionDecl>(decl)->name == rhs)
                {
                  for(auto &annotation : annotations(ctx, decl_cast<FunctionDecl>(decl)))
                  {
                    target.type = annotation.type;

                    break;
                  }

                  break;
                }

                if (decl->kind() == Decl::FieldVar && decl_cast<VarDecl>(decl)->name == rhs)
                {
                  target.type = Annotation::clone;

                  break;
                }
              }

              if (target.type != Annotation::unknown)
                break;

              if (!is_tag_type(type) || !decl_cast<TagDecl>(tagtype->decl)->basetype)
                break;

              type = tagtype->fields[0];
            }

            if (target.type != Annotation::unknown)
            {
              target.text = lhs;
              target.loc = annotation.loc;

              apply(ctx, mir, target, dst, callee, args);

              break;
            }
          }

          arg += 1;
        }

        if (arg == args.size())
        {
          ctx.diag.error("unknown follow parameter", callee.fn, annotation.loc);
        }

        break;
      }

      default:
        ctx.diag.error("unknown lifetime annotation", callee.fn, annotation.loc);
    }
  }

  //|///////////////////// analyse_assign_variable //////////////////////////
  void analyse_assign_variable(Context &ctx, MIR const &mir, MIR::local_t dst, MIR::RValue::VariableData const &variable)
  {
    auto &[op, arg, fields, loc] = variable;

    if (all_of(fields.begin(), fields.end(), [](auto k){ return k.op != MIR::RValue::Val; }))
    {
      switch(op)
      {
        case MIR::RValue::Val:
          ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[arg].depends_upon;
          break;

        case MIR::RValue::Ref:
          ctx.threads[0].locals[dst].depends_upon.insert(arg);
          break;

        case MIR::RValue::Fer:
          for(auto dep : ctx.threads[0].locals[arg].depends_upon)
            ctx.threads[0].locals[dst].depends_upon.insert(ctx.threads[0].locals[dep].depends_upon.begin(), ctx.threads[0].locals[dep].depends_upon.end());
          break;

        case MIR::RValue::Idx:
          assert(false);
          break;
      }

      if (op == MIR::RValue::Ref && fields.empty())
        ctx.threads[0].locals[dst].immune = true;

      if (op == MIR::RValue::Val && fields.empty())
        ctx.threads[0].locals[dst].immune = ctx.threads[0].locals[arg].immune;

      ctx.threads[0].locals[dst].poisoned = ctx.threads[0].locals[arg].poisoned;

      ctx.threads[0].locals[dst].consumed = ctx.threads[0].locals[arg].consumed;
    }
  }

  //|///////////////////// analyse_call /////////////////////////////////////
  void analyse_call(Context &ctx, MIR const &mir, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (callee.fn->flags & FunctionDecl::Destructor)
      return;

    if (callee.fn->name == Ident::op_assign)
    {
      for(auto dep : ctx.threads[0].locals[args[0]].depends_upon)
      {
        ctx.threads[0].locals[dep].immune = false;
        ctx.threads[0].locals[dep].consumed = false;
        ctx.threads[0].locals[dep].poisoned = false;
        ctx.threads[0].locals[dep].toxic = false;
        ctx.threads[0].locals[dep].depends_upon.clear();
      }

      ctx.threads[0].locals[args[0]].immune = false;
      ctx.threads[0].locals[args[0]].consumed = false;
      ctx.threads[0].locals[args[0]].poisoned = false;
    }

    for(auto const &[parm, arg] : zip(callee.parameters(), args))
    {
      switch (ctx.state(arg))
      {
        case State::ok:
          break;

        case State::dangling:
          ctx.diag.error("potentially dangling variable access", mir.fx.fn, loc);
          break;

        case State::consumed:
          ctx.diag.error("potentially consumed variable access", mir.fx.fn, loc);
          break;

        case State::poisoned:
          ctx.diag.error("potentially poisoned variable access", mir.fx.fn, loc);
          break;
      }
    }

    if (callee.fn->flags & FunctionDecl::Builtin)
    {
      switch (callee.fn->builtin)
      {
        case Builtin::Assign:
          for(auto dep : ctx.threads[0].locals[args[0]].depends_upon)
            ctx.threads[0].locals[dep] = ctx.threads[0].locals[args[1]];
          ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[args[0]].depends_upon;
          break;

        case Builtin::PreInc:
        case Builtin::PreDec:
          ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[args[0]].depends_upon;
          break;

        case Builtin::OffsetAdd:
        case Builtin::OffsetSub:
          ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[args[0]].depends_upon;
          break;

        case Builtin::ArrayData:
        case Builtin::ArrayIndex:
        case Builtin::ArrayBegin:
        case Builtin::ArrayEnd:
          ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[args[0]].depends_upon;
          break;

        case Builtin::DeRef:
          ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[args[0]].depends_upon;
          break;

        default:
          break;
      }
    }

    if (callee.fn->flags & FunctionDecl::Defaulted)
    {
      switch (callee.fn->builtin)
      {
        case Builtin::Default_Copytructor:
          // clone(other)
          for(auto dep : ctx.threads[0].locals[args[0]].depends_upon)
            ctx.threads[0].locals[dst].depends_upon.insert(ctx.threads[0].locals[dep].depends_upon.begin(), ctx.threads[0].locals[dep].depends_upon.end());
          break;

        case Builtin::Default_Assignment:
          // assign(this, clone(other))
          for(auto dep : ctx.threads[0].locals[args[0]].depends_upon)
            for(auto src : ctx.threads[0].locals[args[1]].depends_upon)
              ctx.threads[0].locals[dep].depends_upon = ctx.threads[0].locals[src].depends_upon;
          // depend(this)
          for(auto dep : ctx.threads[0].locals[args[0]].depends_upon)
            ctx.threads[0].locals[dst].depends_upon.insert(dep);
          break;

        default:
          break;
      }
    }

    if (callee.fn->flags & FunctionDecl::Lifetimed)
    {
      for(auto &annotation : annotations(ctx, callee.fn))
      {
        apply(ctx, mir, annotation, dst, callee, args);
      }
    }
  }

  //|///////////////////// analyse_cast /////////////////////////////////////
  void analyse_cast(Context &ctx, MIR const &mir, MIR::local_t dst, MIR::RValue::CastData const &cast)
  {
    auto &[arg, loc] = cast;

    ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[arg].depends_upon;
  }

  //|///////////////////// analyse_assign_statement /////////////////////////
  void analyse_assign_statement(Context &ctx, MIR const &mir, MIR::Statement const &statement)
  {
    auto &src = statement.src;
    auto &dst = statement.dst;

    switch (src.kind())
    {
      case MIR::RValue::Empty:
        break;

      case MIR::RValue::Constant:
        break;

      case MIR::RValue::Variable:
        analyse_assign_variable(ctx, mir, dst, src.get<MIR::RValue::Variable>());
        break;

      case MIR::RValue::Call:
        analyse_call(ctx, mir, dst, src.get<MIR::RValue::Call>());
        break;

      case MIR::RValue::Cast:
        analyse_cast(ctx, mir, dst, src.get<MIR::RValue::Cast>());
        break;
    }
  }

  //|///////////////////// analyse_construct_statement //////////////////////
  void analyse_construct_statement(Context &ctx, MIR const &mir, MIR::Statement const &statement)
  {
    auto &dst = statement.dst;

    analyse_assign_statement(ctx, mir, statement);

    for(auto dep : ctx.threads[0].locals[dst - 1].depends_upon)
    {
      ctx.threads[0].locals[dep].consumed |= ctx.threads[0].locals[dst].consumed;
      ctx.threads[0].locals[dep].poisoned |= ctx.threads[0].locals[dst].poisoned;
      ctx.threads[0].locals[dep].depends_upon.insert(ctx.threads[0].locals[dst].depends_upon.begin(), ctx.threads[0].locals[dst].depends_upon.end());
    }
  }

  //|///////////////////// analyse_storage_live /////////////////////////////
  void analyse_storage_live(Context &ctx, MIR const &mir, MIR::Statement const &statement)
  {
    ctx.threads[0].locals[statement.dst].live = true;
  }

  //|///////////////////// analyse_storage_dead /////////////////////////////
  void analyse_storage_dead(Context &ctx, MIR const &mir, MIR::Statement const &statement)
  {
    if (ctx.threads[0].locals[statement.dst].borrowed != 0)
    {
      auto arg = ctx.threads[0].locals[statement.dst].borrowed;

      for(auto dep : ctx.threads[0].locals[arg].depends_upon)
        ctx.threads[0].locals[dep].consumed = false;
    }

    //for(auto &local : ctx.threads[0].locals)
    //{
    //  if (!local.live)
    //    continue;

    //  if (local.depends_upon.find(statement.dst) != local.depends_upon.end())
    //    local.poisoned = true;
    //}

    ctx.threads[0].locals[statement.dst].live = false;
  }

  //|///////////////////// analyse //////////////////////////////////////////
  void analyse(Context &ctx, MIR const &mir)
  {
    if (mir.fx.fn->flags & FunctionDecl::Defaulted)
      return;

    ctx.add_thread(0, vector<Context::Storage>(mir.locals.size() + mir.args_end));

    for(auto arg = mir.args_beg; arg != mir.args_end; ++arg)
    {
      ctx.threads[0].locals[arg].live = true;

      if (is_reference_type(mir.locals[arg].type))
      {
        ctx.threads[0].locals[arg].immune = true;
        ctx.threads[0].locals[arg + mir.locals.size()].live = true;
        ctx.threads[0].locals[arg].depends_upon.insert(arg + mir.locals.size());
      }
    }

    for(size_t block_id = 0; block_id < mir.blocks.size(); ++block_id)
    {
      auto &block = mir.blocks[block_id];

      auto j = find_if(ctx.threads.begin(), ctx.threads.end(), [&](auto &k) { return k.block == block_id; });

      if (j == ctx.threads.end())
        continue;

      if (j != ctx.threads.begin())
        std::swap(ctx.threads.front(), *j);

      for(size_t i = 1; i != ctx.threads.size(); )
      {
        if (ctx.threads[i].block <= block_id)
        {
          for(size_t k = 0; k < ctx.threads[0].locals.size(); ++k)
          {
            ctx.threads[0].locals[k].consumed |= ctx.threads[i].locals[k].consumed;
            ctx.threads[0].locals[k].immune &= ctx.threads[i].locals[k].immune;
            ctx.threads[0].locals[k].poisoned |= ctx.threads[i].locals[k].poisoned;
            ctx.threads[0].locals[k].depends_upon.merge(ctx.threads[i].locals[k].depends_upon);
          }

          ctx.threads.erase(ctx.threads.begin() + i);

          continue;
        }

        ++i;
      }

      for(auto &statement : block.statements)
      {
        //cout << statement << endl;

        switch (statement.kind)
        {
          case MIR::Statement::NoOp:
            break;

          case MIR::Statement::Assign:
            analyse_assign_statement(ctx, mir, statement);
            break;

          case MIR::Statement::Construct:
            analyse_construct_statement(ctx, mir, statement);
            break;

          case MIR::Statement::StorageLive:
            analyse_storage_live(ctx, mir, statement);
            break;

          case MIR::Statement::StorageDead:
            analyse_storage_dead(ctx, mir, statement);
            break;
        }
      }

      switch (block.terminator.kind)
      {
        case MIR::Terminator::Return:
          break;

        case MIR::Terminator::Goto:
          ctx.threads[0].block = block.terminator.blockid;
          break;

        case MIR::Terminator::Switch:
          ctx.threads[0].block = block.terminator.blockid;
          for(auto &[value, block]: block.terminator.targets)
            if (block > block_id)
              ctx.add_thread(block, ctx.threads[0].locals);
          break;

        case MIR::Terminator::Catch:
          ctx.threads[0].block = block.terminator.blockid + 1;
          break;

        case MIR::Terminator::Throw:
          ctx.threads[0].block = block.terminator.blockid;
          break;

        case MIR::Terminator::Unreachable:
          ctx.threads[0].block = mir.blocks.size();
          break;
      }
    }

    ctx.threads[0].locals[0].live = true;

    for(auto arg = mir.args_beg; arg != mir.args_end; ++arg)
    {
      ctx.threads[0].locals[arg].live = false;
    }

    size_t arg = mir.args_beg;
    for(auto &parm : mir.fx.parameters())
    {
      if (is_reference_type(decl_cast<ParmVarDecl>(parm)->type))
      {
        if (ctx.threads[0].locals[arg + mir.locals.size()].consumed && !has_consume(ctx, mir.fx.fn, parm))
          ctx.diag.error("missing consume annotation", mir.fx.fn, parm->loc());

        //if (ctx.threads[0].locals[arg + mir.locals.size()].toxic && !has_poison(ctx, mir.fx.fn, parm))
        //  ctx.diag.error("missing poison annotation", mir.fx.fn, parm->loc());
      }

      arg += 1;
    }

    switch (ctx.state(0))
    {
      case State::ok:
        break;

      case State::dangling:
        ctx.diag.error("potentially dangling return value", mir.fx.fn, mir.fx.fn->loc());
        break;

      case State::consumed:
        ctx.diag.error("potentially consumed return value", mir.fx.fn, mir.fx.fn->loc());
        break;

      case State::poisoned:
        ctx.diag.error("potentially poisoned return value", mir.fx.fn, mir.fx.fn->loc());
        break;
    }
  }
}


//|--------------------- Lifetime -------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// lifetime ///////////////////////////////////////////
void lifetime(MIR const &mir, TypeTable &typetable, Diag &diag)
{
  Context ctx(typetable, diag);

#if 0
  dump_mir(mir);
#endif

  if (ctx.diag.has_errored())
    return;

  analyse(ctx, mir);
}
