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
  struct Context
  {
    Diag &diag;

    struct Storage
    {
      bool live = false;
      bool consumed = false;
      bool immune = false;
      bool poisoned = false;
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

    Type *ptrliteraltype;

    TypeTable &typetable;

    Context(TypeTable &typetable, Diag &diag)
      : diag(diag),
        typetable(typetable)
    {
      ptrliteraltype = type(Builtin::Type_PtrLiteral);
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
      assign,
      depend,
      poison,
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

  //|///////////////////// annotations //////////////////////////////////////
  vector<Annotation> annotations(Context &ctx, FunctionDecl *fn)
  {
    for(auto attr : fn->attributes)
    {
      auto attribute = decl_cast<AttributeDecl>(attr);

      if (attribute->name == "lifetime")
      {
        vector<Annotation> result;

        auto i = attribute->options.find_first_not_of(" \t,", 1);
        auto j = attribute->options.find_first_of(" \t,", i);

        while (i < attribute->options.length() - 1)
        {
          Annotation tok;

          if (string_view(attribute->options).substr(i, 7) == "consume")
          {
            tok.type = Annotation::consume;
            tok.text = trim(string_view(attribute->options).substr(i+8, j-i-8), "( \t)");
            tok.loc = SourceLocation { attribute->loc().lineno, attribute->loc().charpos + int(i) + 16 };
          }

          if (string_view(attribute->options).substr(i, 6) == "borrow")
          {
            tok.type = Annotation::borrow;
            tok.text = trim(string_view(attribute->options).substr(i+7, j-i-7), "( \t)");
            tok.loc = SourceLocation { attribute->loc().lineno, attribute->loc().charpos + int(i) + 15 };
          }

          if (string_view(attribute->options).substr(i, 5) == "clone")
          {
            tok.type = Annotation::clone;
            tok.text = trim(string_view(attribute->options).substr(i+6, j-i-6), "( \t)");
            tok.loc = SourceLocation { attribute->loc().lineno, attribute->loc().charpos + int(i) + 14 };
          }

          if (string_view(attribute->options).substr(i, 6) == "assign")
          {
            tok.type = Annotation::assign;
            tok.text = trim(string_view(attribute->options).substr(i+7, j-i-7), "( \t)");
            tok.loc = SourceLocation { attribute->loc().lineno, attribute->loc().charpos + int(i) + 15 };
          }

          if (string_view(attribute->options).substr(i, 6) == "depend")
          {
            tok.type = Annotation::depend;
            tok.text = trim(string_view(attribute->options).substr(i+7, j-i-7), "( \t)");
            tok.loc = SourceLocation { attribute->loc().lineno, attribute->loc().charpos + int(i) + 15 };
          }

          if (string_view(attribute->options).substr(i, 6) == "poison")
          {
            tok.type = Annotation::poison;
            tok.text = trim(string_view(attribute->options).substr(i+7, j-i-7), "( \t)");
            tok.loc = SourceLocation { attribute->loc().lineno, attribute->loc().charpos + int(i) + 15 };
          }

          result.push_back(tok);

          i = attribute->options.find_first_not_of(" \t,", j);
          j = attribute->options.find_first_of(" \t,", i);
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

  //|///////////////////// is_dangling //////////////////////////////////////
  bool is_dangling(Context &ctx, MIR::local_t arg)
  {
    for(auto i : ctx.threads[0].locals[arg].depends_upon)
    {
      if (!ctx.threads[0].locals[i].live)
        return true;
    }

    return !ctx.threads[0].locals[arg].live;
  }

  //|///////////////////// is_consumed //////////////////////////////////////
  bool is_consumed(Context &ctx, MIR::local_t arg)
  {
    for(auto i : ctx.threads[0].locals[arg].depends_upon)
    {
      if (ctx.threads[0].locals[i].consumed)
        return true;
    }

    return ctx.threads[0].locals[arg].consumed;
  }

  //|///////////////////// is_poisoned //////////////////////////////////////
  bool is_poisoned(Context &ctx, MIR::local_t arg)
  {
    for(auto i : ctx.threads[0].locals[arg].depends_upon)
    {
      if (ctx.threads[0].locals[i].poisoned)
        return true;
    }

    return ctx.threads[0].locals[arg].poisoned;
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
        ctx.threads[0].locals[dep].consumed = false;
        ctx.threads[0].locals[dep].immune = false;
        ctx.threads[0].locals[dep].poisoned = false;
        ctx.threads[0].locals[dep].depends_upon.clear();
      }

      ctx.threads[0].locals[args[0]].immune = false;
      ctx.threads[0].locals[args[0]].poisoned = false;
    }

    for(auto arg : args)
    {
      if (is_dangling(ctx, arg))
        ctx.diag.error("potentially dangling variable access", mir.fx.fn, loc);

      if (is_consumed(ctx, arg))
        ctx.diag.error("potentially consumed variable access", mir.fx.fn, loc);

      if (is_poisoned(ctx, arg))
        ctx.diag.error("potentially poisoned variable access", mir.fx.fn, loc);
    }

    if (callee.fn->flags & FunctionDecl::Builtin)
    {
      switch(callee.fn->builtin)
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
      switch(callee.fn->builtin)
      {
        case Builtin::Default_Copytructor:
          // clone(other)
          for(auto dep : ctx.threads[0].locals[args[0]].depends_upon)
            ctx.threads[0].locals[dst].depends_upon.insert(ctx.threads[0].locals[dep].depends_upon.begin(), ctx.threads[0].locals[dep].depends_upon.end());
          break;

        case Builtin::Default_Assignment:
          // assign(this=other)
          for(auto dep : ctx.threads[0].locals[args[0]].depends_upon)
            for(auto src : ctx.threads[0].locals[args[1]].depends_upon)
              ctx.threads[0].locals[dep].depends_upon = ctx.threads[0].locals[src].depends_upon;
          // depends(this)
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
        if (annotation.type == Annotation::consume)
        {
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
        }

        if (annotation.type == Annotation::borrow)
        {
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
        }

        if (annotation.type == Annotation::clone)
        {
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
        }

        if (annotation.type == Annotation::assign)
        {
          auto lhs = trim(annotation.text.substr(0, annotation.text.find_first_of('=')));
          //auto rhs = trim(annotation.text.substr(annotation.text.find_first_of('=') + 1));

          size_t arg = 0;
          for(auto &parm : callee.parameters())
          {
            if (decl_cast<ParmVarDecl>(parm)->name == lhs)
            {
              for(auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
                for(auto src : ctx.threads[0].locals[args[arg + 1]].depends_upon)
                  ctx.threads[0].locals[dep].depends_upon = ctx.threads[0].locals[src].depends_upon;

              break;
            }

            arg += 1;
          }

          if (arg == args.size())
          {
            ctx.diag.error("unknown assign parameter", callee.fn, annotation.loc);
          }
        }

        if (annotation.type == Annotation::depend)
        {
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
        }

        if (annotation.type == Annotation::poison)
        {
          size_t arg = 0;
          for(auto &parm : callee.parameters())
          {
            if (decl_cast<ParmVarDecl>(parm)->name == annotation.text)
            {
              for(auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
              {
                for(auto &local : ctx.threads[0].locals)
                {
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
        }
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
//        cout << statement << endl;

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

    for(auto arg = mir.args_beg; arg != mir.args_end; ++arg)
    {
      ctx.threads[0].locals[arg].live = false;
    }

    size_t arg = mir.args_beg;
    for(auto &parm : mir.fx.parameters())
    {
      if (is_reference_type(mir.locals[arg].type))
      {
        if (ctx.threads[0].locals[arg + mir.locals.size()].consumed && !has_consume(ctx, mir.fx.fn, parm))
          ctx.diag.error("missing consume annotation", mir.fx.fn, parm->loc());
      }

      arg += 1;
    }

    for(auto i : ctx.threads[0].locals[0].depends_upon)
    {
      if (!ctx.threads[0].locals[i].live)
        ctx.diag.error("potentially dangling return value", mir.fx.fn, mir.fx.fn->loc());
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
