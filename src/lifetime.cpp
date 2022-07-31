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
#include <deque>
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
      vector<MIR::RValue::VariableData const *> depends_upon;
      vector<MIR::RValue::VariableData const *> consumed_fields;
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

    bool is_super_field(vector<MIR::RValue::Field> const &lhs, vector<MIR::RValue::Field> const &rhs)
    {
      for(size_t i = 0; i < min(lhs.size(), rhs.size()); ++i)
      {
        if (lhs[i].index != rhs[i].index)
          return false;
      }

      return lhs.size() <= rhs.size();
    }

    bool is_common_field(vector<MIR::RValue::Field> const &lhs, vector<MIR::RValue::Field> const &rhs)
    {
      for(size_t i = 0; i < min(lhs.size(), rhs.size()); ++i)
      {
        if (lhs[i].index != rhs[i].index)
          return false;
      }

      return true;
    }

    bool is_shared(MIR::local_t arg1, MIR::local_t arg2, int depth = 5)
    {
      for(auto dep1 : threads[0].locals[arg1].depends_upon)
      {
        for(auto dep2: threads[0].locals[arg2].depends_upon)
          if (get<1>(*dep2) == get<1>(*dep1) && is_common_field(get<2>(*dep2), get<2>(*dep1)))
            return true;
      }

      return false;
    }

    bool is_dangling(MIR::local_t arg, int depth = 5)
    {
      for(auto dep : threads[0].locals[arg].depends_upon)
      {
        if (depth != 0 && is_dangling(get<1>(*dep), depth - 1))
          return true;
      }

      return !threads[0].locals[arg].live;
    }

    bool is_consumed(MIR::local_t arg, int depth = 5)
    {
      for(auto dep : threads[0].locals[arg].depends_upon)
      {
#if 0
        cout << "is_consumed: " << arg << " " << *dep << endl;
        for(auto fld : threads[0].locals[get<1>(*dep)].consumed_fields)
          cout << "           : has " << *fld << endl;
#endif

        for(auto fld : threads[0].locals[get<1>(*dep)].consumed_fields)
          if (is_common_field(get<2>(*fld), get<2>(*dep)))
            return true;

        if (depth != 0 && is_consumed(get<1>(*dep), depth - 1))
          return true;
      }

      return false;
    }

    bool is_poisoned(MIR::local_t arg, int depth = 5)
    {
      for(auto dep : threads[0].locals[arg].depends_upon)
      {
        if (depth != 0 && is_poisoned(get<1>(*dep), depth - 1))
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

    deque<MIR::RValue::VariableData> field_allocator;

    MIR::RValue::VariableData *make_field(MIR::local_t local)
    {
      field_allocator.push_back(MIR::RValue::local(MIR::RValue::Ref, local, SourceLocation{}));

      return &field_allocator.back();
    }

    MIR::RValue::VariableData *make_field(MIR::RValue::VariableData const *base, vector<MIR::RValue::Field> const &subfields)
    {
      field_allocator.push_back(*base);

      auto &[op, arg, fields, loc] = field_allocator.back();

      fields.insert(fields.end(), subfields.begin(), subfields.end());

      fields[get<2>(*base).size()].op = MIR::RValue::Ref;

      return &field_allocator.back();
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
      launder,
      restrict,
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

    if (src.substr(0, 7) == "launder")
    {
      tok.type = Annotation::launder;
      tok.text = trim(src.substr(8), "( \t)");
    }

    if (src.substr(0, 8) == "restrict")
    {
      tok.type = Annotation::restrict;
      tok.text = trim(src.substr(9), "( \t)");
    }

    tok.loc = loc;

    return tok;
  }

  //|///////////////////// annotations //////////////////////////////////////
  vector<Annotation> annotations(Context &ctx, FunctionDecl *fn)
  {
    vector<Annotation> result;

    if (fn->flags & FunctionDecl::Lifetimed)
    {
      for(auto attr : fn->attributes)
      {
        auto attribute = decl_cast<AttributeDecl>(attr);

        if (attribute->name == "lifetime")
        {
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
        }
      }
    }

    return result;
  }

  //|///////////////////// has_launder //////////////////////////////////////
  bool has_launder(Context &ctx, vector<Annotation> const &annotations)
  {
    for(auto &annotation : annotations)
    {
      if (annotation.type == Annotation::launder)
        return true;
    }

    return false;
  }

  //|///////////////////// has_consume //////////////////////////////////////
  bool has_consume(Context &ctx, vector<Annotation> const &annotations, Decl *parm)
  {
    for(auto &annotation : annotations)
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
  //bool has_poison(Context &ctx, vector<Annotation> const &annotations, Decl *parm)
  //{
  //  for(auto &annotation : annotations)
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

  //|///////////////////// is_const_reference ///////////////////////////////
  bool is_const_reference(Context &ctx, MIR::Local const &local)
  {
    if (local.flags & MIR::Local::Reference)
    {
      return (local.flags & MIR::Local::Const);
    }

    if (is_reference_type(local.type))
    {
      if (is_qualarg_reference(local.type))
        return (type_cast<QualArgType>(remove_reference_type(local.type))->qualifiers & QualArgType::Const);

      return is_const_reference(local.type);
    }

    return false;
  }

  //|///////////////////// is_rvalue_reference //////////////////////////////
  bool is_rvalue_reference(Context &ctx, MIR::Local const &local)
  {
    if (local.flags & MIR::Local::Reference)
    {
      return (local.flags & MIR::Local::RValue);
    }

    if (is_qualarg_reference(local.type))
    {
      return (type_cast<QualArgType>(remove_reference_type(local.type))->qualifiers & QualArgType::RValue);
    }

    return false;
  }

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
              ctx.threads[0].locals[get<1>(*dep)].consumed = true;

            for(auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
              ctx.threads[0].locals[get<1>(*dep)].consumed_fields.insert(ctx.threads[0].locals[get<1>(*dep)].consumed_fields.end(), ctx.threads[0].locals[args[arg]].depends_upon.begin(), ctx.threads[0].locals[args[arg]].depends_upon.end());

#if 0
            for(auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
              for(auto fld : ctx.threads[0].locals[get<1>(*dep)].consumed_fields)
                cout << "consume: " << *fld << endl;
#endif

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
              ctx.threads[0].locals[get<1>(*dep)].consumed = true;

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
                ctx.threads[0].locals[dst].depends_upon.insert(ctx.threads[0].locals[dst].depends_upon.end(), ctx.threads[0].locals[get<1>(*dep)].depends_upon.begin(), ctx.threads[0].locals[get<1>(*dep)].depends_upon.end());
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
              ctx.threads[0].locals[dst].depends_upon.push_back(dep);

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
#if 0
            for(auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
              cout << "poison: " << *dep << endl;
#endif

            for(auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
            {
              ctx.threads[0].locals[get<1>(*dep)].toxic = true;

              for(auto &local : ctx.threads[0].locals)
              {
                if (!local.live)
                  continue;

                if (local.immune)
                  continue;

                for(auto fld : local.depends_upon)
                {
                  if (get<1>(*fld) != get<1>(*dep))
                    continue;

                  if (!ctx.is_super_field(get<2>(*dep), get<2>(*fld)))
                    continue;

#if 0
                  cout << "      : " << &local - &ctx.threads[0].locals.front() << " has " << *fld << endl;
#endif

                  local.poisoned = true;
                }
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
              ctx.threads[0].locals[get<1>(*dst)].immune = false;
              ctx.threads[0].locals[get<1>(*dst)].consumed = false;
              ctx.threads[0].locals[get<1>(*dst)].poisoned = false;
              ctx.threads[0].locals[get<1>(*dst)].toxic = false;
              ctx.threads[0].locals[get<1>(*dst)].depends_upon.clear();
              ctx.threads[0].locals[get<1>(*dst)].consumed_fields.clear();

              apply(ctx, mir, rhs, get<1>(*dst), callee, args);
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

      case Annotation::launder:
        break;

      case Annotation::restrict:
        break;

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
          ctx.threads[0].locals[dst].immune = ctx.threads[0].locals[arg].immune;
          break;

        case MIR::RValue::Ref:
          ctx.threads[0].locals[dst].depends_upon.push_back(&variable);
          ctx.threads[0].locals[dst].immune = true;
          break;

        case MIR::RValue::Fer:
          for(auto dep : ctx.threads[0].locals[arg].depends_upon)
            ctx.threads[0].locals[dst].depends_upon.insert(ctx.threads[0].locals[dst].depends_upon.end(), ctx.threads[0].locals[get<1>(*dep)].depends_upon.begin(), ctx.threads[0].locals[get<1>(*dep)].depends_upon.end());
          break;

        case MIR::RValue::Idx:
          assert(false);
          break;
      }

      ctx.threads[0].locals[dst].poisoned = ctx.threads[0].locals[arg].poisoned;
      ctx.threads[0].locals[dst].consumed = ctx.threads[0].locals[arg].consumed;
    }

    if (fields.size() != 0 && fields[0].op == MIR::RValue::Val && all_of(fields.begin() + 1, fields.end(), [](auto k){ return k.op != MIR::RValue::Val; }))
    {
      switch(op)
      {
        case MIR::RValue::Val:
          break;

        case MIR::RValue::Ref:
          for(auto dep : ctx.threads[0].locals[arg].depends_upon)
            ctx.threads[0].locals[dst].depends_upon.push_back(ctx.make_field(dep, fields));
          ctx.threads[0].locals[dst].immune = true;
          break;

        case MIR::RValue::Fer:
          break;

        case MIR::RValue::Idx:
          assert(false);
          break;
      }
    }
  }

  //|///////////////////// analyse_call /////////////////////////////////////
  void analyse_call(Context &ctx, MIR const &mir, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (callee.fn->flags & FunctionDecl::Destructor)
      return;

    auto notations = annotations(ctx, callee.fn);

    if (callee.fn->name == Ident::op_assign || has_launder(ctx, notations))
    {
#if 0
      for(auto dep : ctx.threads[0].locals[args[0]].depends_upon)
        cout << "launder: " << *dep << endl;
#endif

      for(auto dep : ctx.threads[0].locals[args[0]].depends_upon)
      {
        auto &consumed_fields = ctx.threads[0].locals[get<1>(*dep)].consumed_fields;

        for(auto i = consumed_fields.begin(); i != consumed_fields.end(); )
        {
          if (ctx.is_super_field(get<2>(*dep), get<2>(**i)))
            i = consumed_fields.erase(i);
          else
            ++i;
        }

        if (consumed_fields.empty())
        {
          ctx.threads[0].locals[get<1>(*dep)].consumed = false;
        }

        if (get<2>(*dep).empty())
        {
          ctx.threads[0].locals[get<1>(*dep)].immune = false;
          ctx.threads[0].locals[get<1>(*dep)].consumed = false;
          ctx.threads[0].locals[get<1>(*dep)].poisoned = false;
          ctx.threads[0].locals[get<1>(*dep)].toxic = false;
          ctx.threads[0].locals[get<1>(*dep)].depends_upon.clear();
          ctx.threads[0].locals[get<1>(*dep)].consumed_fields.clear();
        }
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

      for(auto &annotation : notations)
      {
        switch (annotation.type)
        {
          case Annotation::restrict: {

            if (decl_cast<ParmVarDecl>(parm)->name == annotation.text)
            {
              for(auto const &[other_parm, other_arg] : zip(callee.parameters(), args))
              {
                if (other_arg == arg)
                  continue;

                if (ctx.is_shared(arg, other_arg))
                  ctx.diag.error("potentially shared restrict value", mir.fx.fn, loc);
              }

              break;
            }

            break;
          }

          default:
            break;
        }
      }
    }

    if (callee.fn->flags & FunctionDecl::Builtin)
    {
      switch (callee.fn->builtin)
      {
        case Builtin::Assign:
          for(auto dep : ctx.threads[0].locals[args[0]].depends_upon)
            ctx.threads[0].locals[get<1>(*dep)].depends_upon.insert(ctx.threads[0].locals[get<1>(*dep)].depends_upon.end(), ctx.threads[0].locals[args[1]].depends_upon.begin(), ctx.threads[0].locals[args[1]].depends_upon.end());
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
        case Builtin::Default_Constructor:
          if (is_lambda_type(mir.locals[dst].type))
          {
            auto lambda = decl_cast<LambdaDecl>(type_cast<TagType>(callee.fn->returntype)->decl);

            for(auto &arg : args)
            {
              if (is_reference_type(decl_cast<LambdaVarDecl>(lambda->captures[&arg - &args.front()])->type))
              {
                // clone(arg)
                ctx.threads[0].locals[dst].depends_upon.insert(ctx.threads[0].locals[dst].depends_upon.end(), ctx.threads[0].locals[arg].depends_upon.begin(), ctx.threads[0].locals[arg].depends_upon.end());
              }
            }
          }
          break;

        case Builtin::Default_Copytructor:
          // clone(other)
          for(auto dep : ctx.threads[0].locals[args[0]].depends_upon)
            ctx.threads[0].locals[dst].depends_upon.insert(ctx.threads[0].locals[dst].depends_upon.end(), ctx.threads[0].locals[get<1>(*dep)].depends_upon.begin(), ctx.threads[0].locals[get<1>(*dep)].depends_upon.end());
          break;

        case Builtin::Default_Assignment:
          // assign(this, clone(other))
          for(auto dep : ctx.threads[0].locals[args[0]].depends_upon)
            for(auto src : ctx.threads[0].locals[args[1]].depends_upon)
              ctx.threads[0].locals[get<1>(*dep)].depends_upon = ctx.threads[0].locals[get<1>(*src)].depends_upon;
          // depend(this)
          ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[args[0]].depends_upon;
          break;

        default:
          break;
      }
    }

    if (is_rvalue_reference(ctx, mir.locals[dst].type))
    {
      auto arg = ctx.threads[0].locals.size();
      for(auto &thread : ctx.threads)
        thread.locals.push_back(Context::Storage());

      ctx.threads[0].locals[dst].immune = true;
      ctx.threads[0].locals[arg].live = true;
      ctx.threads[0].locals[dst].depends_upon.push_back(ctx.make_field(arg));
    }

    for(auto &annotation : notations)
    {
      apply(ctx, mir, annotation, dst, callee, args);
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
      ctx.threads[0].locals[get<1>(*dep)].consumed |= ctx.threads[0].locals[dst].consumed;
      ctx.threads[0].locals[get<1>(*dep)].poisoned |= ctx.threads[0].locals[dst].poisoned;
      ctx.threads[0].locals[get<1>(*dep)].depends_upon.insert(ctx.threads[0].locals[get<1>(*dep)].depends_upon.end(), ctx.threads[0].locals[dst].depends_upon.begin(), ctx.threads[0].locals[dst].depends_upon.end());
      ctx.threads[0].locals[get<1>(*dep)].consumed_fields.insert(ctx.threads[0].locals[get<1>(*dep)].consumed_fields.end(), ctx.threads[0].locals[dst].consumed_fields.begin(), ctx.threads[0].locals[dst].consumed_fields.end());
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
        ctx.threads[0].locals[get<1>(*dep)].consumed = false;
    }

    //for(auto &local : ctx.threads[0].locals)
    //{
    //  if (!local.live)
    //    continue;

    //  if (local.depends_upon.find(statement.dst) != local.depends_upon.end())
    //    local.poisoned = true;
    //}

    if ((mir.locals[statement.dst].flags & (MIR::Local::Const | MIR::Local::LValue | MIR::Local::RValue)) == MIR::Local::Const)
      return;

    ctx.threads[0].locals[statement.dst].live = false;
  }

  //|///////////////////// analyse_storage_loop /////////////////////////////
  void analyse_storage_loop(Context &ctx, MIR const &mir, MIR::Statement const &statement)
  {
    auto arg = statement.dst;

    auto loc = [&]() {
      for(auto &info : mir.varinfos)
        if (info.local == statement.dst)
          return info.vardecl->loc();
      return mir.fx.fn->loc();
    };

#if 0
      for(auto dep : ctx.threads[0].locals[arg].depends_upon)
        cout << "loop: " << *dep << endl;
#endif

    switch (ctx.state(arg))
    {
      case State::ok:
        break;

      case State::dangling:
        ctx.diag.error("potentially dangling loop variable", mir.fx.fn, loc());
        break;

      case State::consumed:
        if (!is_rvalue_reference(ctx, mir.locals[arg]))
          ctx.diag.error("potentially consumed loop variable", mir.fx.fn, loc());
        break;

      case State::poisoned:
        ctx.diag.error("potentially poisoned loop variable", mir.fx.fn, loc());
        break;
    }

    ctx.threads[0].locals[arg].consumed = false;
    ctx.threads[0].locals[arg].consumed_fields.clear();
  }

  //|///////////////////// analyse //////////////////////////////////////////
  void analyse(Context &ctx, MIR const &mir)
  {
    if (mir.fx.fn->flags & FunctionDecl::Defaulted)
      return;

    auto notations = annotations(ctx, mir.fx.fn);

    ctx.add_thread(0, vector<Context::Storage>(mir.locals.size() + mir.args_end));

    for(auto arg = mir.args_beg; arg != mir.args_end; ++arg)
    {
      ctx.threads[0].locals[arg].live = true;

      if (is_reference_type(mir.locals[arg].type))
      {
        ctx.threads[0].locals[arg].immune = true;
        ctx.threads[0].locals[arg + mir.locals.size()].live = true;
        ctx.threads[0].locals[arg].depends_upon.push_back(ctx.make_field(arg + mir.locals.size()));
      }
    }

    for(auto &[arg, value] : mir.statics)
    {
      ctx.threads[0].locals[arg].live = true;
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

            for(auto dep : ctx.threads[i].locals[k].depends_upon)
              if (find(ctx.threads[0].locals[k].depends_upon.begin(), ctx.threads[0].locals[k].depends_upon.end(), dep) == ctx.threads[0].locals[k].depends_upon.end())
                ctx.threads[0].locals[k].depends_upon.push_back(dep);

            for(auto fld : ctx.threads[i].locals[k].consumed_fields)
              if (find(ctx.threads[0].locals[k].consumed_fields.begin(), ctx.threads[0].locals[k].consumed_fields.end(), fld) == ctx.threads[0].locals[k].consumed_fields.end())
                ctx.threads[0].locals[k].consumed_fields.push_back(fld);
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

          case MIR::Statement::StorageLoop:
            analyse_storage_loop(ctx, mir, statement);
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

    auto arg = mir.args_beg;
    for(auto &parm : mir.fx.parameters())
    {
      if (is_reference_type(decl_cast<ParmVarDecl>(parm)->type) && !is_const_reference(ctx, mir.locals[arg]))
      {
        ctx.threads[0].locals[arg].live = true;

        switch (ctx.state(arg))
        {
          case State::ok:
            break;

          case State::dangling:
            ctx.diag.error("potentially dangling output value", mir.fx.fn, parm->loc());
            break;

          case State::consumed:
            if (!is_rvalue_reference(ctx, mir.locals[arg]) && !has_consume(ctx, notations, parm))
              ctx.diag.warn("missing consume annotation", mir.fx.fn, parm->loc());
            break;

          case State::poisoned:
//            if (!is_rvalue_reference(ctx, mir.locals[arg]) && !has_poison(ctx, notations, parm))
//              ctx.diag.warn("missing poison annotation", mir.fx.fn, parm->loc());
            break;
        }

        ctx.threads[0].locals[arg].live = false;
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
