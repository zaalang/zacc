//
// lifetime.cpp
//
// Copyright (c) 2020-2024 Peter Niekamp. All rights reserved.
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
      for (size_t i = 0; i < min(lhs.size(), rhs.size()); ++i)
      {
        if (lhs[i].index != rhs[i].index)
          return false;
      }

      return lhs.size() <= rhs.size();
    }

    bool is_common_field(vector<MIR::RValue::Field> const &lhs, vector<MIR::RValue::Field> const &rhs)
    {
      for (size_t i = 0; i < min(lhs.size(), rhs.size()); ++i)
      {
        if (lhs[i].index != rhs[i].index)
          return false;
      }

      return true;
    }

    bool is_shared(MIR::local_t arg1, MIR::local_t arg2, int depth = 5)
    {
      for (auto dep1 : threads[0].locals[arg1].depends_upon)
      {
        for (auto dep2: threads[0].locals[arg2].depends_upon)
        {
          if (get<1>(*dep2) == get<1>(*dep1) && is_common_field(get<2>(*dep2), get<2>(*dep1)))
            return true;

          if (depth != 0 && get<2>(*dep2).empty() && is_shared(arg1, get<1>(*dep2), depth - 1))
            return true;
        }
      }

      return false;
    }

    bool is_dangling(MIR::local_t arg, int depth = 5)
    {
      for (auto dep : threads[0].locals[arg].depends_upon)
      {
        if (depth != 0 && is_dangling(get<1>(*dep), depth - 1))
          return true;
      }

      return !threads[0].locals[arg].live;
    }

    bool is_consumed(MIR::local_t arg, int depth = 5)
    {
      if (threads[0].locals[arg].consumed)
      {
        for (auto dep : threads[0].locals[arg].depends_upon)
        {
          for (auto fld : threads[0].locals[get<1>(*dep)].consumed_fields)
            if (get<1>(*fld) == get<1>(*dep) && is_common_field(get<2>(*fld), get<2>(*dep)))
              return true;

          if (depth != 0 && get<2>(*dep).empty() && is_consumed(get<1>(*dep), depth - 1))
            return true;
        }
      }

      return !threads[0].locals[arg].consumed_fields.empty();
    }

    bool is_poisoned(MIR::local_t arg, int depth = 5)
    {
      for (auto dep : threads[0].locals[arg].depends_upon)
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

    MIR::RValue::VariableData const *make_field(MIR::local_t local)
    {
      field_allocator.emplace_back(MIR::RValue::local(MIR::RValue::Ref, local, SourceLocation{}));

      return &field_allocator.back();
    }

    MIR::RValue::VariableData const *make_field(MIR::RValue::VariableData const *base, vector<MIR::RValue::Field>::const_iterator first, vector<MIR::RValue::Field>::const_iterator last)
    {
      if (first == last)
        return base;

      auto &[op, arg, fields, loc] = field_allocator.emplace_back(*base);

      fields.insert(fields.end(), first, last);

      return &field_allocator.back();
    }

    TypeTable &typetable;

    Context(TypeTable &typetable, Diag &diag)
        : diag(diag),
        typetable(typetable)
    {
    }
  };

  struct Cache
  {
    struct entry
    {
      size_t nlocals;
      size_t args_beg;
      size_t args_end;
      vector<std::tuple<MIR::local_t, MIR::RValue::VariableData>> depends;
    };

    static entry const *lookup(FnSig const &fx)
    {
      auto j = cache.find(fx);

      if (j != cache.end())
        return &j->second;

      return nullptr;
    }

    static void commit(FnSig const &fx, entry &&entry)
    {
      cache.emplace(fx, std::move(entry));
    }

    static inline std::unordered_map<FnSig, entry> cache;
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
  Lifetime parse(string_view src, SourceLocation loc)
  {
    Lifetime tok = {};

    if (src.substr(0, 7) == "consume")
    {
      tok.type = Lifetime::consume;
      tok.text = trim(src.substr(8), "( \t)");
    }

    if (src.substr(0, 6) == "borrow")
    {
      tok.type = Lifetime::borrow;
      tok.text = trim(src.substr(7), "( \t)");
    }

    if (src.substr(0, 6) == "depend")
    {
      tok.type = Lifetime::depend;
      tok.text = trim(src.substr(7), "( \t)");

      if (tok.text.substr(0, 1) == "*")
      {
        tok.type = Lifetime::clone;
        tok.text = trim(tok.text.substr(1));

        if (tok.text.find('.') != tok.text.npos)
        {
          tok.type = Lifetime::follow;
        }
      }
    }

    if (src.substr(0, 6) == "poison")
    {
      tok.type = Lifetime::poison;
      tok.text = trim(src.substr(7), "( \t)");
    }

    if (src.substr(0, 6) == "assign")
    {
      tok.type = Lifetime::assign;
      tok.text = trim(src.substr(7), "( \t)");
    }

    if (src.substr(0, 6) == "append")
    {
      tok.type = Lifetime::append;
      tok.text = trim(src.substr(7), "( \t)");
    }

    if (src.substr(0, 7) == "launder")
    {
      tok.type = Lifetime::launder;
      tok.text = trim(src.substr(8), "( \t)");
    }

    if (src.substr(0, 6) == "repose")
    {
      tok.type = Lifetime::repose;
      tok.text = trim(src.substr(7), "( \t)");
    }

    if (src.substr(0, 4) == "swap")
    {
      tok.type = Lifetime::swap;
      tok.text = trim(src.substr(5), "( \t)");
    }

    tok.loc = loc;

    return tok;
  }

  //|///////////////////// annotations //////////////////////////////////////
  vector<Lifetime> annotations(string_view lifetime, SourceLocation loc)
  {
    vector<Lifetime> result;

    auto i = lifetime.find_first_not_of(" \t", 1);

    while (i < lifetime.length() - 1)
    {
      auto j = lifetime.find('(', i);

      for (int indent = 0; j != string_view::npos; )
      {
        if (lifetime[j] == '(')
          indent += 1;

        if (lifetime[j] == ')')
          if (--indent <= 0)
            break;

        j += 1;
      }

      auto annotation = parse(lifetime.substr(i, j - i + 1), SourceLocation { loc.lineno, loc.charpos + int(i) + 8 });

      result.push_back(annotation);

      i = lifetime.find_first_not_of(" \t,", j + 1);
    }

    return result;
  }

  //|///////////////////// has_launder //////////////////////////////////////
  [[maybe_unused]] bool has_launder(Context &ctx, vector<Lifetime> const &annotations, Decl *parm)
  {
    for (auto &annotation : annotations)
    {
      if (annotation.type == Lifetime::launder)
      {
        if (decl_cast<ParmVarDecl>(parm)->name == annotation.text)
          return true;
      }
    }

    return false;
  }

  //|///////////////////// has_consume //////////////////////////////////////
  [[maybe_unused]] bool has_consume(Context &ctx, vector<Lifetime> const &annotations, Decl *parm)
  {
    for (auto &annotation : annotations)
    {
      if (annotation.type == Lifetime::consume)
      {
        if (decl_cast<ParmVarDecl>(parm)->name == annotation.text)
          return true;
      }
    }

    return false;
  }

  //|///////////////////// has_poison ///////////////////////////////////////
  [[maybe_unused]] bool has_poison(Context &ctx, vector<Lifetime> const &annotations, Decl *parm)
  {
    for (auto &annotation : annotations)
    {
      if (annotation.type == Lifetime::poison)
      {
        auto lhs = trim(annotation.text.substr(0, annotation.text.find('.')));

        if (decl_cast<ParmVarDecl>(parm)->name == lhs)
          return true;
      }

  #if 1
      if (annotation.type == Lifetime::swap)
      {
        auto lhs = trim(annotation.text.substr(0, annotation.text.find(',')));
        auto rhs = trim(annotation.text.substr(annotation.text.find(',') + 1));

        if (decl_cast<ParmVarDecl>(parm)->name == lhs || decl_cast<ParmVarDecl>(parm)->name == rhs)
          return true;
      }
  #endif
    }

    return false;
  }

  //|///////////////////// has_repose ///////////////////////////////////////
  [[maybe_unused]] bool has_repose(Context &ctx, vector<Lifetime> const &annotations, Decl *parm1, Decl *parm2)
  {
    for (auto &annotation : annotations)
    {
      if (annotation.type == Lifetime::launder)
      {
        if (decl_cast<ParmVarDecl>(parm1)->name == annotation.text)
          return true;
      }

      if (annotation.type == Lifetime::repose)
      {
        auto lhs = trim(annotation.text.substr(0, annotation.text.find(',')));
        auto rhs = trim(annotation.text.substr(annotation.text.find(',') + 1));

        if (decl_cast<ParmVarDecl>(parm1)->name == lhs && decl_cast<ParmVarDecl>(parm2)->name == rhs)
          return true;
      }
  #if 1
      if (annotation.type == Lifetime::swap)
      {
        auto lhs = trim(annotation.text.substr(0, annotation.text.find(',')));
        auto rhs = trim(annotation.text.substr(annotation.text.find(',') + 1));

        if (decl_cast<ParmVarDecl>(parm1)->name == lhs && decl_cast<ParmVarDecl>(parm2)->name == rhs)
          return true;

        if (decl_cast<ParmVarDecl>(parm1)->name == rhs && decl_cast<ParmVarDecl>(parm2)->name == lhs)
          return true;
      }
  #endif
    }

    return false;
  }

  //|///////////////////// has_depend ///////////////////////////////////////
  [[maybe_unused]] bool has_depend(Context &ctx, vector<Lifetime> const &annotations)
  {
    for (auto &annotation : annotations)
    {
      if (annotation.type == Lifetime::depend || annotation.type == Lifetime::clone || annotation.type == Lifetime::follow)
        return true;
    }

    return false;
  }

  //|///////////////////// varname //////////////////////////////////////////
  [[maybe_unused]] std::string_view varname(MIR const &mir, MIR::local_t arg)
  {
    for (auto &info : mir.varinfos)
    {
      if (info.local == arg)
        return info.vardecl->name->sv();
    }

    return "";
  }

  //|///////////////////// is_reference /////////////////////////////////////
  [[maybe_unused]] bool is_reference(Context &ctx, MIR::Local const &local)
  {
    if (local.flags & MIR::Local::Reference)
    {
      return true;
    }

    if (is_reference_type(local.type))
    {
      return true;
    }

    return false;
  }

  //|///////////////////// is_const_reference ///////////////////////////////
  [[maybe_unused]] bool is_const_reference(Context &ctx, MIR::Local const &local)
  {
    if (local.flags & MIR::Local::Reference)
    {
      return (local.flags & MIR::Local::Const);
    }

    if (is_reference_type(local.type))
    {
      switch (auto type = remove_reference_type(local.type); type->klass())
      {
        case Type::Const:
          return true;

        case Type::QualArg:
          return (type_cast<QualArgType>(type)->qualifiers & QualArgType::Const);

        default:
          return false;
      }
    }

    return false;
  }

  //|///////////////////// is_mutable_reference /////////////////////////////
  [[maybe_unused]] bool is_mutable_reference(Context &ctx, MIR::Local const &local)
  {
    if (local.flags & MIR::Local::Reference)
    {
      return !(local.flags & MIR::Local::Const);
    }

    if (is_reference_type(local.type))
    {
      switch (auto type = remove_reference_type(local.type); type->klass())
      {
        case Type::Const:
          return false;

        case Type::QualArg:
          return !(type_cast<QualArgType>(type)->qualifiers & QualArgType::Const);

        default:
          return true;
      }
    }

    return false;
  }

  //|///////////////////// is_rvalue_reference //////////////////////////////
  [[maybe_unused]] bool is_rvalue_reference(Context &ctx, MIR::Local const &local)
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

  //|///////////////////// find_arg /////////////////////////////////////////
  pair<ParmVarDecl*, size_t> find_arg(Context &ctx, FnSig const &callee, string_view name)
  {
    size_t arg = 0;

    for (auto &parm : callee.parameters())
    {
      if (decl_cast<ParmVarDecl>(parm)->name == name)
        return { decl_cast<ParmVarDecl>(parm), arg };

      arg += 1;
    }

    return { nullptr, 0 };
  }

  //|///////////////////// depends //////////////////////////////////////////
  void depends(Context &ctx, MIR const &mir, MIR::local_t arg, MIR::RValue::VariableData const *dep)
  {
    if (get<1>(*dep) == arg)
      return;

    for (auto entry : ctx.threads[0].locals[arg].depends_upon)
    {
      if (get<0>(*entry) == get<0>(*dep) && get<1>(*entry) == get<1>(*dep) && get<2>(*entry) == get<2>(*dep))
        return;
    }

    ctx.threads[0].locals[arg].depends_upon.push_back(dep);
  }

  void depends(Context &ctx, MIR const &mir, MIR::local_t arg, vector<MIR::RValue::VariableData const *> const &deps)
  {
    for (auto dep : deps)
      depends(ctx, mir, arg, dep);
  }

  //|///////////////////// consume //////////////////////////////////////////
  void consume(Context &ctx, MIR const &mir, MIR::local_t arg, MIR::RValue::VariableData const *dep)
  {
    ctx.threads[0].locals[get<1>(*dep)].consumed_fields.push_back(dep);

    if (!ctx.threads[0].locals[get<1>(*dep)].consumed)
    {
      ctx.threads[0].locals[get<1>(*dep)].consumed = true;

      if (get<2>(*dep).empty())
      {
        for (auto dep2 : ctx.threads[0].locals[get<1>(*dep)].depends_upon)
          consume(ctx, mir, get<1>(*dep), dep2);
      }
    }

#if 0
    cout << "consume: " << *dep << endl;
    for (auto fld : ctx.threads[0].locals[get<1>(*dep)].consumed_fields)
      cout << "       : " << *fld << endl;
#endif
  }

  //|///////////////////// poison ///////////////////////////////////////////
  void poison(Context &ctx, MIR const &mir, MIR::local_t arg, MIR::RValue::VariableData const *dep)
  {
#if 0
    cout << "poison: " << *dep << endl;
#endif

    if (get<1>(*ctx.threads[0].locals[arg].depends_upon.back()) >= mir.locals.size() && dep != ctx.threads[0].locals[arg].depends_upon.back())
      return;

    ctx.threads[0].locals[get<1>(*dep)].toxic = true;

    for (auto &local : ctx.threads[0].locals)
    {
      if (!local.live)
        continue;

      if (local.immune)
        continue;

      if (local.depends_upon.empty() || (get<1>(*local.depends_upon.back()) >= mir.locals.size() + 3*mir.args_end && local.depends_upon.back() == dep))
        continue;

      for (auto fld : local.depends_upon)
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

  //|///////////////////// launder //////////////////////////////////////////
  void launder(Context &ctx, MIR const &mir, MIR::local_t arg, MIR::RValue::VariableData const *dep)
  {
#if 0
    cout << "launder: " << *dep << endl;
#endif

    auto &consumed_fields = ctx.threads[0].locals[get<1>(*dep)].consumed_fields;

    for (auto i = consumed_fields.begin(); i != consumed_fields.end(); )
    {
      if (ctx.is_super_field(get<2>(*dep), get<2>(**i)))
        i = consumed_fields.erase(i);
      else
        ++i;
    }

    if (consumed_fields.empty())
    {
      if (ctx.threads[0].locals[get<1>(*dep)].consumed)
      {
        ctx.threads[0].locals[get<1>(*dep)].consumed = false;

        if (get<2>(*dep).empty())
        {
          for (auto dep2 : ctx.threads[0].locals[get<1>(*dep)].depends_upon)
            launder(ctx, mir, get<1>(*dep), dep2);
        }
      }
    }

    if (get<2>(*dep).empty())
    {
      ctx.threads[0].locals[get<1>(*dep)].consumed = false;
      ctx.threads[0].locals[get<1>(*dep)].poisoned = false;
      ctx.threads[0].locals[get<1>(*dep)].toxic = false;
      ctx.threads[0].locals[get<1>(*dep)].depends_upon.clear();
      ctx.threads[0].locals[get<1>(*dep)].consumed_fields.clear();
    }

    if (ctx.threads[0].locals[arg].immune)
      ctx.threads[0].locals[arg].poisoned = false;

    ctx.threads[0].locals[arg].consumed = false;
  }

  //|///////////////////// setup ////////////////////////////////////////////
  void setup(Context &ctx, MIR const &mir, Lifetime const &annotation)
  {
    switch (annotation.type)
    {
      case Lifetime::consume:
      case Lifetime::borrow:
      case Lifetime::clone:
      case Lifetime::depend:
      case Lifetime::poison:
      case Lifetime::assign:
      case Lifetime::append:
      case Lifetime::follow:
      case Lifetime::launder:
      case Lifetime::swap:
        break;

      case Lifetime::repose: {

          auto lhs = trim(annotation.text.substr(0, annotation.text.find(',')));
          auto rhs = trim(annotation.text.substr(annotation.text.find(',') + 1));

          auto [parm1, arg1] = find_arg(ctx, mir.fx, lhs);
          auto [parm2, arg2] = find_arg(ctx, mir.fx, rhs);

          if (parm1 && parm2)
          {
            arg1 += mir.args_beg;
            arg2 += mir.args_beg;

            if (is_reference_type(decl_cast<ParmVarDecl>(parm1)->type))
            {
              for (auto dep : ctx.threads[0].locals[arg1].depends_upon)
                depends(ctx, mir, get<1>(*dep), ctx.make_field(arg2 + mir.locals.size()));
            }
            else
            {
              depends(ctx, mir, arg1, ctx.make_field(arg2 + mir.locals.size()));
            }
          }
          else
          {
            ctx.diag.error("unknown repose parameter", mir.fx.fn, annotation.loc);
          }

          break;
        }

      case Lifetime::none:
        break;

      default:
        ctx.diag.error("unknown lifetime annotation", mir.fx.fn, annotation.loc);
    }
  }

  //|///////////////////// prepare //////////////////////////////////////////
  void prepare(Context &ctx, MIR const &mir, vector<Lifetime> const &annotations, MIR::local_t dst, FnSig const &callee, vector<MIR::local_t> const &args, SourceLocation loc)
  {
    if (callee.fn->name == Ident::op_assign)
    {
      for (auto dep : ctx.threads[0].locals[args[0]].depends_upon)
        launder(ctx, mir, args[0], dep);
    }

    for (auto &annotation : annotations)
    {
      if (annotation.type == Lifetime::launder)
      {
        auto lhs = trim(annotation.text.substr(0, annotation.text.find('.')));

        if (auto [parm, arg] = find_arg(ctx, callee, lhs); parm)
        {
          if (lhs == annotation.text)
          {
            for (auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
              launder(ctx, mir, args[arg], dep);
          }
          else
          {
            auto rhs = trim(annotation.text.substr(annotation.text.find('.') + 1));

            Decl *target = nullptr;
            vector<MIR::RValue::Field> subfields;
            for (auto type = mir.locals[args[arg]].type; is_tag_type(type); )
            {
              auto tagtype = type_cast<TagType>(type);

              for (auto &decl : tagtype->fieldvars)
              {
                if (decl_cast<VarDecl>(decl)->name == rhs)
                {
                  target = decl;
                  subfields.push_back(MIR::RValue::Field{ MIR::RValue::Ref, size_t(&decl - &tagtype->fieldvars.front()) });

                  for (auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
                    launder(ctx, mir, args[arg], ctx.make_field(dep, subfields.begin(), subfields.end()));

                  break;
                }
              }

              if (target)
                break;

              if (!is_tag_type(type) || !decl_cast<TagDecl>(tagtype->decl)->basetype)
                break;

              type = tagtype->fields[0];
              subfields.push_back(MIR::RValue::Field{ MIR::RValue::Ref, 0 });
            }

            if (!target)
              ctx.diag.error("unknown launder subfield", callee.fn, annotation.loc);;
          }
        }
        else
        {
          ctx.diag.error("unknown launder parameter", callee.fn, annotation.loc);
        }
      }
    }
  }

  //|///////////////////// apply ////////////////////////////////////////////
  void apply(Context &ctx, MIR const &mir, Lifetime const &annotation, MIR::local_t dst, FnSig const &callee, vector<MIR::local_t> const &args, SourceLocation loc)
  {
    switch (annotation.type)
    {
      case Lifetime::consume: {

        auto lhs = trim(annotation.text.substr(0, annotation.text.find('.')));

        if (auto [parm, arg] = find_arg(ctx, callee, lhs); parm)
        {
          if (lhs == annotation.text)
          {
            for (auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
              consume(ctx, mir, args[arg], dep);
          }
          else
          {
            auto rhs = trim(annotation.text.substr(annotation.text.find('.') + 1));

            Decl *target = nullptr;
            vector<MIR::RValue::Field> subfields;
            for (auto type = mir.locals[args[arg]].type; is_tag_type(type); )
            {
              auto tagtype = type_cast<TagType>(type);

              for (auto &decl : tagtype->fieldvars)
              {
                if (decl_cast<VarDecl>(decl)->name == rhs)
                {
                  target = decl;
                  subfields.push_back(MIR::RValue::Field{ MIR::RValue::Ref, size_t(&decl - &tagtype->fieldvars.front()) });

                  for (auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
                    consume(ctx, mir, args[arg], ctx.make_field(dep, subfields.begin(), subfields.end()));

                  break;
                }
              }

              if (target)
                break;

              if (!is_tag_type(type) || !decl_cast<TagDecl>(tagtype->decl)->basetype)
                break;

              type = tagtype->fields[0];
              subfields.push_back(MIR::RValue::Field{ MIR::RValue::Ref, 0 });
            }

            if (!target)
              ctx.diag.error("unknown consume subfield", callee.fn, annotation.loc);;
          }
        }
        else
        {
          ctx.diag.error("unknown consume parameter", callee.fn, annotation.loc);
        }

        break;
      }

      case Lifetime::borrow: {

        if (auto [parm, arg] = find_arg(ctx, callee, annotation.text); parm)
        {
          for (auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
            ctx.threads[0].locals[get<1>(*dep)].consumed = true;

          ctx.threads[0].locals[dst].borrowed = args[arg];
        }
        else
        {
          ctx.diag.error("unknown borrow parameter", callee.fn, annotation.loc);
        }

        break;
      }

      case Lifetime::clone: {

        if (auto [parm, arg] = find_arg(ctx, callee, annotation.text); parm)
        {
          if (is_pack_type(decl_cast<ParmVarDecl>(parm)->type) || is_reference_type(decl_cast<ParmVarDecl>(parm)->type))
          {
            for (auto src : ctx.threads[0].locals[args[arg]].depends_upon)
              for (auto dep : ctx.threads[0].locals[get<1>(*src)].depends_upon)
                depends(ctx, mir, dst, ctx.make_field(dep, get<2>(*src).begin(), get<2>(*src).end()));
          }
          else
          {
            depends(ctx, mir, dst, ctx.threads[0].locals[args[arg]].depends_upon);
          }
        }
        else
        {
          ctx.diag.error("unknown clone parameter", callee.fn, annotation.loc);
        }

        break;
      }

      case Lifetime::depend: {

        auto lhs = trim(annotation.text.substr(0, annotation.text.find('.')));

        if (auto [parm, arg] = find_arg(ctx, callee, lhs); parm)
        {
          if (lhs == annotation.text)
          {
            depends(ctx, mir, dst, ctx.threads[0].locals[args[arg]].depends_upon);
          }
          else
          {
            auto rhs = trim(annotation.text.substr(annotation.text.find('.') + 1));

            Decl *target = nullptr;
            vector<MIR::RValue::Field> subfields;
            for (auto type = mir.locals[args[arg]].type; is_tag_type(type); )
            {
              auto tagtype = type_cast<TagType>(type);

              for (auto &decl : tagtype->fieldvars)
              {
                if (decl_cast<VarDecl>(decl)->name == rhs)
                {
                  target = decl;
                  subfields.push_back(MIR::RValue::Field{ MIR::RValue::Ref, size_t(&decl - &tagtype->fieldvars.front()) });

                  for (auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
                    depends(ctx, mir, dst, ctx.make_field(dep, subfields.begin(), subfields.end()));

                  break;
                }
              }

              if (target)
                break;

              if (!is_tag_type(type) || !decl_cast<TagDecl>(tagtype->decl)->basetype)
                break;

              type = tagtype->fields[0];
              subfields.push_back(MIR::RValue::Field{ MIR::RValue::Ref, 0 });
            }

            if (!target)
              ctx.diag.error("unknown depend subfield", callee.fn, annotation.loc);;
          }
        }
        else
        {
          if (lhs != "")
            ctx.diag.error("unknown depend parameter", callee.fn, annotation.loc);
        }

        break;
      }

      case Lifetime::poison: {

        auto lhs = trim(annotation.text.substr(0, annotation.text.find('.')));

        if (auto [parm, arg] = find_arg(ctx, callee, lhs); parm)
        {
          if (lhs == annotation.text)
          {
            for (auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
              poison(ctx, mir, args[arg], dep);
          }
          else
          {
            auto rhs = trim(annotation.text.substr(annotation.text.find('.') + 1));

            Decl *target = nullptr;
            vector<MIR::RValue::Field> subfields;
            for (auto type = mir.locals[args[arg]].type; is_tag_type(type); )
            {
              auto tagtype = type_cast<TagType>(type);

              for (auto &decl : tagtype->fieldvars)
              {
                if (decl_cast<VarDecl>(decl)->name == rhs)
                {
                  target = decl;
                  subfields.push_back(MIR::RValue::Field{ MIR::RValue::Ref, size_t(&decl - &tagtype->fieldvars.front()) });

                  for (auto dep : ctx.threads[0].locals[args[arg]].depends_upon)
                    poison(ctx, mir, args[arg], ctx.make_field(dep, subfields.begin(), subfields.end()));

                  break;
                }
              }

              if (target)
                break;

              if (!is_tag_type(type) || !decl_cast<TagDecl>(tagtype->decl)->basetype)
                break;

              type = tagtype->fields[0];
              subfields.push_back(MIR::RValue::Field{ MIR::RValue::Ref, 0 });
            }

            if (!target)
              ctx.diag.error("unknown poison subfield", callee.fn, annotation.loc);;
          }
        }
        else
        {
          ctx.diag.error("unknown poison parameter", callee.fn, annotation.loc);
        }

        break;
      }

      case Lifetime::assign: {

        auto lhs = trim(annotation.text.substr(0, annotation.text.find(',')));

        if (auto [parm, arg] = find_arg(ctx, callee, lhs); parm)
        {
          auto rhs = parse(trim(annotation.text.substr(annotation.text.find(',') + 1)), annotation.loc);

          for (auto dst : ctx.threads[0].locals[args[arg]].depends_upon)
          {
            ctx.threads[0].locals[get<1>(*dst)].consumed = false;
            ctx.threads[0].locals[get<1>(*dst)].poisoned = false;
            ctx.threads[0].locals[get<1>(*dst)].toxic = false;
            ctx.threads[0].locals[get<1>(*dst)].depends_upon.clear();
            ctx.threads[0].locals[get<1>(*dst)].consumed_fields.clear();

            apply(ctx, mir, rhs, get<1>(*dst), callee, args, loc);
          }
        }
        else
        {
          ctx.diag.error("unknown assign parameter", callee.fn, annotation.loc);
        }

        break;
      }

      case Lifetime::append: {

        auto lhs = trim(annotation.text.substr(0, annotation.text.find(',')));

        if (auto [parm, arg] = find_arg(ctx, callee, lhs); parm)
        {
          auto rhs = parse(trim(annotation.text.substr(annotation.text.find(',') + 1)), annotation.loc);

          for (auto dst : ctx.threads[0].locals[args[arg]].depends_upon)
            apply(ctx, mir, rhs, get<1>(*dst), callee, args, loc);
        }
        else
        {
          ctx.diag.error("unknown append parameter", callee.fn, annotation.loc);
        }

        break;
      }

      case Lifetime::follow: {

        auto lhs = trim(annotation.text.substr(0, annotation.text.find('.')));

        if (auto [parm, arg] = find_arg(ctx, callee, lhs); parm)
        {
          auto rhs = trim(annotation.text.substr(annotation.text.find('.') + 1));

          Lifetime target;
          target.text = lhs;
          target.loc = annotation.loc;

          if (auto j = rhs.find(','); j != std::string_view::npos)
          {
            target.text = trim(rhs.substr(j + 1));

            rhs = trim(rhs.substr(0, j));
          }

          auto type = mir.locals[args[arg]].type;

          while (is_tag_type(type))
          {
            auto tagtype = type_cast<TagType>(type);

            for (auto decl : tagtype->decls)
            {
              if (decl->kind() == Decl::Function && decl_cast<FunctionDecl>(decl)->name == rhs)
              {
                target.type = Lifetime::clone;

                for (auto &annotation : decl_cast<FunctionDecl>(decl)->lifetimes)
                {
                  switch (annotation.type)
                  {
                    case Lifetime::clone:
                    case Lifetime::depend:
                      target.type = annotation.type;
                      break;

                    default:
                      continue;
                  }

                  break;
                }

                break;
              }

              if (decl->kind() == Decl::FieldVar && decl_cast<VarDecl>(decl)->name == rhs)
              {
                target.type = Lifetime::clone;

                break;
              }
            }

            if (target.type != Lifetime::unknown)
              break;

            if (!is_tag_type(type) || !decl_cast<TagDecl>(tagtype->decl)->basetype)
              break;

            type = tagtype->fields[0];
          }

          if (is_builtin_type(type) || is_pointer_type(type) || is_string_type(type) || is_array_type(type))
          {
            target.type = Lifetime::clone;

            if (rhs == "[]")
              target.type = Lifetime::depend;

            if (is_array_type(type) && rhs == "data")
              target.type = Lifetime::depend;
          }

          apply(ctx, mir, target, dst, callee, args, loc);
        }
        else
        {
          ctx.diag.error("unknown follow parameter", callee.fn, annotation.loc);
        }

        break;
      }

      case Lifetime::swap: {

        auto lhs = trim(annotation.text.substr(0, annotation.text.find(',')));
        auto rhs = trim(annotation.text.substr(annotation.text.find(',') + 1));

        auto [parm1, arg1] = find_arg(ctx, callee, lhs);
        auto [parm2, arg2] = find_arg(ctx, callee, rhs);

        if (parm1 && parm2)
        {
          auto &src = ctx.threads[0].locals[args[arg1]].depends_upon;
          auto &dst = ctx.threads[0].locals[args[arg2]].depends_upon;

          for (size_t i = 0, end = std::min(src.size(), dst.size()); i != end; ++i)
          {
            swap(ctx.threads[0].locals[get<1>(*src[i])].depends_upon, ctx.threads[0].locals[get<1>(*dst[i])].depends_upon);
          }
        }
        else
        {
          ctx.diag.error("unknown swap parameter", callee.fn, annotation.loc);
        }

        break;
      }

      case Lifetime::launder:
        break;

      case Lifetime::repose:
        break;

      case Lifetime::none:
        break;

      default:
        ctx.diag.error("unknown lifetime annotation", callee.fn, annotation.loc);
    }
  }

  //|///////////////////// apply ////////////////////////////////////////////
  void apply(Context &ctx, MIR const &mir, Cache::entry const *entry, MIR::local_t dst, FnSig const &callee, vector<MIR::local_t> const &args, SourceLocation loc)
  {
    if (entry->depends.empty())
      return;

    auto parms = vector<ParmVarDecl*>();
    for (auto &parm : callee.parameters())
      parms.push_back(decl_cast<ParmVarDecl>(parm));

    for (auto &[lhs, depend] : entry->depends)
    {
      auto op = get<0>(depend);
      auto arg = get<1>(depend);
      auto &fields = get<2>(depend);

      if (arg < entry->args_beg || arg >= entry->args_end)
        continue;

      auto rhs = args[arg - entry->args_beg];
      auto firstfield = fields.begin();

      if (is_pack_type(parms[arg - entry->args_beg]->type))
      {
        if (fields.empty())
          continue;

        for (auto dep : ctx.threads[0].locals[rhs].depends_upon)
          rhs = get<1>(*dep);

        for (auto block = ctx.threads[0].block, statement = mir.blocks[block].statements.size() - 1;; )
        {
          auto &src = mir.blocks[block].statements[statement].src;

          if (src.kind() == MIR::RValue::Variable)
          {
            auto &[op, arg, fields, loc] = src.get<MIR::RValue::Variable>();

            if (arg == rhs && fields.size() == 1 && fields[0].index == firstfield->index)
            {
              rhs = mir.blocks[block].statements[statement].dst + 1;

              break;
            }
          }

          if (statement == 0)
          {
            while (statement == 0 && block != 0)
            {
              block -= 1;
              statement = mir.blocks[block].statements.size();
            }

            if (statement == 0)
              break;
          }

          statement -= 1;
        }

        op = static_cast<MIR::RValue::Op>(op - 1);

        ++firstfield;
      }

      if (lhs == 0)
      {
        if (has_depend(ctx, callee.fn->lifetimes))
          continue;

        switch (op)
        {
          case MIR::RValue::Ref:
            break;

          case MIR::RValue::Val:
            for (auto dep : ctx.threads[0].locals[rhs].depends_upon)
              depends(ctx, mir, dst, ctx.make_field(dep, firstfield, fields.end()));
            break;

          case MIR::RValue::Fer:
            for (auto ref : ctx.threads[0].locals[rhs].depends_upon)
              for (auto dep : ctx.threads[0].locals[get<1>(*ref)].depends_upon)
                depends(ctx, mir, dst, ctx.make_field(ctx.make_field(dep, get<2>(*ref).begin(), get<2>(*ref).end()), firstfield, fields.end()));
            break;

          case MIR::RValue::Idx:
            assert(false);
            break;
        }
      }

      if (lhs >= entry->args_beg && lhs < entry->args_end)
      {
        auto arg = lhs - entry->args_beg;

        if (is_reference_type(parms[arg]->type) && !is_const_reference(parms[arg]->type))
        {
          switch (op)
          {
            case MIR::RValue::Ref:
              break;

            case MIR::RValue::Val:
              for (auto dst : ctx.threads[0].locals[args[arg]].depends_upon)
                for (auto dep : ctx.threads[0].locals[rhs].depends_upon)
                  depends(ctx, mir, get<1>(*dst), ctx.make_field(dep, firstfield, fields.end()));
              break;

            case MIR::RValue::Fer:
              for (auto dst : ctx.threads[0].locals[args[arg]].depends_upon)
                for (auto ref : ctx.threads[0].locals[rhs].depends_upon)
                  if (get<1>(*ref) != get<1>(*dst))
                    for (auto dep : ctx.threads[0].locals[get<1>(*ref)].depends_upon)
                      depends(ctx, mir, get<1>(*dst), ctx.make_field(ctx.make_field(dep, get<2>(*ref).begin(), get<2>(*ref).end()), firstfield, fields.end()));
              break;

            case MIR::RValue::Idx:
              assert(false);
              break;
          }
        }
      }
    }
  }

  //|///////////////////// record ///////////////////////////////////////////
  void record(Context &ctx, MIR const &mir)
  {
    auto entry = Cache::entry();

    entry.args_beg = mir.args_beg;
    entry.args_end = mir.args_end;
    entry.nlocals = mir.locals.size();

    for (auto dep : ctx.threads[0].locals[0].depends_upon)
    {
      auto &[op, arg, fields, loc] = *dep;

      if (arg >= mir.locals.size() && arg < mir.locals.size() + mir.args_end && arg - mir.locals.size() != 0)
      {
        entry.depends.emplace_back(0, MIR::RValue::field(MIR::RValue::Val, arg - mir.locals.size(), fields, loc));
      }

      if (arg >= mir.locals.size() + 1*mir.args_end && arg < mir.locals.size() + 2*mir.args_end && arg - mir.locals.size() - 1*mir.args_end != 0)
      {
        entry.depends.emplace_back(0, MIR::RValue::field(MIR::RValue::Fer, arg - mir.locals.size() - 1*mir.args_end, fields, loc));
      }

      if (arg >= mir.locals.size() + 2*mir.args_end && arg < mir.locals.size() + 3*mir.args_end && arg - mir.locals.size() - 2*mir.args_end != 0)
      {
        entry.depends.emplace_back(0, MIR::RValue::field(MIR::RValue::Idx, arg - mir.locals.size() - 2*mir.args_end, fields, loc));
      }
    }

    for (auto i = mir.args_beg; i != mir.args_end; ++i)
    {
      for (auto dep : ctx.threads[0].locals[mir.locals.size() + i].depends_upon)
      {
        auto &[op, arg, fields, loc] = *dep;

        if (arg >= mir.locals.size() && arg < mir.locals.size() + mir.args_end && arg - mir.locals.size() != i)
        {
          entry.depends.emplace_back(i, MIR::RValue::field(MIR::RValue::Val, arg - mir.locals.size(), fields, loc));
        }

        if (arg >= mir.locals.size() + 1*mir.args_end && arg < mir.locals.size() + 2*mir.args_end && arg - mir.locals.size() - 1*mir.args_end != i)
        {
          entry.depends.emplace_back(i, MIR::RValue::field(MIR::RValue::Fer, arg - mir.locals.size() - 1*mir.args_end, fields, loc));
        }

        if (arg >= mir.locals.size() + 2*mir.args_end && arg < mir.locals.size() + 3*mir.args_end && arg - mir.locals.size() - 2*mir.args_end != i)
        {
          entry.depends.emplace_back(i, MIR::RValue::field(MIR::RValue::Idx, arg - mir.locals.size() - 2*mir.args_end, fields, loc));
        }
      }
    }

#if 0
    for (auto i = entry.depends.size(); i > 1; --i)
    {
      auto lhs = entry.depends.begin() + (i - 1);

      auto j = std::any_of(entry.depends.begin(), lhs, [&](auto &rhs) {
        return get<0>(*lhs) == get<0>(rhs) && get<0>(get<1>(*lhs)) == get<0>(get<1>(rhs)) && get<1>(get<1>(*lhs)) == get<1>(get<1>(rhs)) && ctx.is_super_field(get<2>(get<1>(*lhs)), get<2>(get<1>(rhs)));
      });

      if (j)
        entry.depends.erase(lhs);
    }
#endif

#if 0
    cout << "record " << mir.fx.fn->name->str() << " (" << get_module(mir.fx.fn)->file() << ":" << mir.fx.fn->loc() << ")" << endl;

    for (auto &dep : entry.depends)
    {
      auto &[op, arg, fields, loc] = get<1>(dep);

      cout << "  " << get<0>(dep) << ": " << varname(mir, arg) << " " << get<1>(dep) << endl;
    }
#endif

    Cache::commit(mir.fx, std::move(entry));
  }

  //|///////////////////// analyse_assign_variable //////////////////////////
  void analyse_assign_variable(Context &ctx, MIR const &mir, MIR::local_t dst, MIR::RValue::VariableData const &variable)
  {
    auto &[op, arg, fields, loc] = variable;

    if ((fields.empty() && op == MIR::RValue::Fer) || (!fields.empty() && fields[0].op == MIR::RValue::Val))
    {
      if (ctx.is_dangling(arg))
        ctx.diag.error("potentially dangling dereference", mir.fx.fn, loc);
    }

    if ((fields.empty() && op == MIR::RValue::Fer) || (!fields.empty() && fields[0].op == MIR::RValue::Val))
    {
      if (ctx.is_poisoned(arg))
        ctx.diag.error("potentially poisoned dereference", mir.fx.fn, loc);
    }

    if (op != MIR::RValue::Ref)
    {
      for (auto fld : ctx.threads[0].locals[arg].consumed_fields)
        if (ctx.is_common_field(get<2>(*fld), fields))
          ctx.diag.error("potentially consumed reference", mir.fx.fn, loc);
    }

    if ((mir.locals[dst].flags & MIR::Local::Reference) || is_pointference_type(mir.locals[dst].type))
    {
      switch (op)
      {
        case MIR::RValue::Ref:
          ctx.threads[0].locals[dst].depends_upon.push_back(&variable);
          ctx.threads[0].locals[dst].immune = true;
          break;

        case MIR::RValue::Val:
          for (auto dep : ctx.threads[0].locals[arg].depends_upon)
            ctx.threads[0].locals[dst].depends_upon.push_back(ctx.make_field(dep, fields.begin(), fields.end()));
          ctx.threads[0].locals[dst].immune = ctx.threads[0].locals[arg].immune;
          break;

        case MIR::RValue::Fer:
          for (auto src : ctx.threads[0].locals[arg].depends_upon)
            for (auto dep : ctx.threads[0].locals[get<1>(*src)].depends_upon)
              ctx.threads[0].locals[dst].depends_upon.push_back(dep);
          break;

        case MIR::RValue::Idx:
          assert(false);
          break;
      }

      if (any_of(fields.begin(), fields.end(), [](auto k){ return k.op == MIR::RValue::Val; }))
      {
        ctx.threads[0].locals[dst].depends_upon.clear();

        switch (op)
        {
          case MIR::RValue::Ref:
            for (auto dep : ctx.threads[0].locals[arg].depends_upon)
              ctx.threads[0].locals[dst].depends_upon.push_back(ctx.make_field(dep, fields.begin(), fields.end()));
            ctx.threads[0].locals[dst].immune = ctx.threads[0].locals[arg].immune;
            break;

          case MIR::RValue::Val:
            for (auto src : ctx.threads[0].locals[arg].depends_upon)
              for (auto dep : ctx.threads[0].locals[get<1>(*src)].depends_upon)
                ctx.threads[0].locals[dst].depends_upon.push_back(ctx.make_field(ctx.make_field(dep, get<2>(*src).begin(), get<2>(*src).end()), fields.begin(), fields.end()));
            ctx.threads[0].locals[dst].immune = false;
            break;

          case MIR::RValue::Fer:
            for (auto src : ctx.threads[0].locals[arg].depends_upon)
              for (auto dep1 : ctx.threads[0].locals[get<1>(*src)].depends_upon)
                for (auto dep2 : ctx.threads[0].locals[get<1>(*dep1)].depends_upon)
                  ctx.threads[0].locals[dst].depends_upon.push_back(ctx.make_field(dep2, fields.begin(), fields.end()));
            break;

          case MIR::RValue::Idx:
            assert(false);
            break;
        }
      }

      ctx.threads[0].locals[dst].poisoned = ctx.threads[0].locals[arg].poisoned;
      ctx.threads[0].locals[dst].consumed = ctx.threads[0].locals[arg].consumed;
    }

    if (mir.locals[dst].flags & MIR::Local::MoveRef)
    {
      ctx.threads[0].locals[arg].consumed = true;

      if (fields.size() != 0 && op != MIR::RValue::Ref)
        ctx.threads[0].locals[arg].consumed_fields.push_back(&variable);
    }

    if (is_reference_type(mir.locals[dst].type))
    {
      auto arg = ctx.threads[0].locals.size();

      for (auto &thread : ctx.threads)
        thread.locals.push_back(Context::Storage());

      for (auto &thread : ctx.threads)
        thread.locals[arg].live = true;

      ctx.threads[0].locals[dst].depends_upon.push_back(ctx.make_field(arg));
    }
  }

  //|///////////////////// analyse_call /////////////////////////////////////
  void analyse_call(Context &ctx, MIR const &mir, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (callee.fn->flags & FunctionDecl::Destructor)
      return;

    auto &notations = callee.fn->lifetimes;

    prepare(ctx, mir, notations, dst, callee, args, loc);

    for (auto const &[parm, arg] : zip(callee.parameters(), args))
    {
      switch (ctx.state(arg))
      {
        case State::ok:
          break;

        case State::dangling:
          ctx.diag.error("potentially dangling variable access", mir.fx.fn, loc);
          break;

        case State::consumed:
          if ((mir.fx.fn->flags & (FunctionDecl::Safe | FunctionDecl::Unsafe)) == 0)
            ctx.diag.error("potentially consumed variable access", mir.fx.fn, loc);
          break;

        case State::poisoned:
          ctx.diag.error("potentially poisoned variable access", mir.fx.fn, loc);
          break;
      }

      if (callee.fn->flags & FunctionDecl::Lifetimed)
      {
        if (is_reference_type(decl_cast<ParmVarDecl>(parm)->type) && !is_const_reference(decl_cast<ParmVarDecl>(parm)->type) && is_mutable_reference(ctx, mir.locals[arg]))
        {
          for (auto const &[other_parm, other_arg] : zip(callee.parameters(), args))
          {
            if (other_arg == arg)
              continue;

            if (has_repose(ctx, notations, other_parm, parm))
              continue;

            if (ctx.is_shared(arg, other_arg))
              ctx.diag.warn("potentially shared lifetime parameter", mir.fx.fn, loc);
          }
        }
      }
    }

    for (auto const &[parm, arg] : zip(callee.parameters(), args))
    {
      if (mir.locals[arg].flags & MIR::Local::MoveRef)
      {
        for (auto dep : ctx.threads[0].locals[arg].depends_upon)
          consume(ctx, mir, arg, dep);
      }
    }

    if (callee.fn->flags & FunctionDecl::Builtin)
    {
      switch (callee.fn->builtin)
      {
        case Builtin::Assign:
          if (is_pointference_type(mir.locals[dst].type))
            for (auto dst : ctx.threads[0].locals[args[0]].depends_upon)
              depends(ctx, mir, get<1>(*dst), ctx.threads[0].locals[args[1]].depends_upon);
          depends(ctx, mir, dst, ctx.threads[0].locals[args[0]].depends_upon);
          break;

        case Builtin::PreInc:
        case Builtin::PreDec:
          depends(ctx, mir, dst, ctx.threads[0].locals[args[0]].depends_upon);
          break;

        case Builtin::OffsetAdd:
        case Builtin::OffsetSub:
          depends(ctx, mir, dst, ctx.threads[0].locals[args[0]].depends_upon);
          break;

        case Builtin::ArrayData:
        case Builtin::ArrayIndex:
        case Builtin::ArrayBegin:
        case Builtin::ArrayEnd:
          depends(ctx, mir, dst, ctx.threads[0].locals[args[0]].depends_upon);
          break;

        case Builtin::DeRef:
          depends(ctx, mir, dst, ctx.threads[0].locals[args[0]].depends_upon);
          break;

        case Builtin::Range:
          depends(ctx, mir, dst, ctx.threads[0].locals[args[0]].depends_upon);
          depends(ctx, mir, dst, ctx.threads[0].locals[args[1]].depends_upon);
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

            for (auto &arg : args)
            {
              if (is_reference_type(decl_cast<LambdaVarDecl>(lambda->captures[&arg - &args.front()])->type))
              {
                // depend(*arg)
                depends(ctx, mir, dst, ctx.threads[0].locals[arg].depends_upon);
              }
            }
          }
          break;

        case Builtin::Default_Copytructor:
        case Builtin::Array_Copytructor:
        case Builtin::Tuple_Copytructor:
        case Builtin::Tuple_CopytructorEx:
          // depend(*other)
          for (auto src : ctx.threads[0].locals[args[0]].depends_upon)
            for (auto dep : ctx.threads[0].locals[get<1>(*src)].depends_upon)
              depends(ctx, mir, dst, ctx.make_field(dep, get<2>(*src).begin(), get<2>(*src).end()));
          break;

        case Builtin::Default_Assignment:
        case Builtin::Array_Assignment:
        case Builtin::Tuple_Assignment:
        case Builtin::Tuple_AssignmentEx:
          // append(this, depend(*other))
          for (auto dst : ctx.threads[0].locals[args[0]].depends_upon)
            for (auto src : ctx.threads[0].locals[args[1]].depends_upon)
              if (get<1>(*src) != get<1>(*dst))
                for (auto dep : ctx.threads[0].locals[get<1>(*src)].depends_upon)
                  depends(ctx, mir, get<1>(*dst), ctx.make_field(dep, get<2>(*src).begin(), get<2>(*src).end()));
          // depend(this)
          depends(ctx, mir, dst, ctx.threads[0].locals[args[0]].depends_upon);
          break;

        default:
          break;
      }
    }

    for (auto &annotation : notations)
    {
      apply(ctx, mir, annotation, dst, callee, args, loc);
    }

    if (auto entry = Cache::lookup(callee))
    {
      apply(ctx, mir, entry, dst, callee, args, loc);
    }

    //if (callee.fn->name == Ident::op_index || callee.fn->name == Ident::op_deref || is_reference_type(mir.locals[dst].type))
    if (is_reference(ctx, mir.locals[dst]))
    {
      auto arg = ctx.threads[0].locals.size();

      for (auto &thread : ctx.threads)
        thread.locals.push_back(Context::Storage());

      for (auto &thread : ctx.threads)
        thread.locals[arg].live = true;

      ctx.threads[0].locals[dst].depends_upon.push_back(ctx.make_field(arg));
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

    for (auto dep : ctx.threads[0].locals[dst - 1].depends_upon)
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

      for (auto dep : ctx.threads[0].locals[arg].depends_upon)
        ctx.threads[0].locals[get<1>(*dep)].consumed = false;
    }

    //for (auto &local : ctx.threads[0].locals)
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
      for (auto &info : mir.varinfos)
        if (info.local == statement.dst)
          return info.vardecl->loc();
      return mir.fx.fn->loc();
    };

#if 0
    for (auto dep : ctx.threads[0].locals[arg].depends_upon)
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
        if (!(mir.locals[arg].flags & MIR::Local::RValue))
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

    if ((mir.fx.fn->flags & FunctionDecl::DeclType) == FunctionDecl::MatchDecl)
      return;

    if ((mir.fx.fn->flags & FunctionDecl::DeclType) == FunctionDecl::RequiresDecl)
      return;

    auto &notations = mir.fx.fn->lifetimes;

    ctx.add_thread(0, vector<Context::Storage>(mir.locals.size() + 3*mir.args_end));

    auto arg = mir.args_beg;
    for (auto &parm : mir.fx.parameters())
    {
      ctx.threads[0].locals[arg].live = true;

      ctx.threads[0].locals[arg].immune = true;
      ctx.threads[0].locals[mir.locals.size() + arg].live = true;
      ctx.threads[0].locals[arg].depends_upon.push_back(ctx.make_field(mir.locals.size() + arg));

      if (is_pack_type(decl_cast<ParmVarDecl>(parm)->type) || is_reference_type(decl_cast<ParmVarDecl>(parm)->type))
      {
        ctx.threads[0].locals[mir.locals.size() + arg].immune = true;
        ctx.threads[0].locals[mir.locals.size() + mir.args_end + arg].live = true;
        ctx.threads[0].locals[mir.locals.size() + arg].depends_upon.push_back(ctx.make_field(mir.locals.size() + mir.args_end + arg));

        if (is_pack_type(decl_cast<ParmVarDecl>(parm)->type) && is_reference_type(type_cast<PackType>(decl_cast<ParmVarDecl>(parm)->type)->type))
        {
          ctx.threads[0].locals[mir.locals.size() + mir.args_end + arg].immune = true;
          ctx.threads[0].locals[mir.locals.size() + mir.args_end + mir.args_end + arg].live = true;
          ctx.threads[0].locals[mir.locals.size() + mir.args_end + arg].depends_upon.push_back(ctx.make_field(mir.locals.size() + mir.args_end + mir.args_end + arg));
        }
      }

      arg += 1;
    }

    for (auto &[arg, value] : mir.statics)
    {
      ctx.threads[0].locals[arg].live = true;
    }

    ctx.threads[0].locals[0].live = true;

    for (auto &annotation : notations)
    {
      setup(ctx, mir, annotation);
    }

    for (size_t block_id = 0; block_id < mir.blocks.size(); ++block_id)
    {
      auto &block = mir.blocks[block_id];

      auto j = find_if(ctx.threads.begin(), ctx.threads.end(), [&](auto &k) { return k.block == block_id; });

      if (j == ctx.threads.end())
        continue;

      if (j != ctx.threads.begin())
        std::swap(ctx.threads.front(), *j);

      for (size_t i = 1; i != ctx.threads.size(); )
      {
        if (ctx.threads[i].block <= block_id)
        {
          for (size_t k = 0; k < ctx.threads[0].locals.size(); ++k)
          {
            ctx.threads[0].locals[k].live |= ctx.threads[i].locals[k].live;
            ctx.threads[0].locals[k].consumed |= ctx.threads[i].locals[k].consumed;
            ctx.threads[0].locals[k].immune &= ctx.threads[i].locals[k].immune;
            ctx.threads[0].locals[k].poisoned |= ctx.threads[i].locals[k].poisoned;

            for (auto dep : ctx.threads[i].locals[k].depends_upon)
              if (find(ctx.threads[0].locals[k].depends_upon.begin(), ctx.threads[0].locals[k].depends_upon.end(), dep) == ctx.threads[0].locals[k].depends_upon.end())
                ctx.threads[0].locals[k].depends_upon.push_back(dep);

            for (auto fld : ctx.threads[i].locals[k].consumed_fields)
              if (find(ctx.threads[0].locals[k].consumed_fields.begin(), ctx.threads[0].locals[k].consumed_fields.end(), fld) == ctx.threads[0].locals[k].consumed_fields.end())
                ctx.threads[0].locals[k].consumed_fields.push_back(fld);
          }

          ctx.threads.erase(ctx.threads.begin() + i);

          continue;
        }

        ++i;
      }

      for (auto &statement : block.statements)
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
          for (auto &[value, block]: block.terminator.targets)
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

    record(ctx, mir);

    for (auto arg = mir.args_beg; arg != mir.args_end; ++arg)
    {
      ctx.threads[0].locals[arg].live = false;
    }

    if (mir.fx.fn->flags & FunctionDecl::Destructor)
      return;

    arg = mir.args_beg;
    for (auto &parm : mir.fx.parameters())
    {
      if (is_reference_type(decl_cast<ParmVarDecl>(parm)->type) && !is_const_reference(ctx, mir.locals[arg]))
      {
        ctx.threads[0].locals[arg].live = true;

        switch (ctx.state(arg))
        {
          case State::dangling:
            ctx.diag.error("potentially dangling output value", mir.fx.fn, parm->loc());
            break;

          case State::poisoned:
            ctx.diag.error("potentially poisoned output value", mir.fx.fn, parm->loc());
            break;

          default:
            break;
        }

        if ((mir.fx.fn->flags & FunctionDecl::DeclType) == 0 && !is_rvalue_reference(ctx, mir.locals[arg]))
        {
          if ((mir.fx.fn->flags & (FunctionDecl::Safe | FunctionDecl::Unsafe)) == 0)
          {
            if (ctx.threads[0].locals[arg + mir.locals.size()].consumed && !has_consume(ctx, notations, parm))
              ctx.diag.warn("missing consume annotation", mir.fx.fn, parm->loc());
          }

          if (mir.fx.fn->flags & FunctionDecl::Lifetimed)
          {
            if (ctx.threads[0].locals[arg + mir.locals.size()].toxic && !has_poison(ctx, notations, parm))
              ctx.diag.warn("missing poison annotation", mir.fx.fn, parm->loc());
          }
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
        if ((mir.fx.fn->flags & (FunctionDecl::Safe | FunctionDecl::Unsafe)) == 0)
          ctx.diag.error("potentially consumed return value", mir.fx.fn, mir.fx.fn->loc());
        break;

      case State::poisoned:
        ctx.diag.error("potentially poisoned return value", mir.fx.fn, mir.fx.fn->loc());
        break;
    }
  }
}

vector<Lifetime> parse_lifetime(string_view str, SourceLocation loc)
{
  return annotations(str, loc);
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
