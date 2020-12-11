//
// lower.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "lower.h"
#include "interp.h"
#include "diag.h"
#include <variant>
#include <algorithm>
#include <charconv>
#include <iostream>

using namespace std;

#define PACK_REFS 1
#define TRANSATIVE_CONST 1
#define DEFERRED_DEFAULT_ARGS 1
#define DEDUCE_CONCEPT_ARGS 1

namespace
{
  struct LowerContext
  {
    Diag &diag;

    long flags;

    MIR mir;

    MIR::Block currentblock;
    MIR::block_t currentblockid;

    bool unreachable;
    MIR::local_t errorarg;
    vector<MIR::block_t> throws;
    vector<MIR::block_t> breaks;
    vector<MIR::block_t> continues;
    vector<MIR::block_t> returns;

    struct Barrier
    {
      size_t locals;
      size_t blocks;
      size_t varinfos;
      size_t lineinfos;
      size_t statements;
      MIR::local_t errorarg;
      MIR::block_t firstthrow;
      MIR::block_t firstbreak;
      MIR::block_t firstcontinue;
      MIR::block_t firstreturn;
      vector<MIR::Statement> retires;

      Diag::Marker diagstate;
    };

    vector<Barrier> barriers;

    unordered_map<Decl*, MIR::local_t> locals;
    unordered_map<Decl*, MIR::Fragment> symbols;

    MIR::local_t add_local()
    {
      return mir.add_local(MIR::Local());
    }

    MIR::local_t add_variable()
    {
      auto arg = mir.add_local(MIR::Local());

      add_statement(MIR::Statement::storagelive(arg));
      retire_statement(MIR::Statement::storagedead(arg));

      return arg;
    }

    MIR::local_t add_temporary(Type *type = nullptr, long flags = 0)
    {
      auto arg = mir.add_local(MIR::Local(type, flags));

      add_statement(MIR::Statement::storagelive(arg));
      retire_statement(MIR::Statement::storagedead(arg));

      return arg;
    }

    MIR::block_t add_block(MIR::Terminator terminator)
    {
      mir.add_block(MIR::Block{ std::move(currentblock.statements), std::move(terminator) });

      currentblock.statements.clear();

      return currentblockid++;
    }

    void add_statement(MIR::Statement statement)
    {
      currentblock.statements.push_back(std::move(statement));
    }

    size_t push_barrier()
    {
      auto &barrier = barriers.emplace_back();

      barrier.locals = mir.locals.size();
      barrier.blocks = mir.blocks.size();
      barrier.varinfos = mir.varinfos.size();
      barrier.lineinfos = mir.lineinfos.size();
      barrier.statements = currentblock.statements.size();

      barrier.errorarg = errorarg;
      barrier.firstthrow = throws.size();
      barrier.firstbreak = breaks.size();
      barrier.firstcontinue = continues.size();
      barrier.firstreturn = returns.size();

      barrier.diagstate = diag.marker();

      return barriers.size() - 1;
    }

    void retire_statement(MIR::Statement statement)
    {
      barriers.back().retires.push_back(std::move(statement));
    }

    void retire_barrier(size_t marker)
    {
      while (barriers.size() != marker)
      {
        auto &barrier = barriers.back();

        for(auto i = barrier.firstthrow; i < throws.size(); ++i)
        {
          if (throws[i] != currentblockid)
            mir.blocks[throws[i]].statements.insert(mir.blocks[throws[i]].statements.end(), barrier.retires.rbegin(), barrier.retires.rend());
        }

        for(auto i = barrier.firstbreak; i < breaks.size(); ++i)
        {
          if (breaks[i] != currentblockid)
            mir.blocks[breaks[i]].statements.insert(mir.blocks[breaks[i]].statements.end(), barrier.retires.rbegin(), barrier.retires.rend());
        }

        for(auto i = barrier.firstcontinue; i < continues.size(); ++i)
        {
          if (continues[i] != currentblockid)
            mir.blocks[continues[i]].statements.insert(mir.blocks[continues[i]].statements.end(), barrier.retires.rbegin(), barrier.retires.rend());
        }

        for(auto i = barrier.firstreturn; i < returns.size(); ++i)
        {
          if (returns[i] != currentblockid)
            mir.blocks[returns[i]].statements.insert(mir.blocks[returns[i]].statements.end(), barrier.retires.rbegin(), barrier.retires.rend());
        }

        if (mir.throws && errorarg == 1)
        {
          returns.insert(returns.end(), throws.begin(), throws.end());

          throws.clear();
        }

        for(auto i = barrier.retires.rbegin(); i != barrier.retires.rend(); ++i)
        {
          add_statement(std::move(*i));
        }

        errorarg = barrier.errorarg;

        barriers.pop_back();
      }
    }

    void rollback_barrier(size_t marker)
    {
      while (barriers.size() != marker)
      {
        auto &barrier = barriers.back();

        throws.resize(barrier.firstthrow);
        breaks.resize(barrier.firstbreak);
        continues.resize(barrier.firstcontinue);
        returns.resize(barrier.firstreturn);

        currentblockid = barrier.blocks;

        if (barrier.blocks < mir.blocks.size())
          currentblock = mir.blocks[barrier.blocks];

        currentblock.statements.resize(barrier.statements);

        mir.blocks.resize(barrier.blocks);
        mir.locals.resize(barrier.locals);
        mir.varinfos.resize(barrier.varinfos);
        mir.lineinfos.resize(barrier.lineinfos);

        errorarg = barrier.errorarg;

        diag.revert(barrier.diagstate);

        barriers.pop_back();
      }
    }

    Type *voidtype;
    Type *booltype;
    Type *chartype;
    Type *isizetype;
    Type *usizetype;
    Type *intliteraltype;
    Type *floatliteraltype;
    Type *stringliteraltype;
    Type *ptrliteraltype;

    vector<Scope> stack;

    ModuleDecl *module;
    TranslationUnitDecl *translationunit;

    SourceLocation site;
    SourceLocation site_override{ -1, -1 };

    TypeTable &typetable;

    LowerContext(TypeTable &typetable, Diag &diag, long flags)
      : diag(diag),
        flags(flags),
        typetable(typetable)
    {
      errorarg = 0;
      unreachable = false;
      mir.args_beg = 1;
      mir.args_end = 1;
      mir.throws = false;

      voidtype = type(Builtin::Type_Void);
      booltype = type(Builtin::Type_Bool);
      chartype = type(Builtin::Type_Char);
      isizetype = type(Builtin::Type_ISize);
      usizetype = type(Builtin::Type_USize);
      intliteraltype = type(Builtin::Type_IntLiteral);
      floatliteraltype = type(Builtin::Type_FloatLiteral);
      stringliteraltype = type(Builtin::Type_StringLiteral);
      ptrliteraltype = type(Builtin::Type_PtrLiteral);

      currentblockid = 0;
      currentblock.terminator.kind = MIR::Terminator::Return;
    }
  };

  const long IllSpecified = 0x40000000;
  const long ResolveUsings = 0x10000000;

  Type *resolve_defn(LowerContext &ctx, Type *type);
  Type *resolve_type(LowerContext &ctx, Scope const &scope, Type *type);
  Type *resolve_type(LowerContext &ctx, Scope const &scope, TagDecl *tagdecl);
  Type *resolve_type(LowerContext &ctx, Scope const &scope, EnumConstantDecl *constant);
  Type *resolve_type(LowerContext &ctx, Scope const &scope, TypeOfDecl *typedecl);
  Type *resolve_type_as_value(LowerContext &ctx, Scope const &scope, ParmVarDecl *parm);
  Type *resolve_type_as_reference(LowerContext &ctx, Scope const &scope, ParmVarDecl *parm);
  MIR::Local find_type(LowerContext &ctx, vector<Scope> &stack, Expr *expr);
  MIR::Local find_returntype(LowerContext &ctx, FnSig const &fx);
  FnSig find_refn(LowerContext &ctx, Scope const &scope, ParmVarDecl *parm, MIR::Local const &rhs);
  bool deduce_type(LowerContext &ctx, Scope const &scope, FnSig &fx, Type *lhs, MIR::Local const &rhs);
  bool deduce_type(LowerContext &ctx, Scope const &scope, FnSig &fx, ParmVarDecl *parm, MIR::Local const &rhs);
  bool deduce_calltype(LowerContext &ctx, Scope const &scope, FnSig &fx, FunctionType *lhs, Type *rhs);
  bool deduce_returntype(LowerContext &ctx, Scope const &scope, FnSig &fx, MIR::Local const &lhs, MIR::Local &rhs);
  bool promote_type(LowerContext &ctx, Type *&lhs, Type *rhs);
  void lower_decl(LowerContext &ctx, ParmVarDecl *parmvar);
  bool lower_expr(LowerContext &ctx, MIR::Fragment &result, Expr *expr);
  void lower_statement(LowerContext &ctx, Stmt *stmt);
  void lower_expression(LowerContext &ctx, Expr *expr);

  //|///////////////////// type_scope ///////////////////////////////////////
  Scope type_scope(LowerContext &ctx, Type const *type)
  {
    switch(type = remove_const_type(type); type->klass())
    {
      case Type::Tag:
        return Scope(type_cast<TagType>(type)->decl, type_cast<TagType>(type)->args);

      default:
        break;
    }

    return ctx.translationunit->builtins;
  }

  //|///////////////////// scopeof_type /////////////////////////////////////
  Scope scopeof_type(LowerContext &ctx, Type const *type)
  {
    switch(type = remove_const_type(type); type->klass())
    {
      case Type::Tag:

        if (is_lambda_type(type))
          return type_scope(ctx, type);

        return parent_scope(type_scope(ctx, type));

      default:
        break;
    }

    return ctx.translationunit->builtins;
  }

  //|///////////////////// child_scope //////////////////////////////////////
  Scope child_scope(LowerContext &ctx, Scope const &parent, Decl *decl, vector<Decl*> const &declargs, size_t &k, vector<MIR::Local> const &args, map<string_view, MIR::Local> const &namedargs = {})
  {
    Scope sx(decl, parent.typeargs);

    for(size_t i = 0; i < declargs.size(); ++i)
    {
      auto arg = decl_cast<TypeArgDecl>(declargs[i]);

      if (arg->flags & TypeArgDecl::Pack)
      {
        vector<Type*> defns;
        vector<Type*> fields;

        for( ; k < args.size(); ++k)
        {
          defns.push_back(args[k].defn);
          fields.push_back(args[k].type);
        }

        sx.set_type(arg, ctx.typetable.find_or_create<TupleType>(defns, fields));
      }

      else if (k < args.size())
      {
        sx.set_type(arg, args[k].type);

        k += 1;
      }

      else if (auto j = namedargs.find(arg->name); j != namedargs.end())
      {
        sx.set_type(arg, j->second.type);

        k += 1;
      }

      else if (arg->defult)
      {
#if !DEFERRED_DEFAULT_ARGS
        sx.set_type(arg, resolve_type(ctx, sx, arg->defult));
#endif
      }

      else
        k |= IllSpecified;
    }

    return sx;
  }

  template<typename T>
  Scope child_scope(LowerContext &ctx, Scope const &parent, T *decl, size_t &k, vector<MIR::Local> const &args, map<string_view, MIR::Local> const &namedargs = {})
  {
    return child_scope(ctx, parent, decl, decl->args, k, args, namedargs);
  }

  //|///////////////////// decl_scope ///////////////////////////////////////
  Scope decl_scope(LowerContext &ctx, Scope const &scope, Decl *decl, size_t &k, vector<MIR::Local> const &args, map<string_view, MIR::Local> const &namedargs)
  {
    if (decl->kind() == Decl::TypeAlias && (decl->flags & TypeAliasDecl::Implicit) && (!args.empty() || !namedargs.empty()))
    {
      decl = get<Decl*>(decl->owner);
    }

    switch(decl->kind())
    {
      case Decl::Module:
        return Scope(decl);

      case Decl::Import:
        return Scope(decl_cast<ImportDecl>(decl)->decl);

      case Decl::Struct:
      case Decl::Concept:
      case Decl::Enum:
        return child_scope(ctx, scope, decl_cast<TagDecl>(decl), k, args, namedargs);

      case Decl::Function:
        return child_scope(ctx, scope, decl_cast<FunctionDecl>(decl), k, args, namedargs);

      case Decl::TypeAlias:
        if (auto j = resolve_type(ctx, child_scope(ctx, scope, decl_cast<TypeAliasDecl>(decl), k, args, namedargs), decl_cast<TypeAliasDecl>(decl)->type); j && is_tag_type(j))
          return type_scope(ctx, j);
        break;

      case Decl::TypeArg:
        if (auto j = scope.find_type(decl); j != scope.typeargs.end() && is_tag_type(j->second))
          return type_scope(ctx, j->second);
        break;

      case Decl::EnumConstant:
        return child_scope(scope, decl_cast<EnumConstantDecl>(decl));

      default:
        assert(false);
    }

    return child_scope(scope, decl);
  }

  //|///////////////////// base_scope ///////////////////////////////////////
  Scope base_scope(LowerContext &ctx, Scope const &scope)
  {
    Scope sx;

    if (is_tag_scope(scope))
    {
      auto tagdecl = decl_cast<TagDecl>(get<Decl*>(scope.owner));

      if (tagdecl->kind() == Decl::Struct && decl_cast<StructDecl>(tagdecl)->basetype)
      {
        auto type = resolve_type(ctx, scope, decl_cast<StructDecl>(tagdecl)->basetype);

        if (is_tag_type(type))
          return Scope(type_cast<TagType>(type)->decl, type_cast<TagType>(type)->args);

        return ctx.translationunit->builtins;
      }
    }

    return sx;
  }

  //|///////////////////// eval /////////////////////////////////////////////
  int eval(LowerContext &ctx, Scope const &scope, Expr *expr)
  {
    auto result = evaluate(scope, expr, ctx.symbols, ctx.typetable, ctx.diag, expr->loc());

    if (result.type != ctx.booltype)
    {
      if (result.type == ctx.intliteraltype)
      {
        if (expr_cast<IntLiteralExpr>(result.value)->value().value == 0)
          return false;

        if (expr_cast<IntLiteralExpr>(result.value)->value().value == 1)
          return true;
      }

      ctx.diag.error("non bool condition", scope, expr->loc());

      return -1;
    }

    return expr_cast<BoolLiteralExpr>(result.value)->value();
  }

  //|///////////////////// is_throws ////////////////////////////////////////
  bool is_throws(LowerContext &ctx, FunctionDecl *fn)
  {
    if (fn->throws)
    {
      assert(fn->throws->kind() == Expr::BoolLiteral);

      return expr_cast<BoolLiteralExpr>(fn->throws)->value();
    }

    return false;
  }

  //|///////////////////// is_refn_type /////////////////////////////////////
  bool is_refn_type(LowerContext &ctx, ParmVarDecl *parm)
  {
    if (is_reference_type(parm->type))
    {
      auto basetype = remove_const_type(remove_reference_type(parm->type));

      if (basetype->klass() == Type::TypeArg && type_cast<TypeArgType>(basetype)->koncept)
        return true;
    }

    return false;
  }

  //|///////////////////// is_lambda_decay //////////////////////////////////
  bool is_lambda_decay(LowerContext &ctx, Type *lhs, Type *rhs)
  {
    if (is_pointer_type(rhs) || is_reference_type(rhs) || is_lambda_type(rhs))
    {
      if (lhs->klass() == Type::Pointer || lhs->klass() == Type::Reference)
      {
        lhs = remove_const_type(remove_pointference_type(lhs));
        rhs = remove_const_type(remove_pointference_type(rhs));
      }

      if (is_function_type(lhs) && is_lambda_type(rhs))
        return true;
    }

    return false;
  }

  //|///////////////////// is_base_cast /////////////////////////////////////
  bool is_base_cast(LowerContext &ctx, Type *lhs, Type *rhs)
  {
    if (is_pointer_type(rhs) || is_reference_type(rhs) || is_struct_type(rhs))
    {
      if (rhs->klass() == Type::Pointer || rhs->klass() == Type::Reference)
      {
        lhs = remove_const_type(remove_pointference_type(lhs));
        rhs = remove_const_type(remove_pointference_type(rhs));

        if (lhs == ctx.voidtype && rhs != ctx.voidtype)
          return true;
      }

      if (rhs->klass() == Type::Tag)
      {
        if (lhs->klass() != Type::Tag || type_cast<TagType>(lhs)->decl != type_cast<TagType>(rhs)->decl)
          return true;
      }
    }

    return false;
  }

  //|///////////////////// is_constant //////////////////////////////////////
  bool is_constant(LowerContext &ctx, MIR::Fragment const &condition)
  {
    return condition.value.kind() == MIR::RValue::Constant;
  }

  //|///////////////////// is_true_constant /////////////////////////////////
  bool is_true_constant(LowerContext &ctx, MIR::Fragment const &condition)
  {
    return is_constant(ctx, condition) && get<BoolLiteralExpr*>(condition.value.get<MIR::RValue::Constant>())->value() == true;
  }

  //|///////////////////// is_false_constant ////////////////////////////////
  bool is_false_constant(LowerContext &ctx, MIR::Fragment const &condition)
  {
    return is_constant(ctx, condition) && get<BoolLiteralExpr*>(condition.value.get<MIR::RValue::Constant>())->value() == false;
  }

  //|///////////////////// is_int_literal ///////////////////////////////////
  bool is_int_literal(LowerContext &ctx, Type const *type)
  {
    return is_typelit_type(type) && type_cast<TypeLitType>(type)->value->kind() == Expr::IntLiteral;
  }

  //|///////////////////// is_int_literal ///////////////////////////////////
  bool is_int_literal(LowerContext &ctx, MIR::Fragment const &value)
  {
    return is_constant(ctx, value) && get_if<IntLiteralExpr*>(&value.value.get<MIR::RValue::Constant>());
  }

  //|///////////////////// resolve_defn /////////////////////////////////////
  Type *resolve_defn(LowerContext &ctx, Type *type)
  {
    auto defn = ctx.typetable.var_defn;

    for(type = remove_const_type(type); is_reference_type(type); type = remove_const_type(remove_reference_type(type)))
      defn = ctx.typetable.find_or_create<ReferenceType>(defn);

    return defn;
  }

  //|///////////////////// resolve_deref ////////////////////////////////////
  Type *resolve_deref(LowerContext &ctx, Type *type, Type *defn)
  {
    while (is_reference_type(defn))
    {
      type = remove_reference_type(remove_const_type(type));
      defn = remove_const_type(remove_reference_type(defn));
    }

    return type;
  }

  //|///////////////////// resolve_as_value /////////////////////////////////
  MIR::Local resolve_as_value(LowerContext &ctx, MIR::Local local)
  {
    if (local.flags & MIR::Local::Const)
    {
      local.type = ctx.typetable.find_or_create<ConstType>(local.type);
      local.flags &= ~MIR::Local::Const;
    }

    if (local.flags & MIR::Local::Reference)
    {
      local.type = ctx.typetable.find_or_create<ReferenceType>(local.type);
      local.flags &= ~MIR::Local::Reference;
    }

    return local;
  }

  //|///////////////////// resolve_as_value /////////////////////////////////
  MIR::Local resolve_as_value(LowerContext &ctx, MIR::Local local, vector<MIR::RValue::Field> const &fields)
  {
    local = resolve_as_value(ctx, local);

    for(auto &field : fields)
    {
      if (field.op == MIR::RValue::Val)
        local.type = remove_reference_type(local.type);

      local.type = remove_const_type(local.type);

      switch(local.type->klass())
      {
        case Type::Tag:
        case Type::Tuple:
          local.type = type_cast<CompoundType>(local.type)->fields[field.index];
          break;

        case Type::Array:
          local.type = type_cast<ArrayType>(local.type)->type;
          break;

        default:
          assert(false);
      }
    }

    return local;
  }

  //|///////////////////// resolve_as_reference /////////////////////////////
  MIR::Local resolve_as_reference(LowerContext &ctx, MIR::Local local)
  {
    local.flags &= ~MIR::Local::Const;

    assert(is_reference_type(local.type));

    local.type = remove_reference_type(local.type);
    local.flags |= MIR::Local::Reference;

    if (is_qualarg_type(local.type))
    {
      auto qualarg = type_cast<QualArgType>(local.type);

      if (qualarg->qualifiers & QualArgType::Const)
        local.flags |= MIR::Local::Const;

      if (qualarg->qualifiers & QualArgType::RValue)
        local.flags = (local.flags & ~MIR::Local::LValue) | MIR::Local::XValue;

      local.type = remove_const_type(local.type);
    }

    if (is_const_type(local.type))
    {
      local.type = remove_const_type(local.type);
      local.flags |= MIR::Local::Const;
    }

    return local;
  }

  //|///////////////////// find_decls ///////////////////////////////////////

  void find_decls(LowerContext &ctx, Scope const &scope, vector<Decl*> const &decls, vector<Decl*> &results)
  {
    for(auto &decl : decls)
    {
      if (decl->kind() == Decl::If)
      {
        if (eval(ctx, super_scope(scope, decl), decl_cast<IfDecl>(decl)->cond) == 1)
        {
          find_decls(ctx, scope, decl_cast<IfDecl>(decl)->decls, results);
        }
        else if (auto elseif = decl_cast<IfDecl>(decl)->elseif)
        {
          if (eval(ctx, super_scope(scope, decl), decl_cast<IfDecl>(elseif)->cond) == 1)
          {
            find_decls(ctx, scope, decl_cast<IfDecl>(elseif)->decls, results);
          }
        }

        continue;
      }

      results.push_back(decl);
    }
  }

  void find_decls(LowerContext &ctx, Scope const &scope, string_view name, long queryflags, vector<Decl*> &results)
  {
    if (is_tag_scope(scope))
    {
      auto tagdecl = decl_cast<TagDecl>(get<Decl*>(scope.owner));

      if (auto type = ctx.typetable.find<TagType>(tagdecl, scope.typeargs))
      {
        for(auto &decl : tagdecl->args)
          find_decl(decl, name, queryflags, results);

        for(auto &decl : type_cast<TagType>(type)->decls)
          find_decl(decl, name, queryflags, results);

        return;
      }
    }

    find_decls(scope, name, queryflags, results);

    for(size_t i = 0; i < results.size(); )
    {
      auto decl = results[i];

      if (decl->kind() == Decl::If)
      {
        results.erase(results.begin() + i);

        auto n = results.size();

        results.push_back(decl);

        for(size_t i = n; i < results.size(); )
        {
          if (results[i]->kind() == Decl::If)
          {
            results.erase(results.begin() + i);

            auto ifd = decl_cast<IfDecl>(decl);

            find_decls(ifd, name, queryflags, results);

            if (ifd->elseif)
              find_decls(ifd->elseif, name, queryflags, results);
          }
          else
            ++i;
        }

        if (results.size() != n)
        {
          results.resize(n);

          auto ifd = decl_cast<IfDecl>(decl);

          if ((ifd->flags & IfDecl::ResolvedTrue) || (!(ifd->flags & IfDecl::ResolvedFalse) && eval(ctx, super_scope(scope, decl), ifd->cond) == 1))
            find_decls(decl, name, queryflags, results);
          else
            if (auto elseif = ifd->elseif)
              results.push_back(elseif);
        }
      }
      else
        ++i;
    }
  }

  void find_decls(LowerContext &ctx, Scope const &scope, string_view name, long queryflags, long resolveflags, vector<Decl*> &results)
  {
    find_decls(ctx, scope, name, queryflags, results);

    for(size_t i = 0; i < results.size(); )
    {
      auto decl = results[i];

      if (decl->kind() == Decl::Using && (resolveflags & ResolveUsings))
      {
        results.erase(results.begin() + i);

        auto n = results.size();

        switch(auto usein = decl_cast<UsingDecl>(decl); usein->decl->kind())
        {
          case Decl::Module:
            find_decls(ctx, usein->decl, name, queryflags | QueryFlags::Public, results);
            break;

          case Decl::Struct:
          case Decl::Concept:
          case Decl::Enum:
            if (decl_cast<TagDecl>(usein->decl)->name == name && (queryflags & QueryFlags::Types))
              results.push_back(usein->decl);
            break;

          case Decl::TypeAlias:
            if (decl_cast<TypeAliasDecl>(usein->decl)->name == name && (queryflags & QueryFlags::Types))
              results.push_back(usein->decl);
            break;

          case Decl::DeclRef:
            if (decl_cast<DeclRefDecl>(usein->decl)->name == name && (queryflags & QueryFlags::Functions))
              results.push_back(usein->decl);
            break;

          case Decl::DeclScoped:
            if (decl_cast<DeclRefDecl>(decl_cast<DeclScopedDecl>(usein->decl)->decls.back())->name == name && (queryflags & QueryFlags::Functions))
              results.push_back(usein->decl);
            break;

          case Decl::TypeArg:
            break;

          default:
            assert(false);
        }

        results.erase(remove_if(results.begin() + n, results.end(), [&](auto &decl) {
          return count(results.begin(), results.begin() + n, decl) != 0;
        }), results.end());

        continue;
      }

      ++i;
    }

    for(size_t i = 0; i < results.size(); ++i)
    {
      auto decl = results[i];

      if (decl->kind() == Decl::Import)
      {
        results.erase(remove_if(results.begin() + i + 1, results.end(), [&](auto &decl) {
          return decl->kind() == Decl::Import;
        }), results.end());
      }
    }
  }

  //|///////////////////// find_scoped //////////////////////////////////////

  struct Scoped
  {
    Scope scope;
    DeclRefDecl *decl;

    Scoped(std::nullptr_t = nullptr)
    {
      decl = nullptr;
    }

    Scoped(DeclRefDecl *decl, Scope scope)
      : scope(std::move(scope)), decl(decl)
    {
    }

    explicit operator bool() const { return decl; }
  };

  vector<MIR::Local> typeargs(LowerContext &ctx, Scope const &scope, vector<Type*> const &args)
  {
    vector<MIR::Local> typeargs;

    for(auto &arg : args)
    {
      if (arg->klass() == Type::Unpack)
      {
        if (auto pack = resolve_type(ctx, scope, type_cast<UnpackType>(arg)->type); is_tuple_type(pack))
        {
          for(size_t index = 0; index < type_cast<TupleType>(pack)->fields.size(); ++index)
            typeargs.push_back(MIR::Local(type_cast<TupleType>(pack)->fields[index], type_cast<TupleType>(pack)->defns[index]));
        }

        continue;
      }

      typeargs.push_back(MIR::Local(resolve_type(ctx, scope, arg), resolve_defn(ctx, arg)));
    }

    return typeargs;
  }

  map<string_view, MIR::Local> typeargs(LowerContext &ctx, Scope const &scope, map<string, Type*> const &namedargs)
  {
    map<string_view, MIR::Local> typeargs;

    for(auto &[name, arg] : namedargs)
    {
      typeargs.emplace(name, MIR::Local(resolve_type(ctx, scope, arg), resolve_defn(ctx, arg)));
    }

    return typeargs;
  }

  Scoped find_scoped(LowerContext &ctx, vector<Scope> const &stack, DeclScopedDecl *scoped, long &queryflags)
  {
    vector<Decl*> decls;

    Scope declscope = ctx.translationunit;

    if (scoped->decls[0]->kind() == Decl::TypeOf)
    {
      declscope = type_scope(ctx, resolve_type(ctx, stack.back(), decl_cast<TypeOfDecl>(scoped->decls[0])));

      if (get_module(declscope) != ctx.module)
        queryflags |= QueryFlags::Public;
    }

    if (scoped->decls[0]->kind() == Decl::DeclRef && decl_cast<DeclRefDecl>(scoped->decls[0])->name != "::")
    {
      auto declref = decl_cast<DeclRefDecl>(scoped->decls[0]);

      auto args = typeargs(ctx, stack.back(), declref->args);
      auto namedargs = typeargs(ctx, stack.back(), declref->namedargs);

      for(auto sx = stack.rbegin(); sx != stack.rend(); ++sx)
      {
        find_decls(ctx, *sx, declref->name, QueryFlags::Imports | QueryFlags::Types | QueryFlags::Concepts | QueryFlags::Usings | queryflags, ResolveUsings, decls);

        if (decls.empty())
          continue;

        size_t k = 0;

        declscope = decl_scope(ctx, super_scope(*sx, decls[0]), decls[0], k, args, namedargs);

        if ((k & ~IllSpecified) != args.size() + namedargs.size())
          return nullptr;

        break;
      }

      if (decls.size() != 1)
        return nullptr;

      if (decls[0]->kind() == Decl::Import || decls[0]->kind() == Decl::Module)
        queryflags |= QueryFlags::Public;

      decls.clear();
    }

    for(size_t i = 1; i + 1 < scoped->decls.size(); ++i)
    {
      auto declref = decl_cast<DeclRefDecl>(scoped->decls[i]);

      auto args = typeargs(ctx, stack.back(), declref->args);
      auto namedargs = typeargs(ctx, stack.back(), declref->namedargs);

      find_decls(ctx, declscope, declref->name, QueryFlags::Modules | QueryFlags::Imports | QueryFlags::Types | QueryFlags::Concepts | QueryFlags::Usings | queryflags, ResolveUsings, decls);

      if (decls.size() != 1)
        return nullptr;

      size_t k = 0;

      declscope = decl_scope(ctx, super_scope(declscope, decls[0]), decls[0], k, args, namedargs);

      if ((k & ~IllSpecified) != args.size() + namedargs.size())
        return nullptr;

      if (decls[0]->kind() == Decl::Import || decls[0]->kind() == Decl::Module)
        queryflags |= QueryFlags::Public;

      decls.clear();
    }

    return Scoped{ decl_cast<DeclRefDecl>(scoped->decls.back()), std::move(declscope) };
  }

  //|///////////////////// find_field ///////////////////////////////////////

  struct Field
  {
    size_t index;

    long flags = 0;
    Type *type = nullptr;
    Type *defn = nullptr;

    explicit operator bool() const { return type; }
  };

  Field find_field(LowerContext &ctx, CompoundType *type, size_t index)
  {
    Field field;

    if (index < type->fields.size())
    {
      field.index = index;
      field.type = type->fields[index];

      switch (type->klass())
      {
        case Type::Tuple:

          if (is_const_type(field.type))
          {
            field.type = remove_const_type(field.type);
            field.flags |= VarDecl::Const;
          }

          field.defn = type_cast<TupleType>(type)->defns[index];
          break;

        case Type::Tag:
          field.defn = decl_cast<FieldVarDecl>(type_cast<TagType>(type)->fieldvars[index])->type;
          break;

        default:
          assert(false);
      }
    }

    return field;
  }

  Field find_field(LowerContext &ctx, TagType *tagtype, string_view name)
  {
    Field field;

    field.index = 0;

    for(auto &decl : tagtype->fieldvars)
    {
      if (decl_cast<FieldVarDecl>(decl)->name == name)
      {
        field.type = tagtype->fields[field.index];
        field.defn = decl_cast<FieldVarDecl>(decl)->type;
        field.flags = decl_cast<FieldVarDecl>(decl)->flags;

        break;
      }

      field.index += 1;
    }

    return field;
  }

  //|///////////////////// find_vardecl /////////////////////////////////////

  VarDecl *find_vardecl(LowerContext &ctx, vector<Scope> const &stack, string_view name)
  {
    vector<Decl*> decls;
    long queryflags = QueryFlags::Variables | QueryFlags::Fields;

    for(auto sx = stack.rbegin(); sx != stack.rend(); ++sx)
    {
      find_decls(ctx, *sx, name, queryflags, decls);

      if (decls.empty())
      {
        if (is_fn_scope(*sx))
        {
          if (get<Decl*>(sx->owner) != ctx.mir.fx.fn)
            queryflags &= ~QueryFlags::Fields;

          if (!(decl_cast<FunctionDecl>(get<Decl*>(sx->owner))->flags & (FunctionDecl::Constructor | FunctionDecl::Destructor)))
            queryflags &= ~QueryFlags::Fields;
        }

        if (is_tag_scope(*sx))
        {
          queryflags &= ~QueryFlags::Fields;
        }

        continue;
      }

      break;
    }

    if (decls.size() == 1 && is_var_decl(decls[0]))
    {
      return decl_cast<VarDecl>(decls[0]);
    }

    return nullptr;
  }

  //|///////////////////// find_index ///////////////////////////////////////

  size_t find_index(LowerContext &ctx, vector<Scope> const &stack, string_view name)
  {
    size_t index = size_t(-1);

    if (auto [p, ec] = from_chars(name.data(), name.data() + name.length(), index); ec != std::errc())
    {
      for(auto &[decl, type] : stack.back().typeargs)
      {
        if (decl->kind() == Decl::TypeArg && decl_cast<TypeArgDecl>(decl)->name == name && is_int_literal(ctx, type))
          index = expr_cast<IntLiteralExpr>(type_cast<TypeLitType>(type)->value)->value().value;
      }

      if (auto decl = find_vardecl(ctx, stack, name); decl && (decl->flags & VarDecl::Literal))
      {
        if (auto T = stack.back().find_type(decl); T != stack.back().typeargs.end() && is_int_literal(ctx, T->second))
          index = expr_cast<IntLiteralExpr>(type_cast<TypeLitType>(T->second)->value)->value().value;

        if (auto T = ctx.symbols.find(decl); T != ctx.symbols.end() && is_int_literal(ctx, T->second))
          index = get<IntLiteralExpr*>(T->second.value.get<MIR::RValue::Constant>())->value().value;
      }
    }

    return index;
  }

  //|///////////////////// resolve_type /////////////////////////////////////

  Type *resolve_type(LowerContext &ctx, Scope const &scope, ConstType *consttype)
  {
    return ctx.typetable.find_or_create<ConstType>(remove_const_type(resolve_type(ctx, scope, consttype->type)));
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, PointerType *pointertype)
  {
    return ctx.typetable.find_or_create<PointerType>(resolve_type(ctx, scope, pointertype->type));
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, ReferenceType *reftype)
  {
    return ctx.typetable.find_or_create<ReferenceType>(resolve_type(ctx, scope, reftype->type));
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, ArrayType *arraytype)
  {
    auto elemtype = resolve_type(ctx, scope, arraytype->type);
    auto sizetype = resolve_type(ctx, scope, arraytype->size);

    return ctx.typetable.find_or_create<ArrayType>(elemtype, sizetype);
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TupleType *tupletype)
  {
    vector<Type*> defns;
    vector<Type*> fields;

    for(auto &field : tupletype->fields)
    {
      if (field->klass() == Type::Unpack)
      {
        if (auto pack = resolve_type(ctx, scope, type_cast<UnpackType>(field)->type); is_tuple_type(pack))
        {
          defns.insert(defns.end(), type_cast<TupleType>(pack)->defns.begin(), type_cast<TupleType>(pack)->defns.end());
          fields.insert(fields.end(), type_cast<TupleType>(pack)->fields.begin(), type_cast<TupleType>(pack)->fields.end());
        }

        continue;
      }

      defns.push_back(resolve_defn(ctx, field));
      fields.push_back(resolve_type(ctx, scope, field));
    }

    return ctx.typetable.find_or_create<TupleType>(defns, fields);
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TagDecl *tagdecl)
  {
    if (auto type = ctx.typetable.find<TagType>(tagdecl, scope.typeargs))
      return type;

    vector<Decl*> decls;
    vector<Type*> fields;

    find_decls(ctx, scope, tagdecl->decls, decls);

    auto type = ctx.typetable.create<TagType>(tagdecl, scope.typeargs);

    for(auto &decl : decls)
    {
      if (decl->kind() != Decl::FieldVar)
        continue;

      fields.push_back(remove_const_type(resolve_type(ctx, scope, decl_cast<FieldVarDecl>(decl)->type)));
    }

    type->resolve(std::move(decls), std::move(fields));

    return type;
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TagType *tagtype)
  {
    auto args = tagtype->args;

    for(auto &[decl, arg] : args)
    {
      arg = resolve_type(ctx, scope, arg);
    }

    auto tagdecl = decl_cast<TagDecl>(tagtype->decl);

    return resolve_type(ctx, Scope(tagdecl, args), tagdecl);
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TypeArgType *argtype)
  {
    if (auto j = scope.find_type(argtype->decl); j != scope.typeargs.end())
    {
      return j->second;
    }

    return argtype;
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, QualArgType *argtype)
  {
    return resolve_type(ctx, scope, argtype->type);
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TypeLitType *typelit)
  {
    if (is_literal_expr(typelit->value))
    {
      return ctx.typetable.find_or_create<TypeLitType>(typelit->value);
    }

    if (auto expr = evaluate(scope, typelit->value, ctx.symbols, ctx.typetable, ctx.diag, typelit->value->loc()))
    {
      return ctx.typetable.find_or_create<TypeLitType>(expr.value);
    }

    return typelit;
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, EnumConstantDecl *constant)
  {
    auto enumm = resolve_type(ctx, scope, decl_cast<EnumDecl>(get<Decl*>(scope.owner)));

    if (auto type = ctx.typetable.find<ConstantType>(constant, enumm))
      return type;

    size_t value = 0;
    Expr *lastknown = nullptr;

    for(auto &decl : type_cast<TagType>(enumm)->decls)
    {
      if (decl->kind() == Decl::EnumConstant)
      {
        auto expr = decl_cast<EnumConstantDecl>(decl)->value;

        if (expr)
        {
          value = 0;
          lastknown = expr;
        }

        if (decl == constant)
        {
          auto type = ctx.typetable.create<ConstantType>(constant, enumm);

          if (lastknown)
          {
            expr = lastknown;

            if (expr->kind() != Expr::IntLiteral)
            {
              expr = evaluate(scope, expr, ctx.symbols, ctx.typetable, ctx.diag, constant->loc()).value;

              if (!expr || expr->kind() != Expr::IntLiteral)
              {
                ctx.diag.error("invalid enum value", scope, decl->loc());
                break;
              }
            }

            if (value != 0)
              expr = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(expr_cast<IntLiteralExpr>(expr)->value().sign, expr_cast<IntLiteralExpr>(expr)->value().value + value), constant->loc());
          }
          else
          {
            expr = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, value), constant->loc());
          }

          type->resolve(ctx.typetable.find_or_create<TypeLitType>(expr));

          return type;
        }

        value += 1;
      }
    }

    throw logic_error("unresolved enum constant");
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, ConstantType *constant)
  {
    auto tagtype = resolve_type(ctx, scope, constant->type);

    if (auto type = ctx.typetable.find<ConstantType>(constant->decl, tagtype))
      return type;

    switch(constant->decl->kind())
    {
      case Decl::EnumConstant:
        return resolve_type(ctx, type_scope(ctx, tagtype), decl_cast<EnumConstantDecl>(constant->decl));

      default:
        assert(false);
    }

    throw logic_error("unresolved constant");
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, FunctionType *fntype)
  {
    auto returntype = resolve_type(ctx, scope, fntype->returntype);
    auto paramtuple = resolve_type(ctx, scope, fntype->paramtuple);

    return ctx.typetable.find_or_create<FunctionType>(returntype, paramtuple);
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, VarDecl *vardecl)
  {
    Type *type;

    if (auto j = ctx.symbols.find(vardecl); j != ctx.symbols.end())
    {
      type = resolve_as_value(ctx, j->second.type).type;
    }
    else if (vardecl->kind() == Decl::ParmVar)
    {
      type = resolve_type_as_value(ctx, scope, decl_cast<ParmVarDecl>(vardecl));
    }
    else
    {
      type = resolve_type(ctx, scope, vardecl->type);
    }

    if (is_pack_type(vardecl->type))
    {
      type = remove_reference_type(type);
    }

    return resolve_deref(ctx, type, vardecl->type);
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, FunctionDecl *fn)
  {
    vector<Type*> defns;
    vector<Type*> parms;

    for(auto &parm : fn->parms)
    {
      if (parm->flags & ParmVarDecl::Literal)
        continue;

      defns.push_back(resolve_defn(ctx, decl_cast<ParmVarDecl>(parm)->type));
      parms.push_back(resolve_type_as_value(ctx, scope, decl_cast<ParmVarDecl>(parm)));
    }

    auto returntype = find_returntype(ctx, FnSig(fn, scope.typeargs)).type;
    auto paramtuple = ctx.typetable.find_or_create<TupleType>(defns, parms);

    return ctx.typetable.find_or_create<FunctionType>(returntype, paramtuple);
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TypeOfDecl *typedecl)
  {
    vector<Scope> stack;
    seed_stack(stack, scope);

    // For typeof's in a requires clause parameter block, don't allow self references
    if (is_fn_scope(stack.back()) && (decl_cast<FunctionDecl>(get<Decl*>(stack.back().owner))->flags & FunctionDecl::DeclType) == FunctionDecl::RequiresDecl)
      stack.pop_back();

    if (typedecl->expr->kind() == Expr::DeclRef && expr_cast<DeclRefExpr>(typedecl->expr)->decl->kind() == Decl::DeclRef && !expr_cast<DeclRefExpr>(typedecl->expr)->base)
    {
      auto declref = decl_cast<DeclRefDecl>(expr_cast<DeclRefExpr>(typedecl->expr)->decl);

      vector<Type*> types;
      vector<Decl*> decls;

      auto args = typeargs(ctx, stack.back(), declref->args);
      auto namedargs = typeargs(ctx, stack.back(), declref->namedargs);

      for(auto sx = stack.rbegin(); sx != stack.rend(); ++sx)
      {
        find_decls(ctx, *sx, declref->name, QueryFlags::Variables | QueryFlags::Fields | QueryFlags::Functions, decls);

        for(auto &decl : decls)
        {
          if (is_var_decl(decl))
          {
            if (!args.empty() || !namedargs.empty())
              continue;

            types.push_back(resolve_type(ctx, *sx, decl_cast<VarDecl>(decl)));
          }

          if (is_fn_decl(decl))
          {
            size_t k = 0;

            auto declscope = decl_scope(ctx, super_scope(*sx, decl), decl, k, args, namedargs);

            if (k != args.size() + namedargs.size())
              continue;

            types.push_back(resolve_type(ctx, declscope, decl_cast<FunctionDecl>(decl)));
          }
        }

        if (types.size() == 1)
          return types[0];

        if (decls.empty())
          continue;

        break;
      }
    }

    if (typedecl->expr->kind() == Expr::DeclRef && expr_cast<DeclRefExpr>(typedecl->expr)->decl->kind() == Decl::DeclScoped)
    {
      auto scoped = decl_cast<DeclScopedDecl>(expr_cast<DeclRefExpr>(typedecl->expr)->decl);

      long queryflags = 0;

      if (Scoped declref = find_scoped(ctx, stack, scoped, queryflags))
      {
        vector<Type*> types;
        vector<Decl*> decls;

        auto args = typeargs(ctx, stack.back(), declref.decl->args);
        auto namedargs = typeargs(ctx, stack.back(), declref.decl->namedargs);

        find_decls(ctx, declref.scope, declref.decl->name, QueryFlags::Variables | QueryFlags::Fields | QueryFlags::Functions, decls);

        for(auto &decl : decls)
        {
          if (is_var_decl(decl))
          {
            if (!args.empty() || !namedargs.empty())
              continue;

            types.push_back(resolve_type(ctx, declref.scope, decl_cast<VarDecl>(decl)));
          }

          if (is_fn_decl(decl))
          {
            size_t k = 0;

            auto declscope = decl_scope(ctx, super_scope(declref.scope, decl), decl, k, args, namedargs);

            if (k != args.size() + namedargs.size())
              continue;

            types.push_back(resolve_type(ctx, declscope, decl_cast<FunctionDecl>(decl)));
          }
        }

        if (auto owner = get_if<Decl*>(&declref.scope.owner); owner && *owner && ((*owner)->kind() == Decl::TypeArg || (*owner)->kind() == Decl::TypeAlias))
        {
          auto type = ctx.voidtype;

          if ((*owner)->kind() == Decl::TypeArg)
          {
            if (auto j = scope.find_type(*owner); j != scope.typeargs.end())
              type = j->second;
          }

          if ((*owner)->kind() == Decl::TypeAlias)
          {
            type = resolve_type(ctx, declref.scope, decl_cast<TypeAliasDecl>(*owner)->type);
          }

          if (is_tuple_type(type))
          {
            auto tupletype = type_cast<TupleType>(type);

            if (auto index = find_index(ctx, stack, declref.decl->name); index != size_t(-1))
            {
              if (auto field = find_field(ctx, tupletype, index))
              {
                types.push_back(resolve_deref(ctx, field.type, field.defn));
              }
            }
          }
        }

        if (types.size() == 1)
          return types[0];
      }
    }

    if (is_fn_scope(stack.back()))
    {
      LowerContext cttx(ctx.typetable, ctx.diag, ctx.flags);

      cttx.mir.fx = decl_cast<FunctionDecl>(get<Decl*>(stack.back().owner));
      cttx.stack = stack;
      cttx.translationunit = decl_cast<TranslationUnitDecl>(get<Decl*>(cttx.stack[0].owner));
      cttx.module = decl_cast<ModuleDecl>(get<Decl*>(cttx.stack[1].owner));
      cttx.site_override = ctx.site;

      cttx.add_local();
      cttx.push_barrier();

      for(auto &parm : cttx.mir.fx.parameters())
      {
        lower_decl(cttx, decl_cast<ParmVarDecl>(parm));
      }

      MIR::Fragment result;

      if (lower_expr(cttx, result, typedecl->expr))
        return result.type.type;

      assert(ctx.diag.has_errored());

      return ctx.voidtype;
    }

    if (auto type = find_type(ctx, stack, typedecl->expr).type)
      return type;

    assert(ctx.diag.has_errored());

    return ctx.voidtype;
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, DeclRefDecl *declref)
  {
    throw logic_error("unresolved type");
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, DeclScopedDecl *scoped)
  {
    vector<Scope> stack;
    seed_stack(stack, scope);

    long queryflags = 0;

    if (Scoped declref = find_scoped(ctx, stack, scoped, queryflags))
    {
      vector<Type*> types;
      vector<Decl*> decls;

      auto args = typeargs(ctx, stack.back(), declref.decl->args);
      auto namedargs = typeargs(ctx, stack.back(), declref.decl->namedargs);

      find_decls(ctx, declref.scope, declref.decl->name, QueryFlags::Types | QueryFlags::Functions | QueryFlags::Usings | queryflags, ResolveUsings, decls);

      for(auto &decl : decls)
      {
        size_t k = 0;

        auto declscope = decl_scope(ctx, super_scope(declref.scope, decl), decl, k, args, namedargs);

        if (k != args.size() + namedargs.size())
          continue;

        if (is_tag_decl(decl))
        {
          types.push_back(resolve_type(ctx, declscope, decl_cast<TagDecl>(decl)));
        }

        if (decl->kind() == Decl::TypeAlias)
        {
          types.push_back(resolve_type(ctx, declscope, decl_cast<TypeAliasDecl>(decl)->type));
        }

        if (decl->kind() == Decl::Function)
        {
          types.push_back(resolve_type(ctx, declscope, decl_cast<FunctionDecl>(decl)));
        }
      }

      if (types.size() == 1)
        return types[0];
    }

    ctx.diag.error("no such type", scope, scoped->loc());

    return ctx.typetable.var_defn;
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TypeRefType *typeref, TypeAliasDecl *aliasdecl)
  {
    auto args = typeref->args;

    for(auto &[decl, arg] : args)
    {
      arg = resolve_type(ctx, scope, arg);
    }

    auto declscope = child_scope(super_scope(scope, aliasdecl), aliasdecl, args);

    return resolve_type(ctx, declscope, aliasdecl->type);
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TypeRefType *typeref)
  {
    switch(typeref->decl->kind())
    {
      case Decl::TypeOf:
        return resolve_type(ctx, scope, decl_cast<TypeOfDecl>(typeref->decl));

      case Decl::DeclRef:
        return resolve_type(ctx, scope, decl_cast<DeclRefDecl>(typeref->decl));

      case Decl::DeclScoped:
        return resolve_type(ctx, scope, decl_cast<DeclScopedDecl>(typeref->decl));

      case Decl::TypeAlias:
        return resolve_type(ctx, scope, typeref, decl_cast<TypeAliasDecl>(typeref->decl));

      default:
        assert(false);
    }

    throw logic_error("unresolved type");
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, Type *type)
  {
    switch(type->klass())
    {
      case Type::Builtin:
        return type;

      case Type::Const:
        return resolve_type(ctx, scope, type_cast<ConstType>(type));

      case Type::Pointer:
        return resolve_type(ctx, scope, type_cast<PointerType>(type));

      case Type::Reference:
        return resolve_type(ctx, scope, type_cast<ReferenceType>(type));

      case Type::Array:
        return resolve_type(ctx, scope, type_cast<ArrayType>(type));

      case Type::Tuple:
        return resolve_type(ctx, scope, type_cast<TupleType>(type));

      case Type::Tag:
        return resolve_type(ctx, scope, type_cast<TagType>(type));

      case Type::TypeArg:
        return resolve_type(ctx, scope, type_cast<TypeArgType>(type));

      case Type::QualArg:
        return resolve_type(ctx, scope, type_cast<QualArgType>(type));

      case Type::TypeLit:
        return resolve_type(ctx, scope, type_cast<TypeLitType>(type));

      case Type::Constant:
        return resolve_type(ctx, scope, type_cast<ConstantType>(type));

      case Type::Function:
        return resolve_type(ctx, scope, type_cast<FunctionType>(type));

      case Type::TypeRef:
        return resolve_type(ctx, scope, type_cast<TypeRefType>(type));

      default:
        assert(false);
    }

    throw logic_error("unresolved type");
  }

  Type *resolve_type(LowerContext &ctx, Type *type)
  {
    return resolve_type(ctx, ctx.stack.back(), type);
  }

  //|///////////////////// parameter ////////////////////////////////////////

  Type *resolve_type_as_value(LowerContext &ctx, Scope const &scope, ParmVarDecl *parm)
  {
    if (is_pack_type(parm->type))
    {
      auto lhs = type_cast<PackType>(parm->type)->type;
      auto rhs = resolve_type(ctx, scope, remove_const_type(remove_reference_type(lhs)));

      if (is_reference_type(lhs))
      {
        lhs = type_cast<ReferenceType>(lhs)->type;

        auto j = scope.find_type(parm);

        auto defns = type_cast<TupleType>(rhs)->defns;
        auto fields = type_cast<TupleType>(rhs)->fields;

        for(auto &defn : defns)
        {
          defn = ctx.typetable.find_or_create<ReferenceType>(defn);
        }

        for(auto &field : fields)
        {
          if (is_const_type(lhs))
          {
            field = ctx.typetable.find_or_create<ConstType>(field);
          }

          if (lhs->klass() == Type::QualArg && j != scope.typeargs.end())
          {
            auto index = &field - &fields.front();

            if (auto argtype = type_cast<TupleType>(j->second)->fields[index]; argtype->klass() == Type::QualArg)
            {
              auto qualifiers = type_cast<QualArgType>(argtype)->qualifiers;

              field = ctx.typetable.find_or_create<QualArgType>(qualifiers, field);
            }
          }

          field = ctx.typetable.find_or_create<ReferenceType>(field);
        }

        rhs = ctx.typetable.find_or_create<TupleType>(defns, fields);
      }

      return ctx.typetable.find_or_create<ReferenceType>(rhs);
    }

    if (is_reference_type(parm->type))
    {
      auto lhs = type_cast<ReferenceType>(parm->type)->type;
      auto rhs = resolve_type(ctx, scope, type_cast<ReferenceType>(parm->type)->type);

      if (lhs->klass() == Type::QualArg)
      {
        if (auto j = scope.find_type(parm); j != scope.typeargs.end() && j->second->klass() == Type::QualArg)
        {
          auto qualifiers = type_cast<QualArgType>(j->second)->qualifiers;

          rhs = ctx.typetable.find_or_create<QualArgType>(qualifiers, rhs);
        }
      }

      return ctx.typetable.find_or_create<ReferenceType>(rhs);
    }

    return remove_const_type(resolve_type(ctx, scope, parm->type));
  }

  Type *resolve_type_as_reference(LowerContext &ctx, Scope const &scope, ParmVarDecl *parm)
  {
    auto lhs = parm->type;

    if (is_pack_type(parm->type))
    {
      lhs = type_cast<PackType>(lhs)->type;

      if (is_reference_type(lhs))
      {
        lhs = remove_reference_type(lhs);
      }
    }

    if (is_reference_type(parm->type))
    {
      lhs = remove_reference_type(lhs);
    }

    return remove_const_type(resolve_type(ctx, scope, lhs));
  }

  //|///////////////////// match_concept ////////////////////////////////////
  bool match_concept(LowerContext &ctx, Scope const &scope, FnSig &sig, ConceptDecl *koncept, vector<pair<Decl*, Type*>> const &args, Type *&type)
  {
    assert(sig.typeargs.empty());

    if (koncept->name == "var")
      return true;

//    if (!is_concrete_type(type))
//      return false;

    for(auto &[arg, type] : super_scope(scope, koncept).typeargs)
    {
      sig.set_type(arg, type);
    }

    for(auto &[arg, type] : args)
    {
      if (auto argtype = resolve_type(ctx, scope, type); !is_typearg_type(argtype))
        sig.set_type(arg, argtype);
    }

    auto cache_key = make_tuple(koncept, sig.typeargs, type);

    if (auto j = ctx.typetable.concepts.find(cache_key); j != ctx.typetable.concepts.end())
    {
      sig.typeargs = get<0>(j->second);
      type = get<1>(j->second);
      return true;
    }

    Diag diag(ctx.diag.leader());

    for(auto &decl : koncept->decls)
    {
      if (decl->kind() != Decl::Decl::Requires)
        continue;

      auto reqires = decl_cast<RequiresDecl>(decl);

      if (reqires->flags & RequiresDecl::Condition)
      {
        auto sx = Scope(reqires->fn, sig.typeargs);

        for(auto &arg : reqires->fn->args)
          sx.set_type(arg, type);

        auto expr = stmt_cast<ReturnStmt>(reqires->fn->body)->expr;

        auto result = evaluate(sx, expr, ctx.symbols, ctx.typetable, diag, reqires->loc());

        if (result.type != ctx.booltype || !expr_cast<BoolLiteralExpr>(result.value)->value())
          return false;
      }

      if (reqires->flags & RequiresDecl::Expression)
      {
        auto fx = FnSig(reqires->fn, sig.typeargs);

        for(auto &arg : reqires->fn->args)
          fx.set_type(arg, type);

#if DEDUCE_CONCEPT_ARGS
        if (reqires->requirestype)
        {
          if (auto returntype = resolve_type(ctx, Scope(fx.fn, fx.typeargs), reqires->requirestype); is_concrete_type(returntype))
            fx.returntype = returntype;
        }
#endif

        auto mir = lower(fx, ctx.typetable, diag);

        if (diag.has_errored())
          return false;

        if (reqires->requirestype)
        {
          if (!deduce_type(ctx, scope, sig, reqires->requirestype, mir.locals[0]))
            return false;

#if DEDUCE_CONCEPT_ARGS
          size_t arg = mir.args_beg;
          for(auto &parm : fx.parameters())
          {
            auto lhs = decl_cast<ParmVarDecl>(parm)->type;
            auto rhs = mir.locals[arg].type;

            if (is_reference_type(decl_cast<ParmVarDecl>(parm)->type))
            {
              lhs = remove_const_type(remove_reference_type(lhs));
              rhs = remove_const_type(remove_reference_type(rhs));
            }

            if (is_typearg_type(lhs) && find(fx.fn->args.begin(), fx.fn->args.end(), type_cast<TypeArgType>(lhs)->decl) != fx.fn->args.end())
              type = rhs;

            arg += 1;
          }
#endif
        }
      }
    }

    ctx.typetable.concepts.emplace(std::move(cache_key), std::make_tuple(sig.typeargs, type));

    return true;
  }

  //|///////////////////// match_arguments //////////////////////////////////
  bool match_arguments(LowerContext &ctx, Scope const &scope, FnSig &sig, MatchExpr *match)
  {
    Diag diag(ctx.diag.leader());

    auto fx = FnSig(decl_cast<FunctionDecl>(match->decl), sig.typeargs);

    auto mir = lower(fx, ctx.typetable, diag);

    if (diag.has_errored())
      return false;

    size_t arg = mir.args_beg;
    for(auto &parm : fx.parameters())
    {
      auto lhs = decl_cast<ParmVarDecl>(parm)->type;
      auto rhs = mir.locals[arg].type;

      if (is_reference_type(decl_cast<ParmVarDecl>(parm)->type))
      {
        lhs = remove_const_type(remove_reference_type(lhs));
        rhs = remove_const_type(remove_reference_type(rhs));
      }

      if (!is_typearg_type(lhs))
      {
        ctx.diag.error("match parameter must be of type argument type", fx.fn, parm->loc());
        break;
      }

      sig.set_type(type_cast<TypeArgType>(lhs)->decl, rhs);

      arg += 1;
    }

    return true;
  }

  //|///////////////////// deduce_type //////////////////////////////////////

  struct DeduceContext
  {
    int depth = 0;
    int constdepth = 0;
    int pointerdepth = 0;
    bool allow_const_downcast = true;
    bool allow_object_downcast = true;
    bool allow_pointer_downcast = true;
  };

  bool deduce_type(LowerContext &ctx, DeduceContext &tx, Scope const &scope, FnSig &fx, Type *lhs, Type *rhs)
  {
    tx.depth += 1;

    if (rhs->klass() == Type::QualArg)
      rhs = remove_const_type(rhs);

    if (rhs->klass() == Type::TypeArg)
      return true;

    if (is_struct_type(rhs) && !is_const_type(lhs) && !is_typearg_type(lhs) && ((tx.pointerdepth == 0 && tx.allow_object_downcast) || (tx.pointerdepth == 1 && tx.allow_pointer_downcast)))
    {
      while (is_struct_type(rhs))
      {
        if (lhs->klass() == Type::Tag && type_cast<TagType>(lhs)->decl == type_cast<TagType>(rhs)->decl)
          break;

        if (!decl_cast<StructDecl>(type_cast<TagType>(rhs)->decl)->basetype)
          break;

        rhs = type_cast<TagType>(rhs)->fields[0];
      }
    }

    if (lhs == type(Builtin::Type_Void) && !is_const_type(rhs) && tx.pointerdepth == 1 && tx.allow_pointer_downcast)
      return true;

    if (lhs == rhs)
      return true;

    switch (lhs->klass())
    {
      case Type::Builtin:

        if (rhs == type(Builtin::Type_IntLiteral) && (is_int_type(lhs) || is_char_type(lhs)))
          return true;

        if (rhs == type(Builtin::Type_FloatLiteral) && is_float_type(lhs))
          return true;

        return false;

      case Type::Const:

        tx.constdepth += 1;

        if (!is_const_type(rhs))
        {
          if ((tx.depth > 1 && tx.constdepth < tx.pointerdepth) || !tx.allow_const_downcast)
            return false;
        }

        return deduce_type(ctx, tx, scope, fx, type_cast<ConstType>(lhs)->type, remove_const_type(rhs));

      case Type::Pointer:

        tx.pointerdepth += 1;

        if (rhs == type(Builtin::Type_PtrLiteral))
          return true;

        if (rhs->klass() == Type::Pointer)
          return deduce_type(ctx, tx, scope, fx, type_cast<PointerType>(lhs)->type, type_cast<PointerType>(rhs)->type);

        if (rhs->klass() == Type::Reference)
          return deduce_type(ctx, tx, scope, fx, type_cast<PointerType>(lhs)->type, type_cast<ReferenceType>(rhs)->type);

        if (is_const_type(type_cast<PointerType>(lhs)->type) && is_function_type(remove_const_type(type_cast<PointerType>(lhs)->type)) && is_lambda_type(rhs))
          return deduce_type(ctx, tx, scope, fx, remove_const_type(type_cast<PointerType>(lhs)->type), rhs);

        return false;

      case Type::Reference:

        tx.pointerdepth += 1;

        if (rhs->klass() == Type::Reference)
          return deduce_type(ctx, tx, scope, fx, type_cast<ReferenceType>(lhs)->type, type_cast<ReferenceType>(rhs)->type);

        if (is_const_type(type_cast<ReferenceType>(lhs)->type) && is_function_type(remove_const_type(type_cast<ReferenceType>(lhs)->type)) && is_lambda_type(rhs))
          return deduce_type(ctx, tx, scope, fx, remove_const_type(type_cast<ReferenceType>(lhs)->type), rhs);

        return false;

      case Type::TypeArg:

        if (auto j = fx.find_type(type_cast<TypeArgType>(lhs)->decl); j != fx.typeargs.end())
        {
          if (j->second->klass() == Type::TypeArg)
          {
            if (auto typearg = type_cast<TypeArgType>(j->second); typearg->koncept)
            {
              FnSig sig;

              if (!match_concept(ctx, scope, sig, decl_cast<ConceptDecl>(typearg->koncept), typearg->args, rhs))
                return false;
            }
          }

          if (j->second->klass() != Type::TypeArg)
          {
            promote_type(ctx, rhs, j->second);

            if (j->second == rhs)
              return true;

            if (auto k = scope.find_type(type_cast<TypeArgType>(lhs)->decl); k != scope.typeargs.end())
              return deduce_type(ctx, tx, scope, fx, j->second, rhs);

            promote_type(ctx, j->second, rhs);

            if (j->second != rhs)
              return false;
          }
        }

        if (tx.depth > 1 && is_const_type(rhs))
          return false;

        if (auto typearg = type_cast<TypeArgType>(lhs); typearg->koncept)
        {
          FnSig sig;

          if (!match_concept(ctx, Scope(fx.fn, fx.typeargs), sig, decl_cast<ConceptDecl>(typearg->koncept), typearg->args, rhs))
            return false;

          for(auto &[arg, type] : typearg->args)
          {
            if (auto j = sig.find_type(arg); j != sig.typeargs.end() && is_typearg_type(type))
              fx.set_type(type_cast<TypeArgType>(type)->decl, j->second);
          }
        }

        fx.set_type(type_cast<TypeArgType>(lhs)->decl, rhs);

        return true;

      case Type::Array:

        if (rhs->klass() == Type::Array)
        {
          if (type_cast<ArrayType>(lhs)->type == ctx.typetable.var_defn)
            return false;

          if (!deduce_type(ctx, tx, scope, fx, type_cast<ArrayType>(lhs)->type, type_cast<ArrayType>(rhs)->type))
            return false;

          if (!deduce_type(ctx, tx, scope, fx, type_cast<ArrayType>(lhs)->size, type_cast<ArrayType>(rhs)->size))
            return false;

          return true;
        }

        return false;

      case Type::Tuple:

        if (rhs->klass() == Type::Tuple)
        {
          size_t k = 0;

          for(auto field : type_cast<TupleType>(lhs)->fields)
          {
            DeduceContext ttx;

            ttx.allow_const_downcast = true;
            ttx.allow_object_downcast = false;
            ttx.allow_pointer_downcast = false;

            if (field->klass() == Type::Unpack)
            {
//              auto defns = vector(type_cast<TupleType>(rhs)->fields.size() - k, ctx.typetable.var_defn);
              auto defns = vector(type_cast<TupleType>(rhs)->defns.begin() + k, type_cast<TupleType>(rhs)->defns.end());
              auto fields = vector(type_cast<TupleType>(rhs)->fields.begin() + k, type_cast<TupleType>(rhs)->fields.end());

              if (!deduce_type(ctx, tx, scope, fx, type_cast<UnpackType>(field)->type, ctx.typetable.find_or_create<TupleType>(defns, fields)))
                return false;

              k += fields.size();

              continue;
            }

            if (k == type_cast<TupleType>(rhs)->fields.size())
              return false;

            if (!deduce_type(ctx, ttx, scope, fx, field, type_cast<TupleType>(rhs)->fields[k]))
              return false;

            k += 1;
          }

          if (k != type_cast<TupleType>(rhs)->fields.size())
            return false;

          return true;
        }

        return false;

      case Type::Tag:

        if (rhs->klass() == Type::Tag)
        {
          if (type_cast<TagType>(lhs)->decl != type_cast<TagType>(rhs)->decl)
            return false;

          for(size_t i = 0, j = 0; i < type_cast<TagType>(lhs)->args.size(); ++i)
          {
            DeduceContext ttx;

            ttx.allow_const_downcast = false;
            ttx.allow_object_downcast = false;
            ttx.allow_pointer_downcast = false;

            while (type_cast<TagType>(lhs)->args[i].first != type_cast<TagType>(rhs)->args[j].first)
              ++j;

            if (!deduce_type(ctx, ttx, scope, fx, type_cast<TagType>(lhs)->args[i].second, type_cast<TagType>(rhs)->args[j].second))
              return false;
          }

          return true;
        }

        return false;

      case Type::Function:

        if (rhs->klass() == Type::Function)
        {
          tx.allow_const_downcast = false;
          tx.allow_object_downcast = false;
          tx.allow_pointer_downcast = false;

          if (!deduce_type(ctx, tx, scope, fx, type_cast<FunctionType>(lhs)->returntype, type_cast<FunctionType>(rhs)->returntype))
            return false;

          if (!deduce_type(ctx, tx, scope, fx, type_cast<FunctionType>(lhs)->paramtuple, type_cast<FunctionType>(rhs)->paramtuple))
            return false;

          return true;
        }

        if (is_lambda_type(rhs) && !(decl_cast<LambdaDecl>(type_cast<TagType>(rhs)->decl)->flags & LambdaDecl::Captures) && tx.pointerdepth <= 1)
        {
          FnSig callop(decl_cast<LambdaDecl>(type_cast<TagType>(rhs)->decl)->fn, type_cast<TagType>(rhs)->args);

          if (!deduce_calltype(ctx, Scope(fx.fn, fx.typeargs), callop, type_cast<FunctionType>(lhs), rhs))
            return false;

          return true;
        }

        return false;

      case Type::QualArg:

        tx.pointerdepth -= 1;

        return deduce_type(ctx, tx, scope, fx, type_cast<QualArgType>(lhs)->type, remove_const_type(rhs));

      case Type::TypeRef:

        return deduce_type(ctx, tx, scope, fx, resolve_type(ctx, Scope(fx.fn, fx.typeargs), lhs), rhs);

      case Type::TypeLit:

        return resolve_type(ctx, Scope(fx.fn, fx.typeargs), lhs) == rhs;

      default:
        throw logic_error("unresolved type in query");
    }
  }

  bool deduce_type(LowerContext &ctx, Scope const &scope, FnSig &fx, Type *lhs, MIR::Local const &rhs)
  {
    DeduceContext tx;

    if (is_reference_type(lhs) && (rhs.flags & MIR::Local::Reference))
    {
      lhs = remove_reference_type(lhs);

      if (lhs->klass() != Type::QualArg)
      {
        if (!is_const_type(lhs) && (rhs.flags & MIR::Local::Const))
          return false;
      }
    }

    if (!deduce_type(ctx, tx, scope, fx, remove_const_type(lhs), rhs.type))
      return false;

    return true;
  }

  bool deduce_type(LowerContext &ctx, Scope const &scope, FnSig &fx, ParmVarDecl *parm, MIR::Local const &rhs)
  {
    DeduceContext tx;

    auto qualifiers = [](MIR::Local const &local) {

      auto qualifiers = 0;

      if (local.flags & MIR::Local::Const)
        qualifiers |= QualArgType::Const;

      if (local.flags & MIR::Local::RValue)
        qualifiers |= QualArgType::RValue;

      return qualifiers;
    };

    auto lhs = parm->type;

    if (parm->flags & VarDecl::Literal)
    {
      if (!(rhs.flags & MIR::Local::Literal))
        return false;
    }

    if (is_pack_type(lhs))
    {
      lhs = type_cast<PackType>(lhs)->type;

      auto rhstype = rhs.type;

      if (is_reference_type(lhs))
      {
        lhs = type_cast<ReferenceType>(lhs)->type;

        auto defns = type_cast<TupleType>(rhs.type)->defns;
        auto fields = type_cast<TupleType>(rhs.type)->fields;

        for(auto &defn : defns)
        {
          defn = remove_reference_type(defn);
        }

        for(auto &field : fields)
        {
          field = remove_reference_type(field);

          if (lhs->klass() != Type::QualArg)
          {
            if (!is_const_type(lhs) && is_const_type(field))
              return false;
          }

          field = remove_const_type(field);
        }

        rhstype = ctx.typetable.find_or_create<TupleType>(defns, fields);
      }

      auto lhstype = lhs;

#if PACK_REFS
      if (auto j = scope.find_type(type_cast<TypeArgType>(remove_const_type(lhs))->decl); j != scope.typeargs.end())
      {
        auto defns = type_cast<TupleType>(j->second)->defns;
        auto fields = type_cast<TupleType>(j->second)->fields;

        if (fields.size() != type_cast<TupleType>(rhs.type)->fields.size())
          return false;

        for(size_t i = 0; i < fields.size(); ++i)
        {
          if (is_reference_type(defns[i]))
          {
            fields[i] = remove_reference_type(fields[i]);

            if (fields[i]->klass() != Type::QualArg && is_qualarg_type(remove_reference_type(type_cast<TupleType>(rhs.type)->fields[i])))
            {
              if (!is_const_type(fields[i]) && type_cast<QualArgType>(remove_reference_type(type_cast<TupleType>(rhs.type)->fields[i]))->qualifiers & QualArgType::Const)
                return false;
            }

            fields[i] = remove_const_type(fields[i]);
          }
        }

        lhstype = ctx.typetable.find_or_create<TupleType>(defns, fields);
      }
#endif

      if (!deduce_type(ctx, tx, scope, fx, remove_const_type(lhstype), rhstype))
        return false;

      if (is_qualarg_type(lhs))
      {
        auto defns = type_cast<TupleType>(rhs.type)->defns;
        auto fields = type_cast<TupleType>(rhs.type)->fields;

        for(auto &field : fields)
        {
          field = ctx.typetable.find_or_create<QualArgType>(type_cast<QualArgType>(remove_reference_type(field))->qualifiers, ctx.typetable.var_defn);
        }

        fx.set_type(parm, ctx.typetable.find_or_create<TupleType>(defns, fields));
      }

      return true;
    }

    if (is_reference_type(lhs))
    {
      lhs = type_cast<ReferenceType>(lhs)->type;

      if (lhs->klass() != Type::QualArg)
      {
        if (!is_const_type(lhs) && (rhs.flags & MIR::Local::Const))
          return false;
      }
    }

    if (is_refn_type(ctx, parm))
    {
      if (auto refn = find_refn(ctx, scope, parm, rhs); refn.fn)
      {
        auto returntype = find_returntype(ctx, refn);

        if (!returntype)
          return false;

        if (!deduce_type(ctx, tx, scope, fx, remove_const_type(lhs), returntype.type))
          return false;

        if (is_qualarg_type(lhs))
          fx.set_type(parm, ctx.typetable.find_or_create<QualArgType>(qualifiers(rhs), ctx.typetable.var_defn));

        return true;
      }
    }

    if (!deduce_type(ctx, tx, scope, fx, remove_const_type(lhs), rhs.type))
      return false;

    if (is_qualarg_type(lhs))
      fx.set_type(parm, ctx.typetable.find_or_create<QualArgType>(qualifiers(rhs), ctx.typetable.var_defn));

    return true;
  }

  //|///////////////////// lambda ///////////////////////////////////////////
  bool deduce_calltype(LowerContext &ctx, Scope const &scope, FnSig &fx, FunctionType *lhs, Type *rhs)
  {
    auto fn = decl_cast<LambdaDecl>(type_cast<TagType>(rhs)->decl)->fn;
    auto params = type_cast<TupleType>(resolve_type(ctx, scope, lhs->paramtuple));

    if (params->fields.size() != fn->parms.size())
      return false;

    for(size_t i = 0; i < fn->parms.size(); ++i)
    {
      if (!deduce_type(ctx, scope, fx, decl_cast<ParmVarDecl>(fn->parms[i])->type, params->fields[i]))
        return false;
    }

    fx.returntype = find_returntype(ctx, fx).type;

    if (fx.returntype != resolve_type(ctx, scope, lhs->returntype))
      return false;

    return true;
  }

  //|///////////////////// deduce_returntype ////////////////////////////////
  bool deduce_returntype(LowerContext &ctx, Scope const &scope, FnSig &fx, MIR::Local const &lhs, MIR::Local &rhs)
  {
    bool make_const = false;

    make_const |= is_pointer_type(rhs.type) && is_const_type(remove_pointer_type(rhs.type));
    make_const |= is_reference_type(rhs.type) && is_const_type(remove_reference_type(rhs.type));
    make_const |= is_pointer_type(lhs.type) && is_const_type(remove_pointer_type(lhs.type));
    make_const |= is_reference_type(lhs.type) && is_const_type(remove_reference_type(lhs.type));

    bool make_pointer = false;

    make_pointer |= is_pointer_type(rhs.type) || rhs.type == ctx.ptrliteraltype;
    make_pointer |= is_pointer_type(lhs.type) || lhs.type == ctx.ptrliteraltype;

    auto type = lhs.type;

    if (is_reference_type(type) && make_pointer)
      type = ctx.typetable.find_or_create<PointerType>(remove_reference_type(type));

    if (type == ctx.intliteraltype && is_int_type(rhs.type))
      type = rhs.type;

    if (type == ctx.floatliteraltype && is_float_type(rhs.type))
      type = rhs.type;

    if (type == ctx.ptrliteraltype && is_pointer_type(rhs.type))
      type = rhs.type;

    if (is_reference_type(rhs.type) && make_pointer)
      rhs.type = ctx.typetable.find_or_create<PointerType>(remove_reference_type(rhs.type));

    if (!deduce_type(ctx, scope, fx, type, rhs.type))
      return false;

    if ((lhs.flags & MIR::Local::XValue) != (rhs.flags & MIR::Local::XValue))
      return false;

    if (is_builtin_type(rhs.type) && is_concrete_type(type))
      rhs.type = type;

    if (is_pointer_type(rhs.type) && !is_const_type(remove_pointer_type(rhs.type)) && make_const)
      rhs.type = ctx.typetable.find_or_create<PointerType>(ctx.typetable.find_or_create<ConstType>(remove_pointer_type(rhs.type)));

    if (is_reference_type(rhs.type) && !is_const_type(remove_reference_type(rhs.type)) && make_const)
      rhs.type = ctx.typetable.find_or_create<ReferenceType>(ctx.typetable.find_or_create<ConstType>(remove_reference_type(rhs.type)));

    return true;
  }

  //|///////////////////// find_overloads ///////////////////////////////////

  struct FindContext
  {
    string_view name;
    vector<MIR::Local> args;
    map<string_view, MIR::Local> namedargs;

    vector<Decl*> decls;

    long queryflags;

    FindContext(Type *type, long queryflags = QueryFlags::All);
    FindContext(string_view name, long queryflags = QueryFlags::All);

    FindContext(FindContext const &tx, long queryflags) : name(tx.name), args(tx.args), namedargs(tx.namedargs), queryflags(tx.queryflags | queryflags) { }
    FindContext& operator=(FindContext &&tx) { this->name = tx.name; this->args = std::move(tx.args); this->namedargs = std::move(tx.namedargs); this->queryflags = tx.queryflags; return *this; }
  };

  FindContext::FindContext(string_view name, long queryflags)
    : name(name), queryflags(queryflags)
  {
  }

  FindContext::FindContext(Type *type, long queryflags)
    : queryflags(queryflags)
  {
    switch(type = remove_const_type(type); type->klass())
    {
      case Type::Builtin:
        name = type_cast<BuiltinType>(type)->name();
        break;

      case Type::Pointer:
        name = "#ptr";
        args.push_back(type);
        break;

      case Type::Reference:
        name = "#ref";
        args.push_back(type);
        break;

      case Type::Array:
        name = "#array";
        args.push_back(type);
        break;

      case Type::Tuple:
        name = "#tuple";
        args.push_back(type);
        break;

      case Type::TypeLit:
        switch(auto value = type_cast<TypeLitType>(type)->value; value->kind())
        {
          case Expr::BoolLiteral:
            name = "#lit";
            args.push_back(Builtin::type(Builtin::Type_Bool));
            args.push_back(type);
            break;

          case Expr::CharLiteral:
            name = "#lit";
            args.push_back(Builtin::type(Builtin::Type_Char));
            args.push_back(type);
            break;

          case Expr::IntLiteral:
            name = "#lit";
            args.push_back(Builtin::type(Builtin::Type_IntLiteral));
            args.push_back(type);
            break;

          case Expr::FloatLiteral:
            name = "#lit";
            args.push_back(Builtin::type(Builtin::Type_FloatLiteral));
            args.push_back(type);
            break;

          case Expr::StringLiteral:
            name = "#lit";
            args.push_back(Builtin::type(Builtin::Type_StringLiteral));
            args.push_back(type);
            break;

          default:
            break;
        }

        break;

      case Type::Constant:
        name = "#lit";
        args.push_back(type_cast<ConstantType>(type)->type);
        args.push_back(type_cast<ConstantType>(type)->expr);
        break;

      case Type::Tag:
        name = decl_cast<TagDecl>(type_cast<TagType>(type)->decl)->name;

        if (auto tagtype = type_cast<TagType>(type))
        {
          for(auto &arg : decl_cast<TagDecl>(tagtype->decl)->args)
          {
            auto j = find_if(tagtype->args.begin(), tagtype->args.end(), [&](auto &k) { return k.first == arg; });

            if (decl_cast<TypeArgDecl>(arg)->flags & TypeArgDecl::Pack)
            {
              for(auto &field : type_cast<TupleType>(j->second)->fields)
                args.push_back(field);

              continue;
            }

            args.push_back(j->second);
          }
        }

        break;

      default:
        break;
    }
  }

  void find_overloads(LowerContext &ctx, FindContext &tx, Scope const &scope, vector<MIR::Fragment> const &parms, map<string_view, MIR::Fragment> const &namedparms, vector<FnSig> &results)
  {
    find_decls(ctx, scope, tx.name, tx.queryflags, tx.decls);

    for(auto &decl : tx.decls)
    {
      if (decl->kind() == Decl::Function)
      {
        auto fn = decl_cast<FunctionDecl>(decl);

        if (!(fn->flags & FunctionDecl::Public) && get_module(fn) != ctx.module)
          continue;

        if (find_if(results.begin(), results.end(), [&](auto &k) { return k.fn == fn; }) != results.end())
          continue;

        bool viable = true;

        size_t i = 0, k = 0;

        auto fnscope = child_scope(ctx, scope, fn, k, tx.args, tx.namedargs);

        if ((k & ~IllSpecified) != tx.args.size() + tx.namedargs.size())
          continue;

        auto fx = FnSig(fn, fnscope.typeargs);

        for(i = 0, k = 0; i < fn->parms.size(); ++i)
        {
          auto parm = decl_cast<ParmVarDecl>(fn->parms[i]);

          if (is_pack_type(parm->type))
          {
            vector<Type*> fields;

            for( ; k < parms.size(); ++k)
            {
              auto field = parms[k].type.type;

              if (is_reference_type(type_cast<PackType>(parm->type)->type))
              {
                if (parms[k].type.flags & MIR::Local::Const)
                  field = ctx.typetable.find_or_create<ConstType>(field);

                if (is_qualarg_type(type_cast<ReferenceType>(type_cast<PackType>(parm->type)->type)->type))
                {
                  auto qualifiers = 0;

                  if (parms[k].type.flags & MIR::Local::Const)
                    qualifiers |= QualArgType::Const;

                  if (parms[k].type.flags & MIR::Local::RValue)
                    qualifiers |= QualArgType::RValue;

                  field = ctx.typetable.find_or_create<QualArgType>(qualifiers, remove_const_type(field));
                }

                field = ctx.typetable.find_or_create<ReferenceType>(field);
              }

              fields.push_back(field);
            }

            vector<Type*> defns;

            if (is_reference_type(type_cast<PackType>(parm->type)->type))
              defns = vector<Type*>(fields.size(), ctx.typetable.find_or_create<ReferenceType>(ctx.typetable.var_defn));
            else
              defns = vector<Type*>(fields.size(), ctx.typetable.var_defn);

            MIR::Local pack;

            pack.type = ctx.typetable.find_or_create<TupleType>(defns, fields);

            if (all_of(parms.end() - fields.size(), parms.end(), [](auto &k) { return k.type.flags & MIR::Local::Literal; }))
              pack.flags |= MIR::Local::Const | MIR::Local::Literal;

            pack.flags |= MIR::Local::RValue;
            pack.flags |= MIR::Local::Reference;

#if PACK_REFS
            if (auto j = fx.find_type(type_cast<TypeArgType>(remove_const_type(remove_reference_type(type_cast<PackType>(parm->type)->type)))->decl); j != fx.typeargs.end())
              fnscope.set_type(j->first, j->second);
#endif

            if (deduce_type(ctx, fnscope, fx, parm, pack))
              continue;
          }

          else if (k < parms.size())
          {
            if (deduce_type(ctx, fnscope, fx, parm, parms[k++].type))
              continue;
          }

          else if (auto j = namedparms.find(parm->name); j != namedparms.end())
          {
            ++k;

            if (deduce_type(ctx, fnscope, fx, parm, j->second.type))
              continue;
          }

          else if (auto j = find_if(namedparms.begin(), namedparms.end(), [&](auto &k) { return k.first.back() == '?' && k.first.substr(0, k.first.size()-1) == parm->name; }); j != namedparms.end())
          {
            if (deduce_type(ctx, fnscope, fx, parm, j->second.type))
              continue;
          }

          else if (parm->defult)
          {
            if (is_reference_type(parm->type) && is_qualarg_type(remove_reference_type(parm->type)))
              fx.set_type(parm, ctx.typetable.find_or_create<QualArgType>(MIR::Local::RValue, ctx.typetable.var_defn));

            continue;
          }

          viable = false;
          break;
        }

        k += count_if(namedparms.begin(), namedparms.end(), [&](auto &k) { return k.first.back() == '?'; });

        if (k != parms.size() + namedparms.size())
          continue;

        if (viable)
        {
          if (fn->match)
          {
            viable &= match_arguments(ctx, scope, fx, expr_cast<MatchExpr>(fn->match));
          }
        }

#if DEFERRED_DEFAULT_ARGS
        if (viable)
        {
          for(auto sx = Scope(fn); sx; sx = parent_scope(std::move(sx)))
          {
            vector<Decl*> *declargs = nullptr;

            if (is_fn_scope(sx))
              declargs = &decl_cast<FunctionDecl>(get<Decl*>(sx.owner))->args;

            if (is_tag_scope(sx))
              declargs = &decl_cast<TagDecl>(get<Decl*>(sx.owner))->args;

            if (declargs)
            {
              for(auto &arg : *declargs)
              {
                if (decl_cast<TypeArgDecl>(arg)->defult && fx.find_type(arg) == fx.typeargs.end())
                  fx.set_type(arg, resolve_type(ctx, Scope(fx.fn, fx.typeargs), decl_cast<TypeArgDecl>(arg)->defult));
              }
            }
          }
        }
#endif

        if (viable)
        {
          for(size_t i = 0, k = 0; i < fx.fn->parms.size(); ++i)
          {
            auto parm = decl_cast<ParmVarDecl>(fx.fn->parms[i]);

            if (parm->flags & VarDecl::Literal)
            {
              if (is_pack_type(parm->type))
              {
                vector<Expr*> fields;

                for( ; k < parms.size(); ++k)
                {
                  assert(parms[k].value.kind() == MIR::RValue::Constant);

                  fields.push_back(std::visit([&](auto &v) { return static_cast<Expr*>(v); }, parms[k].value.get<MIR::RValue::Constant>()));
                }

                fx.set_type(parm, ctx.typetable.find_or_create<TypeLitType>(ctx.mir.make_expr<CompoundLiteralExpr>(fields, parm->loc())));
              }

              else if (k < parms.size())
              {
                assert(parms[k].value.kind() == MIR::RValue::Constant);

                auto expr = std::visit([&](auto &v) { return static_cast<Expr*>(v); }, parms[k].value.get<MIR::RValue::Constant>());

                fx.set_type(parm, ctx.typetable.find_or_create<TypeLitType>(expr));
              }

              else if (auto j = namedparms.find(parm->name); j != namedparms.end())
              {
                assert(j->second.value.kind() == MIR::RValue::Constant);

                auto expr = std::visit([&](auto &v) { return static_cast<Expr*>(v); }, j->second.value.get<MIR::RValue::Constant>());

                fx.set_type(parm, ctx.typetable.find_or_create<TypeLitType>(expr));
              }

              else if (parm->defult)
              {
                auto value = parm->defult;

                if (value->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(value)->op() == UnaryOpExpr::Literal)
                {
                  // This roundabout approach is to get __site__ to evaluate to the callsite

                  LowerContext cttx(ctx.typetable, ctx.diag, ctx.flags);

                  seed_stack(cttx.stack, fnscope);

                  cttx.translationunit = ctx.translationunit;
                  cttx.module = ctx.module;
                  cttx.symbols = ctx.symbols;
                  cttx.site_override = ctx.site;

                  lower_expression(cttx, expr_cast<UnaryOpExpr>(value)->subexpr);

                  if (ctx.diag.has_errored())
                    break;

                  if (auto expr = evaluate(fnscope, cttx.mir, ctx.typetable, ctx.diag, parm->defult->loc()))
                  {
                    value = expr.value;
                  }
                }

                if (!is_literal_expr(value))
                {
                  ctx.diag.error("non literal default parameter", fnscope, parm->defult->loc());
                  break;
                }

                fx.set_type(parm, ctx.typetable.find_or_create<TypeLitType>(value));
              }
            }

            k = is_pack_type(parm->type) ? parms.size() : k + 1;
          }
        }

        if (viable)
        {
          if (fn->flags & (FunctionDecl::Builtin | FunctionDecl::Defaulted))
          {
            viable &= Builtin::where(fx);
          }

          if (fn->where)
          {
            viable &= eval(ctx, Scope(fx.fn, fx.typeargs), fn->where) == 1;
          }

          if (viable)
          {
            results.push_back(std::move(fx));
          }
        }
      }

      if (decl->kind() == Decl::Enum)
      {
        if (0 != tx.args.size() + tx.namedargs.size())
          continue;

        if (auto enumm = resolve_type(ctx, scope, decl_cast<EnumDecl>(decl)))
        {
          FindContext ttx("#enum", QueryFlags::All);

          ttx.args.push_back(enumm);

          find_overloads(ctx, ttx, ctx.translationunit->builtins, parms, namedparms, results);
        }
      }

      if (decl->kind() == Decl::EnumConstant)
      {
        if (0 != parms.size() + namedparms.size())
          continue;

        if (0 != tx.args.size() + tx.namedargs.size())
          continue;

        if (find_if(results.begin(), results.end(), [&](auto &k) { return (k.fn->flags & FunctionDecl::Builtin) && k.fn->builtin == Builtin::Type_Lit; }) != results.end())
          continue;

        auto enumm = resolve_type(ctx, scope, decl_cast<EnumDecl>(get<Decl*>(scope.owner)));
        auto value = resolve_type(ctx, scope, decl_cast<EnumConstantDecl>(decl));

        results.push_back(Builtin::fn(ctx.translationunit->builtins, Builtin::Type_Lit, enumm, type_cast<ConstantType>(value)->expr));
      }

      if (decl->kind() == Decl::Struct)
      {
        FindContext ttx(tx.name, QueryFlags::Functions);

        size_t k = 0;

        auto tagdecl = decl_cast<TagDecl>(decl);
        auto typescope = child_scope(ctx, scope, tagdecl, k, tx.args, tx.namedargs);

        if ((k & ~IllSpecified) != tx.args.size() + tx.namedargs.size())
          continue;

        find_overloads(ctx, ttx, typescope, parms, namedparms, results);
      }

      if (decl->kind() == Decl::TypeAlias)
      {
        size_t k = 0;

        auto alias = decl_cast<TypeAliasDecl>(decl);
        auto aliasscope = child_scope(ctx, scope, alias, k, tx.args, tx.namedargs);

        if (alias->flags & TypeAliasDecl::Implicit)
          continue;

        if ((k & ~IllSpecified) != tx.args.size() + tx.namedargs.size())
          continue;

        if (auto aliastype = resolve_type(ctx, aliasscope, alias->type))
        {
          FindContext ttx(aliastype, QueryFlags::All);

          find_overloads(ctx, ttx, scopeof_type(ctx, aliastype), parms, namedparms, results);
        }
      }

      if (decl->kind() == Decl::Using)
      {
        FindContext ttx(tx, QueryFlags::All);

        if (get_module(decl_cast<UsingDecl>(decl)->decl) != ctx.module)
          ttx.queryflags |= QueryFlags::Public;

        switch(auto usein = decl_cast<UsingDecl>(decl); usein->decl->kind())
        {
          case Decl::Module:
            find_overloads(ctx, ttx, usein->decl, parms, namedparms, results);
            break;

          case Decl::Struct:
          case Decl::Concept:
          case Decl::Enum:
            find_overloads(ctx, ttx, parent_scope(usein->decl), parms, namedparms, results);
            break;

          case Decl::TypeAlias:
            find_overloads(ctx, ttx, parent_scope(usein->decl), parms, namedparms, results);
            break;

          case Decl::DeclRef:
            if (tx.name == decl_cast<DeclRefDecl>(usein->decl)->name)
              find_overloads(ctx, ttx, parent_scope(usein->decl), parms, namedparms, results);
            break;

          case Decl::DeclScoped:
            if (tx.name == decl_cast<DeclRefDecl>(decl_cast<DeclScopedDecl>(usein->decl)->decls.back())->name)
              find_overloads(ctx, ttx, parent_scope(usein->decl), parms, namedparms, results);
            break;

          case Decl::TypeArg:
            if (auto j = scope.find_type(usein->decl); j != scope.typeargs.end())
              find_overloads(ctx, ttx, scopeof_type(ctx, j->second), parms, namedparms, results);
            break;

          default:
            assert(false);
        }
      }
    }

    tx.decls.clear();
  }

  void find_overloads(LowerContext &ctx, FindContext &tx, vector<Scope> const &stack, vector<MIR::Fragment> const &parms, map<string_view, MIR::Fragment> const &namedparms, vector<FnSig> &results)
  {
    for(auto sx = stack.rbegin(); sx != stack.rend(); ++sx)
    {
      find_decls(ctx, *sx, tx.name, QueryFlags::Types, tx.decls);

      if (tx.decls.empty())
        continue;

      for(auto &decl : tx.decls)
      {
        if (decl->kind() == Decl::TypeArg)
        {
          if (0 < tx.args.size() || 0 < tx.namedargs.size())
            continue;

          if (auto j = sx->find_type(decl); j != sx->typeargs.end())
          {
            tx = FindContext(j->second, tx.queryflags);

            find_overloads(ctx, tx, scopeof_type(ctx, j->second), parms, namedparms, results);
          }

          break;
        }
      }

      tx.decls.clear();

      break;
    }

    for(auto scope = stack.rbegin(); scope != stack.rend(); ++scope)
    {
      find_overloads(ctx, tx, *scope, parms, namedparms, results);

      for(auto basescope = base_scope(ctx, *scope); basescope; basescope = base_scope(ctx, basescope))
      {
        find_overloads(ctx, tx, basescope, parms, namedparms, results);
      }
    }
  }

  //|///////////////////// resolve_overloads ////////////////////////////////
  void resolve_overloads(LowerContext &ctx, FnSig &match, vector<FnSig> &overloads, vector<MIR::Fragment> const &parms, map<string_view, MIR::Fragment> const &namedparms)
  {
    if (overloads.size() == 1)
    {
      match = overloads[0];
      return;
    }

    int best = std::numeric_limits<int>::max();

    for(auto &fx : overloads)
    {
      int rank = 0;

      for(size_t i = 0, k = 0; i < fx.fn->parms.size(); ++i)
      {
        auto parm = decl_cast<ParmVarDecl>(fx.fn->parms[i]);

        auto rankargs = [&](auto &self, Type const *type, int s) -> void {

          while(true)
          {
            switch (type->klass())
            {
              case Type::Const:
                type = type_cast<ConstType>(type)->type;
                continue;

              case Type::Pointer:
                type = type_cast<PointerType>(type)->type;
                continue;

              case Type::Reference:
                type = type_cast<ReferenceType>(type)->type;
                continue;

              case Type::QualArg:
                type = type_cast<QualArgType>(type)->type;
                continue;

              case Type::TypeArg:
                rank += s;
                break;

              case Type::Array:
                self(self, type_cast<ArrayType>(type)->type, (s - 1) / 2);
                self(self, type_cast<ArrayType>(type)->size, (s - 1) / 2);
                break;

              case Type::Tuple:
                for(auto &field : type_cast<TupleType>(type)->fields)
                  self(self, field, (s - 1) / type_cast<TupleType>(type)->fields.size());
                break;

              case Type::Tag:
                for(auto &[decl, arg] : type_cast<TagType>(type)->args)
                  self(self, arg, (s - 1) / type_cast<TagType>(type)->args.size());
                break;

              default:
                break;
            }

            break;
          }
        };

        auto rankcast = [&](auto &self, Type const *type, MIR::Fragment const &src, int s) -> void {

          auto lhs = remove_const_type(remove_pointference_type(type));
          auto rhs = remove_const_type(remove_pointference_type(src.type.type));

          while (is_struct_type(rhs))
          {
            if (lhs->klass() == Type::TypeArg)
              break;

            if (lhs->klass() == Type::Tag && type_cast<TagType>(lhs)->decl == type_cast<TagType>(rhs)->decl)
              break;

            rank += s;

            if (!decl_cast<StructDecl>(type_cast<TagType>(rhs)->decl)->basetype)
              break;

            rhs = type_cast<TagType>(rhs)->fields[0];
          }

          if (lhs != rhs)
            rank += s;
        };

        if (!is_pack_type(parm->type))
        {
          if (k < parms.size())
          {
            rankcast(rankcast, parm->type, parms[k], 5);
          }
          else if (auto j = namedparms.find(parm->name); j != namedparms.end())
          {
            rankcast(rankcast, parm->type, j->second, 5);
          }
          else
          {
            continue; // Don't penalise defaulted parameters
          }
        }

        if (!(parm->flags & VarDecl::Literal))
        {
          rank += 5;

          rankargs(rankargs, parm->type, 1000000);

          if (is_typearg_type(remove_const_type(remove_reference_type(parm->type))))
          {
            auto typearg = type_cast<TypeArgType>(remove_const_type(remove_reference_type(parm->type)));

            if (!typearg->koncept || decl_cast<ConceptDecl>(typearg->koncept)->name == "var")
              rank += 1;
          }

          if (!((is_pointer_type(parm->type) && !is_const_type(type_cast<PointerType>(parm->type)->type)) ||
               (is_reference_type(parm->type) && !is_const_type(type_cast<ReferenceType>(parm->type)->type)) ||
               (is_pack_type(parm->type) && is_reference_type(type_cast<PackType>(parm->type)->type) && !is_const_type(type_cast<ReferenceType>(type_cast<PackType>(parm->type)->type)->type))))
            rank += 1;
        }

        if (is_pack_type(parm->type))
          rank += 100000000;

        k = is_pack_type(parm->type) ? parms.size() : k + 1;
      }

      if (rank <= best)
      {
        match.fn = nullptr;

        if (rank < best)
        {
          match = fx;
          best = rank;
        }
      }

#if 0
      if (&fx == &overloads[0])
        cout << "Resolve Overloads\n";
      cout << "  " << rank << " : " << *fx.fn << '\n';
#endif
    }
  }

  //|///////////////////// find_refn ////////////////////////////////////////
  FnSig find_refn(LowerContext &ctx, Scope const &scope, ParmVarDecl *parm, MIR::Local const &rhs)
  {
    vector<FnSig> overloads;

    auto typearg = type_cast<TypeArgType>(remove_const_type(remove_reference_type(parm->type)));

    FindContext tx(decl_cast<ConceptDecl>(typearg->koncept)->name, QueryFlags::Functions | QueryFlags::Public);

    for(auto &arg : decl_cast<ConceptDecl>(typearg->koncept)->args)
    {
      if (auto j = find_if(typearg->args.begin(), typearg->args.end(), [&](auto &k) { return k.first == arg; }); j != typearg->args.end())
      {
        if(auto argtype = resolve_type(ctx, scope, j->second); !is_typearg_type(argtype))
          tx.args.push_back(argtype);
      }
    }

    FnSig refn;

    vector<MIR::Fragment> parms(1);
    map<string_view, MIR::Fragment> namedparms;

    parms[0].type = rhs;

    if (is_tag_type(rhs.type))
    {
      auto type = type_cast<TagType>(rhs.type);
      auto typescope = Scope(type->decl, type->args);

      find_overloads(ctx, tx, typescope, parms, namedparms, overloads);
      find_overloads(ctx, tx, scopeof_type(ctx, type), parms, namedparms, overloads);
    }

    find_overloads(ctx, tx, parent_scope(typearg->koncept), parms, namedparms, overloads);

    for(auto &fx: overloads)
    {
      auto fnparm = decl_cast<ParmVarDecl>(fx.fn->parms[0]);

      if (is_reference_type(parm->type) != is_reference_type(fnparm->type))
        continue;

      if (is_reference_type(parm->type) && is_reference_type(fnparm->type))
      {
        auto lhs = remove_reference_type(parm->type);
        auto rhs = remove_reference_type(fnparm->type);

        if (lhs->klass() != Type::QualArg && rhs->klass() != Type::QualArg)
        {
          if (is_const_type(lhs) != is_const_type(rhs))
            continue;
        }
      }

      refn = fx;
    }

    return refn;
  }

  //|///////////////////// find_builtin /////////////////////////////////////

  FnSig find_builtin(LowerContext &ctx, Builtin::Kind kind, Type *T1 = nullptr, Type *T2 = nullptr)
  {
    auto fx = Builtin::fn(ctx.translationunit->builtins, kind, T1, T2);

    fx.returntype = find_returntype(ctx, fx).type;

    return fx;
  }

  FnSig map_builtin(LowerContext &ctx, BinaryOpExpr::OpCode op, Type *T1 = nullptr, Type *T2 = nullptr)
  {
    switch (op)
    {
      case BinaryOpExpr::LT:
        return Builtin::fn(ctx.translationunit->builtins, Builtin::LT, T1, T2);

      case BinaryOpExpr::LE:
        return Builtin::fn(ctx.translationunit->builtins, Builtin::LE, T1, T2);

      case BinaryOpExpr::GT:
        return Builtin::fn(ctx.translationunit->builtins, Builtin::GT, T1, T2);

      case BinaryOpExpr::GE:
        return Builtin::fn(ctx.translationunit->builtins, Builtin::GE, T1, T2);

      case BinaryOpExpr::EQ:
        return Builtin::fn(ctx.translationunit->builtins, Builtin::EQ, T1, T2);

      case BinaryOpExpr::NE:
        return Builtin::fn(ctx.translationunit->builtins, Builtin::NE, T1, T2);

      case BinaryOpExpr::Cmp:
        return Builtin::fn(ctx.translationunit->builtins, Builtin::Cmp, T1, T2);

      default:
        assert(false);
    }

    throw std::logic_error("invalid map_builtin");
  }

  //|///////////////////// find_callee //////////////////////////////////////

  struct Callee
  {
    FnSig fx;
    vector<FnSig> overloads;

    Callee(std::nullptr_t = nullptr)
    {
      fx.fn = nullptr;
    }

    explicit operator bool() const { return fx.fn; }
  };

  Callee find_callee(LowerContext &ctx, Type *type, vector<MIR::Fragment> const &parms = {}, map<string_view, MIR::Fragment> const &namedparms = {})
  {
    Callee callee;

    FindContext tx(type);

    if (is_tag_type(type))
    {
      find_overloads(ctx, tx, type_scope(ctx, type), parms, namedparms, callee.overloads);
    }

    if (callee.overloads.empty())
    {
      find_overloads(ctx, tx, scopeof_type(ctx, type), parms, namedparms, callee.overloads);
    }

    resolve_overloads(ctx, callee.fx, callee.overloads, parms, namedparms);

    return callee;
  }

  Callee find_callee(LowerContext &ctx, Type *type, string_view name, vector<MIR::Fragment> const &parms = {}, map<string_view, MIR::Fragment> const &namedparms = {})
  {
    Callee callee;

    FindContext tx(name);

    if (is_tag_type(type))
    {
      for(auto scope = type_scope(ctx, type); scope; scope = base_scope(ctx, scope))
      {
        find_overloads(ctx, tx, scope, parms, namedparms, callee.overloads);
      }
    }

    if (callee.overloads.empty())
    {
      find_overloads(ctx, tx, scopeof_type(ctx, type), parms, namedparms, callee.overloads);
    }

    resolve_overloads(ctx, callee.fx, callee.overloads, parms, namedparms);

    return callee;
  }

  Callee find_callee(LowerContext &ctx, vector<Scope> const &stack, UnaryOpExpr::OpCode op, vector<MIR::Fragment> const &parms = {}, map<string_view, MIR::Fragment> const &namedparms = {})
  {
    Callee callee;

    FindContext tx(UnaryOpExpr::name(op));

    if (is_tag_type(parms[0].type.type))
    {
      for(auto scope = type_scope(ctx, parms[0].type.type); scope; scope = base_scope(ctx, scope))
      {
        find_overloads(ctx, tx, scope, parms, namedparms, callee.overloads);
      }
    }

    if (callee.overloads.empty())
    {
      find_overloads(ctx, tx, scopeof_type(ctx, parms[0].type.type), parms, namedparms, callee.overloads);
    }

    if (callee.overloads.empty())
    {
      find_overloads(ctx, tx, stack, parms, namedparms, callee.overloads);
    }

    resolve_overloads(ctx, callee.fx, callee.overloads, parms, namedparms);

    return callee;
  }

  Callee find_callee(LowerContext &ctx, vector<Scope> const &stack, BinaryOpExpr::OpCode op, vector<MIR::Fragment> const &parms = {}, map<string_view, MIR::Fragment> const &namedparms = {})
  {
    Callee callee;

    FindContext tx(BinaryOpExpr::name(op));

    if (is_tag_type(parms[0].type.type))
    {
      for(auto scope = type_scope(ctx, parms[0].type.type); scope; scope = base_scope(ctx, scope))
      {
        find_overloads(ctx, tx, scope, parms, namedparms, callee.overloads);
      }
    }

    if (is_tag_type(parms[1].type.type) && parms[1].type.type != parms[0].type.type)
    {
      for(auto scope = type_scope(ctx, parms[1].type.type); scope; scope = base_scope(ctx, scope))
      {
        find_overloads(ctx, tx, scope, parms, namedparms, callee.overloads);
      }
    }

    if (callee.overloads.empty())
    {
      find_overloads(ctx, tx, scopeof_type(ctx, parms[0].type.type), parms, namedparms, callee.overloads);

      if (parms[1].type.type != parms[0].type.type)
        find_overloads(ctx, tx, scopeof_type(ctx, parms[1].type.type), parms, namedparms, callee.overloads);
    }

    if (callee.overloads.empty())
    {
      find_overloads(ctx, tx, stack, parms, namedparms, callee.overloads);
    }

    resolve_overloads(ctx, callee.fx, callee.overloads, parms, namedparms);

    return callee;
  }

  Callee find_callee(LowerContext &ctx, vector<Scope> const &stack, Scope const &basescope, DeclRefDecl *declref, vector<MIR::Fragment> const &parms = {}, map<string_view, MIR::Fragment> const &namedparms = {}, bool is_callop = false)
  {
    Callee callee;

    FindContext tx(declref->name);

    if (is_callop)
      tx.name = "()";

    tx.args = typeargs(ctx, ctx.stack.back(), declref->args);
    tx.namedargs = typeargs(ctx, ctx.stack.back(), declref->namedargs);

    if (basescope)
    {
      for(auto scope = basescope; scope; scope = base_scope(ctx, scope))
      {
        find_overloads(ctx, tx, scope, parms, namedparms, callee.overloads);
      }

      if (callee.overloads.empty() && is_tag_scope(basescope))
      {
        find_overloads(ctx, tx, parent_scope(basescope), parms, namedparms, callee.overloads);
      }
    }

    if (callee.overloads.empty())
    {
      find_overloads(ctx, tx, stack, parms, namedparms, callee.overloads);
    }

    resolve_overloads(ctx, callee.fx, callee.overloads, parms, namedparms);

    return callee;
  }

  Callee find_callee(LowerContext &ctx, vector<Scope> const &stack, Scope const &basescope, DeclScopedDecl *scoped, vector<MIR::Fragment> const &parms = {}, map<string_view, MIR::Fragment> const &namedparms = {}, bool is_callop = false)
  {
    Callee callee;

    long queryflags = 0;

    if (Scoped declref = find_scoped(ctx, stack, scoped, queryflags))
    {
      FindContext tx(declref.decl->name, QueryFlags::Functions | QueryFlags::Types | QueryFlags::Usings | queryflags);

      if (tx.name.substr(0, 1) == "~")
      {
        auto j = find_if(stack.back().typeargs.begin(),stack.back().typeargs.end(), [&](auto &k) {
          return decl_cast<TypeArgDecl>(k.first)->name == tx.name.substr(1);
        });

        if (j != stack.back().typeargs.end())
        {
          if (is_tag_type(j->second))
          {
            for(auto &decl : type_cast<TagType>(j->second)->decls)
            {
              if (decl->kind() == Decl::Function && (decl->flags & FunctionDecl::Destructor))
                tx.name = decl_cast<FunctionDecl>(decl)->name;
            }
          }
          else
          {
            if (is_array_type(j->second))
              tx.name = "~#array";

            if (is_tuple_type(j->second))
              tx.name = "~#tuple";

            if (is_builtin_type(j->second) || is_pointer_type(j->second) || is_reference_type(j->second) || is_enum_type(j->second))
              tx.name = "~#builtin";

            declref.scope = ctx.translationunit->builtins;
          }
        }
      }

      tx.args = typeargs(ctx, ctx.stack.back(), declref.decl->args);
      tx.namedargs = typeargs(ctx, ctx.stack.back(), declref.decl->namedargs);

      find_overloads(ctx, tx, declref.scope, parms, namedparms, callee.overloads);

      resolve_overloads(ctx, callee.fx, callee.overloads, parms, namedparms);
    }

    return callee;
  }

  Callee find_callee(LowerContext &ctx, vector<Scope> const &stack, Scope const &basescope, Decl *callee, vector<MIR::Fragment> const &parms = {}, map<string_view, MIR::Fragment> const &namedparms = {}, bool is_callop = false)
  {
    switch(callee->kind())
    {
      case Decl::DeclRef:
        return find_callee(ctx, stack, basescope, decl_cast<DeclRefDecl>(callee), parms, namedparms, is_callop);

      case Decl::DeclScoped:
        return find_callee(ctx, stack, basescope, decl_cast<DeclScopedDecl>(callee), parms, namedparms, is_callop);

      case Decl::TypeOf:
        ctx.diag.error("typeof in value context", ctx.stack.back(), callee->loc());
        break;

      default:
        assert(false);
    }

    return {};
  }

  //|///////////////////// diag_callee //////////////////////////////////////
  void diag_callee(LowerContext &ctx, Callee const &callee, vector<MIR::Fragment> const &parms, map<string_view, MIR::Fragment> const &namedparms)
  {
    for(auto &overload : callee.overloads)
      ctx.diag << "  function: '" << *overload.fn << "'\n";

    for(auto &parm : parms)
      ctx.diag << "  " << &parm - &parms[0] << ": " << parm.type << '\n';

    for(auto &[name, parm] : namedparms)
      ctx.diag << "  " << name << ": " << parm.type << '\n';
  }

  //|///////////////////// find_destructor //////////////////////////////////
  Callee find_destructor(LowerContext &ctx, Type *type, SourceLocation loc)
  {
    Callee callee;

    vector<MIR::Fragment> parms(1);
    map<string_view, MIR::Fragment> namedparms;

    parms[0].type = type;

    if (is_struct_type(type))
    {
      auto name = "~" + decl_cast<TagDecl>(type_cast<TagType>(type)->decl)->name;

      callee = find_callee(ctx, type, name, parms, namedparms);

      if (!callee)
      {
        ctx.diag.error("cannot resolve destructor", ctx.stack.back(), loc);
        diag_callee(ctx, callee, parms, namedparms);
      }
    }

    if (is_array_type(type))
    {
      callee.fx = find_builtin(ctx, Builtin::Array_Destructor, type);
    }

    if (is_tuple_type(type))
    {
      callee.fx = find_builtin(ctx, Builtin::Tuple_Destructor, type);
    }

    if (callee)
    {
      callee.fx.returntype = ctx.voidtype;
    }

    return callee;
  }

  //|///////////////////// find_type ////////////////////////////////////////
  MIR::Local find_type(LowerContext &ctx, vector<Scope> &stack, Expr *expr)
  {
    MIR::Fragment result;

    auto rm = ctx.push_barrier();

    swap(stack, ctx.stack);

    if (!lower_expr(ctx, result, expr))
    {
      swap(ctx.stack, stack);
      return nullptr;
    }

    swap(ctx.stack, stack);

    ctx.rollback_barrier(rm);

    return result.type;
  }

  //|///////////////////// find_returntype //////////////////////////////////
  MIR::Local find_returntype(LowerContext &ctx, FnSig const &fx)
  {
    MIR::Local returntype;

    assert(!fx.returntype);

    if (fx.fn->returntype)
    {
      returntype = MIR::Local(resolve_type(ctx, Scope(fx.fn, fx.typeargs), fx.fn->returntype), MIR::Local::LValue);

      if (is_const_type(returntype.type) || is_qualarg_type(returntype.type))
        returntype.type = remove_const_type(returntype.type);

      if (is_reference_type(fx.fn->returntype) && is_qualarg_type(remove_reference_type(fx.fn->returntype)))
        returntype.flags = (returntype.flags & ~MIR::Local::LValue) | MIR::Local::RValue;

      returntype.defn = fx.fn->returntype;
    }

    if (!fx.fn->returntype && fx.fn->body)
    {
      // TODO: maybe cache the mir for reuse ?

      auto mir = lower(fx, ctx.typetable, ctx.diag);

      if (mir.locals.empty() || !mir.locals[0])
        return nullptr;

      returntype = mir.locals[0];
    }

    returntype.flags &= ~MIR::Local::Const;
    returntype.flags &= ~MIR::Local::XValue;
    returntype.flags &= ~MIR::Local::Literal;

    if (!(is_reference_type(returntype.type) && (returntype.flags & MIR::Local::LValue)))
    {
      returntype.flags |= MIR::Local::RValue;
      returntype.flags &= ~MIR::Local::LValue;
    }

    return returntype;
  }

  //|///////////////////// commit_type //////////////////////////////////////
  void commit_type(LowerContext &ctx, MIR::local_t dst, Type *type, long flags = 0)
  {
    ctx.mir.locals[dst] = MIR::Local(type, flags);
  }

  //|///////////////////// promote_type /////////////////////////////////////
  bool promote_type(LowerContext &ctx, Type *&lhs, Type *rhs)
  {
    if (lhs == rhs)
      return true;

    rhs = remove_const_type(rhs);

    if (lhs == ctx.ptrliteraltype && is_reference_type(rhs))
      lhs = ctx.typetable.find_or_create<PointerType>(remove_reference_type(rhs));

    if (is_reference_type(lhs) && (is_pointer_type(rhs) || rhs == ctx.ptrliteraltype))
      lhs = ctx.typetable.find_or_create<PointerType>(remove_reference_type(lhs));

    switch (lhs->klass())
    {
      case Type::Const:

        if (auto type = type_cast<ConstType>(lhs)->type; promote_type(ctx, type, remove_const_type(rhs)))
        {
          lhs = ctx.typetable.find_or_create<ConstType>(type);

          return true;
        }

        return false;

      case Type::QualArg:

        if (auto type = type_cast<QualArgType>(lhs)->type; promote_type(ctx, type, remove_const_type(rhs)))
        {
          lhs = ctx.typetable.find_or_create<QualArgType>(type_cast<QualArgType>(lhs)->qualifiers, type);

          return true;
        }

        return false;

      case Type::Pointer:

        if (rhs == type(Builtin::Type_PtrLiteral))
          return true;

        if (!is_pointer_type(rhs) && !is_reference_type(rhs))
          return false;

        if (auto type = type_cast<PointerType>(lhs)->type; promote_type(ctx, type, remove_pointference_type(rhs)))
        {
          lhs = ctx.typetable.find_or_create<PointerType>(type);

          return true;
        }

        return false;

      case Type::Reference:

        if (!is_pointer_type(rhs) && !is_reference_type(rhs))
          return false;

        if (auto type = type_cast<ReferenceType>(lhs)->type; promote_type(ctx, type, remove_pointference_type(rhs)))
        {
          lhs = ctx.typetable.find_or_create<ReferenceType>(type);

          return true;
        }

        return false;

      default: {

        FnSig fx;
        DeduceContext tx;

        tx.allow_const_downcast = true;
        tx.allow_object_downcast = false;
        tx.allow_pointer_downcast = false;

        if (deduce_type(ctx, tx, ctx.stack.back(), fx, rhs, lhs))
        {
          if (lhs->klass() == Type::Tuple)
          {
            auto defns = type_cast<TupleType>(lhs)->defns;
            auto fields = type_cast<TupleType>(rhs)->fields;

            rhs = ctx.typetable.find_or_create<TupleType>(defns, fields);
          }

          lhs = rhs;

          return true;
        }

        return false;
      }
    }
  }

  //|///////////////////// lower_expr ///////////////////////////////////////

  struct Place
  {
    enum Op
    {
      Val,
      Fer,
    };

    Op op;
    MIR::local_t local;

    Place(MIR::local_t local) : op(Val), local(local) { }
    Place(Op op, MIR::local_t local) : op(op), local(local) { }
  };

  void lower_ref(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &expr);
  void lower_fer(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &expr);
  bool lower_call(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, vector<MIR::Fragment> &parms, map<string_view, MIR::Fragment> &namedparms, SourceLocation loc);

  //|///////////////////// realise //////////////////////////////////////////
  void realise(LowerContext &ctx, Place dst, MIR::Fragment &expr, long flags = 0)
  {
    if (flags & VarDecl::Const)
      expr.type.flags |= MIR::Local::Const;

    switch (dst.op)
    {
      case Place::Val:
        ctx.add_statement(MIR::Statement::assign(dst.local, std::move(expr.value)));
        break;

      case Place::Fer:
        ctx.add_statement(MIR::Statement::construct(dst.local, std::move(expr.value)));
        expr.type = resolve_as_value(ctx, expr.type);
        expr.type.flags |= MIR::Local::Reference;
        break;
    }

    if (expr.value.kind() == MIR::RValue::Call)
    {
      auto &[callee, args, loc] = expr.value.get<MIR::RValue::Call>();

      if (callee.throwtype)
      {
        ctx.add_block(MIR::Terminator::catcher(ctx.errorarg, ctx.currentblockid + 1));

        ctx.throws.push_back(ctx.currentblockid);
        ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid));
      }
    }
  }

  //|///////////////////// realise_destructor ///////////////////////////////
  void realise_destructor(LowerContext &ctx, MIR::local_t arg, SourceLocation loc)
  {
    assert(!(ctx.mir.locals[arg].flags & MIR::Local::Reference));

    auto type = ctx.mir.locals[arg].type;

    if (is_trivial_destroy_type(type))
      return;

    if (auto callee = find_destructor(ctx, type, loc))
    {
      auto src = ctx.add_local();

      commit_type(ctx, src, type, MIR::Local::Reference);

      auto dst = ctx.add_local();

      commit_type(ctx, dst, ctx.voidtype);

      ctx.push_barrier();
      ctx.retire_statement(MIR::Statement::storagedead(dst));
      ctx.retire_statement(MIR::Statement::storagedead(src));
      ctx.retire_statement(MIR::Statement::assign(dst, MIR::RValue::call(callee.fx, { src }, loc)));
      ctx.retire_statement(MIR::Statement::assign(src, MIR::RValue::local(MIR::RValue::Ref, arg, loc)));
      ctx.retire_statement(MIR::Statement::storagelive(dst));
      ctx.retire_statement(MIR::Statement::storagelive(src));
    }
  }

  //|///////////////////// realise_as_reference /////////////////////////////
  void realise_as_reference(LowerContext &ctx, Place dst, MIR::Fragment &expr, long flags = 0)
  {
    if (!(expr.type.flags & MIR::Local::Reference))
      lower_ref(ctx, expr, expr);

    realise(ctx, dst, expr, flags);
  }

  //|///////////////////// realise_as_value /////////////////////////////////
  void realise_as_value(LowerContext &ctx, Place dst, MIR::Fragment &expr, long flags = 0)
  {
    if (expr.type.flags & MIR::Local::Reference)
      lower_fer(ctx, expr, expr);

    if (expr.value.kind() == MIR::RValue::Variable || (expr.value.kind() == MIR::RValue::Constant && !(flags & VarDecl::Const)))
    {
      if (is_struct_type(expr.type.type) || is_array_type(expr.type.type) || is_tuple_type(expr.type.type) || is_lambda_type(expr.type.type) || is_function_type(expr.type.type))
      {
        vector<MIR::Fragment> parms(1);
        map<string_view, MIR::Fragment> namedparms;

        parms[0] = std::move(expr);

        auto callee = find_callee(ctx, expr.type.type, parms, namedparms);

        if (!callee)
        {
          ctx.diag.error("cannot resolve copy constructor", ctx.stack.back(), parms[0].value.loc());
          diag_callee(ctx, callee, parms, namedparms);
          return;
        }

        lower_call(ctx, expr, callee.fx, parms, namedparms, parms[0].value.loc());
      }

      expr.type.flags &= ~MIR::Local::Const;
    }

    expr.type.flags &= ~MIR::Local::Literal;

    realise(ctx, dst, expr, flags);
  }

  //|///////////////////// collapse_returns /////////////////////////////////
  void collapse_returns(LowerContext &ctx)
  {
    for(auto i = ctx.barriers.back().firstreturn; i < ctx.returns.size(); ++i)
      ctx.mir.blocks[ctx.returns[i]].terminator.blockid = ctx.currentblockid;

    ctx.returns.resize(ctx.barriers.back().firstreturn);
    ctx.returns.push_back(ctx.currentblockid);
  }

  //|///////////////////// literal_cast /////////////////////////////////////
  bool literal_cast(LowerContext &ctx, MIR::RValue &result, MIR::RValue &expr, Type const *type)
  {
    assert(expr.kind() == MIR::RValue::Constant);

    auto value = expr.get<MIR::RValue::Constant>();

    if (holds_alternative<BoolLiteralExpr*>(value))
    {
      auto literal = get<BoolLiteralExpr*>(value);

      switch (type->klass())
      {
        case Type::Builtin:

          switch(type_cast<BuiltinType>(type)->kind())
          {
            case BuiltinType::Bool:
              result = literal;
              return true;

            case BuiltinType::I8:
            case BuiltinType::I16:
            case BuiltinType::I32:
            case BuiltinType::I64:
            case BuiltinType::ISize:
            case BuiltinType::U8:
            case BuiltinType::U16:
            case BuiltinType::U32:
            case BuiltinType::U64:
            case BuiltinType::USize:
            case BuiltinType::IntLiteral:
              result = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, literal->value()), literal->loc());
              return true;

            case BuiltinType::F32:
            case BuiltinType::F64:
            case BuiltinType::FloatLiteral:
              result = ctx.mir.make_expr<FloatLiteralExpr>(Numeric::float_literal(literal->value()), literal->loc());
              return true;

            default:
              goto boolinvalid;
          }

          break;

        default:
        boolinvalid:
          ctx.diag.error("invalid literal cast", ctx.stack.back(), literal->loc());
          ctx.diag << "  source type: '#bool' destination type: '" << *type << "'\n";
          break;
      }
    }

    if (holds_alternative<CharLiteralExpr*>(value))
    {
      auto literal = get<CharLiteralExpr*>(value);

      switch (type->klass())
      {
        case Type::Builtin:

          switch(type_cast<BuiltinType>(type)->kind())
          {
            case BuiltinType::Char:
              result = literal;
              return true;

            case BuiltinType::I8:
            case BuiltinType::I16:
            case BuiltinType::I32:
            case BuiltinType::I64:
            case BuiltinType::ISize:
            case BuiltinType::U8:
            case BuiltinType::U16:
            case BuiltinType::U32:
            case BuiltinType::U64:
            case BuiltinType::USize:
            case BuiltinType::IntLiteral:
              result = ctx.mir.make_expr<IntLiteralExpr>(literal->value(), literal->loc());
              return true;

            case BuiltinType::F32:
            case BuiltinType::F64:
            case BuiltinType::FloatLiteral:
              result = ctx.mir.make_expr<FloatLiteralExpr>(Numeric::float_cast<double>(literal->value()), literal->loc());
              return true;

            default:
              goto charinvalid;
          }

          break;

        default:
        charinvalid:
          ctx.diag.error("invalid literal cast", ctx.stack.back(), literal->loc());
          ctx.diag << "  source type: '#char' destination type: '" << *type << "'\n";
          break;
      }
    }

    if (holds_alternative<IntLiteralExpr*>(value))
    {
      auto literal = get<IntLiteralExpr*>(value);

      switch(type->klass())
      {
        case Type::Builtin:

          switch(type_cast<BuiltinType>(type)->kind())
          {
            case BuiltinType::Bool:
              result = ctx.mir.make_expr<BoolLiteralExpr>(literal->value().value != 0, literal->loc());
              return true;

            case BuiltinType::Char:
              result = ctx.mir.make_expr<CharLiteralExpr>(literal->value(), literal->loc());
              return true;

            case BuiltinType::I8:
            case BuiltinType::I16:
            case BuiltinType::I32:
            case BuiltinType::I64:
            case BuiltinType::ISize:
            case BuiltinType::U8:
            case BuiltinType::U16:
            case BuiltinType::U32:
            case BuiltinType::U64:
            case BuiltinType::USize:
            case BuiltinType::IntLiteral:
              result = literal;
              return true;

            case BuiltinType::F32:
            case BuiltinType::F64:
            case BuiltinType::FloatLiteral:
              result = ctx.mir.make_expr<FloatLiteralExpr>(Numeric::float_cast<double>(literal->value()), literal->loc());
              return true;

            default:
              goto intinvalid;
          }

          break;

        case BuiltinType::Tag:

          switch (type_cast<TagType>(type)->decl->kind())
          {
            case Decl::Enum:
              result = literal;
              return true;

            default:
              goto intinvalid;
          }

          break;

        case BuiltinType::Pointer:
          break;

        default:
        intinvalid:
          ctx.diag.error("invalid literal cast", ctx.stack.back(), literal->loc());
          ctx.diag << "  source type: '#int' destination type: '" << *type << "'\n";
          break;
      }
    }

    if (holds_alternative<FloatLiteralExpr*>(value))
    {
      auto literal = get<FloatLiteralExpr*>(value);

      switch (type->klass())
      {
        case Type::Builtin:

          switch(type_cast<BuiltinType>(type)->kind())
          {
            case BuiltinType::Bool:
              result = ctx.mir.make_expr<BoolLiteralExpr>(literal->value().value != 0, literal->loc());
              return true;

            case BuiltinType::Char:
              result = ctx.mir.make_expr<CharLiteralExpr>(Numeric::int_cast<double>(literal->value()), literal->loc());
              return true;

            case BuiltinType::I8:
            case BuiltinType::I16:
            case BuiltinType::I32:
            case BuiltinType::I64:
            case BuiltinType::ISize:
            case BuiltinType::U8:
            case BuiltinType::U16:
            case BuiltinType::U32:
            case BuiltinType::U64:
            case BuiltinType::USize:
            case BuiltinType::IntLiteral:
              result = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_cast<double>(literal->value()), literal->loc());
              return true;

            case BuiltinType::F32:
            case BuiltinType::F64:
            case BuiltinType::FloatLiteral:
              result = literal;
              return true;

            default:
              goto fltinvalid;
          }

          break;

        default:
        fltinvalid:
          ctx.diag.error("invalid literal cast", ctx.stack.back(), literal->loc());
          ctx.diag << "  source type: '#float' destination type: '" << *type << "'\n";
          break;
      }
    }

    if (holds_alternative<PointerLiteralExpr*>(value))
    {
      auto literal = get<PointerLiteralExpr*>(value);

      switch (type->klass())
      {
        case Type::Builtin:

          switch(type_cast<BuiltinType>(type)->kind())
          {
            case BuiltinType::Bool:
              result = ctx.mir.make_expr<BoolLiteralExpr>(false, literal->loc());
              return true;

            default:
              goto ptrinvalid;
          }

          break;

        case Type::Pointer:
          result = literal;
          return true;

        default:
        ptrinvalid:
          ctx.diag.error("invalid cast", ctx.stack.back(), literal->loc());
          ctx.diag << "  source type: 'null' destination type: '" << *type << "'\n";
          break;
      }
    }

    return false;
  }

  //|///////////////////// lower_lit ////////////////////////////////////////
  void lower_lit(LowerContext &ctx, MIR::Fragment &result, FnSig &callee)
  {
    auto V = callee.find_type(callee.fn->args[1])->second;

    result.type = MIR::Local(callee.returntype, MIR::Local::Const | MIR::Local::Literal);
    result.value = MIR::RValue::literal(type_cast<TypeLitType>(V)->value);
  }

  //|///////////////////// lower_ctor ///////////////////////////////////////
  void lower_ctor(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, MIR::Fragment &expr, SourceLocation loc)
  {
    if (expr.type.flags & MIR::Local::Reference)
      lower_fer(ctx, expr, expr);

    result.type = MIR::Local(callee.returntype, callee.fn->returntype, expr.type.flags);
    result.value = std::move(expr.value);
  }

  //|///////////////////// lower_trait //////////////////////////////////////
  void lower_trait(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, SourceLocation loc)
  {
    Type *args[2] = {};
    Type *type[2] = {};

    for(size_t i = 0; i < callee.fn->args.size(); ++i)
    {
      args[i] = callee.find_type(callee.fn->args[i])->second;
      type[i] = remove_const_type(args[i]);
    }

    bool match = false;

    switch(callee.fn->builtin)
    {
      case Builtin::is_const:
        match = is_const_type(args[0]) || (is_qualarg_type(args[0]) && (type_cast<QualArgType>(args[0])->qualifiers & QualArgType::Const));
        break;

      case Builtin::is_rvalue:
        match = is_qualarg_type(args[0]) && (type_cast<QualArgType>(args[0])->qualifiers & QualArgType::RValue);
        break;

      case Builtin::is_array:
        match = is_array_type(type[0]);
        break;

      case Builtin::is_tuple:
        match = is_tuple_type(type[0]);
        break;

      case Builtin::is_trivial_copy:
        match = is_trivial_copy_type(type[0]);
        break;

      case Builtin::is_trivial_assign:
        match = is_trivial_assign_type(type[0]);
        break;

      case Builtin::is_trivial_destroy:
        match = is_trivial_destroy_type(type[0]);
        break;

      case Builtin::is_integral:
        match = is_int_type(type[0]) || is_char_type(type[0]);
        break;

      case Builtin::is_floating_point:
        match = is_float_type(type[0]);
        break;

      case Builtin::is_arithmetic:
        match = is_int_type(type[0]) || is_char_type(type[0]) || is_float_type(type[0]);
        break;

      case Builtin::is_same:

        for(size_t i = 0; i < 2; ++i)
        {
          if (is_qualarg_type(args[i]))
          {
            if (type_cast<QualArgType>(args[i])->qualifiers & QualArgType::Const)
              args[i] = ctx.typetable.find_or_create<ConstType>(type_cast<QualArgType>(args[i])->type);
            else
              args[i] = type_cast<QualArgType>(args[i])->type;
          }
        }

        match = (args[0] == args[1]);
        break;

      case Builtin::is_match:

        if (!is_typearg_type(args[0]) || !type_cast<TypeArgType>(args[0])->koncept)
        {
          ctx.diag.error("first argument must be a concept", ctx.stack.back(), loc);
          return;
        }

        if (auto typearg = type_cast<TypeArgType>(args[0]); typearg->koncept)
        {
          FnSig sig;

          match = match_concept(ctx, ctx.stack.back(), sig, decl_cast<ConceptDecl>(typearg->koncept), typearg->args, args[1]);
        }
        break;

      default:
        assert(false);
    }

    result.type = MIR::Local(callee.returntype, MIR::Local::Const | MIR::Local::Literal);
    result.value = ctx.mir.make_expr<BoolLiteralExpr>(match, loc);
  }

  //|///////////////////// array_len ////////////////////////////////////////
  void lower_array_len(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, SourceLocation loc)
  {
    auto type = callee.find_type(callee.fn->args[0])->second;

    while (is_struct_type(type) && decl_cast<StructDecl>(type_cast<TagType>(type)->decl)->basetype)
      type = type_cast<TagType>(type)->fields[0];

    result.type = MIR::Local(callee.returntype, MIR::Local::Const | MIR::Local::Literal);
    result.value = expr_cast<IntLiteralExpr>(type_cast<TypeLitType>(type_cast<ArrayType>(type)->size)->value);
  }

  //|///////////////////// tuple_len ////////////////////////////////////////
  void lower_tuple_len(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, SourceLocation loc)
  {
    auto type = callee.find_type(callee.fn->args[0])->second;

    while (is_struct_type(type) && decl_cast<StructDecl>(type_cast<TagType>(type)->decl)->basetype)
      type = type_cast<TagType>(type)->fields[0];

    result.type = MIR::Local(callee.returntype, MIR::Local::Const | MIR::Local::Literal);
    result.value = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, type_cast<TupleType>(type)->fields.size()), loc);
  }

  //|///////////////////// lower_site ///////////////////////////////////////
  void lower_site(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, SourceLocation loc)
  {
    vector<Expr*> fields;

    fields.push_back(ctx.mir.make_expr<StringLiteralExpr>(ctx.module->file(), loc));
    fields.push_back(ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(ctx.site_override.lineno != -1 ? ctx.site_override.lineno : ctx.site.lineno), loc));
    fields.push_back(ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(ctx.site_override.charpos != -1 ? ctx.site_override.charpos : ctx.site.charpos), loc));
    fields.push_back(ctx.mir.make_expr<StringLiteralExpr>(ctx.mir.fx.fn ? ctx.mir.fx.fn->name : string_view(), loc));

    result.type = MIR::Local(callee.returntype, MIR::Local::Const | MIR::Local::Literal);
    result.value = ctx.mir.make_expr<CompoundLiteralExpr>(fields, loc);
  }

  //|///////////////////// lower_ref ////////////////////////////////////////
  void lower_ref(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &expr)
  {
    assert(!(expr.type.flags & MIR::Local::Reference));

    if (expr.value.kind() != MIR::RValue::Variable || get<0>(expr.value.get<MIR::RValue::Variable>()) == MIR::RValue::Ref)
    {
      auto arg = ctx.add_temporary();

      realise(ctx, arg, expr);

      commit_type(ctx, arg, expr.type.type, expr.type.flags);

      if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
        realise_destructor(ctx, arg, expr.value.loc());

      expr.value = MIR::RValue::local(MIR::RValue::Val, arg, expr.value.loc());
    }

    auto &[op, arg, fields, loc] = expr.value.get<MIR::RValue::Variable>();

    switch (op)
    {
      case MIR::RValue::Ref:
        assert(false);
        break;

      case MIR::RValue::Val:
        op = MIR::RValue::Ref;
        break;

      case MIR::RValue::Fer:
        op = MIR::RValue::Val;
        break;

      case MIR::RValue::Idx:
        assert(false);
        break;
    }

    result.type = expr.type;
    result.type.flags &= ~MIR::Local::Literal;
    result.type.flags |= MIR::Local::Reference;
    result.value = MIR::RValue::field(op, arg, std::move(fields), loc);
  }

  //|///////////////////// lower_fer ////////////////////////////////////////
  void lower_fer(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &expr)
  {
    assert(expr.type.flags & MIR::Local::Reference);

    if (expr.value.kind() != MIR::RValue::Variable || get<0>(expr.value.get<MIR::RValue::Variable>()) == MIR::RValue::Fer)
    {
      auto arg = ctx.add_temporary();

      realise(ctx, arg, expr);

      commit_type(ctx, arg, expr.type.type, expr.type.flags);

      if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
        realise_destructor(ctx, arg, expr.value.loc());

      expr.value = MIR::RValue::local(MIR::RValue::Val, arg, expr.value.loc());
    }

    auto &[op, arg, fields, loc] = expr.value.get<MIR::RValue::Variable>();

    switch (op)
    {
      case MIR::RValue::Ref:
        op = MIR::RValue::Val;
        break;

      case MIR::RValue::Val:
        op = MIR::RValue::Fer;
        break;

      case MIR::RValue::Fer:
        assert(false);
        break;

      case MIR::RValue::Idx:
        assert(false);
        break;
    }

    result.type = expr.type;
    result.type.flags &= ~MIR::Local::Literal;
    result.type.flags &= ~MIR::Local::Reference;
    result.value = MIR::RValue::field(op, arg, std::move(fields), loc);
  }

  //|///////////////////// lower_deref //////////////////////////////////////
  bool lower_deref(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &expr, SourceLocation loc)
  {
    vector<MIR::Fragment> parms(1);
    map<string_view, MIR::Fragment> namedparms;

    parms[0] = std::move(expr);

    auto callee = find_callee(ctx, parms[0].type.type, "*", parms, namedparms);

    if (!callee)
    {
      ctx.diag.error("cannot resolve operator dereference", ctx.stack.back(), loc);
      diag_callee(ctx, callee, parms, namedparms);
      return false;
    }

    return lower_call(ctx, result, callee.fx, parms, namedparms, loc);
  }

  //|///////////////////// lower_deref //////////////////////////////////////
  bool lower_base_deref(LowerContext &ctx, MIR::Fragment &base)
  {
    while (is_pointference_type(base.type.type))
    {
      if (is_pointer_type(base.type.type))
      {
        if (!lower_deref(ctx, base, base, base.value.loc()))
          return false;
      }

      if (is_reference_type(base.type.type))
      {
        if (base.type.flags & MIR::Local::Reference)
          lower_fer(ctx, base, base);

        base.type = resolve_as_reference(ctx, base.type);
      }
    }

    return true;
  }

  //|///////////////////// lower_deref //////////////////////////////////////
  bool lower_expr_deref(LowerContext &ctx, MIR::Fragment &expr)
  {
    while (is_reference_type(expr.type.defn))
    {
      if (expr.type.flags & MIR::Local::Reference)
        lower_fer(ctx, expr, expr);

      expr.type = resolve_as_reference(ctx, expr.type);
      expr.type.defn = remove_const_type(remove_reference_type(expr.type.defn));
    }

    return true;
  }

  //|///////////////////// lower_field //////////////////////////////////////
  bool lower_field(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &base, Field &field, SourceLocation loc)
  {
    if (base.value.kind() == MIR::RValue::Constant)
    {
      auto literal = get<CompoundLiteralExpr*>(base.value.get<MIR::RValue::Constant>());

      result.type = MIR::Local(field.type, base.type.flags);
      result.value = MIR::RValue::literal(literal->fields[field.index]);

      return true;
    }

    if (base.value.kind() != MIR::RValue::Variable || get<0>(base.value.get<MIR::RValue::Variable>()) == MIR::RValue::Fer)
    {
      auto arg = ctx.add_temporary();

      realise(ctx, arg, base);

      commit_type(ctx, arg, base.type.type, base.type.flags);

      base.value = MIR::RValue::local((base.type.flags & MIR::Local::Reference) ? MIR::RValue::Val : MIR::RValue::Ref, arg, loc);
    }

    auto &[op, arg, fields, lloc] = base.value.get<MIR::RValue::Variable>();

    fields.push_back(MIR::RValue::Field{ (base.type.flags & MIR::Local::Reference) ? op : MIR::RValue::Ref, field.index });

    result.type = MIR::Local(field.type, field.defn, base.type.flags);

    if (field.flags & VarDecl::Const)
      result.type.flags |= MIR::Local::Const;

#if TRANSATIVE_CONST
    if ((base.type.flags & MIR::Local::Const) && is_pointer_type(result.type.type))
    {
      if (auto rhs = remove_pointer_type(result.type.type); !is_const_type(rhs))
        result.type.type = ctx.typetable.find_or_create<PointerType>(ctx.typetable.find_or_create<ConstType>(rhs));
    }

    if ((base.type.flags & MIR::Local::Const) && is_reference_type(result.type.type))
    {
      if (auto rhs = remove_reference_type(result.type.type); !is_const_type(rhs))
        result.type.type = ctx.typetable.find_or_create<ReferenceType>(ctx.typetable.find_or_create<ConstType>(rhs));
    }
#endif

    result.type.flags |= MIR::Local::Reference;
    result.value = MIR::RValue::field(MIR::RValue::Ref, arg, std::move(fields), loc);

    if (!lower_expr_deref(ctx, result))
      return false;

    return true;
  }

  //|///////////////////// lower_base_cast //////////////////////////////////
  bool lower_base_cast(LowerContext &ctx, MIR::Fragment &result, Type *type, MIR::Fragment &expr)
  {
    while (is_struct_type(expr.type.type))
    {
      if (expr.type.type == type)
        break;

      if (auto field = find_field(ctx, type_cast<TagType>(expr.type.type), "super"))
      {
        lower_field(ctx, expr, expr, field, expr.value.loc());

        continue;
      }

      break;
    }

    if (expr.type.type != type)
    {
      auto arg = ctx.add_temporary();

      realise_as_value(ctx, arg, expr);

      commit_type(ctx, arg, expr.type.type, expr.type.flags);

      expr.type = MIR::Local(type, expr.type.flags);
      expr.value = MIR::RValue::cast(arg, expr.value.loc());
    }

    result.type = expr.type;
    result.value = expr.value;

    return true;
  }

  //|///////////////////// lower_lambda_decay ///////////////////////////////
  bool lower_lambda_decay(LowerContext &ctx, MIR::Fragment &result, Scope const &scope, Type *type, MIR::Fragment &expr)
  {
    auto lhs = remove_const_type(remove_pointference_type(type));
    auto rhs = remove_const_type(remove_pointference_type(expr.type.type));

    FnSig callop(decl_cast<LambdaDecl>(type_cast<TagType>(rhs)->decl)->fn, type_cast<TagType>(rhs)->args);

    if (!deduce_calltype(ctx, scope, callop, type_cast<FunctionType>(lhs), rhs))
    {
      ctx.diag.error("type mismatch", ctx.stack.back(), expr.value.loc());
      ctx.diag << "  function type: '" << *rhs << "' required type: '" << *lhs << "'\n";
      return false;
    }

    if (!is_pointference_type(type))
      expr.type.flags |= MIR::Local::Reference;
    else
      expr.type.flags &= ~MIR::Local::Reference;

    result.type = MIR::Local(type, expr.type.flags);
    result.value = MIR::RValue::function(callop, expr.value.loc());

    return true;
  }

  //|///////////////////// lower_pack ///////////////////////////////////////
  bool lower_pack(LowerContext &ctx, MIR::Fragment &result, Scope const &scope, ParmVarDecl *parm, vector<MIR::Fragment> &exprs, size_t k, size_t n, SourceLocation loc)
  {
    auto tup = ctx.add_temporary();

    auto parmtype = resolve_type_as_value(ctx, scope, parm);
    auto tupletype = type_cast<TupleType>(remove_reference_type(parmtype));

    for(size_t i = k, index = 0; i < n; ++i, ++index)
    {
      auto type = tupletype->fields[index];

      auto dst = ctx.add_temporary();
      auto res = ctx.add_temporary();

      MIR::Fragment address;
      address.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(type), MIR::Local::LValue);
      address.value = MIR::RValue::field(MIR::RValue::Ref, tup, MIR::RValue::Field{ MIR::RValue::Ref, index }, loc);

      realise_as_value(ctx, dst, address);

      commit_type(ctx, dst, address.type.type, address.type.flags);

      if (is_reference_type(type_cast<PackType>(parm->type)->type))
        type = remove_const_type(remove_reference_type(type));

#if PACK_REFS
      auto defn = tupletype->defns[index];

      if (is_reference_type(type_cast<PackType>(parm->type)->type))
        defn = remove_const_type(remove_reference_type(defn));

      if (is_reference_type(defn))
      {
        if (!(exprs[i].type.flags & MIR::Local::Reference))
          lower_ref(ctx, exprs[i], exprs[i]);

        exprs[i].type = resolve_as_value(ctx, exprs[i].type);
      }
#endif

      if (is_base_cast(ctx, type, exprs[i].type.type))
        lower_base_cast(ctx, exprs[i], type, exprs[i]);

      exprs[i].type.type = type;

      if (is_reference_type(type_cast<PackType>(parm->type)->type))
        realise_as_reference(ctx, Place(Place::Fer, res), exprs[i]);
      else
        realise_as_value(ctx, Place(Place::Fer, res), exprs[i]);

      commit_type(ctx, res, exprs[i].type.type, exprs[i].type.flags);
    }

    commit_type(ctx, tup, tupletype, MIR::Local::RValue);

    if (!(ctx.mir.locals[tup].flags & MIR::Local::Reference))
      realise_destructor(ctx, tup, loc);

    result.type = MIR::Local(tupletype, MIR::Local::RValue | MIR::Local::Reference);
    result.value = MIR::RValue::local(MIR::RValue::Ref, tup, loc);

    return true;
  }

  //|///////////////////// lower_unpack /////////////////////////////////////
  bool lower_unpack(LowerContext &ctx, vector<MIR::Fragment> &parms, Expr *parm, MIR::Fragment &expr)
  {
    auto arg = ctx.add_temporary();

    realise_as_reference(ctx, arg, expr);

    commit_type(ctx, arg, expr.type.type, expr.type.flags);

    auto pack = type_cast<TupleType>(expr.type.type);

    for(size_t index = 0; index < pack->fields.size(); ++index)
    {
      MIR::Fragment field;
      field.type = MIR::Local(pack->fields[index], pack->defns[index], expr.type.flags);
      field.value = MIR::RValue::field(MIR::RValue::Ref, arg, MIR::RValue::Field{ MIR::RValue::Val, index }, parm->loc());

      if (!lower_expr_deref(ctx, field))
        return false;

      if (expr_cast<UnaryOpExpr>(parm)->subexpr->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(expr_cast<UnaryOpExpr>(parm)->subexpr)->op() == UnaryOpExpr::Fwd)
      {
        if (field.type.flags & MIR::Local::XValue)
          field.type.flags = (field.type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;
      }

      parms.push_back(std::move(field));
    }

    return true;
  }

  //|///////////////////// lower_call ///////////////////////////////////////
  bool lower_call(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, vector<MIR::Fragment> &parms, map<string_view, MIR::Fragment> &namedparms, SourceLocation loc)
  {
    auto n = parms.size();

    auto scope = Scope(callee.fn, callee.typeargs);

    // throw type

    if (is_throws(ctx, callee.fn))
    {
      if (!ctx.errorarg)
      {
        ctx.diag.error("calling throws function outside try block", ctx.stack.back(), loc);
        return false;
      }

      callee.throwtype = ctx.mir.locals[ctx.errorarg].type;
    }

    // bake parameters

    for(size_t i = 0, k = 0; i < callee.fn->parms.size(); ++i)
    {
      auto parm = decl_cast<ParmVarDecl>(callee.fn->parms[i]);
      auto parmtype = resolve_type_as_reference(ctx, scope, parm);

      if (is_pack_type(parm->type))
      {
        parms.insert(parms.begin() + k, MIR::Fragment());

        if (!(parm->flags & VarDecl::Literal))
        {
          lower_pack(ctx, parms[k], scope, parm, parms, k + 1, n + 1, loc);

          parmtype = parms[k].type.type;
        }

        parms.erase(parms.begin() + k + 1, parms.begin() + n + 1);
        n = k + 1;
      }

      if (parms.size() <= k)
      {
        if (auto j = namedparms.find(parm->name); j != namedparms.end())
        {
          parms.push_back(std::move(j->second));
        }

        else if (auto j = find_if(namedparms.begin(), namedparms.end(), [&](auto &k) { return k.first.back() == '?' && k.first.substr(0, k.first.size()-1) == parm->name; }); j != namedparms.end())
        {
          parms.push_back(std::move(j->second));
        }

        else if (parm->defult)
        {
          vector<Scope> stack;
          seed_stack(stack, scope);

          swap(stack, ctx.stack);
          swap(loc, ctx.site_override);

          MIR::Fragment expr;

          if (!lower_expr(ctx, expr, parm->defult))
            return false;

          if (expr.type.type != parmtype)
          {
            if (!deduce_type(ctx, ctx.stack.back(), callee, parm, expr.type))
            {
              ctx.diag.error("type mismatch", ctx.stack.back(), parm->loc());
              ctx.diag << "  variable type: '" << *parm->type << "' required type: '" << *expr.type.type << "'\n";
              return false;
            }

            scope = Scope(callee.fn, callee.typeargs);
            parmtype = resolve_type_as_reference(ctx, scope, parm);
          }

          parms.push_back(std::move(expr));

          swap(ctx.site_override, loc);
          swap(ctx.stack, stack);
        }
      }

      if (parm->flags & VarDecl::Literal)
      {
        parms.erase(parms.begin() + k);
        n -= 1;
        continue;
      }

      if (is_refn_type(ctx, parm))
      {
        if (auto refn = find_refn(ctx, scope, parm, parms[k].type); refn.fn)
        {
          vector<MIR::Fragment> callparms(1);
          map<string_view, MIR::Fragment> callnamedparms;

          callparms[0] = std::move(parms[k]);

          lower_call(ctx, parms[k], refn, callparms, callnamedparms, parms[k].value.loc());

          parmtype = parms[k].type.type;
        }
      }

      if (is_lambda_decay(ctx, parmtype, parms[k].type.type))
      {
        if (!lower_lambda_decay(ctx, parms[k], scope, parmtype, parms[k]))
          return false;
      }

      if (is_base_cast(ctx, parmtype, parms[k].type.type))
      {
        if (!lower_base_cast(ctx, parms[k], parmtype, parms[k]))
          return false;
      }

      parms[k].type.type = parmtype;

      k += 1;
    }

    result.type = find_returntype(ctx, callee);

    if (is_function_type(result.type.type))
      ctx.diag.error("cannot return a function type", ctx.stack.back(), loc);

    callee.returntype = resolve_as_value(ctx, result.type).type;

    // handle const builtins

    if (callee.fn->flags & FunctionDecl::Builtin)
    {
      switch(callee.fn->builtin)
      {
        case Builtin::Type_Void:
          lower_expr(ctx, result, ctx.mir.make_expr<VoidLiteralExpr>(loc));
          return true;

        case Builtin::Type_Bool:
        case Builtin::Type_Char:
        case Builtin::Type_I8:
        case Builtin::Type_I16:
        case Builtin::Type_I32:
        case Builtin::Type_I64:
        case Builtin::Type_ISize:
        case Builtin::Type_U8:
        case Builtin::Type_U16:
        case Builtin::Type_U32:
        case Builtin::Type_U64:
        case Builtin::Type_USize:
        case Builtin::Type_F32:
        case Builtin::Type_F64:
        case Builtin::Type_IntLiteral:
        case Builtin::Type_FloatLiteral:
        case Builtin::Type_StringLiteral:
        case Builtin::Type_Ptr:
        case Builtin::Type_Ref:
        case Builtin::Type_Enum:
          lower_ctor(ctx, result, callee, parms[0], loc);
          return true;

        case Builtin::Type_PtrLiteral:
          lower_expr(ctx, result, ctx.mir.make_expr<PointerLiteralExpr>(loc));
          result.type.type = callee.returntype;
          return true;

        case Builtin::Type_Lit:
          lower_lit(ctx, result, callee);
          return true;

        case Builtin::Builtin_Destructor:
          lower_expr(ctx, result, ctx.mir.make_expr<VoidLiteralExpr>(loc));
          return true;

        case Builtin::ArrayLen:
        case Builtin::array_len:
          lower_array_len(ctx, result, callee, loc);
          return true;

        case Builtin::TupleLen:
        case Builtin::tuple_len:
          lower_tuple_len(ctx, result, callee, loc);
          return true;

        case Builtin::is_const:
        case Builtin::is_rvalue:
        case Builtin::is_array:
        case Builtin::is_tuple:
        case Builtin::is_trivial_copy:
        case Builtin::is_trivial_assign:
        case Builtin::is_trivial_destroy:
        case Builtin::is_integral:
        case Builtin::is_floating_point:
        case Builtin::is_arithmetic:
        case Builtin::is_same:
        case Builtin::is_match:
          lower_trait(ctx, result, callee, loc);
          return true;

        case Builtin::__site__:
          lower_site(ctx, result, callee, loc);
          return true;

        default:
          break;
      }
    }

    // constant fold

    if (callee.fn->flags & FunctionDecl::Const)
    {
      if (all_of(parms.begin(), parms.end(), [](auto &k) { return k.type.flags & MIR::Local::Literal; }) && is_trivial_copy_type(callee.returntype))
      {
        vector<EvalResult> arglist;

        for(auto const &[parm, expr] : zip(callee.parameters(), parms))
        {
          EvalResult arg;

          arg.type = resolve_type(ctx, scope, decl_cast<ParmVarDecl>(parm)->type);
          arg.value = std::visit([&](auto &v) -> Expr* { return v; }, expr.value.get<MIR::RValue::Constant>());

          arglist.push_back(arg);
        }

        if (auto expr = evaluate(ctx.stack.back(), callee, arglist, ctx.typetable, ctx.diag, loc))
        {
          lower_expr(ctx, result, expr.value);

          result.type.type = expr.type;

          return true;
        }
      }
    }

    // resolve arguments

    vector<MIR::local_t> arglist;

    for(auto const &[parm, expr] : zip(callee.parameters(), parms))
    {
      auto arg = ctx.add_temporary();

      if (is_reference_type(decl_cast<ParmVarDecl>(parm)->type) || is_pack_type(decl_cast<ParmVarDecl>(parm)->type))
        realise_as_reference(ctx, arg, expr);
      else
        realise_as_value(ctx, arg, expr, parm->flags & VarDecl::Const);

      commit_type(ctx, arg, expr.type.type, expr.type.flags);

      if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
        realise_destructor(ctx, arg, loc);

      arglist.push_back(arg);
    }

    result.value = MIR::RValue::call(callee, arglist, loc);

    if (!lower_expr_deref(ctx, result))
      return false;

    return true;
  }

  //|///////////////////// lower_cast ///////////////////////////////////////
  bool lower_cast(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &expr, Type *type, SourceLocation loc)
  {
    vector<MIR::Fragment> parms(1);
    map<string_view, MIR::Fragment> namedparms;

    parms[0] = std::move(expr);

    auto callee = find_callee(ctx, parms[0].type.type, type_cast<BuiltinType>(type)->name(), parms, namedparms);

    if (!callee)
    {
      ctx.diag.error("cannot resolve implicit cast", ctx.stack.back(), loc);
      diag_callee(ctx, callee, parms, namedparms);
      return false;
    }

    lower_call(ctx, result, callee.fx, parms, namedparms, loc);

    if (!is_bool_type(result.type.type))
      return false;

    return true;
  }

  //|///////////////////// lower_new ////////////////////////////////////////
  bool lower_new(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &address, Type *type, vector<Expr*> const &parms, map<string, Expr*> const &namedparms, SourceLocation loc)
  {
    vector<MIR::Fragment> callparms;
    map<string_view, MIR::Fragment> callnamedparms;

    for(auto &parm : parms)
    {
      MIR::Fragment expr;

      if (!lower_expr(ctx, expr, parm))
        return false;

      if (parm->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(parm)->op() == UnaryOpExpr::Unpack)
      {
        if (!lower_unpack(ctx, callparms, parm, expr))
          return false;

        continue;
      }

      callparms.push_back(std::move(expr));
    }

    for(auto &[name, parm] : namedparms)
    {
      MIR::Fragment expr;

      if (!lower_expr(ctx, expr, parm))
        return false;

      callnamedparms.emplace(name, std::move(expr));
    }

    if (type->klass() == Type::TypeArg)
    {
      ctx.diag.error("unresolved type for constructor", ctx.stack.back(), loc);
      return false;
    }

    auto callee = find_callee(ctx, type, callparms, callnamedparms);

    if (!callee)
    {
      ctx.diag.error("cannot resolve constructor", ctx.stack.back(), loc);
      ctx.diag << "  for type: " << *type << '\n';
      diag_callee(ctx, callee, callparms, callnamedparms);
      return false;
    }

    lower_call(ctx, result, callee.fx, callparms, callnamedparms, loc);

    auto dst = ctx.add_temporary();
    auto res = ctx.add_temporary();

    realise_as_value(ctx, dst, address);

    commit_type(ctx, dst, address.type.type, address.type.flags);

    realise_as_value(ctx, Place(Place::Fer, res), result);

    commit_type(ctx, res, result.type.type, result.type.flags);

    result.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(type), MIR::Local::LValue);
    result.value = MIR::RValue::local(MIR::RValue::Val, res, loc);

    return true;
  }

  //|///////////////////// lower_const //////////////////////////////////////
  bool lower_const(LowerContext &ctx, UnaryOpExpr *unaryop, MIR::Fragment &var)
  {
    vector<MIR::Fragment> parms(1);

    parms[0].type = var.type.type;
    parms[0].value = std::move(var.value);

    auto callee = find_callee(ctx, ctx.stack, unaryop->op(), parms);

    if (!callee)
    {
      ctx.diag.error("cannot resolve operator reference", ctx.stack.back(), unaryop->loc());
      return false;
    }

    callee.fx.returntype = find_returntype(ctx, callee.fx).type;

    MIR mir = {};
    mir.add_local(MIR::Local(parms[0].type.type));
    mir.add_local(MIR::Local(parms[0].type.type, MIR::Local::Reference));
    mir.add_local(MIR::Local(parms[0].type.type, MIR::Local::Reference));
    mir.args_beg = mir.args_end = 1;

    mir.add_block(MIR::Block());
    mir.add_statement(MIR::Statement::assign(0, std::move(parms[0].value)));
    mir.add_statement(MIR::Statement::assign(1, MIR::RValue::local(MIR::RValue::Ref, 0, unaryop->loc())));
    mir.add_statement(MIR::Statement::assign(2, MIR::RValue::call(callee.fx, { 1 }, unaryop->loc())));

    if (auto expr = evaluate(ctx.stack.back(), mir, ctx.typetable, ctx.diag, unaryop->loc()))
    {
      var.value = MIR::RValue::literal(expr.value);

      return true;
    }

    return false;
  }

  //|///////////////////// lower_const //////////////////////////////////////
  bool lower_const(LowerContext &ctx, BinaryOpExpr *binaryop, MIR::Fragment &var)
  {
    vector<MIR::Fragment> parms(2);

    parms[0].type = var.type.type;
    parms[0].value = std::move(var.value);

    if (!lower_expr(ctx, parms[1], binaryop->rhs))
      return false;

    auto callee = find_callee(ctx, ctx.stack, binaryop->op(), parms);

    if (!callee || !(parms[1].type.flags & MIR::Local::Literal))
    {
      ctx.diag.error("cannot resolve operator reference", ctx.stack.back(), binaryop->loc());
      return false;
    }

    callee.fx.returntype = find_returntype(ctx, callee.fx).type;

    MIR mir = {};
    mir.add_local(MIR::Local(parms[0].type.type));
    mir.add_local(MIR::Local(parms[0].type.type, MIR::Local::Reference));
    mir.add_local(MIR::Local(parms[1].type.type));
    mir.add_local(MIR::Local(parms[0].type.type, MIR::Local::Reference));
    mir.args_beg = mir.args_end = 1;

    mir.add_block(MIR::Block());
    mir.add_statement(MIR::Statement::assign(0, std::move(parms[0].value)));
    mir.add_statement(MIR::Statement::assign(1, MIR::RValue::local(MIR::RValue::Ref, 0, binaryop->loc())));
    mir.add_statement(MIR::Statement::assign(2, std::move(parms[1].value)));
    mir.add_statement(MIR::Statement::assign(3, MIR::RValue::call(callee.fx, { 1, 2 }, binaryop->loc())));

    if (auto expr = evaluate(ctx.stack.back(), mir, ctx.typetable, ctx.diag, binaryop->loc()))
    {
      var.value = MIR::RValue::literal(expr.value);

      return true;
    }

    return false;
  }

  //|///////////////////// lower_void ///////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, VoidLiteralExpr *voidliteral)
  {
    result.type = MIR::Local(ctx.voidtype, MIR::Local::Const | MIR::Local::Literal);
    result.value = voidliteral;
  }

  //|///////////////////// lower_bool ///////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, BoolLiteralExpr *boolliteral)
  {
    result.type = MIR::Local(ctx.booltype, MIR::Local::Const | MIR::Local::Literal);
    result.value = boolliteral;
  }

  //|///////////////////// lower_char ///////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, CharLiteralExpr *charliteral)
  {
    result.type = MIR::Local(ctx.chartype, MIR::Local::Const | MIR::Local::Literal);
    result.value = charliteral;
  }

  //|///////////////////// lower_int ////////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, IntLiteralExpr *intliteral)
  {
    result.type = MIR::Local(ctx.intliteraltype, MIR::Local::Const | MIR::Local::Literal);
    result.value = intliteral;
  }

  //|///////////////////// lower_float //////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, FloatLiteralExpr *floatliteral)
  {
    result.type = MIR::Local(ctx.floatliteraltype, MIR::Local::Const | MIR::Local::Literal);
    result.value = floatliteral;
  }

  //|///////////////////// lower_null ///////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, PointerLiteralExpr *ptrliteral)
  {
    result.type = MIR::Local(ctx.ptrliteraltype, MIR::Local::Const | MIR::Local::Literal);
    result.value = ptrliteral;
  }

  //|///////////////////// lower_string /////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, StringLiteralExpr *stringliteral)
  {
    result.type = MIR::Local(ctx.stringliteraltype, MIR::Local::Const | MIR::Local::Literal);
    result.value = stringliteral;
  }

  //|///////////////////// lower_array //////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, ArrayLiteralExpr *arrayliteral)
  {
    auto type = ctx.typetable.var_defn;

    if (arrayliteral->elements.size() != 0)
    {
      type = find_type(ctx, ctx.stack, arrayliteral->elements.front()).type;

      if (!type)
        return;
    }

    auto size = resolve_type(ctx, arrayliteral->size);

    result.type = MIR::Local(ctx.typetable.find_or_create<ArrayType>(type, size), MIR::Local::Const | MIR::Local::Literal);

    if (all_of(arrayliteral->elements.begin(), arrayliteral->elements.end(), [](auto &k) { return is_literal_expr(k); }))
    {
      result.value = arrayliteral;
      return;
    }

    vector<MIR::Fragment> values(arrayliteral->elements.size());

    for(size_t i = 0; i < values.size(); ++i)
    {
      if (!lower_expr(ctx, values[i], arrayliteral->elements[i]))
        return;
    }

    if (all_of(values.begin(), values.end(), [](auto &k) { return k.type.flags & MIR::Local::Literal; }))
    {
      vector<Expr*> elements;

      for(auto &value : values)
      {
        elements.push_back(std::visit([&](auto &v) { return static_cast<Expr*>(v); }, value.value.get<MIR::RValue::Constant>()));
      }

      result.value = ctx.mir.make_expr<ArrayLiteralExpr>(elements, size, arrayliteral->loc());
      return;
    }

    auto arg = ctx.add_temporary();

    auto typeref = ctx.typetable.find_or_create<ReferenceType>(type);

    for(auto &value : values)
    {
      auto index = size_t(&value - &values.front());

      auto dst = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto res = ctx.add_temporary();

      ctx.add_statement(MIR::Statement::assign(dst, MIR::RValue::field(MIR::RValue::Ref, arg, MIR::RValue::Field{ MIR::RValue::Ref, index }, value.value.loc())));

      MIR::Fragment result;

      vector<MIR::Fragment> parms = { value };
      map<string_view, MIR::Fragment> namedparms;

      auto callee = find_callee(ctx, type, parms, namedparms);

      if (!callee)
      {
        ctx.diag.error("cannot resolve array element constructor", ctx.stack.back(), value.value.loc());
        diag_callee(ctx, callee, parms, namedparms);
        return;
      }

      lower_call(ctx, result, callee.fx, parms, namedparms, value.value.loc());

      realise_as_value(ctx, Place(Place::Fer, res), result);

      commit_type(ctx, res, result.type.type, result.type.flags);
    }

    commit_type(ctx, arg, result.type.type, MIR::Local::RValue);

    if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
      realise_destructor(ctx, arg, arrayliteral->loc());

    result.type.flags &= ~MIR::Local::Const;
    result.type.flags &= ~MIR::Local::Literal;
    result.type.flags |= MIR::Local::RValue;
    result.type.flags |= MIR::Local::Reference;
    result.value = MIR::RValue::local(MIR::RValue::Ref, arg, arrayliteral->loc());
  }

  //|///////////////////// lower_compound ///////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, CompoundLiteralExpr *compoundliteral)
  {
    vector<Type*> fields;

    for(auto &field : compoundliteral->fields)
    {
      fields.push_back(find_type(ctx, ctx.stack, field).type);
    }

    if (any_of(fields.begin(), fields.end(), [](auto &k) { return !k; }))
      return;

    result.type = MIR::Local(ctx.typetable.find_or_create<TupleType>(vector(fields.size(), ctx.typetable.var_defn), fields), MIR::Local::Const | MIR::Local::Literal);
    result.value = compoundliteral;
  }

  //|///////////////////// lower_paren //////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, ParenExpr *paren)
  {
    assert(paren->subexpr);

    lower_expr(ctx, result, paren->subexpr);
  }

  //|///////////////////// lower_vardecl  ///////////////////////////////////
  bool lower_expr(LowerContext &ctx, MIR::Fragment &result, VarDecl *vardecl, SourceLocation loc)
  {
    if (vardecl->flags & VarDecl::Literal)
    {
      if (vardecl->kind() == Decl::ParmVar)
      {
        if (auto j = ctx.stack.back().find_type(vardecl); j != ctx.stack.back().typeargs.end())
        {
          result.type = resolve_type_as_reference(ctx, ctx.stack.back(), decl_cast<ParmVarDecl>(vardecl));
          result.type.flags = MIR::Local::Const | MIR::Local::Literal;
          result.value = MIR::RValue::literal(type_cast<TypeLitType>(j->second)->value);
          return true;
        }
      }

      if (auto j = ctx.symbols.find(vardecl); j != ctx.symbols.end())
      {
        result = j->second;
        return true;
      }
    }

    if (vardecl->kind() == Decl::FieldVar)
    {
      MIR::Fragment base;

      if (ctx.mir.fx.fn->flags & FunctionDecl::Constructor)
      {
        base.type = ctx.mir.locals[0];
        base.value = MIR::RValue::local(MIR::RValue::Ref, 0, loc);
      }
      else
      {
        base.type = resolve_as_reference(ctx, ctx.mir.locals[1]);
        base.value = MIR::RValue::local(MIR::RValue::Val, 1, loc);
      }

      auto field = find_field(ctx, type_cast<TagType>(base.type.type), decl_cast<FieldVarDecl>(vardecl)->name);

      lower_field(ctx, result, base, field, loc);

      return true;
    }

    auto j = ctx.locals.find(vardecl);

    if (j == ctx.locals.end())
    {
      ctx.diag.error("variable not defined in this context", ctx.stack.back(), loc);
      return false;
    }

    auto arg = j->second;

    result.type = MIR::Local(ctx.mir.locals[arg].type, vardecl->type, ctx.mir.locals[arg].flags);
    result.type.flags |= MIR::Local::Reference;
    result.value = MIR::RValue::local(MIR::RValue::Ref, arg, loc);

    if (is_pack_type(vardecl->type))
    {
      lower_fer(ctx, result, result);

      result.type = resolve_as_reference(ctx, result.type);
    }

    if (!lower_expr_deref(ctx, result))
      return false;

    return true;
  }

  //|///////////////////// lower_declref /////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &base, DeclRefExpr *declref)
  {
    Scope basescope;
    vector<MIR::Fragment> parms;
    map<string_view, MIR::Fragment> namedparms;

    auto &name = decl_cast<DeclRefDecl>(declref->decl)->name;

    if (is_tag_type(base.type.type))
      basescope = type_scope(ctx, base.type.type);

    if (is_array_type(base.type.type) || is_tuple_type(base.type.type))
      basescope = ctx.translationunit->builtins;

    parms.push_back(base);

    if (is_tuple_type(base.type.type))
    {
      auto tupletype = type_cast<TupleType>(base.type.type);

      if (auto index = find_index(ctx, ctx.stack, name); index != size_t(-1))
      {
        if (tupletype->fields.size() <= index)
        {
          ctx.diag.error("tuple field out of range", ctx.stack.back(), declref->loc());
          return;
        }

        if (auto field = find_field(ctx, tupletype, index))
        {
          lower_field(ctx, result, base, field, declref->loc());

          return;
        }
      }
    }

    while (is_struct_type(base.type.type))
    {
      auto tagtype = type_cast<TagType>(base.type.type);

      if (auto field = find_field(ctx, tagtype, name))
      {
        if ((field.flags & Decl::Public) || get_module(tagtype->decl) == ctx.module)
        {
          lower_field(ctx, result, base, field, declref->loc());

          return;
        }
      }

      if (auto field = find_field(ctx, tagtype, "super"))
      {
        lower_field(ctx, base, base, field, declref->base->loc());

        continue;
      }

      break;
    }

    auto callee = find_callee(ctx, ctx.stack, basescope, declref->decl, parms, namedparms);

    if (!callee)
    {
      ctx.diag.error("cannot resolve function reference", ctx.stack.back(), declref->loc());
      diag_callee(ctx, callee, parms, namedparms);
      return;
    }

    lower_call(ctx, result, callee.fx, parms, namedparms, declref->loc());
  }

  //|///////////////////// lower_declref /////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, DeclRefExpr *declref)
  {
    Scope basescope;
    MIR::Fragment base;
    vector<MIR::Fragment> parms;
    map<string_view, MIR::Fragment> namedparms;

    if (declref->base)
    {
      if (!lower_expr(ctx, base, declref->base))
        return;

      if (!lower_base_deref(ctx, base))
        return;

      if (is_tag_type(base.type.type))
        basescope = type_scope(ctx, base.type.type);

      parms.push_back(base);
    }

    if (declref->decl->kind() == Decl::DeclRef)
    {
      auto &name = decl_cast<DeclRefDecl>(declref->decl)->name;

      if (declref->base)
      {
        lower_expr(ctx, result, base, declref);

        return;
      }

      if (auto vardecl = find_vardecl(ctx, ctx.stack, name))
      {
        lower_expr(ctx, result, vardecl, declref->loc());

        return;
      }
    }

    auto callee = find_callee(ctx, ctx.stack, basescope, declref->decl, parms, namedparms);

    if (!callee)
    {
      ctx.diag.error("cannot resolve function reference", ctx.stack.back(), declref->loc());
      diag_callee(ctx, callee, parms, namedparms);
      return;
    }

    lower_call(ctx, result, callee.fx, parms, namedparms, declref->loc());
  }

  //|///////////////////// lower_unaryop ////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, UnaryOpExpr::OpCode unaryop, vector<MIR::Fragment> &parms, map<string_view, MIR::Fragment> &namedparms, SourceLocation loc)
  {
    if (unaryop == UnaryOpExpr::Unpack)
    {
      result = std::move(parms[0]);

      if (!is_tuple_type(result.type.type))
      {
        ctx.diag.error("tuple type required", ctx.stack.back(), loc);
        return;
      }

      return;
    }

    if (unaryop == UnaryOpExpr::Ref && (parms[0].type.flags & MIR::Local::Reference))
    {
      result = std::move(parms[0]);

      result.type = resolve_as_value(ctx, result.type);
      result.type.defn = ctx.typetable.find_or_create<ReferenceType>(result.type.defn);

      return;
    }

    if (unaryop == UnaryOpExpr::Fer && is_reference_type(parms[0].type.type))
    {
      result = std::move(parms[0]);

      if (result.type.flags & MIR::Local::Reference)
        lower_fer(ctx, result, result);

      result.type = resolve_as_reference(ctx, result.type);
      result.type.defn = remove_const_type(remove_reference_type(result.type.defn));

      return;
    }

    if (unaryop == UnaryOpExpr::Fwd && (parms[0].type.flags & MIR::Local::Reference))
    {
      result = std::move(parms[0]);

      if (result.type.flags & MIR::Local::XValue)
        result.type.flags = (result.type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;

      return;
    }

    if (unaryop == UnaryOpExpr::PostInc || unaryop == UnaryOpExpr::PostDec)
    {
      MIR::Fragment dummy;
      dummy.type = ctx.voidtype;

      parms.push_back(std::move(dummy));
    }

    auto callee = find_callee(ctx, ctx.stack, unaryop, parms, namedparms);

    if (!callee && (unaryop == UnaryOpExpr::PostInc || unaryop == UnaryOpExpr::PostDec))
    {
      parms.resize(1);

      if (callee = find_callee(ctx, ctx.stack, unaryop, parms, namedparms); callee)
      {
        result = parms[0];

        auto arg = ctx.add_temporary();

        realise_as_value(ctx, arg, result);

        commit_type(ctx, arg, result.type.type, result.type.flags);

        if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
          realise_destructor(ctx, arg, loc);

        {
          lower_call(ctx, result, callee.fx, parms, namedparms, loc);

          auto arg = ctx.add_temporary();

          realise(ctx, arg, result);

          commit_type(ctx, arg, result.type.type, result.type.flags);

          if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
            realise_destructor(ctx, arg, loc);
        }

        result.value = MIR::RValue::local(MIR::RValue::Ref, arg, loc);

        return;
      }
    }

    if (!callee && unaryop == UnaryOpExpr::LNot)
    {
      if (!lower_cast(ctx, parms[0], parms[0], ctx.booltype, parms[0].value.loc()))
        return;

      callee.fx = Builtin::fn(ctx.translationunit->builtins, Builtin::LNot);
    }

    if (!callee)
    {
      ctx.diag.error("cannot resolve operator reference", ctx.stack.back(), loc);
      diag_callee(ctx, callee, parms, namedparms);
      return;
    }

    lower_call(ctx, result, callee.fx, parms, namedparms, loc);
  }

  //|///////////////////// lower_unaryop ////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, UnaryOpExpr *unaryop)
  {
    vector<MIR::Fragment> parms(1);
    map<string_view, MIR::Fragment> namedparms;

    if (unaryop->op() == UnaryOpExpr::Literal)
    {
      if (auto expr = evaluate(ctx.stack.back(), unaryop->subexpr, ctx.symbols, ctx.typetable, ctx.diag, unaryop->loc()))
      {
        lower_expr(ctx, result, expr.value);

        result.type.type = expr.type;
      }

      return;
    }

    if (!lower_expr(ctx, parms[0], unaryop->subexpr))
      return;

    lower_expr(ctx, result, unaryop->op(), parms, namedparms, unaryop->loc());
  }

  //|///////////////////// lower_binaryop ///////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, BinaryOpExpr::OpCode binaryop, vector<MIR::Fragment> &parms, map<string_view, MIR::Fragment> &namedparms, SourceLocation loc)
  {
    if (binaryop == BinaryOpExpr::Assign)
    {
      if (parms[0].type.flags & MIR::Local::RValue)
      {
        ctx.diag.error("invalid assignment epression", ctx.stack.back(), loc);
        return;
      }
    }

    auto callee = find_callee(ctx, ctx.stack, binaryop, parms, namedparms);

    if (!callee && binaryop == BinaryOpExpr::Assign)
    {
      if (!(parms[0].type.flags & MIR::Local::Const) && is_pointference_type(parms[0].type.type) && is_pointference_type(parms[1].type.type))
      {
        auto lhs = remove_pointference_type(parms[0].type.type);
        auto rhs = remove_pointference_type(parms[1].type.type);

        if (is_const_type(lhs))
        {
          lhs = remove_const_type(lhs);
          rhs = remove_const_type(rhs);
        }

        while (lhs != rhs && is_struct_type(rhs) && decl_cast<StructDecl>(type_cast<TagType>(rhs)->decl)->basetype)
          rhs = type_cast<TagType>(rhs)->fields[0];

        if (lhs == rhs)
          callee.fx = Builtin::fn(ctx.translationunit->builtins, Builtin::Assign, parms[0].type.type);
      }
    }

    if (!callee && (binaryop == BinaryOpExpr::LT || binaryop == BinaryOpExpr::GT || binaryop == BinaryOpExpr::LE || binaryop == BinaryOpExpr::GE || binaryop == BinaryOpExpr::EQ || binaryop == BinaryOpExpr::NE || binaryop == BinaryOpExpr::Cmp))
    {
      if (is_pointference_type(parms[0].type.type) && is_pointference_type(parms[1].type.type))
      {
        auto lhs = remove_const_type(remove_pointference_type(parms[0].type.type));
        auto rhs = remove_const_type(remove_pointference_type(parms[1].type.type));

        if (lhs == rhs)
          callee.fx = map_builtin(ctx, binaryop, parms[0].type.type);

        if (lhs != rhs)
        {
          while (lhs != rhs && is_struct_type(lhs) && decl_cast<StructDecl>(type_cast<TagType>(lhs)->decl)->basetype)
            lhs = type_cast<TagType>(lhs)->fields[0];

          if (lhs == rhs)
            callee.fx = map_builtin(ctx, binaryop, parms[0].type.type);
        }

        if (lhs != rhs)
        {
          lhs = remove_const_type(remove_pointference_type(parms[0].type.type));

          while (rhs != lhs && is_struct_type(rhs) && decl_cast<StructDecl>(type_cast<TagType>(rhs)->decl)->basetype)
            rhs = type_cast<TagType>(rhs)->fields[0];

          if (rhs == lhs)
            callee.fx = map_builtin(ctx, binaryop, parms[1].type.type);
        }
      }
    }

    if (!callee && binaryop == BinaryOpExpr::EQ)
    {
      swap(parms[0], parms[1]);

      callee = find_callee(ctx, ctx.stack, BinaryOpExpr::EQ, parms, namedparms);

      if (!callee)
        swap(parms[1], parms[0]);
    }

    if (!callee && binaryop == BinaryOpExpr::Cmp)
    {
      swap(parms[0], parms[1]);

      callee = find_callee(ctx, ctx.stack, BinaryOpExpr::Cmp, parms, namedparms);

      if (!callee)
        swap(parms[1], parms[0]);

      if (callee)
      {
        lower_call(ctx, result, callee.fx, parms, namedparms, loc);

        parms[0].type = MIR::Local(ctx.intliteraltype, MIR::Local::Const | MIR::Local::Literal);
        parms[0].value = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, 0), loc);
        parms[1] = std::move(result);

        callee.fx = Builtin::fn(ctx.translationunit->builtins, Builtin::Cmp, type(Builtin::Type_I32));
      }
    }

    if (!callee && binaryop == BinaryOpExpr::NE)
    {
      callee = find_callee(ctx, ctx.stack, BinaryOpExpr::EQ, parms, namedparms);

      if (!callee)
      {
        swap(parms[0], parms[1]);

        callee = find_callee(ctx, ctx.stack, BinaryOpExpr::EQ, parms, namedparms);

        if (!callee)
          swap(parms[1], parms[0]);
      }

      if (callee)
      {
        lower_call(ctx, result, callee.fx, parms, namedparms, loc);

        parms.resize(1);
        parms[0] = std::move(result);

        callee.fx = Builtin::fn(ctx.translationunit->builtins, Builtin::LNot);
      }
    }

    if (!callee && (binaryop == BinaryOpExpr::LT || binaryop == BinaryOpExpr::LE || binaryop == BinaryOpExpr::GT || binaryop == BinaryOpExpr::GE))
    {
      bool swapped = false;

      callee = find_callee(ctx, ctx.stack, BinaryOpExpr::Cmp, parms, namedparms);

      if (!callee)
      {
        swap(parms[0], parms[1]);

        callee = find_callee(ctx, ctx.stack, BinaryOpExpr::Cmp, parms, namedparms);

        if (!callee)
          swap(parms[1], parms[0]);

        swapped = true;
      }

      if (callee)
      {
        lower_call(ctx, result, callee.fx, parms, namedparms, loc);

        parms[0] = std::move(result);
        parms[1].type = MIR::Local(ctx.intliteraltype, MIR::Local::Const | MIR::Local::Literal);
        parms[1].value = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, 0), loc);

        if (swapped)
          swap(parms[0], parms[1]);

        callee.fx = map_builtin(ctx, binaryop, type(Builtin::Type_I32));
      }
    }

    if (!callee)
    {
      ctx.diag.error("cannot resolve operator reference", ctx.stack.back(), loc);
      diag_callee(ctx, callee, parms, namedparms);
      return;
    }

    lower_call(ctx, result, callee.fx, parms, namedparms, loc);
  }

  //|///////////////////// lower_binaryop ///////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, BinaryOpExpr *binaryop)
  {
    vector<MIR::Fragment> parms(2);
    map<string_view, MIR::Fragment> namedparms;

    if (binaryop->op() == BinaryOpExpr::Assign)
    {
      if (binaryop->lhs->kind() == Expr::DeclRef && expr_cast<DeclRefExpr>(binaryop->lhs)->base)
      {
        if (!lower_expr(ctx, parms[0], expr_cast<DeclRefExpr>(binaryop->lhs)->base))
          return;

        if (!lower_base_deref(ctx, parms[0]))
          return;

        if (!lower_expr(ctx, parms[1], binaryop->rhs))
          return;

        if (is_tag_type(parms[0].type.type) && expr_cast<DeclRefExpr>(binaryop->lhs)->decl->kind() == Decl::DeclRef)
        {
          string name = decl_cast<DeclRefDecl>(expr_cast<DeclRefExpr>(binaryop->lhs)->decl)->name + '=';

          if (auto callee = find_callee(ctx, parms[0].type.type, name, parms, namedparms); callee)
          {
            lower_call(ctx, result, callee.fx, parms, namedparms, binaryop->loc());

            return;
          }
        }

        lower_expr(ctx, parms[0], parms[0], expr_cast<DeclRefExpr>(binaryop->lhs));

        lower_expr(ctx, result, binaryop->op(), parms, namedparms, binaryop->loc());

        return;
      }
    }

    if (!lower_expr(ctx, parms[0], binaryop->lhs))
      return;

    if (binaryop->op() == BinaryOpExpr::LAnd || binaryop->op() == BinaryOpExpr::LOr)
    {
      auto rm = ctx.push_barrier();

      MIR::Fragment lhs = parms[0];

      if (!is_bool_type(lhs.type.type))
      {
        lower_cast(ctx, lhs, lhs, ctx.booltype, binaryop->lhs->loc());
      }

      if (ctx.flags & LowerFlags::Clause)
      {
        if (binaryop->op() == BinaryOpExpr::LAnd && is_false_constant(ctx, lhs))
        {
          ctx.rollback_barrier(rm);
          result.type = MIR::Local(ctx.booltype, MIR::Local::Const | MIR::Local::Literal);
          result.value = std::move(lhs.value);
          return;
        }

        if (binaryop->op() == BinaryOpExpr::LOr && is_true_constant(ctx, lhs))
        {
          ctx.rollback_barrier(rm);
          result.type = MIR::Local(ctx.booltype, MIR::Local::Const | MIR::Local::Literal);
          result.value = std::move(lhs.value);
          return;
        }
      }

      auto dst = ctx.add_temporary();

      realise_as_value(ctx, dst, lhs);

      auto block_lhs = ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

      if (!lower_expr(ctx, parms[1], binaryop->rhs))
        return;

      MIR::Fragment rhs = parms[1];

      if (!is_bool_type(rhs.type.type))
      {
        lower_cast(ctx, rhs, rhs, ctx.booltype, binaryop->rhs->loc());
      }

      realise_as_value(ctx, dst, rhs);

      auto callee = find_callee(ctx, ctx.stack, binaryop->op(), parms, namedparms);

      if (!callee || (callee.fx.fn->flags & FunctionDecl::Builtin))
      {
        ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

        if (binaryop->op() == BinaryOpExpr::LAnd)
        {
          if (is_false_constant(ctx, lhs))
          {
            ctx.rollback_barrier(rm);
            result.type = MIR::Local(ctx.booltype, MIR::Local::Const | MIR::Local::Literal);
            result.value = std::move(lhs.value);
            return;
          }

          if (is_constant(ctx, lhs) && is_constant(ctx, rhs))
          {
            ctx.rollback_barrier(rm);
            result.type = MIR::Local(ctx.booltype, MIR::Local::Const | MIR::Local::Literal);
            result.value = ctx.mir.make_expr<BoolLiteralExpr>(is_true_constant(ctx, lhs) && is_true_constant(ctx, rhs), binaryop->loc());
            return;
          }

          callee.fx = Builtin::fn(ctx.translationunit->builtins, Builtin::LAnd);

          ctx.mir.blocks[block_lhs].terminator = MIR::Terminator::switcher(dst, ctx.currentblockid, block_lhs + 1);
        }

        if (binaryop->op() == BinaryOpExpr::LOr)
        {
          if (is_true_constant(ctx, lhs))
          {
            ctx.rollback_barrier(rm);
            result.type = MIR::Local(ctx.booltype, MIR::Local::Const | MIR::Local::Literal);
            result.value = std::move(lhs.value);
            return;
          }

          if (is_constant(ctx, lhs) && is_constant(ctx, rhs))
          {
            ctx.rollback_barrier(rm);
            result.type = MIR::Local(ctx.booltype, MIR::Local::Const | MIR::Local::Literal);
            result.value = ctx.mir.make_expr<BoolLiteralExpr>(is_true_constant(ctx, lhs) || is_true_constant(ctx, rhs), binaryop->loc());
            return;
          }

          callee.fx = Builtin::fn(ctx.translationunit->builtins, Builtin::LOr);

          ctx.mir.blocks[block_lhs].terminator = MIR::Terminator::switcher(dst, block_lhs + 1, ctx.currentblockid);
        }

        commit_type(ctx, dst, ctx.booltype, MIR::Local::RValue);

        result.type = MIR::Local(ctx.booltype, MIR::Local::RValue);
        result.value = MIR::RValue::local(MIR::RValue::Val, dst, binaryop->loc());

        ctx.retire_barrier(rm);

        return;
      }

      ctx.rollback_barrier(rm);
    }

    if (!lower_expr(ctx, parms[1], binaryop->rhs))
      return;

    lower_expr(ctx, result, binaryop->op(), parms, namedparms, binaryop->loc());
  }

  //|///////////////////// lower_ternaryop ///////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, TernaryOpExpr *ternaryop)
  {
    MIR::Fragment condition;

    if (!lower_expr(ctx, condition, ternaryop->cond))
      return;

    if (!is_bool_type(condition.type.type))
    {
      if (!lower_cast(ctx, condition, condition, ctx.booltype, ternaryop->cond->loc()))
        return;
    }

    if (condition.type.flags & MIR::Local::Literal)
    {
      bool cond = is_true_constant(ctx, condition);

      lower_expr(ctx, result, cond ? ternaryop->lhs : ternaryop->rhs);

      return;
    }

    auto dst = ctx.add_temporary();

    auto cond = ctx.add_temporary();

    realise_as_value(ctx, cond, condition);

    commit_type(ctx, cond, condition.type.type, condition.type.flags);

    auto block_switch = ctx.add_block(MIR::Terminator::switcher(cond, ctx.currentblockid + 1));

    bool by_value = false;

    MIR::Fragment lhs;

    if (!lower_expr(ctx, lhs, ternaryop->lhs))
      return;

    if (!(lhs.type.flags & MIR::Local::Reference) || !(find_type(ctx, ctx.stack, ternaryop->rhs).flags & MIR::Local::Reference))
      by_value = true;

    if (by_value)
      realise_as_value(ctx, dst, lhs);
    else
      realise(ctx, dst, lhs);

    auto block_true = ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    ctx.mir.blocks[block_switch].terminator.targets.emplace_back(0, ctx.currentblockid);

    MIR::Fragment rhs;

    if (!lower_expr(ctx, rhs, ternaryop->rhs))
      return;

    if (by_value)
      realise_as_value(ctx, dst, rhs);
    else
      realise(ctx, dst, rhs);

    ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    ctx.mir.blocks[block_true].terminator.blockid = ctx.currentblockid;

    if (lhs.type.type != rhs.type.type)
    {
      promote_type(ctx, lhs.type.type, rhs.type.type);

      if (lhs.type.type != rhs.type.type)
      {
        promote_type(ctx, rhs.type.type, lhs.type.type);

        if (lhs.type.type != rhs.type.type)
        {
          FnSig fx;
          DeduceContext tx;

          if (deduce_type(ctx, tx, ctx.stack.back(), fx, lhs.type.type, rhs.type.type))
            rhs.type.type = lhs.type.type;

          if (lhs.type.type != rhs.type.type)
          {
            FnSig fx;
            DeduceContext tx;

            if (deduce_type(ctx, tx, ctx.stack.back(), fx, rhs.type.type, lhs.type.type))
              lhs.type.type = rhs.type.type;
          }
        }
      }
    }

    if (lhs.type.type != rhs.type.type || (lhs.type.flags & MIR::Local::Reference) != (rhs.type.flags & MIR::Local::Reference)|| (lhs.type.flags & MIR::Local::XValue) != (rhs.type.flags & MIR::Local::XValue))
    {
      ctx.diag.error("ternary operands differing types", ctx.stack.back(), ternaryop->loc());
      ctx.diag << "  lhs type: '" << *lhs.type.type << "' rhs type: '" << *rhs.type.type << "'\n";
      return;
    }

    commit_type(ctx, dst, lhs.type.type, lhs.type.flags & ~MIR::Local::Const);

    if (!(ctx.mir.locals[dst].flags & MIR::Local::Reference))
      realise_destructor(ctx, dst, ternaryop->loc());

    result.type = ctx.mir.locals[dst];
    result.type.flags |= MIR::Local::Reference;
    result.value = MIR::RValue::local((ctx.mir.locals[dst].flags & MIR::Local::Reference) ? MIR::RValue::Val : MIR::RValue::Ref, dst, ternaryop->loc());
  }

  //|///////////////////// lower_sizeof /////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, SizeofExpr *call)
  {
    Type *type = nullptr;

    if (call->type)
    {
      type = resolve_type(ctx, call->type);
    }

    if (call->expr)
    {
      type = find_type(ctx, ctx.stack, call->expr).type;

      if (!type)
        return;
    }

    result.type = MIR::Local(ctx.intliteraltype, MIR::Local::RValue);
    result.value = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, sizeof_type(type)), call->loc());
  }

  //|///////////////////// lower_alignof ///////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, AlignofExpr *call)
  {
    Type *type = nullptr;

    if (call->type)
    {
      type = resolve_type(ctx, call->type);
    }

    if (call->expr)
    {
      type = find_type(ctx, ctx.stack, call->expr).type;

      if (!type)
        return;
    }

    result.type = MIR::Local(ctx.intliteraltype, MIR::Local::RValue);
    result.value = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, alignof_type(type)), call->loc());
  }

  //|///////////////////// lower_cast ///////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, CastExpr *cast)
  {
    MIR::Fragment source;

    if (!lower_expr(ctx, source, cast->expr))
      return;

    result.type = MIR::Local(resolve_type(ctx, remove_const_type(cast->type)), remove_const_type(cast->type), MIR::Local::LValue);

    if (is_concrete_type(result.type.type) && (source.type.flags & MIR::Local::Literal))
    {
      if (literal_cast(ctx, result.value, source.value, result.type.type))
      {
        result.type.flags = MIR::Local::Const | MIR::Local::Literal;
        return;
      }
    }

    if (is_function_type(remove_const_type(remove_pointference_type(result.type.type))) && is_lambda_type(source.type.type))
    {
      lower_lambda_decay(ctx, result, ctx.stack.back(), result.type.type, source);
      return;
    }

    auto arg = ctx.add_temporary();

    if (is_reference_type(result.type.type) && (source.type.flags & MIR::Local::Reference))
    {
      result.type = resolve_as_reference(ctx, result.type);
      result.type.defn = remove_const_type(remove_reference_type(result.type.defn));

      // use &&cast<T mut &>(value) to cast away const, retain rvalue
      // use &&cast<T &&>(value) to cast, retain rvalue and const

      result.type.flags |= source.type.flags & MIR::Local::XValue;

      if (is_qualarg_type(remove_reference_type(cast->type)))
        result.type.flags |= source.type.flags & MIR::Local::Const;

      realise_as_reference(ctx, arg, source);
    }
    else
    {
      if (!is_builtin_type(source.type.type) && !is_enum_type(source.type.type) && !is_pointer_type(source.type.type) && !is_reference_type(source.type.type))
      {
        ctx.diag.error("invalid cast", ctx.stack.back(), cast->loc());
        return;
      }

      realise_as_value(ctx, arg, source);
    }

    commit_type(ctx, arg, source.type.type, source.type.flags);

    result.value = MIR::RValue::cast(arg, cast->loc());
  }

  //|///////////////////// lower_newexpr ////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, NewExpr *call)
  {
    MIR::Fragment address;

    if (!lower_expr(ctx, address, call->address))
      return;

    auto type = resolve_type(ctx, call->type);

    if (!((is_pointer_type(address.type.type) && (type_cast<PointerType>(address.type.type)->type == type || is_void_type(type_cast<PointerType>(address.type.type)->type))) ||
          (is_reference_type(address.type.type) && (type_cast<ReferenceType>(address.type.type)->type == type || is_void_type(type_cast<ReferenceType>(address.type.type)->type)))))
    {
      ctx.diag.error("address type mismatch", ctx.stack.back(), call->loc());
      ctx.diag << "  variable type: '" << *address.type.type << "' required type: 'void*'\n";
      return;
    }

    lower_new(ctx, result, address, type, call->parms, call->namedparms, call->loc());
  }

  //|///////////////////// lower_call ///////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, CallExpr *call)
  {
    Scope basescope;
    MIR::Fragment base;
    vector<MIR::Fragment> parms;
    map<string_view, MIR::Fragment> namedparms;

    if (call->base)
    {
      if (!lower_expr(ctx, base, call->base))
        return;

      if (!lower_base_deref(ctx, base))
        return;

      if (is_tag_type(base.type.type))
        basescope = type_scope(ctx, base.type.type);

      if (is_array_type(base.type.type) || is_tuple_type(base.type.type))
        basescope = ctx.translationunit->builtins;

      parms.push_back(base);
    }

    bool is_callop = false;

    if (call->callee->kind() == Decl::DeclRef)
    {
      auto &name = decl_cast<DeclRefDecl>(call->callee)->name;

      if (call->base)
      {
        while (is_struct_type(base.type.type))
        {
          auto tagtype = type_cast<TagType>(base.type.type);

          if (auto field = find_field(ctx, tagtype, name))
          {
            if ((field.flags & Decl::Public) || get_module(tagtype->decl) == ctx.module)
            {
              if (!lower_field(ctx, parms[0], base, field, call->loc()))
                return;

              is_callop = true;

              break;
            }
          }

          if (auto field = find_field(ctx, tagtype, "super"))
          {
            lower_field(ctx, base, base, field, call->base->loc());

            continue;
          }

          break;
        }

        if (is_lambda_type(base.type.type))
          is_callop = true;
      }
      else
      {
        if (auto vardecl = find_vardecl(ctx, ctx.stack, name))
        {
          parms.resize(1);

          if (!lower_expr(ctx, parms[0], vardecl, call->loc()))
            return;

          is_callop = true;
        }
      }
    }

    for(auto &parm : call->parms)
    {
      MIR::Fragment expr;

      if (!lower_expr(ctx, expr, parm))
        return;

      if (parm->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(parm)->op() == UnaryOpExpr::Unpack)
      {
        if (!lower_unpack(ctx, parms, parm, expr))
          return;

        continue;
      }

      parms.push_back(std::move(expr));
    }

    for(auto &[name, parm] : call->namedparms)
    {
      MIR::Fragment expr;

      if (!lower_expr(ctx, expr, parm))
        return;

      namedparms.emplace(name, std::move(expr));
    }

    if (is_callop)
    {
      if (!lower_base_deref(ctx, parms[0]))
        return;

      if (is_tag_type(parms[0].type.type))
        basescope = type_scope(ctx, parms[0].type.type);

      if (is_lambda_type(parms[0].type.type) && !(decl_cast<LambdaDecl>(type_cast<TagType>(parms[0].type.type)->decl)->flags & LambdaDecl::Captures))
      {
        auto arg = ctx.add_variable();

        realise(ctx, arg, parms[0]);

        commit_type(ctx, arg, parms[0].type.type, parms[0].type.flags);

        if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
          realise_destructor(ctx, arg, call->loc());

        parms.erase(parms.begin());
      }
    }

    auto callee = find_callee(ctx, ctx.stack, basescope, call->callee, parms, namedparms, is_callop);

    if (!callee)
    {
      ctx.diag.error("cannot resolve function reference", ctx.stack.back(), call->loc());
      diag_callee(ctx, callee, parms, namedparms);
      return;
    }

    lower_call(ctx, result, callee.fx, parms, namedparms, call->loc());
  }

  //|///////////////////// lower_requires ///////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, RequiresExpr *reqires)
  {
    Diag diag(ctx.diag.leader());

    lower(FnSig(decl_cast<FunctionDecl>(reqires->decl), ctx.stack.back().typeargs), ctx.typetable, diag);

    result.type = MIR::Local(ctx.booltype, MIR::Local::Const | MIR::Local::Literal);
    result.value = ctx.mir.make_expr<BoolLiteralExpr>(!diag.has_errored(), reqires->loc());
  }

  //|///////////////////// lower_lambda /////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, LambdaExpr *lambda)
  {
    auto decl = decl_cast<LambdaDecl>(lambda->decl);

    vector<MIR::Fragment> parms;
    map<string_view, MIR::Fragment> namedparms;

    Callee callee;

    FindContext tx(decl->name, QueryFlags::Functions);

    find_overloads(ctx, tx, child_scope(ctx.stack.back(), decl), parms, namedparms, callee.overloads);

    resolve_overloads(ctx, callee.fx, callee.overloads, parms, namedparms);

    lower_call(ctx, result, callee.fx, parms, namedparms, lambda->loc());
  }

  //|///////////////////// lower_expr ///////////////////////////////////////
  bool lower_expr(LowerContext &ctx, MIR::Fragment &result, Expr *expr)
  {
    ctx.site = expr->loc();

    switch (expr->kind())
    {
      case Expr::VoidLiteral:
        lower_expr(ctx, result, expr_cast<VoidLiteralExpr>(expr));
        break;

      case Expr::BoolLiteral:
        lower_expr(ctx, result, expr_cast<BoolLiteralExpr>(expr));
        break;

      case Expr::CharLiteral:
        lower_expr(ctx, result, expr_cast<CharLiteralExpr>(expr));
        break;

      case Expr::IntLiteral:
        lower_expr(ctx, result, expr_cast<IntLiteralExpr>(expr));
        break;

      case Expr::FloatLiteral:
        lower_expr(ctx, result, expr_cast<FloatLiteralExpr>(expr));
        break;

      case Expr::PtrLiteral:
        lower_expr(ctx, result, expr_cast<PointerLiteralExpr>(expr));
        break;

      case Expr::StringLiteral:
        lower_expr(ctx, result, expr_cast<StringLiteralExpr>(expr));
        break;

      case Expr::ArrayLiteral:
        lower_expr(ctx, result, expr_cast<ArrayLiteralExpr>(expr));
        break;

      case Expr::CompoundLiteral:
        lower_expr(ctx, result, expr_cast<CompoundLiteralExpr>(expr));
        break;

      case Expr::Paren:
        lower_expr(ctx, result, expr_cast<ParenExpr>(expr));
        break;

      case Expr::DeclRef:
        lower_expr(ctx, result, expr_cast<DeclRefExpr>(expr));
        break;

      case Expr::UnaryOp:
        lower_expr(ctx, result, expr_cast<UnaryOpExpr>(expr));
        break;

      case Expr::BinaryOp:
        lower_expr(ctx, result, expr_cast<BinaryOpExpr>(expr));
        break;

      case Expr::TernaryOp:
        lower_expr(ctx, result, expr_cast<TernaryOpExpr>(expr));
        break;

      case Expr::Call:
        lower_expr(ctx, result, expr_cast<CallExpr>(expr));
        break;

      case Expr::Sizeof:
        lower_expr(ctx, result, expr_cast<SizeofExpr>(expr));
        break;

      case Expr::Alignof:
        lower_expr(ctx, result, expr_cast<AlignofExpr>(expr));
        break;

      case Expr::Cast:
        lower_expr(ctx, result, expr_cast<CastExpr>(expr));
        break;

      case Expr::New:
        lower_expr(ctx, result, expr_cast<NewExpr>(expr));
        break;

      case Expr::Requires:
        lower_expr(ctx, result, expr_cast<RequiresExpr>(expr));
        break;

      case Expr::Lambda:
        lower_expr(ctx, result, expr_cast<LambdaExpr>(expr));
        break;

      default:
        assert(false);
    }

    assert(result.value || ctx.diag.has_errored());

    return !!result.value;
  }

  //|///////////////////// lower_var ///////////////////////////////////////
  void lower_decl(LowerContext &ctx, VarDecl *vardecl, MIR::Fragment &value)
  {
    if (is_typearg_type(value.type.type) || ((ctx.flags & LowerFlags::Runtime) && is_tag_type(value.type.type) && !is_concrete_type(value.type.type)))
    {
      ctx.diag.error("unresolved type for variable", ctx.stack.back(), vardecl->loc());
      ctx.diag << "  variable type : '" << *value.type.type << "'\n";
      return;
    }

    if (vardecl->flags & VarDecl::Literal)
    {
      if (!(value.type.flags & MIR::Local::Literal))
      {
        ctx.diag.error("non literal value", ctx.stack.back(), vardecl->loc());
        return;
      }

      ctx.symbols[vardecl] = value;

      return;
    }

    auto arg = ctx.add_variable();

    if (vardecl->flags & VarDecl::Static)
    {
      if (!(value.type.flags & MIR::Local::Literal))
      {
        ctx.diag.error("non literal static value", ctx.stack.back(), vardecl->loc());
        return;
      }

      if (is_reference_type(vardecl->type))
      {
        ctx.diag.error("invalid reference type", ctx.stack.back(), vardecl->loc());
        return;
      }

      ctx.mir.statics.emplace_back(arg, std::move(value.value));

      if (!(vardecl->flags & VarDecl::Const))
        value.type.flags &= ~MIR::Local::Const;

      value.type.flags &= ~MIR::Local::Literal;
    }
    else if (is_reference_type(vardecl->type))
    {
      if (!(value.type.flags & MIR::Local::Reference))
      {
        ctx.diag.error("non reference type", ctx.stack.back(), vardecl->loc());
        return;
      }

      if (value.type.flags & MIR::Local::RValue)
      {
        ctx.diag.error("cannot bind to rvalue reference", ctx.stack.back(), vardecl->loc());
        return;
      }

      realise_as_reference(ctx, arg, value, vardecl->flags & VarDecl::Const);

      value.type = resolve_as_value(ctx, value.type);
    }
    else
    {
      realise_as_value(ctx, arg, value, vardecl->flags & VarDecl::Const);
    }

    commit_type(ctx, arg, value.type.type, value.type.flags);

    ctx.mir.locals[arg].flags |= MIR::Local::LValue;
    ctx.mir.locals[arg].flags &= ~MIR::Local::XValue;
    ctx.mir.locals[arg].flags &= ~MIR::Local::RValue;

    if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference) && !(vardecl->flags & VarDecl::Static))
      realise_destructor(ctx, arg, vardecl->loc());

    ctx.mir.add_varinfo(arg, vardecl->name, vardecl->loc());

    ctx.locals[vardecl] = arg;
    ctx.symbols[vardecl].type = ctx.mir.locals[arg];
  }

  //|///////////////////// lower_voidvar ////////////////////////////////////
  void lower_decl(LowerContext &ctx, VoidVarDecl *voidvar)
  {
    auto arg = ctx.add_variable();

    ctx.mir.locals[arg].type = resolve_type(ctx, voidvar->type);
    ctx.mir.locals[arg].flags = MIR::Local::LValue;

    if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
      realise_destructor(ctx, arg, voidvar->loc());

    ctx.mir.add_varinfo(arg, voidvar->name, voidvar->loc());

    ctx.locals[voidvar] = arg;
    ctx.symbols[voidvar].type = ctx.mir.locals[arg];
  }

  //|///////////////////// lower_stmtvar ////////////////////////////////////
  void lower_decl(LowerContext &ctx, StmtVarDecl *stmtvar)
  {
    MIR::Fragment value;

    if (!lower_expr(ctx, value, stmtvar->value))
      return;

    lower_decl(ctx, stmtvar, value);
  }

  //|///////////////////// lower_parmvar ////////////////////////////////////
  void lower_decl(LowerContext &ctx, ParmVarDecl *parmvar)
  {
    auto arg = ctx.add_local();

    ctx.mir.locals[arg].type = resolve_type_as_value(ctx, ctx.stack.back(), parmvar);
    ctx.mir.locals[arg].flags = MIR::Local::LValue;

    if (parmvar->flags & VarDecl::Const)
      ctx.mir.locals[arg].flags |= MIR::Local::Const;

    ctx.mir.add_varinfo(arg, parmvar->name, parmvar->loc());

    ctx.locals[parmvar] = arg;
    ctx.symbols[parmvar].type = ctx.mir.locals[arg];
  }

  //|///////////////////// lower_errorvar ///////////////////////////////////
  void lower_decl(LowerContext &ctx, ErrorVarDecl *errorvar)
  {
    auto arg = ctx.add_variable();

    ctx.mir.locals[arg].type = resolve_type(ctx, errorvar->type);
    ctx.mir.locals[arg].flags = MIR::Local::LValue;

    ctx.mir.add_varinfo(arg, errorvar->name, errorvar->loc());

    ctx.errorarg = arg;
    ctx.locals[errorvar] = arg;
    ctx.symbols[errorvar].type = ctx.mir.locals[arg];
  }

  //|///////////////////// lower_thisvar ////////////////////////////////////
  void lower_decl(LowerContext &ctx, ThisVarDecl *thisvar)
  {
    assert(ctx.mir.fx.fn->flags & FunctionDecl::Constructor);

    ctx.add_statement(MIR::Statement::storagelive(0));

    ctx.mir.add_varinfo(0, thisvar->name, thisvar->loc());

    ctx.locals[thisvar] = 0;
    ctx.symbols[thisvar].type = ctx.mir.locals[0];
  }

  //|///////////////////// lower_initialisers ///////////////////////////////
  void lower_initialisers(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<TagType>(ctx.mir.locals[0].type);

    auto sm = ctx.push_barrier();

    for(size_t index = 0; index < thistype->fields.size(); ++index)
    {
      auto type = thistype->fields[index];
      auto decl = decl_cast<FieldVarDecl>(thistype->fieldvars[index]);

      MIR::Fragment result;

      MIR::Fragment address;
      address.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(type), MIR::Local::LValue);
      address.value = MIR::RValue::field(MIR::RValue::Ref, 0, MIR::RValue::Field{ MIR::RValue::Ref, index }, decl->loc());

      auto j = find_if(fn->inits.begin(), fn->inits.end(), [&](auto &k) { return decl_cast<DeclRefDecl>(decl_cast<InitialiserDecl>(k)->decl)->name == decl->name; });

      if (j != fn->inits.end())
      {
        auto init = decl_cast<InitialiserDecl>(*j);

        if (init->flags & InitialiserDecl::VoidInit)
          continue;

        ctx.mir.add_lineinfo(ctx.currentblockid, ctx.currentblock.statements.size(), init->loc().lineno);

        lower_new(ctx, result, address, type, init->parms, init->namedparms, decl->loc());
      }
      else
      {
        vector<Expr*> parms;
        map<string, Expr*> namedparms;

        lower_new(ctx, result, address, type, parms, namedparms, decl->loc());
      }
    }

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_deinitialisers /////////////////////////////
  void lower_deinitialisers(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<TagType>(resolve_as_reference(ctx, ctx.mir.locals[1]).type);

    auto sm = ctx.push_barrier();

    auto res = ctx.add_temporary(ctx.voidtype, MIR::Local::LValue);

    for(size_t index = thistype->fields.size(); index-- != 0; )
    {
      auto type = thistype->fields[index];

      if (auto callee = find_destructor(ctx, type, fn->loc()))
      {
        auto src = ctx.add_temporary(type, MIR::Local::Reference);

        ctx.add_statement(MIR::Statement::assign(src, MIR::RValue::field(MIR::RValue::Ref, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc())));
        ctx.add_statement(MIR::Statement::assign(res, MIR::RValue::call(callee.fx, { src }, fn->loc())));
      }
    }

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_trivial_copytructor ////////////////////////
  void lower_trivial_copytructor(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = ctx.mir.locals[0].type;

    auto memcpy = find_builtin(ctx, Builtin::memcpy);

    auto dst = ctx.add_temporary(thistype, MIR::Local::LValue | MIR::Local::Reference);
    auto size = ctx.add_temporary(ctx.usizetype, MIR::Local::LValue | MIR::Local::Literal);
    auto res = ctx.add_temporary(thistype, MIR::Local::LValue | MIR::Local::Reference);

    ctx.add_statement(MIR::Statement::assign(dst, MIR::RValue::local(MIR::RValue::Ref, 0, fn->loc())));
    ctx.add_statement(MIR::Statement::assign(size, MIR::RValue::literal(ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, sizeof_type(thistype)), fn->loc()))));
    ctx.add_statement(MIR::Statement::assign(res, MIR::RValue::call(memcpy, { dst, 1, size }, fn->loc())));
  }

  //|///////////////////// lower_trivial_assignment /////////////////////////
  void lower_trivial_assignment(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = resolve_as_reference(ctx, ctx.mir.locals[1]).type;

    auto memcpy = find_builtin(ctx, Builtin::memcpy);

    auto size = ctx.add_temporary(ctx.usizetype, MIR::Local::LValue | MIR::Local::Literal);

    ctx.add_statement(MIR::Statement::assign(size, MIR::RValue::literal(ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, sizeof_type(thistype)), fn->loc()))));
    ctx.add_statement(MIR::Statement::assign(0, MIR::RValue::call(memcpy, { 1, 2, size }, fn->loc())));
  }

  //|///////////////////// lower_default_constructor ////////////////////////
  void lower_default_constructor(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<CompoundType>(ctx.mir.locals[0].type);

    MIR::Fragment allocator;
    if (fn->parms.size() == 1)
    {
      if (!lower_expr(ctx, allocator, decl_cast<ParmVarDecl>(fn->parms[0]), fn->loc()))
        return;
    }

    for(size_t index = 0; index < thistype->fields.size(); ++index)
    {
      auto type = thistype->fields[index];

      if (is_typearg_type(type))
      {
        ctx.diag.error("unresolved type for constructor", ctx.stack.back(), fn->loc());
        return;
      }

      MIR::Fragment result;

      vector<MIR::Fragment> parms;
      map<string_view, MIR::Fragment> namedparms;

      if (allocator)
        namedparms.emplace("allocator?", allocator);

      auto callee = find_callee(ctx, type, parms, namedparms);

      if (!callee)
      {
        ctx.diag.error("cannot resolve constructor", ctx.stack.back(), fn->loc());
        ctx.diag << "  for type: " << *type << '\n';
        diag_callee(ctx, callee, parms, namedparms);
        return;
      }

      lower_call(ctx, result, callee.fx, parms, namedparms, fn->loc());

      auto dst = ctx.add_temporary();
      auto res = ctx.add_temporary();

      MIR::Fragment address;
      address.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(type), MIR::Local::LValue);
      address.value = MIR::RValue::field(MIR::RValue::Ref, 0, MIR::RValue::Field{ MIR::RValue::Ref, index }, fn->loc());

      realise_as_value(ctx, dst, address);

      commit_type(ctx, dst, address.type.type, address.type.flags);

      realise_as_value(ctx, Place(Place::Fer, res), result);

      commit_type(ctx, res, result.type.type, result.type.flags);
    }
  }

  //|///////////////////// lower_default_copytructor ////////////////////////
  void lower_default_copytructor(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<CompoundType>(ctx.mir.locals[0].type);
    auto thattype = resolve_as_reference(ctx, ctx.mir.locals[1]);

    MIR::Fragment allocator;
    if (fn->parms.size() == 2)
    {
      if (!lower_expr(ctx, allocator, decl_cast<ParmVarDecl>(fn->parms[1]), fn->loc()))
        return;
    }

    for(size_t index = 0; index < thistype->fields.size(); ++index)
    {
      auto type = thistype->fields[index];

      MIR::Fragment result;

      vector<MIR::Fragment> parms(1);
      map<string_view, MIR::Fragment> namedparms;

      parms[0].type = MIR::Local(type, thattype.flags);
      parms[0].value = MIR::RValue::field(MIR::RValue::Ref, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

      if (parms[0].type.flags & MIR::Local::XValue)
        parms[0].type.flags = (parms[0].type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;

      if (allocator)
        namedparms.emplace("allocator?", allocator);

      auto callee = find_callee(ctx, type, parms, namedparms);

      if (!callee)
      {
        ctx.diag.error("cannot resolve constructor", ctx.stack.back(), fn->loc());
        ctx.diag << "  for type: " << *type << '\n';
        diag_callee(ctx, callee, parms, namedparms);
        return;
      }

      lower_call(ctx, result, callee.fx, parms, namedparms, fn->loc());

      auto dst = ctx.add_temporary();
      auto res = ctx.add_temporary();

      MIR::Fragment address;
      address.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(type), MIR::Local::LValue);
      address.value = MIR::RValue::field(MIR::RValue::Ref, 0, MIR::RValue::Field{ MIR::RValue::Ref, index }, fn->loc());

      realise_as_value(ctx, dst, address);

      commit_type(ctx, dst, address.type.type, address.type.flags);

      realise_as_value(ctx, Place(Place::Fer, res), result);

      commit_type(ctx, res, result.type.type, result.type.flags);
    }
  }

  //|///////////////////// lower_default_assignment /////////////////////////
  void lower_default_assignment(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<CompoundType>(resolve_as_reference(ctx, ctx.mir.locals[1]).type);
    auto thattype = resolve_as_reference(ctx, ctx.mir.locals[2]);

    for(size_t index = 0; index < thistype->fields.size(); ++index)
    {
      MIR::Fragment result;

      vector<MIR::Fragment> parms(2);
      map<string_view, MIR::Fragment> namedparms;

      auto lhsfield = find_field(ctx, thistype, index);

      parms[0].type = MIR::Local(lhsfield.type, lhsfield.defn, MIR::Local::LValue | MIR::Local::Reference);
      parms[0].value = MIR::RValue::field(MIR::RValue::Ref, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

      lower_expr_deref(ctx, parms[0]);

      auto rhsfield = find_field(ctx, type_cast<CompoundType>(thattype.type), index);

      parms[1].type = MIR::Local(rhsfield.type, rhsfield.defn, thattype.flags);
      parms[1].value = MIR::RValue::field(MIR::RValue::Ref, 2, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

      if (parms[1].type.flags & MIR::Local::XValue)
        parms[1].type.flags = (parms[1].type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;

      lower_expr_deref(ctx, parms[1]);

      lower_expr(ctx, result, BinaryOpExpr::Assign, parms, namedparms, fn->loc());

      auto res = ctx.add_temporary();

      realise(ctx, Place(Place::Val, res), result);

      commit_type(ctx, res, result.type.type, result.type.flags);
    }

    ctx.add_statement(MIR::Statement::assign(0, MIR::RValue::local(MIR::RValue::Val, 1, fn->loc())));
  }

  //|///////////////////// lower_default_equality ///////////////////////////
  void lower_default_equality(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<CompoundType>(resolve_as_reference(ctx, ctx.mir.locals[1]).type);
    auto thattype = type_cast<CompoundType>(resolve_as_reference(ctx, ctx.mir.locals[2]).type);

    for(size_t index = 0; index < thistype->fields.size(); ++index)
    {
      MIR::Fragment result;

      vector<MIR::Fragment> parms(2);
      map<string_view, MIR::Fragment> namedparms;

      auto lhsfield = find_field(ctx, thistype, index);

      parms[0].type = MIR::Local(lhsfield.type, lhsfield.defn, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
      parms[0].value = MIR::RValue::field(MIR::RValue::Ref, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

      lower_expr_deref(ctx, parms[0]);

      auto rhsfield = find_field(ctx, thattype, index);

      parms[1].type = MIR::Local(rhsfield.type, rhsfield.defn, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
      parms[1].value = MIR::RValue::field(MIR::RValue::Ref, 2, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

      lower_expr_deref(ctx, parms[1]);

      lower_expr(ctx, result, BinaryOpExpr::EQ, parms, namedparms, fn->loc());

      realise(ctx, Place(Place::Val, 0), result);

      commit_type(ctx, 0, result.type.type, result.type.flags);

      ctx.add_block(MIR::Terminator::switcher(0, ctx.currentblockid + thistype->fields.size() - index, ctx.currentblockid + 1));
    }

    if (thistype->fields.empty())
    {
      ctx.add_statement(MIR::Statement::assign(0, ctx.mir.make_expr<BoolLiteralExpr>(true, fn->loc())));
    }
  }

  //|///////////////////// lower_default_compare ////////////////////////////
  void lower_default_compare(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<CompoundType>(resolve_as_reference(ctx, ctx.mir.locals[1]).type);
    auto thattype = type_cast<CompoundType>(resolve_as_reference(ctx, ctx.mir.locals[2]).type);

    for(size_t index = 0; index < thistype->fields.size(); ++index)
    {
      MIR::Fragment result;

      vector<MIR::Fragment> parms(2);
      map<string_view, MIR::Fragment> namedparms;

      auto lhsfield = find_field(ctx, thistype, index);

      parms[0].type = MIR::Local(lhsfield.type, lhsfield.defn, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
      parms[0].value = MIR::RValue::field(MIR::RValue::Ref, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

      lower_expr_deref(ctx, parms[0]);

      auto rhsfield = find_field(ctx, thattype, index);

      parms[1].type = MIR::Local(rhsfield.type, rhsfield.defn, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
      parms[1].value = MIR::RValue::field(MIR::RValue::Ref, 2, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

      lower_expr_deref(ctx, parms[1]);

      lower_expr(ctx, result, BinaryOpExpr::Cmp, parms, namedparms, fn->loc());

      realise(ctx, Place(Place::Val, 0), result);

      commit_type(ctx, 0, result.type.type, result.type.flags);

      auto tst = find_builtin(ctx, Builtin::EQ, Builtin::type(Builtin::Type_I32));
      auto zero = ctx.add_temporary(Builtin::type(Builtin::Type_I32), MIR::Local::Const | MIR::Local::Literal);

      ctx.add_statement(MIR::Statement::assign(zero, ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, 0), fn->loc())));

      auto res = ctx.add_temporary(ctx.booltype, MIR::Local::LValue);

      ctx.add_statement(MIR::Statement::assign(res, MIR::RValue::call(tst, { 0, zero }, fn->loc())));

      ctx.add_block(MIR::Terminator::switcher(res, ctx.currentblockid + thistype->fields.size() - index, ctx.currentblockid + 1));
    }

    if (thistype->fields.empty())
    {
      ctx.add_statement(MIR::Statement::assign(0, ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, 0), fn->loc())));
    }
  }

  //|///////////////////// lower_default_destructor /////////////////////////
  void lower_default_destructor(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<CompoundType>(resolve_as_reference(ctx, ctx.mir.locals[1]).type);

    auto res = ctx.add_temporary(ctx.voidtype, MIR::Local::LValue);

    for(size_t index = thistype->fields.size(); index-- != 0; )
    {
      auto type = thistype->fields[index];
      auto decl = decl_cast<FieldVarDecl>(type_cast<TagType>(thistype)->fieldvars[index]);

      if (auto callee = find_destructor(ctx, type, decl->loc()))
      {
        auto src = ctx.add_temporary(type, MIR::Local::Reference);

        ctx.add_statement(MIR::Statement::assign(src, MIR::RValue::field(MIR::RValue::Ref, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc())));
        ctx.add_statement(MIR::Statement::assign(res, MIR::RValue::call(callee.fx, { src }, fn->loc())));
      }
    }
  }

  //|///////////////////// flattened_array //////////////////////////////////
  void flatten_array_range(Type* &type, size_t &len, vector<MIR::RValue::Field> &head, vector<MIR::RValue::Field> &tail)
  {
    while (is_array_type(type))
    {
      auto subtype = type_cast<ArrayType>(type)->type;
      auto subsize = array_len(type_cast<ArrayType>(type));

      head.push_back(MIR::RValue::Field{ MIR::RValue::Idx, 0 });

      tail.back().index -= 1;
      tail.push_back(MIR::RValue::Field{ MIR::RValue::Idx, subsize });

      type = subtype;
      len *= subsize;
    }
  }

  //|///////////////////// lower_array_constructor //////////////////////////
  void lower_array_constructor(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<ArrayType>(ctx.mir.locals[0].type);

    auto type = thistype->type;
    auto arraylen = array_len(thistype);

    if (type->flags & Type::ZeroSized)
    {
      ctx.diag.error("arrays of zerosized types not implemented", ctx.stack.back(), fn->loc());
      return;
    }

    if (arraylen != 0)
    {
      auto head = vector{ MIR::RValue::Field{ MIR::RValue::Idx, 0 } };
      auto tail = vector{ MIR::RValue::Field{ MIR::RValue::Idx, arraylen } };

      flatten_array_range(type, arraylen, head, tail);

      auto typeref = ctx.typetable.find_or_create<ReferenceType>(type);

      auto inc = find_builtin(ctx, Builtin::PreInc, typeref);
      auto cmp = find_builtin(ctx, Builtin::NE, typeref);

      auto dst = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto res = ctx.add_temporary();
      auto end = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto dsr = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto dsi = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto flg = ctx.add_temporary(ctx.booltype, MIR::Local::LValue);

      ctx.add_statement(MIR::Statement::assign(dst, MIR::RValue::field(MIR::RValue::Ref, 0, head, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(end, MIR::RValue::field(MIR::RValue::Ref, 0, tail, fn->loc())));

      ctx.add_statement(MIR::Statement::assign(dsr, MIR::RValue::local(MIR::RValue::Ref, dst, fn->loc())));

      auto block_head = ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

      MIR::Fragment result;

      vector<MIR::Fragment> parms;
      map<string_view, MIR::Fragment> namedparms;

      auto callee = find_callee(ctx, type, parms, namedparms);

      if (!callee)
      {
        ctx.diag.error("cannot resolve array element constructor", ctx.stack.back(), fn->loc());
        diag_callee(ctx, callee, parms, namedparms);
        return;
      }

      lower_call(ctx, result, callee.fx, parms, namedparms, fn->loc());

      realise_as_value(ctx, Place(Place::Fer, res), result);

      commit_type(ctx, res, result.type.type, result.type.flags);

      ctx.add_statement(MIR::Statement::assign(dsi, MIR::RValue::call(inc, { dsr }, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(flg, MIR::RValue::call(cmp, { dst, end }, fn->loc())));
      ctx.add_block(MIR::Terminator::switcher(flg, ctx.currentblockid + 1, block_head + 1));
    }
  }

  //|///////////////////// lower_array_copytructor //////////////////////////
  void lower_array_copytructor(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<ArrayType>(ctx.mir.locals[0].type);
    auto thattype = resolve_as_reference(ctx, ctx.mir.locals[1]);

    auto type = thistype->type;
    auto arraylen = array_len(thistype);

    if (arraylen != 0)
    {
      auto head = vector{ MIR::RValue::Field{ MIR::RValue::Idx, 0 } };
      auto tail = vector{ MIR::RValue::Field{ MIR::RValue::Idx, arraylen } };

      flatten_array_range(type, arraylen, head, tail);

      auto typeref = ctx.typetable.find_or_create<ReferenceType>(type);

      auto inc = find_builtin(ctx, Builtin::PreInc, typeref);
      auto cmp = find_builtin(ctx, Builtin::NE, typeref);

      auto src = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto dst = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto res = ctx.add_temporary();
      auto end = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto srr = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto sri = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto dsr = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto dsi = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto flg = ctx.add_temporary(ctx.booltype, MIR::Local::LValue);

      ctx.add_statement(MIR::Statement::assign(dst, MIR::RValue::field(MIR::RValue::Ref, 0, head, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(end, MIR::RValue::field(MIR::RValue::Ref, 0, tail, fn->loc())));

      head[0].op = MIR::RValue::Val;

      ctx.add_statement(MIR::Statement::assign(src, MIR::RValue::field(MIR::RValue::Ref, 1, head, fn->loc())));

      ctx.add_statement(MIR::Statement::assign(srr, MIR::RValue::local(MIR::RValue::Ref, src, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(dsr, MIR::RValue::local(MIR::RValue::Ref, dst, fn->loc())));

      auto block_head = ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

      MIR::Fragment result;

      vector<MIR::Fragment> parms(1);
      map<string_view, MIR::Fragment> namedparms;

      parms[0].type = MIR::Local(type, thattype.flags);
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, src, fn->loc());

      if (parms[0].type.flags & MIR::Local::XValue)
        parms[0].type.flags = (parms[0].type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;

      auto callee = find_callee(ctx, type, parms, namedparms);

      if (!callee)
      {
        ctx.diag.error("cannot resolve array element constructor", ctx.stack.back(), fn->loc());
        diag_callee(ctx, callee, parms, namedparms);
        return;
      }

      lower_call(ctx, result, callee.fx, parms, namedparms, fn->loc());

      realise_as_value(ctx, Place(Place::Fer, res), result);

      commit_type(ctx, res, result.type.type, result.type.flags);

      ctx.add_statement(MIR::Statement::assign(sri, MIR::RValue::call(inc, { srr }, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(dsi, MIR::RValue::call(inc, { dsr }, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(flg, MIR::RValue::call(cmp, { dst, end }, fn->loc())));
      ctx.add_block(MIR::Terminator::switcher(flg, ctx.currentblockid + 1, block_head + 1));
    }
  }

  //|///////////////////// lower_array_assignment ///////////////////////////
  void lower_array_assignment(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<ArrayType>(resolve_as_reference(ctx, ctx.mir.locals[1]).type);
    auto thattype = resolve_as_reference(ctx, ctx.mir.locals[2]);

    auto type = thistype->type;
    auto arraylen = array_len(thistype);

    if (arraylen != 0)
    {
      auto head = vector{ MIR::RValue::Field{ MIR::RValue::Val, 0 } };
      auto tail = vector{ MIR::RValue::Field{ MIR::RValue::Val, arraylen } };

      flatten_array_range(type, arraylen, head, tail);

      auto typeref = ctx.typetable.find_or_create<ReferenceType>(type);

      auto inc = find_builtin(ctx, Builtin::PreInc, typeref);
      auto cmp = find_builtin(ctx, Builtin::NE, typeref);

      auto src = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto dst = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto res = ctx.add_temporary();
      auto end = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto srr = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto sri = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto dsr = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto dsi = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto flg = ctx.add_temporary(ctx.booltype, MIR::Local::LValue);

      ctx.add_statement(MIR::Statement::assign(dst, MIR::RValue::field(MIR::RValue::Ref, 1, head, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(end, MIR::RValue::field(MIR::RValue::Ref, 1, tail, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(src, MIR::RValue::field(MIR::RValue::Ref, 2, head, fn->loc())));

      ctx.add_statement(MIR::Statement::assign(srr, MIR::RValue::local(MIR::RValue::Ref, src, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(dsr, MIR::RValue::local(MIR::RValue::Ref, dst, fn->loc())));

      auto block_head = ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

      MIR::Fragment result;

      vector<MIR::Fragment> parms(2);
      map<string_view, MIR::Fragment> namedparms;

      parms[0].type = MIR::Local(type, MIR::Local::LValue | MIR::Local::Reference);
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, dst, fn->loc());

      parms[1].type = MIR::Local(type, thattype.flags);
      parms[1].value = MIR::RValue::local(MIR::RValue::Val, src, fn->loc());

      if (parms[1].type.flags & MIR::Local::XValue)
        parms[1].type.flags = (parms[1].type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;

      lower_expr(ctx, result, BinaryOpExpr::Assign, parms, namedparms, fn->loc());

      realise(ctx, Place(Place::Val, res), result);

      commit_type(ctx, res, result.type.type, result.type.flags);

      ctx.add_statement(MIR::Statement::assign(sri, MIR::RValue::call(inc, { srr }, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(dsi, MIR::RValue::call(inc, { dsr }, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(flg, MIR::RValue::call(cmp, { dst, end}, fn->loc())));
      ctx.add_block(MIR::Terminator::switcher(flg, ctx.currentblockid + 1, block_head + 1));
    }

    ctx.add_statement(MIR::Statement::assign(0, MIR::RValue::local(MIR::RValue::Val, 1, fn->loc())));
  }

  //|///////////////////// lower_array_equality /////////////////////////////
  void lower_array_equality(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<ArrayType>(resolve_as_reference(ctx, ctx.mir.locals[1]).type);

    auto type = thistype->type;
    auto arraylen = array_len(thistype);

    if (arraylen != 0)
    {
      auto head = vector{ MIR::RValue::Field{ MIR::RValue::Val, 0 } };
      auto tail = vector{ MIR::RValue::Field{ MIR::RValue::Val, arraylen } };

      flatten_array_range(type, arraylen, head, tail);

      auto typeref = ctx.typetable.find_or_create<ReferenceType>(type);

      auto inc = find_builtin(ctx, Builtin::PreInc, typeref);
      auto cmp = find_builtin(ctx, Builtin::NE, typeref);

      auto lhs = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto rhs = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto end = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto srr = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto sri = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto dsr = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto dsi = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto flg = ctx.add_temporary(ctx.booltype, MIR::Local::LValue);

      ctx.add_statement(MIR::Statement::assign(rhs, MIR::RValue::field(MIR::RValue::Ref, 1, head, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(end, MIR::RValue::field(MIR::RValue::Ref, 1, tail, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(lhs, MIR::RValue::field(MIR::RValue::Ref, 2, head, fn->loc())));

      ctx.add_statement(MIR::Statement::assign(srr, MIR::RValue::local(MIR::RValue::Ref, lhs, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(dsr, MIR::RValue::local(MIR::RValue::Ref, rhs, fn->loc())));

      auto block_head = ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

      MIR::Fragment result;

      vector<MIR::Fragment> parms(2);
      map<string_view, MIR::Fragment> namedparms;

      parms[0].type = MIR::Local(type, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, rhs, fn->loc());

      parms[1].type = MIR::Local(type, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
      parms[1].value = MIR::RValue::local(MIR::RValue::Val, lhs, fn->loc());

      lower_expr(ctx, result, BinaryOpExpr::EQ, parms, namedparms, fn->loc());

      realise(ctx, Place(Place::Val, 0), result);

      commit_type(ctx, 0, result.type.type, result.type.flags);

      ctx.add_block(MIR::Terminator::switcher(0, ctx.currentblockid + 2, ctx.currentblockid + 1));

      ctx.add_statement(MIR::Statement::assign(sri, MIR::RValue::call(inc, { srr }, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(dsi, MIR::RValue::call(inc, { dsr }, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(flg, MIR::RValue::call(cmp, { rhs, end}, fn->loc())));
      ctx.add_block(MIR::Terminator::switcher(flg, ctx.currentblockid + 1, block_head + 1));
    }

    if (arraylen == 0)
    {
      ctx.add_statement(MIR::Statement::assign(0, ctx.mir.make_expr<BoolLiteralExpr>(true, fn->loc())));
    }
  }

  //|///////////////////// lower_array_compare //////////////////////////////
  void lower_array_compare(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<ArrayType>(resolve_as_reference(ctx, ctx.mir.locals[1]).type);

    auto type = thistype->type;
    auto arraylen = array_len(thistype);

    if (arraylen != 0)
    {
      auto head = vector{ MIR::RValue::Field{ MIR::RValue::Val, 0 } };
      auto tail = vector{ MIR::RValue::Field{ MIR::RValue::Val, arraylen } };

      flatten_array_range(type, arraylen, head, tail);

      auto typeref = ctx.typetable.find_or_create<ReferenceType>(type);

      auto inc = find_builtin(ctx, Builtin::PreInc, typeref);
      auto cmp = find_builtin(ctx, Builtin::NE, typeref);

      auto lhs = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto rhs = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto end = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto srr = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto sri = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto dsr = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto dsi = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto flg = ctx.add_temporary(ctx.booltype, MIR::Local::LValue);

      ctx.add_statement(MIR::Statement::assign(rhs, MIR::RValue::field(MIR::RValue::Ref, 1, head, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(end, MIR::RValue::field(MIR::RValue::Ref, 1, tail, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(lhs, MIR::RValue::field(MIR::RValue::Ref, 2, head, fn->loc())));

      ctx.add_statement(MIR::Statement::assign(srr, MIR::RValue::local(MIR::RValue::Ref, lhs, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(dsr, MIR::RValue::local(MIR::RValue::Ref, rhs, fn->loc())));

      auto block_head = ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

      MIR::Fragment result;

      vector<MIR::Fragment> parms(2);
      map<string_view, MIR::Fragment> namedparms;

      parms[0].type = MIR::Local(type, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, rhs, fn->loc());

      parms[1].type = MIR::Local(type, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
      parms[1].value = MIR::RValue::local(MIR::RValue::Val, lhs, fn->loc());

      lower_expr(ctx, result, BinaryOpExpr::Cmp, parms, namedparms, fn->loc());

      realise(ctx, Place(Place::Val, 0), result);

      commit_type(ctx, 0, result.type.type, result.type.flags);

      auto tst = find_builtin(ctx, Builtin::EQ, Builtin::type(Builtin::Type_I32));
      auto zero = ctx.add_temporary(Builtin::type(Builtin::Type_I32), MIR::Local::Const | MIR::Local::Literal);

      ctx.add_statement(MIR::Statement::assign(zero, ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, 0), fn->loc())));

      auto res = ctx.add_temporary(ctx.booltype, MIR::Local::LValue);

      ctx.add_statement(MIR::Statement::assign(res, MIR::RValue::call(tst, { 0, zero }, fn->loc())));

      ctx.add_block(MIR::Terminator::switcher(res, ctx.currentblockid + 2, ctx.currentblockid + 1));

      ctx.add_statement(MIR::Statement::assign(sri, MIR::RValue::call(inc, { srr }, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(dsi, MIR::RValue::call(inc, { dsr }, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(flg, MIR::RValue::call(cmp, { rhs, end}, fn->loc())));
      ctx.add_block(MIR::Terminator::switcher(flg, ctx.currentblockid + 1, block_head + 1));
    }

    if (arraylen == 0)
    {
      ctx.add_statement(MIR::Statement::assign(0, ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, 0), fn->loc())));
    }
  }

  //|///////////////////// lower_array_destructor ///////////////////////////
  void lower_array_destructor(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<ArrayType>(resolve_as_reference(ctx, ctx.mir.locals[1]).type);

    auto type = thistype->type;
    auto arraylen = array_len(thistype);

    if (arraylen != 0)
    {
      auto head = vector{ MIR::RValue::Field{ MIR::RValue::Val, 0 } };
      auto tail = vector{ MIR::RValue::Field{ MIR::RValue::Val, arraylen } };

      flatten_array_range(type, arraylen, head, tail);

      if (auto callee = find_destructor(ctx, type, fn->loc()))
      {
        auto typeref = ctx.typetable.find_or_create<ReferenceType>(type);

        auto inc = find_builtin(ctx, Builtin::PreInc, typeref);
        auto cmp = find_builtin(ctx, Builtin::NE, typeref);

        auto src = ctx.add_temporary(typeref, MIR::Local::LValue);
        auto res = ctx.add_temporary(ctx.voidtype, MIR::Local::LValue);
        auto end = ctx.add_temporary(typeref, MIR::Local::LValue);
        auto srr = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
        auto sri = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
        auto flg = ctx.add_temporary(ctx.booltype, MIR::Local::LValue);

        ctx.add_statement(MIR::Statement::assign(src, MIR::RValue::field(MIR::RValue::Ref, 1, head, fn->loc())));
        ctx.add_statement(MIR::Statement::assign(end, MIR::RValue::field(MIR::RValue::Ref, 1, tail, fn->loc())));

        ctx.add_statement(MIR::Statement::assign(srr, MIR::RValue::local(MIR::RValue::Ref, src, fn->loc())));

        auto block_head = ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

        ctx.add_statement(MIR::Statement::assign(res, MIR::RValue::call(callee.fx, { src }, fn->loc())));

        ctx.add_statement(MIR::Statement::assign(sri, MIR::RValue::call(inc, { srr }, fn->loc())));
        ctx.add_statement(MIR::Statement::assign(flg, MIR::RValue::call(cmp, { src, end }, fn->loc())));
        ctx.add_block(MIR::Terminator::switcher(flg, ctx.currentblockid + 1, block_head + 1));
      }
    }
  }

  //|///////////////////// lower_tuple_inittructor //////////////////////////
  void lower_tuple_inittructor(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<TupleType>(ctx.mir.locals[0].type);
    auto thattype = resolve_as_reference(ctx, ctx.mir.locals[1]);

    for(size_t index = 0; index < thistype->fields.size(); ++index)
    {
      auto type = thistype->fields[index];

      MIR::Fragment result;

      vector<MIR::Fragment> parms(1);
      map<string_view, MIR::Fragment> namedparms;

      parms[0].type = resolve_as_reference(ctx, type_cast<TupleType>(thattype.type)->fields[index]);
      parms[0].value = MIR::RValue::field(MIR::RValue::Val, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

      if (parms[0].type.flags & MIR::Local::XValue)
        parms[0].type.flags = (parms[0].type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;

      auto callee = find_callee(ctx, type, parms, namedparms);

      if (!callee)
      {
        ctx.diag.error("cannot resolve tuple element constructor", ctx.stack.back(), fn->loc());
        diag_callee(ctx, callee, parms, namedparms);
        return;
      }

      lower_call(ctx, result, callee.fx, parms, namedparms, fn->loc());

      auto dst = ctx.add_temporary();
      auto res = ctx.add_temporary();

      MIR::Fragment address;
      address.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(type), MIR::Local::LValue);
      address.value = MIR::RValue::field(MIR::RValue::Ref, 0, MIR::RValue::Field{ MIR::RValue::Ref, index }, fn->loc());

      realise_as_value(ctx, dst, address);

      commit_type(ctx, dst, address.type.type, address.type.flags);

      realise_as_value(ctx, Place(Place::Fer, res), result);

      commit_type(ctx, res, result.type.type, result.type.flags);
    }
  }

  //|///////////////////// lower_defaulted_body /////////////////////////////
  void lower_defaulted_body(LowerContext &ctx)
  {
    auto sm = ctx.push_barrier();

    switch(ctx.mir.fx.fn->builtin)
    {
      case Builtin::Default_Constructor:
        lower_default_constructor(ctx);
        break;

      case Builtin::Default_Copytructor:
        if (is_trivial_copy_type(ctx.mir.locals[0].type))
          lower_trivial_copytructor(ctx);
        else
          lower_default_copytructor(ctx);
        break;

      case Builtin::Default_Assignment:
        if (is_trivial_assign_type(resolve_as_reference(ctx, ctx.mir.locals[1]).type))
          lower_trivial_assignment(ctx);
        else
          lower_default_assignment(ctx);
        break;

      case Builtin::Default_Equality:
        lower_default_equality(ctx);
        break;

      case Builtin::Default_Compare:
        lower_default_compare(ctx);
        break;

      case Builtin::Default_Destructor:
        lower_default_destructor(ctx);
        break;

      case Builtin::Array_Constructor:
        lower_array_constructor(ctx);
        break;

      case Builtin::Array_Copytructor:
        if (is_trivial_copy_type(ctx.mir.locals[0].type))
          lower_trivial_copytructor(ctx);
        else
          lower_array_copytructor(ctx);
        break;

      case Builtin::Array_Assignment:
        if (is_trivial_assign_type(resolve_as_reference(ctx, ctx.mir.locals[1]).type))
          lower_trivial_assignment(ctx);
        else
          lower_array_assignment(ctx);
        break;

      case Builtin::ArrayEq:
        lower_array_equality(ctx);
        break;

      case Builtin::ArrayCmp:
        lower_array_compare(ctx);
        break;

      case Builtin::Array_Destructor:
        lower_array_destructor(ctx);
        break;

      case Builtin::Tuple_Constructor:
        lower_default_constructor(ctx);
        break;

      case Builtin::Tuple_Inittructor:
        lower_tuple_inittructor(ctx);
        break;

      case Builtin::Tuple_Copytructor:
        if (is_trivial_copy_type(ctx.mir.locals[0].type))
          lower_trivial_copytructor(ctx);
        else
          lower_default_copytructor(ctx);
        break;

      case Builtin::Tuple_Assignment:
        if (is_trivial_assign_type(resolve_as_reference(ctx, ctx.mir.locals[1]).type))
          lower_trivial_assignment(ctx);
        else
          lower_default_assignment(ctx);
        break;

      case Builtin::Tuple_AssignmentEx:
        lower_default_assignment(ctx);
        break;

      case Builtin::TupleEq:
      case Builtin::TupleEqEx:
        lower_default_equality(ctx);
        break;

      case Builtin::TupleCmp:
      case Builtin::TupleCmpEx:
        lower_default_compare(ctx);
        break;

      case Builtin::Tuple_Destructor:
        lower_default_destructor(ctx);
        break;

      default:
        ctx.diag.error("invalid defaulted function", ctx.stack.back(), ctx.mir.fx.fn->loc());
    }

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_declaration_statement //////////////////////
  void lower_declaration_statement(LowerContext &ctx, DeclStmt *stmt)
  {
    switch(stmt->decl->kind())
    {
      case Decl::VoidVar:
        lower_decl(ctx, decl_cast<VoidVarDecl>(stmt->decl));
        break;

      case Decl::StmtVar:
        lower_decl(ctx, decl_cast<StmtVarDecl>(stmt->decl));
        break;

      case Decl::ThisVar:
        lower_decl(ctx, decl_cast<ThisVarDecl>(stmt->decl));
        break;

      case Decl::ErrorVar:
        break;

      case Decl::Function:
      case Decl::TypeAlias:
      case Decl::Struct:
      case Decl::Concept:
      case Decl::Enum:
      case Decl::Import:
      case Decl::Using:
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// lower_expression_statement ///////////////////////
  void lower_expression_statement(LowerContext &ctx, ExprStmt *stmt)
  {
    auto sm = ctx.push_barrier();

    if (stmt->expr)
    {
      MIR::Fragment result;

      if (!lower_expr(ctx, result, stmt->expr))
        return;

      auto arg = ctx.add_variable();

      realise(ctx, arg, result);

      commit_type(ctx, arg, result.type.type, result.type.flags);

      if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
        realise_destructor(ctx, arg, stmt->loc());
    }

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_if_statement ///////////////////////////////
  void lower_if_statement(LowerContext &ctx, IfStmt *ifs)
  {
    auto sm = ctx.push_barrier();
    ctx.stack.emplace_back(ifs, ctx.stack.back().typeargs);

    for(auto &init : ifs->inits)
    {
      ctx.stack.back().goalpost = init;

      lower_statement(ctx, init);
    }

    ctx.stack.back().goalpost = nullptr;

    MIR::Fragment condition;

    if (!lower_expr(ctx, condition, ifs->cond))
      return;

    if (!is_bool_type(condition.type.type))
    {
      if (!lower_cast(ctx, condition, condition, ctx.booltype, ifs->cond->loc()))
        return;
    }

    auto cond = ctx.add_variable();

    realise_as_value(ctx, cond, condition);

    commit_type(ctx, cond, condition.type.type, condition.type.flags);

    auto block_switch = ctx.add_block(MIR::Terminator::switcher(cond, ctx.currentblockid + 1));

    bool unreachable[2] = { false, false };

    lower_statement(ctx, ifs->stmts[0]);

    auto block_true = ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    ctx.mir.blocks[block_switch].terminator.targets.emplace_back(0, ctx.currentblockid);

    swap(ctx.unreachable, unreachable[0]);

    if (ifs->stmts[1])
    {
      lower_statement(ctx, ifs->stmts[1]);

      ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

      ctx.mir.blocks[block_true].terminator.blockid = ctx.currentblockid;

      swap(ctx.unreachable, unreachable[1]);
    }

    if (is_true_constant(ctx, condition))
      unreachable[1] = true;

    if (is_false_constant(ctx, condition))
      unreachable[0] = true;

    if (unreachable[0] && unreachable[1])
    {
      collapse_returns(ctx);

      ctx.unreachable = true;
    }

    ctx.stack.pop_back();
    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_if_statement ///////////////////////////////
  void lower_static_if_statement(LowerContext &ctx, IfStmt *ifs)
  {
    auto sm = ctx.push_barrier();
    ctx.stack.emplace_back(ifs, ctx.stack.back().typeargs);

    for(auto &init : ifs->inits)
    {
      ctx.stack.back().goalpost = init;

      lower_statement(ctx, init);
    }

    ctx.stack.back().goalpost = nullptr;

    if (eval(ctx, ctx.stack.back(), ifs->cond) == 1)
    {
      lower_statement(ctx, ifs->stmts[0]);
    }
    else
    {
      if (ifs->stmts[1])
        lower_statement(ctx, ifs->stmts[1]);
    }

    ctx.stack.pop_back();
    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_for_statement //////////////////////////////
  void lower_for_statement(LowerContext &ctx, ForStmt *fors)
  {
    auto sm = ctx.push_barrier();
    ctx.stack.emplace_back(fors, ctx.stack.back().typeargs);

    vector<tuple<RangeVarDecl*, MIR::local_t, MIR::local_t>> ranges;

    for(auto &init : fors->inits)
    {
      ctx.stack.back().goalpost = init;

      if (init->kind() == Stmt::Declaration && stmt_cast<DeclStmt>(init)->decl->kind() == Decl::RangeVar)
      {
        auto rangevar = decl_cast<RangeVarDecl>(stmt_cast<DeclStmt>(init)->decl);

        MIR::Fragment range;

        if (!lower_expr(ctx, range, rangevar->range))
          return;

        auto arg = ctx.add_variable();

        realise(ctx, arg, range);

        if (is_reference_type(rangevar->type))
          range.type.flags &= ~MIR::Local::RValue;

        commit_type(ctx, arg, range.type.type, range.type.flags);

        auto beg = ctx.add_variable();

        {
          MIR::Fragment iterator;

          vector<MIR::Fragment> parms(1);
          map<string_view, MIR::Fragment> namedparms;

          parms[0].type = ctx.mir.locals[arg];
          parms[0].value = MIR::RValue::local(MIR::RValue::Val, arg, rangevar->loc());

          auto callee = find_callee(ctx, parms[0].type.type, "begin", parms, namedparms);

          if (!callee)
          {
            ctx.diag.error("cannot resolve range begin", ctx.stack.back(), rangevar->loc());
            diag_callee(ctx, callee, parms, namedparms);
            return;
          }

          if (!lower_call(ctx, iterator, callee.fx, parms, namedparms, rangevar->loc()))
            return;

          realise(ctx, beg, iterator);

          commit_type(ctx, beg, iterator.type.type, iterator.type.flags);

          if (!(ctx.mir.locals[beg].flags & MIR::Local::Reference))
            realise_destructor(ctx, beg, rangevar->loc());
        }

        auto end = ctx.add_variable();

        {
          MIR::Fragment iterator;

          vector<MIR::Fragment> parms(1);
          map<string_view, MIR::Fragment> namedparms;

          parms[0].type = ctx.mir.locals[arg];
          parms[0].value = MIR::RValue::local(MIR::RValue::Val, arg, rangevar->loc());

          auto callee = find_callee(ctx, parms[0].type.type, "end", parms, namedparms);

          if (!callee)
          {
            ctx.diag.error("cannot resolve range end", ctx.stack.back(), rangevar->loc());
            diag_callee(ctx, callee, parms, namedparms);
            return;
          }

          if (!lower_call(ctx, iterator, callee.fx, parms, namedparms, rangevar->loc()))
            return;

          realise(ctx, end, iterator);

          commit_type(ctx, end, iterator.type.type, iterator.type.flags);

          if (!(ctx.mir.locals[end].flags & MIR::Local::Reference))
            realise_destructor(ctx, end, rangevar->loc());
        }

        ranges.push_back({ rangevar, beg, end});

        continue;
      }

      lower_statement(ctx, init);
    }

    ctx.stack.back().goalpost = nullptr;

    ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    auto block_loop = ctx.currentblockid;

    vector<MIR::block_t> block_conds;

    for(auto &range : ranges)
    {
      MIR::Fragment compare;

      vector<MIR::Fragment> parms(2);
      map<string_view, MIR::Fragment> namedparms;

      auto beg = get<1>(range);
      parms[0].type = ctx.mir.locals[beg];
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, beg, get<0>(range)->loc());

      auto end = get<2>(range);
      parms[1].type = ctx.mir.locals[end];
      parms[1].value = MIR::RValue::local(MIR::RValue::Val, end, get<0>(range)->loc());

      auto callee = find_callee(ctx, parms[0].type.type, "!=", parms, namedparms);

      if (!callee)
      {
        if (callee = find_callee(ctx, parms[0].type.type, "==", parms, namedparms); callee)
        {
          if (!lower_call(ctx, compare, callee.fx, parms, namedparms, fors->loc()))
            return;

          parms.resize(1);
          parms[0] = std::move(compare);

          callee.fx = Builtin::fn(ctx.translationunit->builtins, Builtin::LNot);
        }
      }

      if (!callee)
      {
        ctx.diag.error("cannot resolve iterator inequality", ctx.stack.back(), get<0>(range)->loc());
        diag_callee(ctx, callee, parms, namedparms);
        return;
      }

      if (!lower_call(ctx, compare, callee.fx, parms, namedparms, fors->loc()))
        return;

      auto flg = ctx.add_temporary();

      realise_as_value(ctx, flg, compare);

      commit_type(ctx, flg, compare.type.type, compare.type.flags);

      block_conds.push_back(ctx.add_block(MIR::Terminator::switcher(flg, ctx.currentblockid + 1)));
    }

    MIR::Fragment condition;

    if (fors->cond)
    {
      if (!lower_expr(ctx, condition, fors->cond))
        return;

      if (!is_bool_type(condition.type.type))
      {
        if (!lower_cast(ctx, condition, condition, ctx.booltype, fors->cond->loc()))
          return;
      }

      auto cond = ctx.add_variable();

      realise_as_value(ctx, cond, condition);

      commit_type(ctx, cond, condition.type.type, condition.type.flags);

      block_conds.push_back(ctx.add_block(MIR::Terminator::switcher(cond, ctx.currentblockid + 1)));
    }

    auto ssm = ctx.push_barrier();

    for(auto &range : ranges)
    {
      MIR::Fragment value;
      value.type = ctx.mir.locals[get<1>(range)];
      value.value = MIR::RValue::local(MIR::RValue::Val, get<1>(range), get<0>(range)->loc());

      if (!lower_deref(ctx, value, value, get<0>(range)->loc()))
        return;

      lower_decl(ctx, get<0>(range), value);
    }

    lower_statement(ctx, fors->stmt);

    ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    auto block_step = ctx.currentblockid;

    for(auto &range : ranges)
    {
      MIR::Fragment increment;

      vector<MIR::Fragment> parms(1);
      map<string_view, MIR::Fragment> namedparms;

      auto beg = get<1>(range);
      parms[0].type = ctx.mir.locals[beg];
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, beg, get<0>(range)->loc());

      auto callee = find_callee(ctx, parms[0].type.type, "++", parms, namedparms);

      if (!callee)
      {
        ctx.diag.error("cannot resolve iterator increment", ctx.stack.back(), get<0>(range)->loc());
        diag_callee(ctx, callee, parms, namedparms);
        return;
      }

      if (!lower_call(ctx, increment, callee.fx, parms, namedparms, fors->loc()))
        return;

      auto res = ctx.add_temporary();

      realise(ctx, res, increment);

      commit_type(ctx, res, increment.type.type, increment.type.flags);
    }

    for(auto &iter : fors->iters)
    {
      lower_statement(ctx, iter);
    }

    ctx.retire_barrier(ssm);

    ctx.add_block(MIR::Terminator::gotoer(block_loop));

    for(auto &block_cond : block_conds)
      ctx.mir.blocks[block_cond].terminator.targets.emplace_back(0, ctx.currentblockid);

    for(auto i = ctx.barriers.back().firstcontinue; i < ctx.continues.size(); ++i)
      ctx.mir.blocks[ctx.continues[i]].terminator.blockid = block_step;

    ctx.continues.resize(ctx.barriers.back().firstcontinue);

    for(auto i = ctx.barriers.back().firstbreak; i < ctx.breaks.size(); ++i)
      ctx.mir.blocks[ctx.breaks[i]].terminator.blockid = ctx.currentblockid;

    ctx.unreachable = (!fors->cond || (fors->cond && is_true_constant(ctx, condition))) && ranges.empty() && ctx.barriers.back().firstbreak == ctx.breaks.size();

    ctx.breaks.resize(ctx.barriers.back().firstbreak);

    ctx.stack.pop_back();
    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_rof_statement //////////////////////////////
  void lower_rof_statement(LowerContext &ctx, RofStmt *rofs)
  {
    auto sm = ctx.push_barrier();
    ctx.stack.emplace_back(rofs, ctx.stack.back().typeargs);

    vector<tuple<RangeVarDecl*, MIR::local_t, MIR::local_t>> ranges;

    for(auto &init : rofs->inits)
    {
      ctx.stack.back().goalpost = init;

      if (init->kind() == Stmt::Declaration && stmt_cast<DeclStmt>(init)->decl->kind() == Decl::RangeVar)
      {
        auto rangevar = decl_cast<RangeVarDecl>(stmt_cast<DeclStmt>(init)->decl);

        MIR::Fragment range;

        if (!lower_expr(ctx, range, rangevar->range))
          return;

        auto arg = ctx.add_variable();

        realise(ctx, arg, range);

        if (is_reference_type(rangevar->type))
          range.type.flags &= ~MIR::Local::RValue;

        commit_type(ctx, arg, range.type.type, range.type.flags);

        auto beg = ctx.add_variable();

        {
          MIR::Fragment iterator;

          vector<MIR::Fragment> parms(1);
          map<string_view, MIR::Fragment> namedparms;

          parms[0].type = ctx.mir.locals[arg];
          parms[0].value = MIR::RValue::local(MIR::RValue::Val, arg, rangevar->loc());

          auto callee = find_callee(ctx, parms[0].type.type, "begin", parms, namedparms);

          if (!callee)
          {
            ctx.diag.error("cannot resolve range begin", ctx.stack.back(), rangevar->loc());
            diag_callee(ctx, callee, parms, namedparms);
            return;
          }

          if (!lower_call(ctx, iterator, callee.fx, parms, namedparms, rangevar->loc()))
            return;

          realise(ctx, beg, iterator);

          commit_type(ctx, beg, iterator.type.type, iterator.type.flags);

          if (!(ctx.mir.locals[beg].flags & MIR::Local::Reference))
            realise_destructor(ctx, beg, rangevar->loc());
        }

        auto end = ctx.add_variable();

        {
          MIR::Fragment iterator;

          vector<MIR::Fragment> parms(1);
          map<string_view, MIR::Fragment> namedparms;

          parms[0].type = ctx.mir.locals[arg];
          parms[0].value = MIR::RValue::local(MIR::RValue::Val, arg, rangevar->loc());

          auto callee = find_callee(ctx, parms[0].type.type, "end", parms, namedparms);

          if (!callee)
          {
            ctx.diag.error("cannot resolve range end", ctx.stack.back(), rangevar->loc());
            diag_callee(ctx, callee, parms, namedparms);
            return;
          }

          if (!lower_call(ctx, iterator, callee.fx, parms, namedparms, rangevar->loc()))
            return;

          realise(ctx, end, iterator);

          commit_type(ctx, end, iterator.type.type, iterator.type.flags);

          if (!(ctx.mir.locals[end].flags & MIR::Local::Reference))
            realise_destructor(ctx, end, rangevar->loc());
        }

        ranges.push_back({ rangevar, beg, end });

        continue;
      }

      lower_statement(ctx, init);
    }

    ctx.stack.back().goalpost = nullptr;

    ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    auto block_loop = ctx.currentblockid;

    vector<MIR::block_t> block_conds;

    for(auto &range : ranges)
    {
      MIR::Fragment compare;

      vector<MIR::Fragment> parms(2);
      map<string_view, MIR::Fragment> namedparms;

      auto beg = get<1>(range);
      parms[0].type = ctx.mir.locals[beg];
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, beg, get<0>(range)->loc());

      auto end = get<2>(range);
      parms[1].type = ctx.mir.locals[end];
      parms[1].value = MIR::RValue::local(MIR::RValue::Val, end, get<0>(range)->loc());

      auto callee = find_callee(ctx, parms[0].type.type, "==", parms, namedparms);

      if (!callee)
      {
        ctx.diag.error("cannot resolve iterator equality", ctx.stack.back(), get<0>(range)->loc());
        diag_callee(ctx, callee, parms, namedparms);
        return;
      }

      if (!lower_call(ctx, compare, callee.fx, parms, namedparms, rofs->loc()))
        return;

      auto flg = ctx.add_temporary();

      realise_as_value(ctx, flg, compare);

      commit_type(ctx, flg, compare.type.type, compare.type.flags);

      block_conds.push_back(ctx.add_block(MIR::Terminator::switcher(flg, ctx.currentblockid + 1, ctx.currentblockid + 1)));
    }

    MIR::Fragment condition;

    if (rofs->cond)
    {
      if (!lower_expr(ctx, condition, rofs->cond))
        return;

      if (!is_bool_type(condition.type.type))
      {
        if (!lower_cast(ctx, condition, condition, ctx.booltype, rofs->cond->loc()))
          return;
      }

      auto cond = ctx.add_variable();

      realise_as_value(ctx, cond, condition);

      commit_type(ctx, cond, condition.type.type, condition.type.flags);

      block_conds.push_back(ctx.add_block(MIR::Terminator::switcher(cond, ctx.currentblockid + 1, ctx.currentblockid + 1)));
    }

    auto ssm = ctx.push_barrier();

    for(auto &range : ranges)
    {
      MIR::Fragment decrement;

      vector<MIR::Fragment> parms(1);
      map<string_view, MIR::Fragment> namedparms;

      auto end = get<2>(range);
      parms[0].type = ctx.mir.locals[end];
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, end, get<0>(range)->loc());

      auto callee = find_callee(ctx, ctx.mir.locals[end].type, "--", parms, namedparms);

      if (!callee)
      {
        ctx.diag.error("cannot resolve iterator decrement", ctx.stack.back(), get<0>(range)->loc());
        diag_callee(ctx, callee, parms, namedparms);
        return;
      }

      if (!lower_call(ctx, decrement, callee.fx, parms, namedparms, rofs->loc()))
        return;

      auto res = ctx.add_temporary();

      realise(ctx, res, decrement);

      commit_type(ctx, res, decrement.type.type, decrement.type.flags);
    }

    for(auto &iter : rofs->iters)
    {
      lower_statement(ctx, iter);
    }

    for(auto &range : ranges)
    {
      MIR::Fragment value;
      value.type = ctx.mir.locals[get<2>(range)];
      value.value = MIR::RValue::local(MIR::RValue::Val, get<2>(range), get<0>(range)->loc());

      if (!lower_deref(ctx, value, value, get<0>(range)->loc()))
        return;

      lower_decl(ctx, get<0>(range), value);
    }

    lower_statement(ctx, rofs->stmt);

    ctx.retire_barrier(ssm);

    ctx.add_block(MIR::Terminator::gotoer(block_loop));

    for(auto &block_cond : block_conds)
      ctx.mir.blocks[block_cond].terminator.blockid = ctx.currentblockid;

    for(auto i = ctx.barriers.back().firstcontinue; i < ctx.continues.size(); ++i)
      ctx.mir.blocks[ctx.continues[i]].terminator.blockid = block_loop;

    ctx.continues.resize(ctx.barriers.back().firstcontinue);

    ctx.unreachable = (!rofs->cond || (rofs->cond && is_false_constant(ctx, condition))) && ranges.empty() && ctx.barriers.back().firstbreak == ctx.breaks.size();

    for(auto i = ctx.barriers.back().firstbreak; i < ctx.breaks.size(); ++i)
      ctx.mir.blocks[ctx.breaks[i]].terminator.blockid = ctx.currentblockid;

    ctx.breaks.resize(ctx.barriers.back().firstbreak);

    ctx.stack.pop_back();
    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_for_statement //////////////////////////////
  void lower_static_for_statement(LowerContext &ctx, ForStmt *fors)
  {
    auto sm = ctx.push_barrier();
    ctx.stack.emplace_back(fors, ctx.stack.back().typeargs);

    size_t iterations = size_t(-1);
    map<string_view, StmtVarDecl*> vars;
    vector<tuple<RangeVarDecl*, MIR::Fragment>> ranges;

    for(auto &init : fors->inits)
    {
      ctx.stack.back().goalpost = init;

      if (init->kind() == Stmt::Declaration && stmt_cast<DeclStmt>(init)->decl->kind() == Decl::StmtVar)
      {
        auto var = decl_cast<StmtVarDecl>(stmt_cast<DeclStmt>(init)->decl);

        lower_statement(ctx, init);

        vars.emplace(var->name, var);

        continue;
      }

      if (init->kind() == Stmt::Declaration && stmt_cast<DeclStmt>(init)->decl->kind() == Decl::RangeVar)
      {
        auto rangevar = decl_cast<RangeVarDecl>(stmt_cast<DeclStmt>(init)->decl);

        MIR::Fragment base;

        if (!lower_expr(ctx, base, rangevar->range))
          return;

        if (base.value.kind() != MIR::RValue::Constant)
        {
          auto arg = ctx.add_variable();

          realise_as_reference(ctx, arg, base);

          commit_type(ctx, arg, base.type.type, base.type.flags);

          base.type = ctx.mir.locals[arg];
          base.value = MIR::RValue::local(MIR::RValue::Val, arg, rangevar->loc());
        }

        if (is_tuple_type(base.type.type))
        {
          iterations = min(iterations, type_cast<TupleType>(base.type.type)->fields.size());

          ranges.push_back({ rangevar, base });

          continue;
        }

        ctx.diag.error("unsupported static for initialiser", ctx.stack.back(), init->loc());
        return;
      }

      lower_statement(ctx, init);
    }

    ctx.stack.back().goalpost = nullptr;

    for(size_t index = 0; index < iterations; ++index)
    {
      auto ssm = ctx.push_barrier();

      for(auto &range : ranges)
      {
        MIR::Fragment value = get<1>(range);

        auto field = find_field(ctx, type_cast<TupleType>(value.type.type), index);

        if (!lower_field(ctx, value, value, field, get<0>(range)->loc()))
          return;

        lower_decl(ctx, get<0>(range), value);
      }

      if (fors->cond)
      {
        if (eval(ctx, ctx.stack.back(), fors->cond) != 1)
        {
          ctx.retire_barrier(ssm);

          break;
        }
      }

      lower_statement(ctx, fors->stmt);

      ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

      if (ctx.barriers.back().firstcontinue != ctx.continues.size())
        ctx.unreachable = false;

      for(auto i = ctx.barriers.back().firstcontinue; i < ctx.continues.size(); ++i)
        ctx.mir.blocks[ctx.continues[i]].terminator.blockid = ctx.currentblockid;

      ctx.continues.resize(ctx.barriers.back().firstcontinue);

      for(auto &iter : fors->iters)
      {
        auto expr = stmt_cast<ExprStmt>(iter)->expr;

        if (expr->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(expr)->subexpr->kind() == Expr::DeclRef && !expr_cast<DeclRefExpr>(expr_cast<UnaryOpExpr>(expr)->subexpr)->base)
        {
          auto unaryop = expr_cast<UnaryOpExpr>(expr);
          auto declref = decl_cast<DeclRefDecl>(expr_cast<DeclRefExpr>(unaryop->subexpr)->decl);

          if (auto var = vars.find(declref->name); var != vars.end() && (var->second->flags & VarDecl::Literal))
          {
            if (lower_const(ctx, unaryop, ctx.symbols.find(var->second)->second))
              continue;
          }
        }

        if (expr->kind() == Expr::BinaryOp && expr_cast<BinaryOpExpr>(expr)->lhs->kind() == Expr::DeclRef && !expr_cast<DeclRefExpr>(expr_cast<BinaryOpExpr>(expr)->lhs)->base)
        {
          auto binaryop = expr_cast<BinaryOpExpr>(expr);
          auto declref = decl_cast<DeclRefDecl>(expr_cast<DeclRefExpr>(binaryop->lhs)->decl);

          if (auto var = vars.find(declref->name); var != vars.end() && (var->second->flags & VarDecl::Literal))
          {
            if (lower_const(ctx, binaryop, ctx.symbols.find(var->second)->second))
              continue;
          }
        }

        lower_statement(ctx, iter);
      }

      ctx.retire_barrier(ssm);

      if (ctx.unreachable)
        break;

      if (ctx.diag.has_errored())
        return;

      ctx.unreachable = false;
    }

    if (ctx.barriers.back().firstbreak != ctx.breaks.size())
      ctx.unreachable = false;

    for(auto i = ctx.barriers.back().firstbreak; i < ctx.breaks.size(); ++i)
      ctx.mir.blocks[ctx.breaks[i]].terminator.blockid = ctx.currentblockid;

    ctx.breaks.resize(ctx.barriers.back().firstbreak);

    ctx.stack.pop_back();
    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_while_statement ////////////////////////////
  void lower_while_statement(LowerContext &ctx, WhileStmt *wile)
  {
    auto sm = ctx.push_barrier();
    ctx.stack.emplace_back(wile, ctx.stack.back().typeargs);

    for(auto &init : wile->inits)
    {
      ctx.stack.back().goalpost = init;

      lower_statement(ctx, init);
    }

    ctx.stack.back().goalpost = nullptr;

    ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    auto block_loop = ctx.currentblockid;

    MIR::Fragment condition;

    if (!lower_expr(ctx, condition, wile->cond))
      return;

    if (!is_bool_type(condition.type.type))
    {
      if (!lower_cast(ctx, condition, condition, ctx.booltype, wile->cond->loc()))
        return;
    }

    auto cond = ctx.add_variable();

    realise_as_value(ctx, cond, condition);

    commit_type(ctx, cond, condition.type.type, condition.type.flags);

    auto block_cond = ctx.add_block(MIR::Terminator::switcher(cond, ctx.currentblockid + 1));

    lower_statement(ctx, wile->stmt);

    ctx.add_block(MIR::Terminator::gotoer(block_loop));

    ctx.mir.blocks[block_cond].terminator.targets.emplace_back(0, ctx.currentblockid);

    for(auto i = ctx.barriers.back().firstcontinue; i < ctx.continues.size(); ++i)
      ctx.mir.blocks[ctx.continues[i]].terminator.blockid = block_loop;

    ctx.continues.resize(ctx.barriers.back().firstcontinue);

    ctx.unreachable = is_true_constant(ctx, condition) && ctx.barriers.back().firstbreak == ctx.breaks.size();

    for(auto i = ctx.barriers.back().firstbreak; i < ctx.breaks.size(); ++i)
      ctx.mir.blocks[ctx.breaks[i]].terminator.blockid = ctx.currentblockid;

    ctx.breaks.resize(ctx.barriers.back().firstbreak);

    ctx.stack.pop_back();
    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_try_statement //////////////////////////////
  void lower_try_statement(LowerContext &ctx, TryStmt *trys)
  {
    auto sm = ctx.push_barrier();

    lower_decl(ctx, decl_cast<ErrorVarDecl>(trys->errorvar));

    bool unreachable[2] = { false, false };

    lower_statement(ctx, trys->body);

    auto block_body = ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    swap(ctx.unreachable, unreachable[0]);

    if (ctx.barriers.back().firstthrow != ctx.throws.size())
    {
      for(auto i = ctx.barriers.back().firstthrow; i < ctx.throws.size(); ++i)
        ctx.mir.blocks[ctx.throws[i]].terminator.blockid = ctx.currentblockid;

      ctx.throws.resize(ctx.barriers.back().firstthrow);

      auto ssm = ctx.push_barrier();

      if (!(ctx.mir.locals[ctx.errorarg].flags & MIR::Local::Reference))
        realise_destructor(ctx, ctx.errorarg, trys->handler->loc());

      ctx.errorarg = ctx.barriers[sm].errorarg;

      lower_statement(ctx, trys->handler);

      ctx.retire_barrier(ssm);

      ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

      ctx.mir.blocks[block_body].terminator.blockid = ctx.currentblockid;

      swap(ctx.unreachable, unreachable[1]);
    }

    if (unreachable[0] && unreachable[1])
    {
      collapse_returns(ctx);

      ctx.unreachable = true;
    }

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_throw_statement ////////////////////////////
  void lower_throw_statement(LowerContext &ctx, ThrowStmt *throwe)
  {
    auto sm = ctx.push_barrier();

    if (!ctx.errorarg)
    {
      ctx.diag.error("throw outside try block", ctx.stack.back(), throwe->loc());
      return;
    }

    MIR::Fragment result;

    if (!lower_expr(ctx, result, throwe->expr))
      return;

    realise_as_value(ctx, ctx.errorarg, result);

    if (!deduce_type(ctx, ctx.stack.back(), ctx.mir.fx, ctx.mir.locals[ctx.errorarg].type, result.type))
    {
      ctx.diag.error("type mismatch", ctx.stack.back(), throwe->loc());
      ctx.diag << "  throw type: '" << *result.type.type << "' required type: '" << *ctx.mir.locals[ctx.errorarg].type << "'\n";
      return;
    }

    ctx.throws.push_back(ctx.currentblockid);
    ctx.add_block(MIR::Terminator::thrower(ctx.errorarg, ctx.currentblockid));
    ctx.unreachable = true;

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_break_statement ////////////////////////////
  void lower_break_statement(LowerContext &ctx, BreakStmt *breck)
  {
    ctx.breaks.push_back(ctx.currentblockid);
    ctx.unreachable = true;
  }

  //|///////////////////// lower_continue_statement /////////////////////////
  void lower_continue_statement(LowerContext &ctx, ContinueStmt *continu)
  {
    ctx.continues.push_back(ctx.currentblockid);
    ctx.unreachable = true;
  }

  //|///////////////////// lower_return_statement ///////////////////////////
  void lower_return_statement(LowerContext &ctx, ReturnStmt *retrn)
  {
    auto sm = ctx.push_barrier();

    if (retrn->expr)
    {
      MIR::Fragment result;

      if (!lower_expr(ctx, result, retrn->expr))
        return;

      if (ctx.mir.locals[0])
      {
        if (!deduce_returntype(ctx, ctx.stack.back(), ctx.mir.fx, ctx.mir.locals[0], result.type))
        {
          ctx.diag.error("type mismatch", ctx.stack.back(), retrn->loc());
          ctx.diag << "  return type: '" << *result.type.type << "' required type: '" << *ctx.mir.locals[0].type << "'\n";
          return;
        }
      }

      if (ctx.mir.fx.fn->returntype)
      {
        if (is_lambda_decay(ctx, ctx.mir.locals[0].type, result.type.type))
        {
          if (!lower_lambda_decay(ctx, result, ctx.stack.back(), ctx.mir.locals[0].type, result))
            return;
        }

        if (is_base_cast(ctx, ctx.mir.locals[0].type, result.type.type))
        {
          if (!lower_base_cast(ctx, result, ctx.mir.locals[0].type, result))
            return;
        }
      }

      // Implicit move from local
      if (result.value.kind() == MIR::RValue::Variable && !(result.type.flags & MIR::Local::Const))
      {
        auto &[op, arg, fields, loc] = result.value.get<MIR::RValue::Variable>();

        if (op == MIR::RValue::Ref && ctx.mir.args_end <= arg && fields.empty())
          result.type.flags |= MIR::Local::RValue;
      }

      realise_as_value(ctx, 0, result);

      if (!ctx.mir.fx.fn->returntype)
      {
        if (ctx.mir.locals[0])
        {
          auto lhs = result.type.defn;
          auto rhs = ctx.mir.locals[0].defn;

          while (is_reference_type(lhs) && is_reference_type(rhs))
          {
            lhs = remove_const_type(remove_reference_type(lhs));
            rhs = remove_const_type(remove_reference_type(rhs));
          }

          if (is_reference_type(lhs) || is_reference_type(rhs))
          {
            ctx.diag.error("ambiguous return definitions", ctx.stack.back(), retrn->loc());
            ctx.diag << "  return type: '" << *result.type.defn << "' required type: '" << *ctx.mir.locals[0].defn << "'\n";
            return;
          }
        }

        commit_type(ctx, 0, result.type.type, result.type.flags);

        ctx.mir.locals[0].defn = result.type.defn;
        ctx.mir.locals[0].flags &= ~MIR::Local::RValue;
      }
    }
    else
    {
      if (ctx.mir.locals[0] && !is_void_type(ctx.mir.locals[0].type) && !(ctx.mir.fx.fn->flags & FunctionDecl::Constructor))
      {
        ctx.diag.error("missing return expression", ctx.stack.back(), retrn->loc());
        return;
      }
    }

    ctx.returns.push_back(ctx.currentblockid);
    ctx.unreachable = true;

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_compound_statement /////////////////////////
  void lower_compound_statement(LowerContext &ctx, CompoundStmt *compound)
  {
    auto sm = ctx.push_barrier();
    ctx.stack.emplace_back(compound, ctx.stack.back().typeargs);

    for(auto &stmt : compound->stmts)
    {
      ctx.stack.back().goalpost = stmt;

      if (ctx.unreachable)
        break;

      lower_statement(ctx, stmt);
    }

    // return block consolidation
    if (!ctx.unreachable && ctx.returns.size() > 1 && ctx.barriers.back().retires.size() > 0)
    {
      ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 2));

      collapse_returns(ctx);

      ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid));
    }

    if (!ctx.unreachable)
      ctx.mir.add_lineinfo(ctx.currentblockid, ctx.currentblock.statements.size(), compound->endloc.lineno);

    ctx.stack.pop_back();
    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_statement //////////////////////////////////
  void lower_statement(LowerContext &ctx, Stmt *stmt)
  {
    ctx.mir.add_lineinfo(ctx.currentblockid, ctx.currentblock.statements.size(), stmt->loc().lineno);

    switch(stmt->kind())
    {
      case Stmt::Null:
        break;

      case Stmt::Declaration:
        lower_declaration_statement(ctx, stmt_cast<DeclStmt>(stmt));
        break;

      case Stmt::Expression:
        lower_expression_statement(ctx, stmt_cast<ExprStmt>(stmt));
        break;

      case Stmt::If:
        if (stmt_cast<IfStmt>(stmt)->flags & ForStmt::Static)
          lower_static_if_statement(ctx, stmt_cast<IfStmt>(stmt));
        else
          lower_if_statement(ctx, stmt_cast<IfStmt>(stmt));
        break;

      case Stmt::For:
        if (stmt_cast<ForStmt>(stmt)->flags & ForStmt::Static)
          lower_static_for_statement(ctx, stmt_cast<ForStmt>(stmt));
        else
          lower_for_statement(ctx, stmt_cast<ForStmt>(stmt));
        break;

      case Stmt::Rof:
        lower_rof_statement(ctx, stmt_cast<RofStmt>(stmt));
        break;

      case Stmt::While:
        lower_while_statement(ctx, stmt_cast<WhileStmt>(stmt));
        break;

      case Stmt::Try:
        lower_try_statement(ctx, stmt_cast<TryStmt>(stmt));
        break;

      case Stmt::Throw:
        lower_throw_statement(ctx, stmt_cast<ThrowStmt>(stmt));
        break;

      case Stmt::Break:
        lower_break_statement(ctx, stmt_cast<BreakStmt>(stmt));
        break;

      case Stmt::Continue:
        lower_continue_statement(ctx, stmt_cast<ContinueStmt>(stmt));
        break;

      case Stmt::Return:
        lower_return_statement(ctx, stmt_cast<ReturnStmt>(stmt));
        break;

      case Stmt::Compound:
        lower_compound_statement(ctx, stmt_cast<CompoundStmt>(stmt));
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// lower_expression /////////////////////////////////
  void lower_expression(LowerContext &ctx, Expr *expr)
  {
    ctx.add_local();

    auto sm = ctx.push_barrier();

    MIR::Fragment result;

    if (!lower_expr(ctx, result, expr))
      return;

    realise_as_value(ctx, 0, result);

    commit_type(ctx, 0, result.type.type, result.type.flags);

    ctx.retire_barrier(sm);

    ctx.add_block(MIR::Terminator::returner());
  }

  //|///////////////////// lower_function ///////////////////////////////////
  void lower_function(LowerContext &ctx, FnSig const &fx)
  {
    auto fn = fx.fn;

    ctx.add_local();

    if (fn->returntype)
    {
      commit_type(ctx, 0, remove_const_type(resolve_type(ctx, fn->returntype)));
    }

    if (is_throws(ctx, fx.fn))
    {
      assert(fx.throwtype);

      ctx.errorarg = ctx.add_local();

      commit_type(ctx, ctx.errorarg, fx.throwtype);
    }

    ctx.mir.throws = fx.throwtype;

    ctx.mir.args_beg = ctx.mir.locals.size();

    for(auto &parm : fx.parameters())
    {
      lower_decl(ctx, decl_cast<ParmVarDecl>(parm));
    }

    ctx.mir.args_end = ctx.mir.locals.size();

    ctx.mir.add_lineinfo(ctx.currentblockid, ctx.currentblock.statements.size(), fn->loc().lineno);

    if (fn->body)
    {
      if (fn->flags & FunctionDecl::Constructor)
      {
        lower_initialisers(ctx);
      }

      lower_statement(ctx, fn->body);

      if (!ctx.mir.locals[0].type)
      {
        commit_type(ctx, 0, ctx.voidtype);
      }

      if (!ctx.unreachable && ctx.mir.locals[0].type != ctx.voidtype && !(ctx.mir.fx.fn->flags & FunctionDecl::Constructor))
      {
        ctx.diag.error("missing return statement", ctx.stack.back(), fn->loc());
      }

      if (fn->flags & FunctionDecl::Destructor)
      {
        lower_deinitialisers(ctx);
      }
    }

    if (fn->flags & FunctionDecl::Defaulted)
    {
      lower_defaulted_body(ctx);
    }

    if (!ctx.returns.empty())
    {
      ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

      for(auto &retn : ctx.returns)
        ctx.mir.blocks[retn].terminator.blockid = ctx.currentblockid;
    }

    if (fn->body && fn->body->kind() == Stmt::Compound)
      ctx.mir.add_lineinfo(ctx.currentblockid, ctx.currentblock.statements.size(), stmt_cast<CompoundStmt>(fn->body)->endloc.lineno);

    ctx.add_block(MIR::Terminator::returner());
  }

  //|///////////////////// diag_mismatch ////////////////////////////////////

  void diag_mismatch(LowerContext &ctx, const char *name, MIR::local_t arg, Type *required)
  {
    ctx.diag << "  " << name << ": '" << Diag::white() << *ctx.mir.locals[arg].type << Diag::normal() << "' required type: '" << Diag::white() << *required << Diag::normal() << "'\n";
  }

  void diag_mismatch(LowerContext &ctx, const char *name, Type *vartype, MIR::local_t arg)
  {
    ctx.diag << "  " << name << ": '" << Diag::white() << *vartype << Diag::normal() << "' required type: '" << Diag::white() << *ctx.mir.locals[arg].type << Diag::normal() << "'";

    for(auto &block : ctx.mir.blocks)
    {
      for(auto &statement : block.statements)
      {
        if (statement.kind == MIR::Statement::NoOp)
          continue;

        if (statement.src.kind() == MIR::RValue::Call)
        {
          auto &[callee, args, loc] = statement.src.get<MIR::RValue::Call>();

          if (any_of(args.begin(), args.end(), [&](auto k) { return k == arg; }))
          {
            ctx.diag << " in call " << Diag::white() << loc << ':' << Diag::normal() << "'" << Diag::white() << *callee.fn << Diag::normal() << Diag::normal() << "'";
          }
        }
      }
    }

    ctx.diag << "\n";
  }

  //|///////////////////// promote //////////////////////////////////////////

  bool promote_type(LowerContext &ctx, MIR::local_t id, Type *type, long flags = 0)
  {
    type = remove_const_type(type);

    if (ctx.mir.locals[id].flags & MIR::Local::Reference)
      type = remove_reference_type(type);

    if (ctx.mir.locals[id].flags & MIR::Local::Const)
      type = remove_const_type(type);

    if (ctx.mir.locals[id].type == type)
      return true;

#if 0
  cout << "promote _" << id << ": " << *ctx.mir.locals[id].type << " to " << *type << endl;
#endif

    if (!promote_type(ctx, ctx.mir.locals[id].type, type))
      return false;

    ctx.mir.locals[id].flags |= flags;

    if (is_concrete_type(ctx.mir.locals[id].type))
    {
      for(auto &block : ctx.mir.blocks)
      {
        for(auto &statement : block.statements)
        {
          if (statement.kind == MIR::Statement::Construct)
          {
            if (statement.dst == id)
            {
              promote_type(ctx, ctx.mir.locals[statement.dst - 1].type, ctx.typetable.find_or_create<ReferenceType>(type));
            }

            if (statement.dst - 1 == id)
            {
              promote_type(ctx, ctx.mir.locals[statement.dst].type, remove_const_type(remove_reference_type(type)));
            }
          }

          if (statement.src.kind() == MIR::RValue::Variable)
          {
            auto &[op, arg, fields, loc] = statement.src.get<MIR::RValue::Variable>();

            if (arg == id)
            {
              auto vartype = resolve_as_value(ctx, ctx.mir.locals[arg], fields).type;

              if (op == MIR::RValue::Ref)
                vartype = ctx.typetable.find_or_create<ReferenceType>(vartype);

              if (op == MIR::RValue::Fer)
                vartype = remove_pointference_type(vartype);

              if (statement.kind == MIR::Statement::Construct)
                vartype = ctx.typetable.find_or_create<ReferenceType>(vartype);

              if (!promote_type(ctx, statement.dst, vartype))
              {
                ctx.diag.error("type mismatch", ctx.mir.fx.fn, loc);
                diag_mismatch(ctx, "variable type", vartype, statement.dst);
              }
            }
          }

          if (statement.src.kind() == MIR::RValue::Call)
          {
            auto &[callee, args, loc] = statement.src.get<MIR::RValue::Call>();

            if (any_of(args.begin(), args.end(), [&](auto arg) { return arg == id; }))
            {
              callee.returntype = nullptr;

              for(auto const &[parm, arg] : zip(callee.parameters(), args))
              {
                if (!deduce_type(ctx, callee.fn, callee, decl_cast<ParmVarDecl>(parm), ctx.mir.locals[arg]))
                {
                  ctx.diag.error("type mismatch", ctx.mir.fx.fn, loc);
                  diag_mismatch(ctx, "parameter type", arg, resolve_type_as_reference(ctx, Scope(callee.fn, callee.typeargs), decl_cast<ParmVarDecl>(parm)));
                }
              }

              auto scope = Scope(callee.fn, callee.typeargs);

              if (callee.fn->where && eval(ctx, scope, callee.fn->where) != 1)
              {
                ctx.diag.error("invalid call resolution", ctx.mir.fx.fn, loc);

                for(auto const &[parm, arg] : zip(callee.parameters(), args))
                  diag_mismatch(ctx, "parameter type", arg, decl_cast<ParmVarDecl>(parm)->type);

                return false;
              }

              callee.returntype = find_returntype(ctx, callee).type;

              if (is_concrete_type(callee.returntype))
              {
                auto returntype = callee.returntype;

                if (statement.kind == MIR::Statement::Construct)
                  returntype = ctx.typetable.find_or_create<ReferenceType>(returntype);

                if (!promote_type(ctx, statement.dst, returntype))
                {
                  ctx.diag.error("type mismatch", ctx.mir.fx.fn, loc);
                  diag_mismatch(ctx, "return type", statement.dst, returntype);
                }
              }
            }
          }
        }
      }
    }

    return true;
  }

  //|///////////////////// backfill /////////////////////////////////////////

  void backfill(LowerContext &ctx, MIR &mir)
  {
    if (mir.fx.returntype && !promote_type(ctx, 0, mir.fx.returntype, 0))
    {
      ctx.diag.error("type mismatch", mir.fx.fn, mir.fx.fn->loc());
      diag_mismatch(ctx, "return type", 0, mir.fx.returntype);
    }

    if (mir.fx.fn->flags & FunctionDecl::Defaulted)
      return;

    for(size_t iteration = 0; iteration < 3; ++iteration)
    {
      for(auto block = mir.blocks.rbegin(); block != mir.blocks.rend(); ++block)
      {
        for(auto statement = block->statements.rbegin(); statement != block->statements.rend(); ++statement)
        {
          auto dst = mir.locals[statement->dst];

          if (statement->kind == MIR::Statement::Construct)
            dst.flags &= ~MIR::Local::Reference;

          if (statement->src.kind() == MIR::RValue::Variable)
          {
            auto &[op, arg, fields, loc] = statement->src.get<MIR::RValue::Variable>();

            if (is_concrete_type(dst.type) && !is_concrete_type(mir.locals[arg].type))
            {
              auto vartype = resolve_as_value(ctx, dst).type;

              if (op == MIR::RValue::Ref)
                vartype = remove_pointference_type(vartype);

              if (op == MIR::RValue::Fer)
                vartype = ctx.typetable.find_or_create<ReferenceType>(vartype);

              if (fields.size() != 0)
              {
                if (!is_tuple_type(mir.locals[arg].type) || fields.size() != 1)
                  continue;

                auto tupletype = type_cast<TupleType>(mir.locals[arg].type);

                auto tupledefns = tupletype->defns;
                auto tuplefields = tupletype->fields;

                promote_type(ctx, tuplefields[fields[0].index], vartype);

                vartype = ctx.typetable.find_or_create<TupleType>(tupledefns, tuplefields);

                if (mir.locals[arg].flags & MIR::Local::Reference)
                  vartype = ctx.typetable.find_or_create<ReferenceType>(vartype);
              }

              if (!promote_type(ctx, arg, vartype))
              {
                ctx.diag.error("type mismatch", ctx.mir.fx.fn, loc);
                diag_mismatch(ctx, "variable type", arg, vartype);
              }
            }
          }

          if (statement->src.kind() == MIR::RValue::Call)
          {
            auto &[callee, args, loc] = statement->src.get<MIR::RValue::Call>();

            if (any_of(args.begin(), args.end(), [&](auto arg) { return !is_concrete_type(mir.locals[arg].type); }))
            {
              if (callee.fn->returntype)
              {
                deduce_type(ctx, callee.fn, callee, callee.fn->returntype, dst);
              }

              auto scope = Scope(callee.fn, callee.typeargs);

              for(auto const &[parm, arg] : zip(callee.parameters(), args))
              {
                if (!is_concrete_type(mir.locals[arg].type))
                {
                  auto parmtype = resolve_type_as_value(ctx, scope, decl_cast<ParmVarDecl>(parm));

                  if (!promote_type(ctx, arg, parmtype))
                  {
                    ctx.diag.error("type mismatch", ctx.mir.fx.fn, loc);
                    diag_mismatch(ctx, "parameter type", arg, parmtype);
                  }
                }
              }
            }

            if (is_concrete_type(dst.type) && !is_concrete_type(callee.returntype))
            {
              if (!promote_type(ctx, callee.returntype, dst.type))
              {
                ctx.diag.error("type mismatch", ctx.mir.fx.fn, loc);
                diag_mismatch(ctx, "return type", statement->dst, callee.returntype);
              }
            }
          }
        }
      }

      if (ctx.diag.has_errored())
        return;
    }
  }

  //|///////////////////// deducer //////////////////////////////////////////
  void deducer(LowerContext &ctx, MIR &mir)
  {
    bool changed = false;

    for(auto &block : ctx.mir.blocks)
    {
      for(auto &statement : block.statements)
      {
        auto dst = mir.locals[statement.dst];

        if (statement.kind == MIR::Statement::NoOp)
          continue;

        if (statement.src.kind() == MIR::RValue::Constant)
        {
          if (dst.type == ctx.intliteraltype)
            changed |= promote_type(ctx, statement.dst, type(Builtin::Type_I32));

          if (dst.type == ctx.floatliteraltype)
            changed |= promote_type(ctx, statement.dst, type(Builtin::Type_F64));

          if (dst.type->klass() == Type::Array && type_cast<ArrayType>(dst.type)->type == ctx.intliteraltype)
            changed |= promote_type(ctx, statement.dst, ctx.typetable.find_or_create<ArrayType>(type(Builtin::Type_I32), type_cast<ArrayType>(dst.type)->size));

          if (dst.type->klass() == Type::Array && type_cast<ArrayType>(dst.type)->type == ctx.floatliteraltype)
            changed |= promote_type(ctx, statement.dst, ctx.typetable.find_or_create<ArrayType>(type(Builtin::Type_F64), type_cast<ArrayType>(dst.type)->size));
        }
      }
    }

    if (changed)
    {
      backfill(ctx, mir);
    }
  }

  //|///////////////////// inliner //////////////////////////////////////////
  void inliner(LowerContext &ctx, MIR &mir)
  {
    for(auto &block : ctx.mir.blocks)
    {
      for(auto &statement : block.statements)
      {
        auto dst = mir.locals[statement.dst];

        if (statement.src.kind() == MIR::RValue::Cast)
        {
          auto &[arg, loc] = statement.src.get<MIR::RValue::Cast>();

          if (ctx.mir.locals[arg].flags & MIR::Local::Literal)
          {
            if (auto assignment = find_assignment(ctx.mir, arg, block, statement))
            {
              if (literal_cast(ctx, statement.src, assignment->src, dst.type))
              {
                assignment->kind = MIR::Statement::NoOp;
              }
            }

            if (is_typearg_type(dst.type))
            {
              ctx.diag.error("unresolved cast", ctx.mir.fx.fn, loc);
              diag_mismatch(ctx, "cast type", statement.dst, ctx.mir.locals[arg].type);
            }
          }
        }
      }
    }
  }
}


//|--------------------- Lower ----------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// lower //////////////////////////////////////////////
MIR lower(FnSig const &fx, TypeTable &typetable, Diag &diag, long flags)
{
  LowerContext ctx(typetable, diag, flags);

  seed_stack(ctx.stack, Scope(fx.fn, fx.typeargs));

  ctx.mir.fx = fx;
  ctx.translationunit = decl_cast<TranslationUnitDecl>(get<Decl*>(ctx.stack[0].owner));
  ctx.module = decl_cast<ModuleDecl>(get<Decl*>(ctx.stack[1].owner));

  lower_function(ctx, fx);

#if 0
  dump_mir(ctx.mir);
#endif

  if (diag.has_errored())
    return ctx.mir;

  backfill(ctx, ctx.mir);

  if (flags & LowerFlags::Runtime)
  {
    deducer(ctx, ctx.mir);

    inliner(ctx, ctx.mir);
  }

  return ctx.mir;
}

//|///////////////////// lower //////////////////////////////////////////////
MIR lower(Scope const &scope, Expr *expr, unordered_map<Decl*, MIR::Fragment> const &symbols, TypeTable &typetable, Diag &diag, long flags)
{
  LowerContext ctx(typetable, diag, flags);

  seed_stack(ctx.stack, scope);

  ctx.translationunit = decl_cast<TranslationUnitDecl>(get<Decl*>(ctx.stack[0].owner));
  ctx.module = decl_cast<ModuleDecl>(get<Decl*>(ctx.stack[1].owner));
  ctx.symbols = symbols;

  lower_expression(ctx, expr);

#if 0
  dump_mir(ctx.mir);
#endif

  return ctx.mir;
}
