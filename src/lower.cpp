//
// lower.cpp
//
// Copyright (c) 2020-2024 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "lower.h"
#include "interp.h"
#include "diag.h"
#include <limits>
#include <variant>
#include <algorithm>
#include <iostream>

using namespace std;

#define PACK_REFS 1
#define TRANSATIVE_CONST 1
#define STRICT_BINDING 1
#define REFERENCE_DECAY 1
#define ASSOCIATED_DEREF 0

namespace
{
  enum Unreachable
  {
    No = 0,
    Unwind,
    Yes,
  };

  struct LowerContext
  {
    Diag diag;

    MIR mir;

    MIR::Block currentblock;
    MIR::block_t currentblockid;

    Unreachable unreachable;
    MIR::local_t errorarg;
    vector<MIR::block_t> throws;
    vector<MIR::block_t> breaks;
    vector<MIR::block_t> continues;
    vector<MIR::block_t> returns;
    vector<std::tuple<MIR::block_t, Expr*>> gotos;

    struct Barrier
    {
      size_t locals;
      size_t blocks;
      size_t varinfos;
      size_t lineinfos;
      size_t statements;
      size_t pack_expansion;
      SourceLocation site;
      MIR::local_t errorarg;
      MIR::block_t firstthrow;
      MIR::block_t firstbreak;
      MIR::block_t firstcontinue;
      MIR::block_t firstreturn;
      MIR::block_t firstgoto;
      vector<MIR::Statement> retires;

      Diag::Marker diagstate;
    };

    vector<Barrier> barriers;

    unordered_map<Decl*, MIR::local_t> locals;
    unordered_map<Decl*, MIR::Fragment> symbols;

    unordered_map<Decl*, bool> suppressed;

    MIR::local_t add_local()
    {
      return mir.add_local(MIR::Local());
    }

    MIR::local_t add_variable()
    {
      auto arg = mir.add_local(MIR::Local());

      add_statement(MIR::Statement::storagelive(arg));
      retiring_statement(MIR::Statement::storagedead(arg));

      return arg;
    }

    MIR::local_t add_temporary(Type *type = nullptr, long flags = 0)
    {
      auto arg = mir.add_local(MIR::Local(type, flags));

      add_statement(MIR::Statement::storagelive(arg));
      retiring_statement(MIR::Statement::storagedead(arg));

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
      barrier.pack_expansion = pack_expansion;

      barrier.site = site;
      barrier.errorarg = errorarg;
      barrier.firstthrow = throws.size();
      barrier.firstbreak = breaks.size();
      barrier.firstcontinue = continues.size();
      barrier.firstreturn = returns.size();
      barrier.firstgoto = gotos.size();

      barrier.diagstate = diag.marker();

      return barriers.size() - 1;
    }

    void retiring_statement(MIR::Statement statement)
    {
      barriers.back().retires.push_back(std::move(statement));
    }

    void retire_barrier(size_t marker)
    {
      while (barriers.size() != marker)
      {
        auto &barrier = barriers.back();

        for (auto i = barrier.firstthrow; i < throws.size(); ++i)
        {
          if (auto blk = throws[i]; blk != currentblockid)
            mir.blocks[blk].statements.insert(mir.blocks[blk].statements.end(), barrier.retires.rbegin(), barrier.retires.rend());
        }

        for (auto i = barrier.firstbreak; i < breaks.size(); ++i)
        {
          if (auto blk = breaks[i]; blk != currentblockid)
            mir.blocks[blk].statements.insert(mir.blocks[blk].statements.end(), barrier.retires.rbegin(), barrier.retires.rend());
        }

        for (auto i = barrier.firstcontinue; i < continues.size(); ++i)
        {
          if (auto blk = continues[i]; blk != currentblockid)
            mir.blocks[blk].statements.insert(mir.blocks[blk].statements.end(), barrier.retires.rbegin(), barrier.retires.rend());
        }

        for (auto i = barrier.firstreturn; i < returns.size(); ++i)
        {
          if (auto blk = returns[i]; blk != currentblockid)
            mir.blocks[blk].statements.insert(mir.blocks[blk].statements.end(), barrier.retires.rbegin(), barrier.retires.rend());
        }

        for (auto i = barrier.firstgoto; i < gotos.size(); ++i)
        {
          if (auto blk = get<0>(gotos[i]); blk != currentblockid)
            mir.blocks[blk].statements.insert(mir.blocks[blk].statements.end(), barrier.retires.rbegin(), barrier.retires.rend());
        }

        if (mir.throws && errorarg == 1)
        {
          returns.insert(returns.end(), throws.begin() + barrier.firstthrow, throws.end());

          throws.resize(barrier.firstthrow);
        }

        if (unreachable != Unreachable::Yes)
        {
          for (auto i = barrier.retires.rbegin(); i != barrier.retires.rend(); ++i)
          {
            add_statement(std::move(*i));
          }
        }

        pack_expansion = barrier.pack_expansion;
        errorarg = barrier.errorarg;
        site = barrier.site;

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

        pack_expansion = barrier.pack_expansion;
        errorarg = barrier.errorarg;
        site = barrier.site;

        diag.revert(barrier.diagstate);

        barriers.pop_back();
      }
    }

    struct Guard
    {
      size_t level;
      size_t marker;
      LowerContext *ctx;

      Guard(LowerContext *ctx)
        : ctx(ctx)
      {
        level = ctx->stack.size();
        marker = ctx->barriers.size();
      }

      ~Guard()
      {
        ctx->barriers.resize(marker - 1);
        ctx->stack.resize(level - 1);
      }
    };

    Guard push_scope(Stmt *owner, std::vector<std::pair<Decl*, Type*>> typeargs)
    {
      stack.emplace_back(owner, std::move(typeargs));

      return Guard(this);
    }

    Type *voidtype;
    Type *booltype;
    Type *chartype;
    Type *isizetype;
    Type *usizetype;
    Type *intliteraltype;
    Type *floatliteraltype;
    Type *stringliteraltype;
    Type *declidliteraltype;
    Type *typeidliteraltype;
    Type *ptrliteraltype;

    vector<Scope> stack;

    Scope labelscope;

    VarDecl *nrvo = nullptr;
    bool is_expression = false;
    size_t pack_expansion = size_t(-1);

    ModuleDecl *module;
    TranslationUnitDecl *translationunit;

    SourceLocation site;
    SourceLocation site_override{ -1, -1 };

    TypeTable &typetable;

    Diag &outdiag;

    LowerContext(TypeTable &typetable, Diag &diag)
      : diag(diag.leader()),
        typetable(typetable),
        outdiag(diag)
    {
      errorarg = 0;
      unreachable = Unreachable::No;
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
      declidliteraltype = type(Builtin::Type_DeclidLiteral);
      typeidliteraltype = type(Builtin::Type_TypeidLiteral);
      ptrliteraltype = type(Builtin::Type_PtrLiteral);

      currentblockid = 0;
      currentblock.terminator.kind = MIR::Terminator::Return;
    }

    ~LowerContext()
    {
      outdiag << diag;
    }
  };

  struct Cache
  {
    struct entry
    {
      MIR mir;
      Diag diag;
    };

    static entry const *lookup(FnSig const &fx)
    {
      auto j = cache.find(fx);

      if (j != cache.end())
        return &j->second;

      return nullptr;
    }

    static bool begin(FnSig const &fx)
    {
      return inflight.emplace(fx, true).second;
    }

    static MIR const &commit(FnSig const &fx, MIR &&mir, Diag const &diag)
    {
      return cache.emplace(fx, entry{ std::move(mir), diag }).first->second.mir;
    }

    static inline std::unordered_map<FnSig, entry> cache;
    static inline std::unordered_map<FnSig, bool> inflight;
  };

  const long IllSpecified = 0x40000000;
  const long WrongArgCount = 0x01000000;
  const long WrongParmCount = 0x02000000;
  const long MatchExprFailed = 0x03000000;
  const long WhereExprFailed = 0x04000000;
  const long ResolveUsings = 0x10000000;

  Type *resolve_defn(LowerContext &ctx, Type *type);
  Type *resolve_type(LowerContext &ctx, Scope scope, Decl *decl);
  Type *resolve_type(LowerContext &ctx, Scope const &scope, Type *type);
  Type *resolve_type(LowerContext &ctx, Scope const &scope, Type *enumm, EnumConstantDecl *constant);
  Type *resolve_type(LowerContext &ctx, Scope const &scope, TypeOfDecl *typedecl);
  Type *resolve_type_as_value(LowerContext &ctx, Scope const &scope, ParmVarDecl *parm);
  Type *resolve_type_as_reference(LowerContext &ctx, Scope const &scope, ParmVarDecl *parm);
  MIR::Local find_type(LowerContext &ctx, vector<Scope> &stack, Expr *expr);
  MIR::Local find_returntype(LowerContext &ctx, FnSig const &fx);
  FnSig find_refn(LowerContext &ctx, Scope const &fx, ParmVarDecl *parm, MIR::Local const &rhs);
  bool deduce_type(LowerContext &ctx, Scope const &scope, Scope &fx, Type *lhs, MIR::Local const &rhs);
  bool deduce_type(LowerContext &ctx, Scope const &scope, Scope &fx, ParmVarDecl *parm, MIR::Local const &rhs);
  bool deduce_calltype(LowerContext &ctx, Scope const &scope, FnSig &fx, FunctionType *lhs, Type *rhs);
  bool deduce_returntype(LowerContext &ctx, Scope const &scope, FunctionDecl *fn, const MIR::Local &lhs, MIR::Local &rhs);
  void commit_type(LowerContext &ctx, MIR::local_t dst, Type *type, long flags);
  bool promote_type(LowerContext &ctx, Type *&lhs, Type *rhs);
  void lower_decl(LowerContext &ctx, ParmVarDecl *parmvar);
  bool lower_expr(LowerContext &ctx, MIR::Fragment &result, Expr *expr);
  bool lower_expr(LowerContext &ctx, MIR::Fragment &result, VarDecl *vardecl, SourceLocation loc);
  void lower_statement(LowerContext &ctx, Stmt *stmt);
  void lower_expression(LowerContext &ctx, Expr *expr);
  void backfill(LowerContext &ctx, MIR &mir);

  //|///////////////////// type_scope ///////////////////////////////////////
  Scope type_scope(LowerContext &ctx, Type const *type)
  {
    switch (type = remove_const_type(type); type->klass())
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
    switch (type = remove_const_type(type); type->klass())
    {
      case Type::Tag:
        return parent_scope(type_scope(ctx, type));

      default:
        break;
    }

    return ctx.translationunit->builtins;
  }

  //|///////////////////// child_scope //////////////////////////////////////
  Scope child_scope(LowerContext &ctx, Scope const &parent, Decl *decl, vector<Decl*> const &declargs, size_t &k, vector<MIR::Local> const &args, map<Ident*, MIR::Local> const &namedargs = {})
  {
    Scope sx(decl, parent.typeargs);

    for (size_t i = 0; i < declargs.size(); ++i)
    {
      auto arg = decl_cast<TypeArgDecl>(declargs[i]);

      if (arg->flags & TypeArgDecl::Pack)
      {
        vector<Type*> defns;
        vector<Type*> fields;

        for ( ; k < args.size(); ++k)
        {
          defns.push_back(args[k].defn);
          fields.push_back(args[k].type);
        }

        sx.set_type(arg, ctx.typetable.find_or_create<TupleType>(std::move(defns), std::move(fields)));
      }

      else if (arg->flags & TypeArgDecl::SplitFn)
      {
        i += 1;

        if (k < args.size() && is_function_type(args[k].type))
        {
          sx.set_type(arg, type_cast<FunctionType>(args[k].type)->returntype);
          sx.set_type(decl_cast<TypeArgDecl>(declargs[i]), type_cast<FunctionType>(args[k].type)->paramtuple);

          k += 1;
        }
      }

      else if (arg->flags & TypeArgDecl::SplitArray)
      {
        i += 1;

        if (k < args.size() && is_array_type(args[k].type))
        {
          sx.set_type(arg, type_cast<ArrayType>(args[k].type)->type);
          sx.set_type(decl_cast<TypeArgDecl>(declargs[i]), type_cast<ArrayType>(args[k].type)->size);

          k += 1;
        }
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
      }

      else
        k |= IllSpecified;
    }

    return sx;
  }

  template<typename T>
  Scope child_scope(LowerContext &ctx, Scope const &parent, T *decl, size_t &k, vector<MIR::Local> const &args, map<Ident*, MIR::Local> const &namedargs = {})
  {
    return child_scope(ctx, parent, decl, decl->args, k, args, namedargs);
  }

  //|///////////////////// inner_scope //////////////////////////////////////
  Scope inner_scope(LowerContext &ctx, Scope const &scope, Decl *decl, size_t &k, vector<MIR::Local> const &args, map<Ident*, MIR::Local> const &namedargs)
  {
    switch (decl->kind())
    {
      case Decl::Module:
        return Scope(decl);

      case Decl::Import:
        return Scope(decl_cast<ImportDecl>(decl)->decl);

      case Decl::Struct:
      case Decl::Union:
      case Decl::VTable:
      case Decl::Concept:
      case Decl::Enum:
        return child_scope(ctx, scope, decl_cast<TagDecl>(decl), k, args, namedargs);

      case Decl::Function:
        return child_scope(ctx, scope, decl_cast<FunctionDecl>(decl), k, args, namedargs);

      case Decl::TypeAlias:
        if (auto typescope = child_scope(ctx, scope, decl_cast<TypeAliasDecl>(decl), k, args, namedargs))
        {
          auto type = resolve_type(ctx, typescope, decl_cast<TypeAliasDecl>(decl)->type);

          if (is_typearg_type(type) && type_cast<TypeArgType>(type)->koncept)
            return Scope(type_cast<TypeArgType>(type)->koncept, type_cast<TypeArgType>(type)->args);

          if (is_tag_type(type))
            return Scope(type_cast<TagType>(type)->decl, type_cast<TagType>(type)->args);

          return typescope;
        }
        break;

      case Decl::TypeArg:
        if (auto j = scope.find_type(decl); j != scope.typeargs.end() && is_tag_type(remove_const_type(j->second)))
          return type_scope(ctx, j->second);
        break;

      default:
        assert(ctx.diag.has_errored());
    }

    return child_scope(scope, decl);
  }

  //|///////////////////// fill_defaultargs /////////////////////////////////
  void fill_defaultargs(LowerContext &ctx, Decl *decl, std::vector<std::pair<Decl*, Type*>> &typeargs)
  {
    for (auto sx = decl; sx; sx = parent_decl(sx))
    {
      vector<Decl*> *declargs = nullptr;

      switch (sx->kind())
      {
        case Decl::Function:
          declargs = &decl_cast<FunctionDecl>(sx)->args;
          break;

        case Decl::Struct:
        case Decl::Union:
        case Decl::VTable:
        case Decl::Concept:
        case Decl::Lambda:
        case Decl::Enum:
          declargs = &decl_cast<TagDecl>(sx)->args;
          break;

        default:
          break;
      }

      if (declargs)
      {
        for (auto &arg : *declargs)
        {
          if (decl_cast<TypeArgDecl>(arg)->defult)
          {
            auto j = lower_bound(typeargs.begin(), typeargs.end(), arg, [](auto &lhs, auto &rhs) { return lhs.first < rhs; });

            if (j == typeargs.end() || j->first != arg)
            {
              typeargs.emplace(j, arg, remove_const_type(resolve_type(ctx, Scope(decl, typeargs), decl_cast<TypeArgDecl>(arg)->defult)));
            }
          }
        }
      }
    }
  }

  //|///////////////////// base_scope ///////////////////////////////////////
  Scope base_scope(LowerContext &ctx, Scope const &scope, long flags = 0)
  {
    Scope sx;

    if (is_tag_scope(scope))
    {
      if (auto tagdecl = decl_cast<TagDecl>(get<Decl*>(scope.owner)); tagdecl->basetype && (!(flags & QueryFlags::Public) || (tagdecl->flags & TagDecl::PublicBase)))
      {
        return type_scope(ctx, resolve_type(ctx, scope, tagdecl->basetype));
      }
    }

    return sx;
  }

  //|///////////////////// eval /////////////////////////////////////////////
  int eval(LowerContext &ctx, Scope const &scope, unordered_map<Decl*, MIR::Fragment> const &symbols, Expr *expr)
  {
    if (ctx.suppressed.size() != 0)
      return -1;

    auto result = evaluate(scope, expr, symbols, ctx.typetable, ctx.diag, expr->loc());

    if (result.type != ctx.booltype)
    {
      if (result.type == ctx.intliteraltype)
      {
        if (expr_cast<IntLiteralExpr>(result.value)->value().value == 0)
          return false;

        if (expr_cast<IntLiteralExpr>(result.value)->value().value == 1)
          return true;
      }

      if (result.type == ctx.declidliteraltype)
      {
        return expr_cast<IntLiteralExpr>(result.value)->value().value != 0;
      }

      if (result.type == ctx.typeidliteraltype)
      {
        return expr_cast<IntLiteralExpr>(result.value)->value().value != 0;
      }

      ctx.diag.error("non bool condition", scope, expr->loc());

      return -1;
    }

    return expr_cast<BoolLiteralExpr>(result.value)->value();
  }

  int eval(LowerContext &ctx, Scope const &scope, Expr *expr)
  {
    return eval(ctx, scope, {}, expr);
  }

  //|///////////////////// is_throws ////////////////////////////////////////
  bool is_throws(LowerContext &ctx, FnSig const &fx, vector<MIR::Fragment> const &parms, map<Ident*, MIR::Fragment> const &namedparms, Type **type = nullptr)
  {
    if (fx.fn->throws)
    {
      auto throwtype = resolve_type(ctx, Scope(fx.fn, fx.typeargs), fx.fn->throws);

      if (throwtype != ctx.voidtype)
      {
        if (type)
          *type = throwtype;

        return true;
      }
    }

    if ((fx.fn->flags & FunctionDecl::Builtin) && fx.fn->builtin == Builtin::CallOp && is_function_type(parms[0].type.type) && type_cast<FunctionType>(parms[0].type.type)->throwtype != ctx.voidtype)
    {
      if (type)
        *type = type_cast<FunctionType>(parms[0].type.type)->throwtype;

      return true;
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

  //|///////////////////// is_impl_type /////////////////////////////////////
  bool is_impl_type(LowerContext &ctx, Type *lhs, MIR::Local const &rhs)
  {
    return (rhs.flags & MIR::Local::ImplRef);
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
    if (is_typearg_type(lhs))
      return false;

    if (lhs == ctx.ptrliteraltype)
      return false;

    if (rhs == ctx.ptrliteraltype && is_pointer_type(lhs))
      return true;

    if (is_pointer_type(rhs) || is_reference_type(rhs) || is_struct_type(rhs) || is_vtable_type(rhs))
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
  bool is_int_literal(LowerContext &ctx, MIR::Fragment const &value)
  {
    return is_constant(ctx, value) && get_if<IntLiteralExpr*>(&value.value.get<MIR::RValue::Constant>());
  }

  //|///////////////////// is_call_inhibited ////////////////////////////////
  bool is_call_inhibited(LowerContext &ctx, MIR::Fragment const &value)
  {
    return get<0>(value.value.get<MIR::RValue::Call>()).fn->flags & FunctionDecl::Inhibited;
  }

  //|///////////////////// is_call_nodiscard ////////////////////////////////
  bool is_call_nodiscard(LowerContext &ctx, MIR::Fragment const &value)
  {
    return get<0>(value.value.get<MIR::RValue::Call>()).fn->flags & FunctionDecl::NoDiscard;
  }

  //|///////////////////// is_return_reference //////////////////////////////
  bool is_return_reference(LowerContext &ctx, Expr *expr)
  {
    if (expr->kind() == Expr::UnaryOp)
    {
      return expr_cast<UnaryOpExpr>(expr)->op() == UnaryOpExpr::Ref;
    }

    if (expr->kind() == Expr::TernaryOp)
    {
      auto ternaryop = expr_cast<TernaryOpExpr>(expr);
      auto lhs = ternaryop->lhs->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(ternaryop->lhs)->op() == UnaryOpExpr::Ref;
      auto rhs = ternaryop->rhs->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(ternaryop->rhs)->op() == UnaryOpExpr::Ref;

      return lhs && rhs;
    }

    return false;
  }

  //|///////////////////// resolve_defn /////////////////////////////////////
  Type *resolve_defn(LowerContext &ctx, Type *type)
  {
    auto defn = ctx.typetable.var_defn;

    for (type = remove_const_type(type); is_reference_type(type); type = remove_const_type(remove_reference_type(type)))
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
    }

    if (local.flags & MIR::Local::Reference)
    {
      if ((local.flags & (MIR::Local::RValue | MIR::Local::Const)) == MIR::Local::RValue)
        local.type = ctx.typetable.find_or_create<QualArgType>(QualArgType::RValue, local.type);

      local.type = ctx.typetable.find_or_create<ReferenceType>(local.type);
    }

    local.flags &= ~MIR::Local::Reference;
    local.flags &= ~MIR::Local::LValue;
    local.flags &= ~MIR::Local::Const;

    return local;
  }

  //|///////////////////// resolve_as_value /////////////////////////////////
  MIR::Local resolve_as_value(LowerContext &ctx, MIR::Local local, vector<MIR::RValue::Field> const &fields)
  {
    local = resolve_as_value(ctx, local);

    for (auto &field : fields)
    {
      if (field.op == MIR::RValue::Val)
        local.type = remove_reference_type(local.type);

      local.type = remove_const_type(local.type);

      switch (local.type->klass())
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
    assert(is_reference_type(local.type));
    assert(~local.flags & MIR::Local::Reference);

    local.type = remove_reference_type(local.type);
    local.flags &= ~MIR::Local::RValue;
    local.flags &= ~MIR::Local::XValue;
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

  //|///////////////////// resolve_run //////////////////////////////////////
  Expr *resolve_run(LowerContext &ctx, Scope const &scope, RunDecl *rundecl)
  {
    auto fx = FnSig(decl_cast<FunctionDecl>(rundecl->fn), scope.typeargs);

    auto j = ctx.typetable.injections.find(fx);

    if (j == ctx.typetable.injections.end())
    {
      j = ctx.typetable.injections.emplace(fx, nullptr).first;

      if (auto result = evaluate(scope, fx, ctx.voidtype, {}, ctx.typetable, ctx.diag, fx.fn->loc()); result.value)
        j->second = result.value;
    }

    return j->second;
  }

  //|///////////////////// find_decls ///////////////////////////////////////

  void find_decls(LowerContext &ctx, Scope const &scope, vector<Decl*> const &decls, vector<Decl*> &results)
  {
    for (auto &decl : decls)
    {
      if (decl->kind() == Decl::If)
      {
        if (eval(ctx, scope, decl_cast<IfDecl>(decl)->cond) == 1)
        {
          find_decls(ctx, scope, decl_cast<IfDecl>(decl)->decls, results);
        }
        else if (auto elseif = decl_cast<IfDecl>(decl)->elseif)
        {
          find_decls(ctx, scope, vector<Decl*>{ elseif }, results);
        }

        continue;
      }

      if (decl->kind() == Decl::Run)
      {
        if (auto result = resolve_run(ctx, scope, decl_cast<RunDecl>(decl)); result && result->kind() == Expr::Fragment)
        {
          find_decls(ctx, scope, expr_cast<FragmentExpr>(result)->decls, results);
        }

        continue;
      }

      results.push_back(decl);
    }
  }

  void find_decls(LowerContext &ctx, Scope const &scope, Ident *name, long queryflags, vector<Decl*> &results)
  {
    if (is_module_scope(scope))
    {
      auto module = decl_cast<ModuleDecl>(get<Decl*>(scope.owner));

      if (module->flags & ModuleDecl::Indexed)
      {
        if (auto j = module->index.find(name); j != module->index.end())
          for (auto decl : j->second)
            find_decl(decl, name, queryflags, results);

        if (auto j = module->index.find(nullptr); j != module->index.end())
          for (auto decl : j->second)
            find_decl(decl, name, queryflags, results);

        return;
      }
    }

    if (is_tag_scope(scope))
    {
      auto tagdecl = decl_cast<TagDecl>(get<Decl*>(scope.owner));

      if (auto type = ctx.typetable.find<TagType>(tagdecl, scope.typeargs))
      {
        for (auto &decl : tagdecl->args)
          find_decl(decl, name, queryflags, results);

        for (auto &decl : type_cast<TagType>(type)->decls)
          find_decl(decl, name, queryflags, results);

        return;
      }
    }

    find_decls(scope, name, queryflags, results);

    for (size_t i = 0; i < results.size(); ++i)
    {
      auto decl = results[i];

      if (decl->kind() == Decl::If)
      {
        auto sx = scope;
        auto ifd = decl_cast<IfDecl>(decl);

        if (scope.goalpost == decl)
          break;

        sx.goalpost = ifd->root;

        if ((ifd->flags & IfDecl::ResolvedTrue) || (!(ifd->flags & IfDecl::ResolvedFalse) && eval(ctx, sx, ifd->cond) == 1))
          find_decls(decl, name, queryflags, results);
        else
          if (auto elseif = ifd->elseif)
            results.push_back(elseif);
      }

      if (decl->kind() == Decl::Run)
      {
        if (auto result = resolve_run(ctx, scope, decl_cast<RunDecl>(decl)); result && result->kind() == Expr::Fragment)
        {
          if (is_tag_scope(scope) && ctx.typetable.find<TagType>(decl_cast<TagDecl>(get<Decl*>(scope.owner)), scope.typeargs))
            ctx.diag.error("injecting into closed scope", decl, decl->loc());

          for (auto &decl : expr_cast<FragmentExpr>(result)->decls)
            find_decl(decl, name, queryflags, results);
        }
      }
    }

    results.erase(remove_if(results.begin(), results.end(), [&](auto &decl) {
      return decl->kind() == Decl::If || decl->kind() == Decl::Run;
    }), results.end());
  }

  void find_decls(LowerContext &ctx, Scope const &scope, Ident *name, long queryflags, long resolveflags, vector<Decl*> &results)
  {
    find_decls(ctx, scope, name, queryflags, results);

    for (size_t i = 0; i < results.size(); ++i)
    {
      auto decl = results[i];

      if (decl->kind() == Decl::Using && (resolveflags & ResolveUsings))
      {
        auto n = results.size();

        switch (auto usein = decl_cast<UsingDecl>(decl); usein->decl->kind())
        {
          case Decl::Module:
            find_decls(ctx, usein->decl, name, queryflags | QueryFlags::Public, results);
            break;

          case Decl::Struct:
          case Decl::Union:
          case Decl::VTable:
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

          case Decl::TypeOf:
            break;

          default:
            assert(false);
        }

        results.erase(remove_if(results.begin() + n, results.end(), [&](auto &decl) {
          return count(results.begin(), results.begin() + n, decl) != 0;
        }), results.end());
      }
    }

    for (size_t i = 0; i < results.size(); ++i)
    {
      if (results[i]->kind() == Decl::Import)
      {
        results.erase(remove_if(results.begin() + i + 1, results.end(), [&](auto &decl) {
          return decl->kind() == Decl::Import;
        }), results.end());
      }
    }

    if (resolveflags & ResolveUsings)
    {
      results.erase(remove_if(results.begin(), results.end(), [&](auto &decl) {
        return decl->kind() == Decl::Using;
      }), results.end());
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

    for (auto &arg : args)
    {
      if (arg->klass() == Type::Unpack)
      {
        auto type = resolve_type(ctx, scope, type_cast<UnpackType>(arg)->type);

        if (is_compound_type(type))
        {
          auto pack = type_cast<CompoundType>(type);

          for (size_t index = 0; index < pack->fields.size(); ++index)
            typeargs.push_back(MIR::Local(pack->fields[index]));
        }

        if (is_array_type(type))
        {
          auto pack = type_cast<ArrayType>(type);

          for (size_t index = 0; index < array_len(pack); ++index)
            typeargs.push_back(MIR::Local(pack->type));
        }

        continue;
      }

      typeargs.push_back(MIR::Local(resolve_type(ctx, scope, arg), resolve_defn(ctx, arg)));
    }

    return typeargs;
  }

  map<Ident*, MIR::Local> typeargs(LowerContext &ctx, Scope const &scope, map<Ident*, Type*> const &namedargs)
  {
    map<Ident*, MIR::Local> typeargs;

    for (auto &[name, arg] : namedargs)
    {
      typeargs.emplace(name, MIR::Local(resolve_type(ctx, scope, arg), resolve_defn(ctx, arg)));
    }

    return typeargs;
  }

  Scoped find_scoped(LowerContext &ctx, vector<Scope> const &stack, DeclScopedDecl *scoped, long &querymask)
  {
    vector<Decl*> decls;

    Scope declscope = ctx.translationunit;

    if (scoped->decls[0]->kind() == Decl::TypeOf)
    {
      if (auto type = resolve_type(ctx, stack.back(), decl_cast<TypeOfDecl>(scoped->decls[0])); is_tag_type(remove_const_type(type)))
        declscope = type_scope(ctx, type);
      else
        declscope = child_scope(stack.back(), scoped->decls[0]);

      if (get_module(declscope) != ctx.module)
        querymask |= QueryFlags::Public;
    }

    if (scoped->decls[0]->kind() == Decl::TypeName)
    {
      if (auto type = resolve_type(ctx, stack.back(), decl_cast<TypeNameDecl>(scoped->decls[0])->type); is_tag_type(remove_const_type(type)))
        declscope = type_scope(ctx, type);
      else
        declscope = child_scope(stack.back(), scoped->decls[0]);

      if (get_module(declscope) != ctx.module)
        querymask |= QueryFlags::Public;
    }

    if (scoped->decls[0]->kind() == Decl::DeclRef && decl_cast<DeclRefDecl>(scoped->decls[0])->name != Ident::op_scope)
    {
      auto declref = decl_cast<DeclRefDecl>(scoped->decls[0]);

      auto args = typeargs(ctx, stack.back(), declref->args);
      auto namedargs = typeargs(ctx, stack.back(), declref->namedargs);

      for (auto sx = stack.rbegin(); sx != stack.rend(); ++sx)
      {
        find_decls(ctx, *sx, declref->name, QueryFlags::Imports | QueryFlags::Types | QueryFlags::Concepts | QueryFlags::Usings | querymask, ResolveUsings, decls);

        if (decls.empty())
          continue;

        size_t k = 0;

        if (decls[0]->kind() == Decl::TypeAlias && (decls[0]->flags & TypeAliasDecl::Implicit) && !declref->argless)
          decls[0] = get<Decl*>(decls[0]->owner);

        declscope = inner_scope(ctx, outer_scope(*sx, decls[0]), decls[0], k, args, namedargs);

        if ((k & ~IllSpecified) != args.size() + namedargs.size())
          return nullptr;

        break;
      }

      if (decls.size() != 1)
        return nullptr;

      if (decls[0]->kind() == Decl::Import || decls[0]->kind() == Decl::Module)
        querymask |= QueryFlags::Public;

      decls.clear();
    }

    for (size_t i = 1; i + 1 < scoped->decls.size(); ++i)
    {
      auto declref = decl_cast<DeclRefDecl>(scoped->decls[i]);

      auto args = typeargs(ctx, stack.back(), declref->args);
      auto namedargs = typeargs(ctx, stack.back(), declref->namedargs);

      find_decls(ctx, declscope, declref->name, QueryFlags::Modules | QueryFlags::Imports | QueryFlags::Types | QueryFlags::Concepts | QueryFlags::Usings | querymask, ResolveUsings, decls);

      if (decls.size() != 1)
        return nullptr;

      size_t k = 0;

      declscope = inner_scope(ctx, outer_scope(declscope, decls[0]), decls[0], k, args, namedargs);

      if ((k & ~IllSpecified) != args.size() + namedargs.size())
        return nullptr;

      if (decls[0]->kind() == Decl::Import || decls[0]->kind() == Decl::Module)
        querymask |= QueryFlags::Public;

      decls.clear();
    }

    return Scoped{ decl_cast<DeclRefDecl>(scoped->decls.back()), std::move(declscope) };
  }

  //|///////////////////// find_vardecl /////////////////////////////////////

  VarDecl *find_vardecl(LowerContext &ctx, vector<Scope> const &stack, Ident *name)
  {
    vector<Decl*> decls;
    long queryflags = QueryFlags::Parameters | QueryFlags::Variables | QueryFlags::Fields;

    for (auto sx = stack.rbegin(); sx != stack.rend(); ++sx)
    {
      find_decls(ctx, *sx, name, queryflags, decls);

      if (decls.size() != 0 && sx->goalpost == decls[0])
        decls.clear();

      if (decls.empty())
      {
        if (is_fn_scope(*sx))
        {
          auto fn = decl_cast<FunctionDecl>(get<Decl*>(sx->owner));

          if (!(fn->flags & (FunctionDecl::Constructor | FunctionDecl::Destructor)) && (fn->flags & FunctionDecl::DeclType) != FunctionDecl::LambdaDecl)
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

  size_t find_index(LowerContext &ctx, vector<Scope> const &stack, std::vector<Decl*> const &decls, Ident *ident)
  {
    if (ident->kind() == Ident::Index)
    {
      return static_cast<IndexIdent*>(ident)->value();
    }

    if (ident->kind() == Ident::Hash)
    {
      EvalResult result = {};

      auto id = static_cast<HashIdent*>(ident)->value();

      if (auto vardecl = find_vardecl(ctx, stack, id); vardecl && (vardecl->flags & VarDecl::Literal))
      {
        MIR::Fragment literal;

        if (!lower_expr(ctx, literal, vardecl, vardecl->loc()))
          return size_t(-1);

        result.type = literal.type.type;
        result.value = std::visit([&](auto &v) -> Expr * { return v; }, literal.value.get<MIR::RValue::Constant>());
      }

      if (!result)
      {
        DeclRefDecl decl(id, {});
        DeclRefExpr expr(&decl, decl.loc());

        result = evaluate(stack.back(), &expr, ctx.symbols, ctx.typetable, ctx.diag, expr.loc());
      }

      if (result.type && is_int_type(result.type))
      {
        return expr_cast<IntLiteralExpr>(result.value)->value().value;
      }

      if (result.type && is_string_type(result.type))
      {
        for (size_t index = 0; index < decls.size(); ++index)
        {
          if (decl_name(decls[index]) == expr_cast<StringLiteralExpr>(result.value)->value())
            return index;
        }
      }

      if (result.type && is_declid_type(result.type))
      {
        auto declid = reinterpret_cast<Decl*>(expr_cast<IntLiteralExpr>(result.value)->value().value);

        if (auto j = std::find(decls.begin(), decls.end(), declid); j != decls.end())
          return j - decls.begin();
      }
    }

    if (ident->kind() == Ident::String)
    {
      for (size_t index = 0; index < decls.size(); ++index)
      {
        if (decl_name(decls[index]) == ident)
          return index;
      }
    }

    return size_t(-1);
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

  Field find_field(LowerContext &ctx, ArrayType *type, size_t index)
  {
    Field field;

    if (index < array_len(type))
    {
      field.index = index;
      field.type = type->type;
      field.defn = type->type;
      field.flags = 0;

      if (is_const_type(field.type) || is_qualarg_type(field.type))
      {
        if (is_const_type(field.type) || type_cast<QualArgType>(field.type)->qualifiers & QualArgType::Const)
          field.flags |= MIR::Local::Const;

        field.type = remove_const_type(field.type);
      }
    }

    return field;
  }

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
          field.defn = type_cast<TupleType>(type)->defns[index];
          break;

        case Type::Tag:
          field.defn = decl_cast<FieldVarDecl>(type_cast<TagType>(type)->fieldvars[index])->type;
          field.flags = decl_cast<FieldVarDecl>(type_cast<TagType>(type)->fieldvars[index])->flags;
          break;

        default:
          assert(false);
      }

      if (is_const_type(field.type) || is_qualarg_type(field.type))
      {
        if (is_const_type(field.type) || type_cast<QualArgType>(field.type)->qualifiers & QualArgType::Const)
          field.flags |= MIR::Local::Const;

        field.type = remove_const_type(field.type);
      }
    }

    return field;
  }

  Field find_field(LowerContext &ctx, vector<Scope> const &stack, Type *type, Ident *ident)
  {
    Field field;

    switch (type->klass())
    {
      case Type::Array:

        if (auto index = find_index(ctx, stack, {}, ident); index != size_t(-1))
        {
          field = find_field(ctx, type_cast<ArrayType>(type), index);
        }

        break;

      case Type::Tuple:

        if (auto index = find_index(ctx, stack, {}, ident); index != size_t(-1))
        {
          field = find_field(ctx, type_cast<CompoundType>(type), index);
        }

        break;

      case Type::Tag:

        if (auto index = find_index(ctx, stack, type_cast<TagType>(type)->fieldvars, ident); index != size_t(-1))
        {
          field = find_field(ctx, type_cast<TagType>(type), index);
        }

        break;

      default:
        break;
    }

    return field;
  }

  //|///////////////////// synthesise_union_enum ////////////////////////////
  void synthesise_union_enum(LowerContext &ctx, Scope const &scope, UnionDecl *unnion, vector<Decl*> &decls)
  {
    auto kindtype = ctx.mir.make_decl<EnumDecl>(unnion->loc());

    kindtype->name = Ident::type_enum;
    kindtype->flags |= EnumDecl::Public;
    kindtype->owner = unnion;

    auto kindtypefield = ctx.mir.make_decl<FieldVarDecl>(unnion->loc());

    kindtypefield->name = Ident::type_enum;
    kindtypefield->type = type(Builtin::Type_ISize);
    kindtypefield->owner = kindtype;

    kindtype->decls.push_back(kindtypefield);

    kindtype->decls.push_back(ctx.mir.make_decl<EnumConstantDecl>(unnion->loc()));

    for (auto &decl : decls)
    {
      if (decl->kind() != Decl::FieldVar)
        continue;

      auto kindconstant = ctx.mir.make_decl<EnumConstantDecl>(decl_cast<FieldVarDecl>(decl)->name, unnion->loc());

      if (decl->flags & VarDecl::Public)
        kindconstant->flags |= VarDecl::Public;

      kindtype->decls.push_back(kindconstant);
    }

    for (auto &decl : kindtype->decls)
    {
      decl->owner = kindtype;
    }

    decls.insert(decls.begin(), kindtype);

    auto kindfield = ctx.mir.make_decl<FieldVarDecl>(unnion->loc());

    kindfield->name = Ident::kw_kind;
    kindfield->flags |= VarDecl::Public;
    kindfield->flags |= VarDecl::Const;
    kindfield->type = resolve_type(ctx, scope, kindtype);
    kindfield->owner = unnion;

    decls.insert(decls.begin(), kindfield);
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

  Type *resolve_type(LowerContext &ctx, Scope const &scope, SliceType *slicetype)
  {
    return ctx.typetable.find_or_create<SliceType>(resolve_type(ctx, scope, slicetype->type));
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

    for (auto &field : tupletype->fields)
    {
      if (field->klass() == Type::Unpack)
      {
        auto pack = resolve_type(ctx, scope, type_cast<UnpackType>(field)->type);

        if (is_reference_type(type_cast<UnpackType>(field)->type))
        {
          pack = remove_reference_type(pack);

          if (is_const_reference(type_cast<UnpackType>(field)->type))
            pack = remove_const_type(pack);
        }

        if (is_compound_type(pack))
        {
          for (auto element : type_cast<CompoundType>(pack)->fields)
          {
            if (is_reference_type(type_cast<UnpackType>(field)->type))
            {
              if (is_const_reference(type_cast<UnpackType>(field)->type))
                element = ctx.typetable.find_or_create<ConstType>(element);

              element = ctx.typetable.find_or_create<ReferenceType>(element);
            }

            defns.push_back(resolve_defn(ctx, type_cast<UnpackType>(field)->type));
            fields.push_back(element);
          }
        }

        if (is_array_type(pack))
        {
          auto element = type_cast<ArrayType>(pack)->type;

          if (is_reference_type(type_cast<UnpackType>(field)->type))
          {
            if (is_const_reference(type_cast<UnpackType>(field)->type))
              element = ctx.typetable.find_or_create<ConstType>(element);

            element = ctx.typetable.find_or_create<ReferenceType>(element);
          }

          for (size_t index = 0; index < array_len(type_cast<ArrayType>(pack)); ++index)
          {
            defns.push_back(resolve_defn(ctx, type_cast<UnpackType>(field)->type));
            fields.push_back(element);
          }
        }

        continue;
      }

      defns.push_back(resolve_defn(ctx, field));
      fields.push_back(resolve_type(ctx, scope, field));
    }

    return ctx.typetable.find_or_create<TupleType>(std::move(defns), std::move(fields));
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TagDecl *tagdecl)
  {
    if (auto type = ctx.typetable.find<TagType>(tagdecl, scope.typeargs))
      return type;

    auto rr = recursion_counter<__COUNTER__>();

    if (rr.count > 256)
    {
      ctx.diag.error("unable to resolve type", tagdecl, tagdecl->loc());

      throw runtime_error("recursion limit reached");
    }

    vector<Decl*> decls;

    find_decls(ctx, scope, tagdecl->decls, decls);

    switch (tagdecl->kind())
    {
      case Decl::Union:
        synthesise_union_enum(ctx, scope, decl_cast<UnionDecl>(tagdecl), decls);
        break;

      default:
        break;
    }

    auto type = ctx.typetable.create<TagType>(tagdecl, scope.typeargs);

    type->resolve(std::move(decls));

    vector<Type*> fields;

    for (auto &decl : type->decls)
    {
      if (decl->kind() != Decl::FieldVar)
        continue;

      fields.push_back(resolve_type(ctx, scope, decl_cast<FieldVarDecl>(decl)->type));
    }

    type->resolve(std::move(fields));

    return type;
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TagType *tagtype)
  {
    Scope tx(tagtype->decl, tagtype->args);

    for (auto &[decl, arg] : tx.typeargs)
    {
      arg = resolve_type(ctx, scope, arg);

      if (is_unresolved_type(arg))
        ctx.diag.error("unresolved type argument", decl, decl->loc());
    }

    for (auto sx = tagtype->decl; sx; sx = parent_decl(sx))
    {
      if (sx->kind() == Decl::Function)
      {
        for (auto parm : decl_cast<FunctionDecl>(sx)->parms)
        {
          if (auto j = scope.find_type(parm); j != scope.typeargs.end())
            tx.set_type(parm, j->second);
        }
      }
    }

    return resolve_type(ctx, tx, decl_cast<TagDecl>(tagtype->decl));
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TypeArgType *argtype)
  {
    if (auto j = scope.find_type(argtype->decl); j != scope.typeargs.end())
      return j->second;

    if (argtype->decl->kind() == Decl::TypeArg)
    {
      if (auto argdecl = decl_cast<TypeArgDecl>(argtype->decl); argdecl->defult)
        return remove_const_type(resolve_type(ctx, scope, argdecl->defult));
    }

    if (argtype->args.size() != 0)
    {
      auto type = ctx.typetable.make_type<TypeArgType>(argtype->decl, argtype->koncept, argtype->args);

      for (auto &[decl, arg] : type->args)
      {
        arg = resolve_type(ctx, scope, arg);
      }

      return type;
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

  Type *resolve_type(LowerContext &ctx, Scope const &scope, Type *enumm, EnumConstantDecl *constant)
  {
    assert(is_enum_type(enumm));

    if (auto type = ctx.typetable.find<ConstantType>(constant, enumm))
      return type;

    size_t value = 0;
    Expr *lastknown = nullptr;

    for (auto &decl : type_cast<TagType>(enumm)->decls)
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
              expr = evaluate(scope, expr, {}, ctx.typetable, ctx.diag, constant->loc()).value;

              if (expr && expr->kind() == Expr::CharLiteral)
              {
                expr = ctx.mir.make_expr<IntLiteralExpr>(expr_cast<CharLiteralExpr>(expr)->value(), constant->loc());
              }

              if (!expr || expr->kind() != Expr::IntLiteral)
              {
                ctx.diag.error("invalid enum value", scope, decl->loc());
                break;
              }
            }

            if (value != 0)
              expr = ctx.mir.make_expr<IntLiteralExpr>(expr_cast<IntLiteralExpr>(expr)->value() + Numeric::int_literal(value), constant->loc());
          }
          else
          {
            expr = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(value), constant->loc());
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

    switch (constant->decl->kind())
    {
      case Decl::EnumConstant:
        return resolve_type(ctx, type_scope(ctx, tagtype), tagtype, decl_cast<EnumConstantDecl>(constant->decl));

      default:
        assert(false);
    }

    throw logic_error("unresolved constant");
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, FunctionType *fntype)
  {
    auto returntype = resolve_type(ctx, scope, fntype->returntype);
    auto paramtuple = resolve_type(ctx, scope, fntype->paramtuple);
    auto throwtype = resolve_type(ctx, scope, fntype->throwtype);

    return ctx.typetable.find_or_create<FunctionType>(returntype, paramtuple, throwtype);
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

    return type;
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, FunctionDecl *fn)
  {
    vector<Type*> defns;
    vector<Type*> parms;

    for (auto &parm : fn->parms)
    {
      if (parm->flags & ParmVarDecl::Literal)
        continue;

      defns.push_back(resolve_defn(ctx, decl_cast<ParmVarDecl>(parm)->type));
      parms.push_back(resolve_type_as_value(ctx, scope, decl_cast<ParmVarDecl>(parm)));
    }

    auto returntype = find_returntype(ctx, FnSig(fn, scope.typeargs)).type;
    auto paramtuple = ctx.typetable.find_or_create<TupleType>(std::move(defns), std::move(parms));
    auto throwtype = (fn->throws) ? resolve_type(ctx, scope, fn->throws) : ctx.voidtype;

    return ctx.typetable.find_or_create<FunctionType>(returntype, paramtuple, throwtype);
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TypeOfDecl *typedecl)
  {
    vector<Scope> stack;
    seed_stack(stack, scope);

    if (auto declref = is_declrefdecl_expr(typedecl->expr))
    {
      if (!expr_cast<DeclRefExpr>(typedecl->expr)->base && declref->argless)
      {
        if (declref->name == string_view("__decl__"))
        {
          return ctx.declidliteraltype;
        }

        if (auto vardecl = find_vardecl(ctx, stack, declref->name); vardecl)
        {
          return resolve_deref(ctx, resolve_type(ctx, stack.back(), decl_cast<VarDecl>(vardecl)), vardecl->type);
        }

        if (declref->name == Ident::kw_this)
        {
          for (auto sx = stack.rbegin(); sx != stack.rend(); ++sx)
          {
            if (auto owner = get_if<Decl*>(&sx->owner); owner && *owner && is_tag_decl(*owner))
              return resolve_type(ctx, parent_scope(*sx), *owner);
          }
        }
      }
    }

    if (auto declscoped = is_declscopeddecl_expr(typedecl->expr))
    {
      long queryflags = 0;

      if (Scoped declref = find_scoped(ctx, stack, declscoped, queryflags))
      {
        if (is_type_scope(declref.scope))
        {
          auto type = resolve_type(ctx, declref.scope, get<Decl*>(declref.scope.owner));

          if (is_compound_type(type))
          {
            if (auto field = find_field(ctx, ctx.stack, type, declref.decl->name))
              return resolve_deref(ctx, field.type, field.defn);
          }

          if (is_enum_type(type))
          {
            if (declref.decl->name == Ident::kw_super)
              return type_cast<TagType>(type)->fields[0];
          }
        }
      }
    }

    LowerContext cttx(ctx.typetable, ctx.diag);

    cttx.stack = std::move(stack);
    cttx.translationunit = decl_cast<TranslationUnitDecl>(get<Decl*>(cttx.stack[0].owner));
    cttx.module = decl_cast<ModuleDecl>(get<Decl*>(cttx.stack[1].owner));
    cttx.symbols = ctx.symbols;

    cttx.add_local();
    cttx.errorarg = cttx.add_local();
    cttx.push_barrier();

    for (auto sx = cttx.stack.rbegin(); sx != cttx.stack.rend(); ++sx)
    {
      if (!is_fn_scope(*sx))
        continue;

      auto fn = decl_cast<FunctionDecl>(get<Decl*>(sx->owner));

      if ((fn->flags & FunctionDecl::DeclType) == FunctionDecl::RequiresDecl)
        continue;

      for (auto &parm : FnSig(fn).parameters())
      {
        if (scope.goalpost == parm)
          break;

        cttx.stack.back().goalpost = parm;

        lower_decl(cttx, decl_cast<ParmVarDecl>(parm));
      }

      cttx.stack.back().goalpost = nullptr;

      if (fn == ctx.mir.fx.fn)
      {
        for (auto &[var, arg] : ctx.locals)
        {
          cttx.locals[var] = cttx.mir.add_local(ctx.mir.locals[arg]);
        }
      }

      break;
    }

    MIR::Fragment result;

    if (auto stmt = get_if<Stmt*>(&typedecl->owner); stmt)
      cttx.stack.back().goalpost = *stmt;

    if (lower_expr(cttx, result, typedecl->expr))
    {
      if (result.type.flags & MIR::Local::Const)
        result.type.type = ctx.typetable.find_or_create<ConstType>(result.type.type);

      if ((result.type.flags & (MIR::Local::RValue | MIR::Local::Const)) == MIR::Local::RValue)
        result.type.type = ctx.typetable.find_or_create<QualArgType>(QualArgType::RValue, result.type.type);

      return result.type.type;
    }

    assert(cttx.diag.has_errored());

    return ctx.voidtype;
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TypeRefType *typeref, Scope const &sx, Decl *decl, size_t &k, vector<MIR::Local> const &args, map<Ident*, MIR::Local> const &namedargs)
  {
    switch (decl->kind())
    {
      case Decl::Struct:
      case Decl::Union:
      case Decl::VTable:
      case Decl::Enum:
        return resolve_type(ctx, child_scope(ctx, sx, decl_cast<TagDecl>(decl), k, args, namedargs), decl);

      case Decl::TypeAlias:
        return resolve_type(ctx, child_scope(ctx, sx, decl_cast<TypeAliasDecl>(decl), k, args, namedargs), decl);

      case Decl::EnumConstant:
        return resolve_type(ctx, scope, decl);

      case Decl::Function:
        return resolve_type(ctx, child_scope(ctx, sx, decl_cast<FunctionDecl>(decl), k, args, namedargs), decl);

      case Decl::TypeArg: {
        auto type = ctx.typetable.find_or_create<TypeArgType>(decl, nullptr, {});

        if (auto j = scope.find_type(decl); j != scope.typeargs.end())
          return j->second;

        return type;
      }

      case Decl::Concept: {
        auto type = ctx.typetable.find_or_create<TypeArgType>(typeref->decl, decl, child_scope(ctx, sx, decl_cast<TagDecl>(decl), k, args, namedargs).typeargs);

        if (auto j = scope.find_type(typeref->decl); j != scope.typeargs.end())
          return j->second;

        return type;
      }

      default:
        assert(ctx.diag.has_errored());
    }

    return resolve_type(ctx, sx, decl);
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TypeRefType *typeref, DeclRefDecl *declref)
  {
    vector<Type*> types;
    vector<Decl*> decls;

    auto args = typeargs(ctx, scope, declref->args);
    auto namedargs = typeargs(ctx, scope, declref->namedargs);

    for (auto sx = scope; sx; sx = parent_scope(std::move(sx)))
    {
      find_decls(ctx, sx, declref->name, QueryFlags::Types | QueryFlags::Concepts | QueryFlags::Enums | QueryFlags::Usings, ResolveUsings, decls);

      for (auto &decl : decls)
      {
        size_t k = 0;

        if (decl->kind() == Decl::TypeAlias && (decl->flags & TypeAliasDecl::Implicit) && !declref->argless)
          decl = get<Decl*>(decl->owner);

        auto type = resolve_type(ctx, scope, typeref, outer_scope(sx, decl), decl, k, args, namedargs);

        if (k != args.size() + namedargs.size())
          continue;

        types.push_back(type);
      }

      if (decls.empty())
        continue;

      break;
    }

    if (types.size() == 1)
      return types[0];

    ctx.diag.error("no such type", scope, declref->loc());

    return ctx.typetable.var_defn;
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TypeRefType *typeref, DeclScopedDecl *scoped)
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

      for (auto sx = declref.scope; sx; sx = base_scope(ctx, sx, QueryFlags::Public))
      {
        find_decls(ctx, sx, declref.decl->name, QueryFlags::Types | QueryFlags::Concepts | QueryFlags::Enums | QueryFlags::Usings | queryflags, ResolveUsings, decls);

        for (auto &decl : decls)
        {
          size_t k = 0;

          auto type = resolve_type(ctx, scope, typeref, outer_scope(sx, decl), decl, k, args, namedargs);

          if (k != args.size() + namedargs.size())
            continue;

          types.push_back(type);
        }

        if (decls.empty())
          continue;

        break;
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

    for (auto &[decl, arg] : args)
    {
      arg = resolve_type(ctx, scope, arg);
    }

    auto declscope = child_scope(outer_scope(scope, aliasdecl), aliasdecl, args);

    return resolve_type(ctx, declscope, aliasdecl->type);
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, TypeRefType *typeref)
  {
    switch (typeref->decl->kind())
    {
      case Decl::TypeOf:
        return resolve_type(ctx, scope, decl_cast<TypeOfDecl>(typeref->decl));

      case Decl::DeclRef:
        return resolve_type(ctx, scope, typeref, decl_cast<DeclRefDecl>(typeref->decl));

      case Decl::DeclScoped:
        return resolve_type(ctx, scope, typeref, decl_cast<DeclScopedDecl>(typeref->decl));

      case Decl::TypeAlias:
        return resolve_type(ctx, scope, typeref, decl_cast<TypeAliasDecl>(typeref->decl));

      case Decl::Struct:
      case Decl::Union:
      case Decl::VTable:
      case Decl::Lambda:
      case Decl::Enum:
        return resolve_type(ctx, super_scope(scope, typeref->decl), decl_cast<TagDecl>(typeref->decl));

      case Decl::Concept:
        return resolve_type(ctx, super_scope(scope, typeref->decl), decl_cast<ConceptDecl>(typeref->decl));

      default:
        assert(ctx.diag.has_errored());
    }

    return ctx.typetable.var_defn;
  }

  Type *resolve_type(LowerContext &ctx, Scope const &scope, Type *type)
  {
    switch (type->klass())
    {
      case Type::Builtin:
        return type;

      case Type::Const:
        return resolve_type(ctx, scope, type_cast<ConstType>(type));

      case Type::Pointer:
        return resolve_type(ctx, scope, type_cast<PointerType>(type));

      case Type::Reference:
        return resolve_type(ctx, scope, type_cast<ReferenceType>(type));

      case Type::Slice:
        return resolve_type(ctx, scope, type_cast<SliceType>(type));

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

      case Type::Pack:
        return resolve_type(ctx, scope, type_cast<PackType>(type)->type);

      default:
        assert(ctx.diag.has_errored());
    }

    return ctx.typetable.var_defn;
  }

  Type *resolve_type(LowerContext &ctx, Scope scope, Decl *decl)
  {
    fill_defaultargs(ctx, get<Decl*>(scope.owner), scope.typeargs);

    switch (decl->kind())
    {
      case Decl::Struct:
      case Decl::Concept:
      case Decl::VTable:
      case Decl::Lambda:
      case Decl::Union:
      case Decl::Enum:
        return resolve_type(ctx, scope, decl_cast<TagDecl>(decl));

      case Decl::TypeAlias:
        return resolve_type(ctx, scope, decl_cast<TypeAliasDecl>(decl)->type);

      case Decl::Function:
        return resolve_type(ctx, scope, decl_cast<FunctionDecl>(decl));

      case Decl::EnumConstant:
        return resolve_type(ctx, scope, resolve_type(ctx, scope, get<Decl*>(scope.owner)), decl_cast<EnumConstantDecl>(decl));

      case Decl::VoidVar:
      case Decl::StmtVar:
      case Decl::ParmVar:
      case Decl::FieldVar:
      case Decl::ThisVar:
      case Decl::ErrorVar:
        return resolve_type(ctx, scope, decl_cast<VarDecl>(decl));

      case Decl::TypeOf:
        return resolve_type(ctx, scope, decl_cast<TypeOfDecl>(decl));

      case Decl::TypeName:
        return resolve_type(ctx, scope, decl_cast<TypeNameDecl>(decl)->type);

      case Decl::TypeArg:
        if (auto j = scope.find_type(decl); j != scope.typeargs.end())
          return j->second;
        break;

      default:
        assert(ctx.diag.has_errored());
    }

    return ctx.typetable.var_defn;
  }

  Type *resolve_type(LowerContext &ctx, Type *type)
  {
    return resolve_type(ctx, ctx.stack.back(), type);
  }

  //|///////////////////// resolve_value_type ///////////////////////////////
  Type *resolve_value_type(LowerContext &ctx, Type *type)
  {
    auto tupletype = type_cast<TupleType>(type);

    auto defns = tupletype->defns;
    auto fields = tupletype->fields;

    for (size_t i = 0; i < fields.size(); ++i)
    {
      while (is_reference_type(defns[i]))
      {
        defns[i] = remove_const_type(remove_reference_type(defns[i]));
        fields[i] = remove_const_type(remove_reference_type(fields[i]));
      }

      if (is_tuple_type(fields[i]))
      {
        fields[i] = resolve_value_type(ctx, fields[i]);
      }
    }

    return ctx.typetable.find_or_create<TupleType>(std::move(defns), std::move(fields));
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

        for (auto &defn : defns)
        {
          defn = ctx.typetable.find_or_create<ReferenceType>(defn);
        }

        for (auto &field : fields)
        {
          if (is_const_type(lhs))
          {
            field = ctx.typetable.find_or_create<ConstType>(field);
          }

          if (lhs->klass() == Type::QualArg && j != scope.typeargs.end() && j->second->klass() == Type::Tuple)
          {
            auto index = &field - &fields.front();

            if (auto argtype = type_cast<TupleType>(j->second)->fields[index]; argtype->klass() == Type::QualArg)
            {
              field = ctx.typetable.find_or_create<QualArgType>(type_cast<QualArgType>(argtype)->qualifiers, remove_const_type(field));
            }
          }

          field = ctx.typetable.find_or_create<ReferenceType>(field);
        }

        rhs = ctx.typetable.find_or_create<TupleType>(std::move(defns), std::move(fields));
      }

      return ctx.typetable.find_or_create<ReferenceType>(rhs);
    }

    if (is_reference_type(parm->type))
    {
      auto lhs = type_cast<ReferenceType>(parm->type)->type;
      auto rhs = resolve_type(ctx, scope, type_cast<ReferenceType>(parm->type)->type);

      if (lhs->klass() == Type::QualArg)
      {
        auto j = scope.find_type(parm);

        if (j != scope.typeargs.end() && j->second->klass() == Type::QualArg)
        {
          if (type_cast<QualArgType>(j->second)->qualifiers & QualArgType::Const)
            rhs = ctx.typetable.find_or_create<ConstType>(remove_const_type(rhs));

          if ((type_cast<QualArgType>(j->second)->qualifiers & (QualArgType::RValue | QualArgType::Const)) == QualArgType::RValue)
            rhs = ctx.typetable.find_or_create<QualArgType>(QualArgType::RValue, rhs);
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
  bool match_concept(LowerContext &ctx, Scope const &scope, Scope &sig, ConceptDecl *koncept, vector<pair<Decl*, Type*>> const &args, Type *&type)
  {
    assert(sig.typeargs.empty());

    if (koncept->name == Ident::kw_var)
      return true;

    for (auto &[arg, type] : outer_scope(scope, koncept).typeargs)
    {
      sig.set_type(arg, type);
    }

    for (auto &[arg, type] : args)
    {
      sig.set_type(arg, resolve_type(ctx, scope, type));
    }

    auto cache_key = make_tuple(koncept, sig.typeargs, type);

    if (auto j = ctx.typetable.concepts.find(cache_key); j != ctx.typetable.concepts.end())
    {
      sig.typeargs = get<0>(j->second);
      type = get<1>(j->second);
      return get<2>(j->second);
    }

    bool match = true;
    Diag diag(ctx.diag.leader());

    for (auto &decl : koncept->decls)
    {
      if (decl->kind() != Decl::Decl::Requires)
        continue;

      auto reqires = decl_cast<RequiresDecl>(decl);

      auto fn = decl_cast<FunctionDecl>(reqires->fn);

      auto sx = Scope(fn, sig.typeargs);

      for (auto &arg : fn->args)
        sx.set_type(arg, type);

      if (reqires->flags & RequiresDecl::Match)
      {
        LowerContext cttx(ctx.typetable, diag);

        cttx.translationunit = ctx.translationunit;
        cttx.module = ctx.module;

        auto requirestype = resolve_type(cttx, sx, reqires->requirestype);

        if (match = is_typearg_type(requirestype) && type_cast<TypeArgType>(requirestype)->koncept == koncept; match)
        {
          for (auto &[arg, type] : type_cast<TypeArgType>(requirestype)->args)
          {
            if (auto j = sig.find_type(arg); j != sig.typeargs.end())
              if (!deduce_type(ctx, scope, sig, j->second, type))
                match = false;

            sig.set_type(arg, type);
          }
        }
      }

      if (reqires->flags & RequiresDecl::Condition)
      {
        auto expr = stmt_cast<ReturnStmt>(fn->body)->expr;

        auto result = evaluate(sx, expr, {}, ctx.typetable, diag, reqires->loc());

        if (result.type != ctx.booltype || !expr_cast<BoolLiteralExpr>(result.value)->value())
          match = false;
      }

      if (reqires->flags & RequiresDecl::Expression)
      {
        auto fx = FnSig(fn, std::move(sx.typeargs));

        auto &mir = lower(fx, ctx.typetable, diag);

        if (diag.has_errored())
          match = false;

        if (match && reqires->requirestype)
        {
          auto returntype = mir.locals[0];

          if (is_reference_type(returntype.defn))
            returntype = resolve_as_reference(ctx, returntype);

          if (!deduce_type(ctx, scope, sig, reqires->requirestype, returntype))
            match = false;
        }
      }

      if (!match)
        break;
    }

    ctx.typetable.concepts.emplace(std::move(cache_key), std::make_tuple(sig.typeargs, type, match));

    return match;
  }

  //|///////////////////// resolve_concept //////////////////////////////////
  bool resolve_concept(LowerContext &ctx, Scope const &scope, Scope &fx, TypeArgType *typearg, Type *&type)
  {
    Scope sig;

    if (!match_concept(ctx, fx, sig, decl_cast<ConceptDecl>(typearg->koncept), typearg->args, type))
      return false;

    for (auto &[arg, type] : typearg->args)
    {
      if (!is_typearg_type(type))
        continue;

      if (auto j = sig.find_type(arg); j != sig.typeargs.end())
      {
        if (type_cast<TypeArgType>(type)->koncept)
        {
          if (!resolve_concept(ctx, scope, fx, type_cast<TypeArgType>(type), j->second))
            return false;
        }

        fx.set_type(type_cast<TypeArgType>(type)->decl, j->second);
      }
    }

    return true;
  }

  //|///////////////////// match_arguments //////////////////////////////////
  bool match_arguments(LowerContext &ctx, Scope const &scope, Scope &sig, FunctionDecl *fn)
  {
    Diag diag(ctx.diag.leader());

    auto fx = FnSig(fn, sig.typeargs);

    auto &mir = lower(fx, ctx.typetable, diag);

    if (diag.has_errored())
      return false;

    size_t arg = mir.args_beg;
    for (auto &parm : fx.parameters())
    {
      if (is_typearg_type(remove_qualifiers_type(decl_cast<ParmVarDecl>(parm)->type)))
      {
        if (!deduce_type(ctx, scope, sig, decl_cast<ParmVarDecl>(parm)->type, mir.locals[arg]))
          return false;
      }

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

  bool deduce_type(LowerContext &ctx, DeduceContext &tx, Scope const &scope, Scope &fx, Type *lhs, Type *rhs)
  {
    tx.depth += 1;

    switch (lhs->klass())
    {
      case Type::Const:
      case Type::QualArg:
      case Type::TypeArg:
      case Type::TypeRef:
        break;

      default:

        if (rhs->klass() == Type::QualArg && !(type_cast<QualArgType>(rhs)->qualifiers & QualArgType::Const))
          rhs = remove_const_type(rhs);

        if ((tx.pointerdepth == 0 && tx.allow_object_downcast) || (tx.pointerdepth == 1 && tx.allow_pointer_downcast))
        {
          while (is_tag_type(rhs))
          {
            if (lhs->klass() == Type::Tag && type_cast<TagType>(lhs)->decl == type_cast<TagType>(rhs)->decl)
              break;

            if (!decl_cast<TagDecl>(type_cast<TagType>(rhs)->decl)->basetype || !(type_cast<TagType>(rhs)->decl->flags & TagDecl::PublicBase))
              break;

            rhs = type_cast<TagType>(rhs)->fields[0];
          }
        }
    }

    if (rhs->klass() == Type::TypeArg)
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

        if (is_void_type(lhs) && !is_const_type(rhs) && tx.pointerdepth >= 1 && tx.allow_pointer_downcast)
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

        if (rhs->klass() == Type::Reference && (tx.pointerdepth == tx.constdepth + 1))
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
              Scope sig;

              if (!match_concept(ctx, scope, sig, decl_cast<ConceptDecl>(typearg->koncept), typearg->args, rhs))
                return false;
            }
          }

          if (j->second->klass() != Type::TypeArg)
          {
            promote_type(ctx, rhs, remove_const_type(j->second));

            if (remove_const_type(j->second) == rhs)
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
          if (!resolve_concept(ctx, scope, fx, typearg, rhs))
            return false;
        }

        fx.set_type(type_cast<TypeArgType>(lhs)->decl, rhs);

        return true;

      case Type::Array:

        if (rhs->klass() == Type::Array)
        {
          DeduceContext ttx;

          ttx.allow_const_downcast = tx.allow_const_downcast;
          ttx.allow_object_downcast = false;
          ttx.allow_pointer_downcast = tx.allow_pointer_downcast;

          if (type_cast<ArrayType>(lhs)->type == ctx.typetable.var_defn)
            return false;

          if (!deduce_type(ctx, ttx, scope, fx, type_cast<ArrayType>(lhs)->type, type_cast<ArrayType>(rhs)->type))
            return false;

          if (!deduce_type(ctx, ttx, scope, fx, type_cast<ArrayType>(lhs)->size, type_cast<ArrayType>(rhs)->size))
            return false;

          return true;
        }

        return false;

      case Type::Tuple:

        if (rhs->klass() == Type::Tuple)
        {
          size_t k = 0;

          for (size_t i = 0; i < type_cast<TupleType>(lhs)->fields.size(); ++i)
          {
            auto field = type_cast<TupleType>(lhs)->fields[i];

            if (field->klass() == Type::Unpack)
            {
              auto defns = vector(type_cast<TupleType>(rhs)->defns.begin() + k, type_cast<TupleType>(rhs)->defns.end());
              auto fields = vector(type_cast<TupleType>(rhs)->fields.begin() + k, type_cast<TupleType>(rhs)->fields.end());

              if (!deduce_type(ctx, tx, scope, fx, type_cast<UnpackType>(field)->type, ctx.typetable.find_or_create<TupleType>(std::move(defns), std::move(fields))))
                return false;

              k = type_cast<TupleType>(rhs)->fields.size();

              continue;
            }

            if (k == type_cast<TupleType>(rhs)->fields.size())
              return false;

            DeduceContext ttx;

            ttx.allow_const_downcast = tx.allow_const_downcast;
            ttx.allow_object_downcast = false;
            ttx.allow_pointer_downcast = tx.allow_pointer_downcast;

            if (i < type_cast<TupleType>(lhs)->defns.size() && is_reference_type(type_cast<TupleType>(lhs)->defns[i]))
            {
              ttx.allow_object_downcast = tx.allow_object_downcast;
              ttx.pointerdepth += 1;
            }

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

          for (size_t i = 0, j = 0; i < type_cast<TagType>(lhs)->args.size(); ++i)
          {
            DeduceContext ttx;

            ttx.allow_const_downcast = false;
            ttx.allow_object_downcast = false;
            ttx.allow_pointer_downcast = false;

            while (true)
            {
              if (j == type_cast<TagType>(rhs)->args.size())
                return false;

              if (type_cast<TagType>(lhs)->args[i].first == type_cast<TagType>(rhs)->args[j].first)
                break;

              ++j;
            }

            if (!deduce_type(ctx, ttx, scope, fx, type_cast<TagType>(lhs)->args[i].second, type_cast<TagType>(rhs)->args[j].second))
              return false;
          }

          return true;
        }

        return false;

      case Type::Function:

        if (rhs->klass() == Type::Function)
        {
          DeduceContext ttx;

          ttx.allow_const_downcast = false;
          ttx.allow_object_downcast = false;
          ttx.allow_pointer_downcast = tx.allow_pointer_downcast;

          if (!deduce_type(ctx, ttx, scope, fx, type_cast<FunctionType>(lhs)->returntype, type_cast<FunctionType>(rhs)->returntype))
            return false;

          if (!deduce_type(ctx, ttx, scope, fx, type_cast<FunctionType>(lhs)->paramtuple, type_cast<FunctionType>(rhs)->paramtuple))
            return false;

          if (!deduce_type(ctx, ttx, scope, fx, type_cast<FunctionType>(lhs)->throwtype, type_cast<FunctionType>(rhs)->throwtype))
            return false;

          return true;
        }

        if (is_lambda_type(rhs) && !(type_cast<TagType>(rhs)->decl->flags & LambdaDecl::Captures) && tx.pointerdepth <= 1)
        {
          FnSig callop;

          if (!deduce_calltype(ctx, fx, callop, type_cast<FunctionType>(lhs), rhs))
            return false;

          return true;
        }

        return false;

      case Type::QualArg:

        if (type_cast<QualArgType>(lhs)->qualifiers & QualArgType::Const)
          tx.constdepth += 1;

        return deduce_type(ctx, tx, scope, fx, type_cast<QualArgType>(lhs)->type, remove_const_type(rhs));

      case Type::Slice:

        if (rhs->klass() == Type::Slice)
        {
          return deduce_type(ctx, tx, scope, fx, type_cast<SliceType>(lhs)->type, type_cast<SliceType>(rhs)->type);
        }

        return false;

      case Type::TypeRef:

        if (!fx)
          return false;

        return deduce_type(ctx, tx, scope, fx, resolve_type(ctx, fx, lhs), rhs);

      case Type::TypeLit:
      case Type::Constant:

        if (!fx)
          return false;

        return resolve_type(ctx, fx, lhs) == rhs;

      default:
        throw logic_error("unresolved type in query");
    }
  }

  bool deduce_type(LowerContext &ctx, Scope const &scope, Scope &fx, Type *lhs, MIR::Local const &rhs)
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

  bool deduce_type(LowerContext &ctx, Scope const &scope, Scope &fx, ParmVarDecl *parm, MIR::Local const &rhs)
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

        for (auto &defn : defns)
        {
          defn = remove_reference_type(defn);
        }

        for (auto &field : fields)
        {
          field = remove_reference_type(field);

          if (!is_const_type(lhs) && !is_qualarg_type(lhs) && is_const_type(field))
            return false;

          field = remove_const_type(field);
        }

        rhstype = ctx.typetable.find_or_create<TupleType>(std::move(defns), std::move(fields));
      }

      if (!is_typearg_type(remove_const_type(lhs)))
        return false;

      auto lhstype = lhs;

#if PACK_REFS
      if (auto j = scope.find_type(type_cast<TypeArgType>(remove_const_type(lhs))->decl); j != scope.typeargs.end())
      {
        if (!is_tuple_type(j->second) || type_cast<TupleType>(j->second)->fields.size() != type_cast<TupleType>(rhs.type)->fields.size())
          return false;

        auto defns = type_cast<TupleType>(j->second)->defns;
        auto fields = type_cast<TupleType>(j->second)->fields;

        for (size_t i = 0; i < fields.size(); ++i)
        {
          if (is_reference_type(defns[i]))
          {
            fields[i] = remove_reference_type(fields[i]);

            if (!is_const_type(fields[i]) && !is_qualarg_type(fields[i]) && is_qualarg_reference(type_cast<TupleType>(rhs.type)->fields[i]) && (type_cast<QualArgType>(remove_reference_type(type_cast<TupleType>(rhs.type)->fields[i]))->qualifiers & QualArgType::Const))
              return false;

            fields[i] = remove_const_type(fields[i]);
          }
        }

        lhstype = ctx.typetable.find_or_create<TupleType>(std::move(defns), std::move(fields));
      }
#endif

      if (!deduce_type(ctx, tx, scope, fx, remove_const_type(lhstype), rhstype))
        return false;

      if (is_qualarg_type(lhs))
      {
        auto defns = type_cast<TupleType>(rhs.type)->defns;
        auto fields = type_cast<TupleType>(rhs.type)->fields;

        for (auto &field : fields)
        {
          field = ctx.typetable.find_or_create<QualArgType>(type_cast<QualArgType>(remove_reference_type(field))->qualifiers, ctx.typetable.var_defn);
        }

        fx.set_type(parm, ctx.typetable.find_or_create<TupleType>(std::move(defns), std::move(fields)));
      }

      return true;
    }

    if (is_impl_type(ctx, lhs, rhs))
    {
      lhs = resolve_type(ctx, fx, lhs);

      if (!is_vtable_type(remove_const_type(remove_pointference_type(lhs))))
        return false;

      return true;
    }

    if (is_reference_type(lhs))
    {
      lhs = type_cast<ReferenceType>(lhs)->type;

      if (!is_const_type(lhs) && !is_qualarg_type(lhs) && (rhs.flags & MIR::Local::Const))
        return false;

      if (!(is_const_type(lhs) || (rhs.flags & MIR::Local::Const)))
        tx.pointerdepth += 1;

      if (is_refn_type(ctx, parm))
      {
        if (auto refn = find_refn(ctx, fx, parm, rhs); refn.fn)
        {
          auto returntype = find_returntype(ctx, refn);

          if (is_reference_type(returntype.defn))
            returntype = resolve_as_reference(ctx, returntype);

          if (!deduce_type(ctx, tx, scope, fx, remove_const_type(lhs), returntype.type))
            return false;

          if (is_qualarg_type(lhs))
            fx.set_type(parm, ctx.typetable.find_or_create<QualArgType>(qualifiers(rhs), ctx.typetable.var_defn));

          return true;
        }
      }
    }

    if (!deduce_type(ctx, tx, scope, fx, remove_const_type(lhs), rhs.type))
      return false;

    if (is_qualarg_type(lhs))
    {
      auto flags = qualifiers(rhs);

      if (is_voidpointer_type(type_cast<QualArgType>(lhs)->type) && is_pointference_type(rhs.type) && !is_voidpointer_type(rhs.type))
        flags |= QualArgType::RValue;

      fx.set_type(parm, ctx.typetable.find_or_create<QualArgType>(flags, ctx.typetable.var_defn));
    }

    return true;
  }

  //|///////////////////// lambda ///////////////////////////////////////////
  bool deduce_calltype(LowerContext &ctx, Scope const &scope, FnSig &fx, FunctionType *lhs, Type *rhs)
  {
    auto fn = decl_cast<FunctionDecl>(decl_cast<LambdaDecl>(type_cast<TagType>(rhs)->decl)->fn);
    auto params = type_cast<TupleType>(resolve_type(ctx, scope, lhs->paramtuple));
    auto throwtype = resolve_type(ctx, scope, lhs->throwtype);
    auto returntype = resolve_type(ctx, scope, lhs->returntype);

    Scope sig(fn, type_cast<TagType>(rhs)->args);

    if (params->fields.size() != fn->parms.size())
      return false;

    for (size_t i = 0; i < fn->parms.size(); ++i)
    {
      if (!deduce_type(ctx, scope, sig, params->fields[i], decl_cast<ParmVarDecl>(fn->parms[i])->type))
        return false;

      if (!deduce_type(ctx, scope, sig, decl_cast<ParmVarDecl>(fn->parms[i])->type, params->fields[i]))
        return false;
    }

    fx = FnSig(fn, std::move(sig.typeargs));

    if (is_throws(ctx, fx, {}, {}, &fx.throwtype) && !(throwtype != ctx.voidtype))
      return false;

    if (find_returntype(ctx, fx).type != returntype)
      return false;

    if (throwtype != ctx.voidtype)
    {
      if (!fx.throwtype)
        fx.throwtype = throwtype;

      if (fx.throwtype != throwtype)
        return false;
    }

    return true;
  }

  //|///////////////////// deduce_returntype ////////////////////////////////
  bool deduce_returntype(LowerContext &ctx, Scope const &scope, FunctionDecl *fn, MIR::Local const &lhs, MIR::Local &rhs)
  {
    auto type = lhs.type;

    bool make_const = false;

    make_const |= is_const_pointer(lhs.type);
    make_const |= is_const_reference(lhs.type);

    if (!fn->returntype)
    {
      promote_type(ctx, type, rhs.type);

      make_const |= is_const_pointer(rhs.type);
      make_const |= is_const_reference(rhs.type);

      if (is_pointer_type(type) && !is_const_pointer(type) && make_const)
        type = ctx.typetable.find_or_create<PointerType>(ctx.typetable.find_or_create<ConstType>(remove_const_type(remove_pointer_type(type))));

      if (is_reference_type(type) && !is_const_reference(type) && make_const)
        type = ctx.typetable.find_or_create<ReferenceType>(ctx.typetable.find_or_create<ConstType>(remove_const_type(remove_reference_type(type))));

      if (is_reference_type(lhs.type) && is_reference_type(rhs.type) && (lhs.flags & MIR::Local::RValue) != (rhs.flags & MIR::Local::RValue))
      {
        rhs.flags &= ~MIR::Local::RValue;

        if (is_qualarg_reference(type))
          type = ctx.typetable.find_or_create<ReferenceType>(remove_const_type(remove_reference_type(type)));
      }
    }

    Scope fx(fn);

    if (!deduce_type(ctx, scope, fx, type, rhs.type))
      return false;

    if (is_lambda_type(rhs.type))
      return true;

    if (!fx.typeargs.empty())
      type = resolve_type(ctx, fx, type);

    promote_type(ctx, rhs.type, type);

    if (is_tuple_type(rhs.type))
      rhs.type = type;

    if (is_pointer_type(rhs.type) && !is_const_pointer(rhs.type) && make_const)
      rhs.type = ctx.typetable.find_or_create<PointerType>(ctx.typetable.find_or_create<ConstType>(remove_const_type(remove_pointer_type(rhs.type))));

    if (is_reference_type(rhs.type) && !is_const_reference(rhs.type) && make_const)
      rhs.type = ctx.typetable.find_or_create<ReferenceType>(ctx.typetable.find_or_create<ConstType>(remove_const_type(remove_reference_type(rhs.type))));

    if (is_pointer_type(rhs.type))
      rhs.defn = ctx.typetable.var_defn;

    return !!fn->returntype || type == rhs.type;
  }

  //|///////////////////// find_overloads ///////////////////////////////////

  struct FindContext
  {
    Ident *name;
    vector<MIR::Local> args;
    map<Ident*, MIR::Local> namedargs;

    vector<Decl*> decls;

    long queryflags;

    FindContext(LowerContext &ctx, Type *type, long queryflags = QueryFlags::All);
    FindContext(LowerContext &ctx, Ident *name, long queryflags = QueryFlags::All);

    FindContext(FindContext const &tx, long queryflags) : name(tx.name), args(tx.args), namedargs(tx.namedargs), queryflags(queryflags) { }
  };

  FindContext::FindContext(LowerContext &ctx, Ident *name, long queryflags)
    : name(name), queryflags(queryflags)
  {
  }

  FindContext::FindContext(LowerContext &ctx, Type *type, long queryflags)
    : name(), queryflags(queryflags)
  {
    switch (type = remove_const_type(type); type->klass())
    {
      case Type::Builtin:
        name = type_cast<BuiltinType>(type)->name();
        break;

      case Type::Pointer:
        name = Ident::type_ptr;
        args.push_back(type);
        break;

      case Type::Reference:
        name = Ident::type_ref;
        args.push_back(type);
        break;

      case Type::Array:
        name = Ident::type_array;
        args.push_back(type);
        break;

      case Type::Tuple:
        name = Ident::type_tuple;
        args.push_back(type);
        break;

      case Type::TypeLit:
        switch (auto value = type_cast<TypeLitType>(type)->value; value->kind())
        {
          case Expr::BoolLiteral:
            name = Ident::type_lit;
            args.push_back(Builtin::type(Builtin::Type_Bool));
            args.push_back(type);
            break;

          case Expr::CharLiteral:
            name = Ident::type_lit;
            args.push_back(Builtin::type(Builtin::Type_Char));
            args.push_back(type);
            break;

          case Expr::IntLiteral:
            name = Ident::type_lit;
            args.push_back(Builtin::type(Builtin::Type_IntLiteral));
            args.push_back(type);
            break;

          case Expr::FloatLiteral:
            name = Ident::type_lit;
            args.push_back(Builtin::type(Builtin::Type_FloatLiteral));
            args.push_back(type);
            break;

          case Expr::StringLiteral:
            name = Ident::type_lit;
            args.push_back(Builtin::type(Builtin::Type_StringLiteral));
            args.push_back(type);
            break;

          case Expr::ArrayLiteral:
          case Expr::CompoundLiteral:
            name = Ident::type_lit;
            args.push_back(type);
            args.push_back(type);
            if (auto result = evaluate(type_scope(ctx, type), value, ctx.symbols, ctx.typetable, ctx.diag, value->loc()))
              args[0] = result.type;
            break;

          default:
            break;
        }

        break;

      case Type::Constant:
        name = Ident::type_lit;
        args.push_back(type_cast<ConstantType>(type)->type);
        args.push_back(type_cast<ConstantType>(type)->expr);
        break;

      case Type::Tag:
        name = decl_cast<TagDecl>(type_cast<TagType>(type)->decl)->name;

        if (auto tagtype = type_cast<TagType>(type))
        {
          for (size_t i = 0; i < decl_cast<TagDecl>(tagtype->decl)->args.size(); ++i)
          {
            auto arg = decl_cast<TagDecl>(tagtype->decl)->args[i];

            auto j = find_if(tagtype->args.begin(), tagtype->args.end(), [&](auto &k) { return k.first == arg; });

            if (decl_cast<TypeArgDecl>(arg)->flags & TypeArgDecl::Pack)
            {
              for (auto &field : type_cast<TupleType>(j->second)->fields)
                args.push_back(field);

              continue;
            }

            if (decl_cast<TypeArgDecl>(arg)->flags & TypeArgDecl::SplitFn)
            {
              auto k = find_if(tagtype->args.begin(), tagtype->args.end(), [&](auto &k) { return k.first == decl_cast<TagDecl>(tagtype->decl)->args[i+1]; });

              args.push_back(ctx.typetable.find_or_create<FunctionType>(j->second, k->second, nullptr));

              i += 1;
              continue;
            }

            if (decl_cast<TypeArgDecl>(arg)->flags & TypeArgDecl::SplitArray)
            {
              auto k = find_if(tagtype->args.begin(), tagtype->args.end(), [&](auto &k) { return k.first == decl_cast<TagDecl>(tagtype->decl)->args[i+1]; });

              args.push_back(ctx.typetable.find_or_create<ArrayType>(j->second, k->second));

              i += 1;
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

  void find_overloads(LowerContext &ctx, FindContext &tx, Scope const &scope, vector<MIR::Fragment> const &parms, map<Ident*, MIR::Fragment> const &namedparms, vector<std::tuple<FnSig, size_t>> &candidates, vector<FnSig> &results)
  {
    find_decls(ctx, scope, tx.name, tx.queryflags, tx.decls);

    for (auto &decl : tx.decls)
    {
      if (decl->kind() == Decl::Function)
      {
        auto fn = decl_cast<FunctionDecl>(decl);

        if (!(fn->flags & FunctionDecl::Public) && get_module(fn) != ctx.module)
          continue;

        if (find_if(results.begin(), results.end(), [&](auto &k) { return k.fn == fn; }) != results.end())
          continue;

        if (find_if(candidates.begin(), candidates.end(), [&](auto &k) { return get<0>(k).fn == fn; }) != candidates.end())
          continue;

        bool viable = true;

        size_t i = 0, k = 0;

        auto fnscope = child_scope(ctx, scope, fn, k, tx.args, tx.namedargs);

        if ((k & ~IllSpecified) != tx.args.size() + tx.namedargs.size())
        {
          candidates.push_back(std::make_tuple(fn, WrongArgCount));

          viable = false;
        }

        auto fx = fnscope;

        if (viable)
        {
          for (i = 0, k = 0; i < fn->parms.size(); ++i)
          {
            fx.goalpost = fn->parms[i];

            auto parm = decl_cast<ParmVarDecl>(fn->parms[i]);

            if (is_pack_type(parm->type))
            {
              vector<Type*> defns;
              vector<Type*> fields;

              auto n = parms.size();

              if (auto arg = remove_qualifiers_type(type_cast<PackType>(parm->type)->type); is_typearg_type(arg))
              {
                if (auto j = fnscope.find_type(type_cast<TypeArgType>(arg)->decl); j != fnscope.typeargs.end())
                  if (is_tuple_type(j->second))
                    n = min(n, k + tuple_len(type_cast<TupleType>(j->second)));
              }

              bool literal = true;

              for ( ; k < n; ++k)
              {
                auto defn = ctx.typetable.var_defn;
                auto field = parms[k].type.type;

                if (is_reference_type(type_cast<PackType>(parm->type)->type))
                {
                  defn = ctx.typetable.find_or_create<ReferenceType>(defn);

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

                literal &= (parms[k].type.flags & MIR::Local::Literal) != 0;

                defns.push_back(defn);
                fields.push_back(field);
              }

              MIR::Local pack;

              pack.type = ctx.typetable.find_or_create<TupleType>(std::move(defns), std::move(fields));

              if (literal)
                pack.flags |= MIR::Local::Const | MIR::Local::Literal;

              pack.flags |= MIR::Local::RValue;
              pack.flags |= MIR::Local::Reference;

#if PACK_REFS
              if (auto arg = remove_const_type(remove_reference_type(type_cast<PackType>(parm->type)->type)); is_typearg_type(arg))
              {
                if (auto j = fx.find_type(type_cast<TypeArgType>(arg)->decl); j != fx.typeargs.end())
                  fnscope.set_type(j->first, j->second);
              }
#endif
              if (!deduce_type(ctx, fnscope, fx, parm, pack))
                viable = false;
            }

            else if (k < parms.size())
            {
              if (!deduce_type(ctx, fnscope, fx, parm, parms[k].type))
                viable = false;

              k += 1;
            }

            else if (auto j = namedparms.find(parm->name); j != namedparms.end())
            {
              if (!deduce_type(ctx, fnscope, fx, parm, j->second.type))
                viable = false;

              k += 1;
            }

            else if (auto j = find_if(namedparms.begin(), namedparms.end(), [&](auto &k) { auto name = k.first->sv(); return name.back() == '?' && parm->name && name.substr(0, name.size()-1) == parm->name->sv(); }); j != namedparms.end())
            {
              if (!deduce_type(ctx, fnscope, fx, parm, j->second.type))
                viable = false;
            }

            else if (parm->defult)
            {
              if (is_qualarg_reference(parm->type))
                fx.set_type(parm, ctx.typetable.find_or_create<QualArgType>(MIR::Local::RValue, ctx.typetable.var_defn));
            }

            else
            {
              viable = false;
            }

            if (!viable)
            {
              candidates.push_back(std::make_tuple(fn, i));

              break;
            }
          }
        }

        fx.goalpost = nullptr;

        if (viable)
        {
          k += count_if(namedparms.begin(), namedparms.end(), [&](auto &k) { auto name = k.first->sv(); return name.back() == '?'; });

          if (k != parms.size() + namedparms.size())
          {
            candidates.push_back(std::make_tuple(fn, WrongParmCount));

            viable = false;
          }
        }

        if (viable)
        {
          fill_defaultargs(ctx, fn, fx.typeargs);

          for (size_t i = 0; i < fn->parms.size(); ++i)
          {
            auto parm = decl_cast<ParmVarDecl>(fn->parms[i]);
            auto basetype = remove_qualifiers_type(parm->type);

            if (parm->defult && is_typearg_type(basetype))
            {
              auto arg = type_cast<TypeArgType>(basetype)->decl;

              if (fx.find_type(arg) == fx.typeargs.end())
              {
                vector<Scope> stack;
                seed_stack(stack, fx);

                if (auto type = find_type(ctx, stack, parm->defult))
                {
                  type.flags |= MIR::Local::RValue;
                  type.flags |= MIR::Local::Literal;

                  if (!deduce_type(ctx, fnscope, fx, parm, type))
                    viable = false;
                }
              }
            }
          }
        }

        if (viable)
        {
          for (size_t i = 0, k = 0; i < fn->parms.size(); ++i)
          {
            auto parm = decl_cast<ParmVarDecl>(fn->parms[i]);

            if (parm->flags & VarDecl::Literal)
            {
              if (is_pack_type(parm->type))
              {
                vector<Expr*> fields;

                for ( ; k < parms.size(); ++k)
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
                  value = expr_cast<UnaryOpExpr>(value)->subexpr;

                if (value->kind() == Expr::Cast && is_literal_expr(expr_cast<CastExpr>(value)->expr))
                  value = expr_cast<CastExpr>(value)->expr;

                if (!is_literal_expr(value))
                {
                  // This roundabout approach is to get __site__ to evaluate to the callsite

                  LowerContext cttx(ctx.typetable, ctx.diag);

                  seed_stack(cttx.stack, fnscope);

                  cttx.translationunit = ctx.translationunit;
                  cttx.module = ctx.module;
                  cttx.symbols = ctx.symbols;
                  cttx.site_override = ctx.site;

                  lower_expression(cttx, value);

                  if (cttx.diag.has_errored())
                    break;

                  if (auto expr = evaluate(fnscope, cttx.mir, cttx.typetable, cttx.diag, parm->defult->loc()))
                  {
                    value = expr.value;
                  }

                  if (!is_literal_expr(value))
                  {
                    ctx.diag.error("non literal default parameter", fnscope, parm->defult->loc());
                    break;
                  }
                }

                fx.set_type(parm, ctx.typetable.find_or_create<TypeLitType>(value));
              }
            }

            k = is_pack_type(parm->type) ? parms.size() : k + 1;
          }
        }

        if (viable)
        {
          if ((fn->flags & FunctionDecl::Defaulted) && (fn->builtin == Builtin::Default_Copytructor || fn->builtin == Builtin::Default_Assignment || fn->builtin == Builtin::Default_Equality || fn->builtin == Builtin::Default_Compare))
          {
            viable &= match_arguments(ctx, scope, fx, fn);

            if (!viable)
              candidates.push_back(std::make_tuple(fn, MatchExprFailed));
          }

          if ((fn->flags & FunctionDecl::DeclType) == FunctionDecl::LambdaDecl)
          {
            if (auto lambdadecl = decl_cast<LambdaDecl>(get<Decl*>(scope.owner)); lambdadecl->flags & LambdaDecl::Quick)
              match_arguments(ctx, scope, fx, fn);
          }

          for (auto &expr : fn->constraints)
          {
            switch (expr->kind())
            {
              case Expr::Where:

                if (eval(ctx, fx, expr_cast<WhereExpr>(expr)->expr) != 1)
                {
                  candidates.push_back(std::make_tuple(fn, WhereExprFailed));

                  viable = false;
                }

                break;

              case Expr::Match:

                if (!match_arguments(ctx, scope, fx, decl_cast<FunctionDecl>(expr_cast<MatchExpr>(expr)->decl)))
                {
                  candidates.push_back(std::make_tuple(fn, MatchExprFailed));

                  viable = false;
                }

                for (size_t i = 0, k = 0; i < fn->parms.size(); ++i)
                {
                  auto parm = decl_cast<ParmVarDecl>(fn->parms[i]);

                  if (is_refn_type(ctx, parm))
                  {
                    if (k < parms.size())
                    {
                      if (!deduce_type(ctx, fnscope, fx, parm, parms[k].type))
                        viable = false;
                    }

                    else if (auto j = namedparms.find(parm->name); j != namedparms.end())
                    {
                      if (!deduce_type(ctx, fnscope, fx, parm, j->second.type))
                        viable = false;
                    }
                  }

                  k = is_pack_type(parm->type) ? parms.size() : k + 1;
                }

                break;

              default:
                assert(false);
            }
          }

          if (fn->flags & (FunctionDecl::Builtin | FunctionDecl::Defaulted))
          {
            viable &= Builtin::where(fn, fx.typeargs);
          }
        }

        if (viable)
        {
          results.push_back(FnSig(fn, std::move(fx.typeargs)));
        }
      }

      if (decl->kind() == Decl::Enum)
      {
        if (0 != tx.args.size() + tx.namedargs.size())
          continue;

        if (find_if(results.begin(), results.end(), [&](auto &k) { return (k.fn->flags & FunctionDecl::Builtin) && k.fn->builtin == Builtin::Type_Enum; }) != results.end())
          continue;

        size_t k = 0;

        auto tagdecl = decl_cast<TagDecl>(decl);
        auto typescope = child_scope(ctx, scope, tagdecl, k, tx.args, tx.namedargs);

        fill_defaultargs(ctx, decl, typescope.typeargs);

        auto enumm = resolve_type(ctx, typescope, decl_cast<EnumDecl>(decl));

        if (parms.size() == 0 || (parms.size() == 1 && deduce_type(ctx, typescope, typescope, enumm, parms[0].type)))
          results.push_back(Builtin::fn(ctx.translationunit->builtins, Builtin::Type_Enum, enumm));
      }

      if (decl->kind() == Decl::EnumConstant)
      {
        if (0 != parms.size() + namedparms.size())
          continue;

        if (0 != tx.args.size() + tx.namedargs.size())
          continue;

        if (find_if(results.begin(), results.end(), [&](auto &k) { return (k.fn->flags & FunctionDecl::Builtin) && k.fn->builtin == Builtin::Type_Lit; }) != results.end())
          continue;

        auto typescope = scope;

        fill_defaultargs(ctx, decl, typescope.typeargs);

        auto enumm = resolve_type(ctx, typescope, decl_cast<EnumDecl>(get<Decl*>(scope.owner)));
        auto value = resolve_type(ctx, typescope, enumm, decl_cast<EnumConstantDecl>(decl));

        if (!type_cast<ConstantType>(value)->expr)
          continue;

        results.push_back(Builtin::fn(ctx.translationunit->builtins, Builtin::Type_Lit, enumm, type_cast<ConstantType>(value)->expr));
      }

      if (decl->kind() == Decl::Struct || decl->kind() == Decl::Union || decl->kind() == Decl::Enum || decl->kind() == Decl::Lambda || decl->kind() == Decl::VTable)
      {
        size_t k = 0;

        auto tagdecl = decl_cast<TagDecl>(decl);
        auto typescope = child_scope(ctx, scope, tagdecl, k, tx.args, tx.namedargs);

        if ((k & ~IllSpecified) != tx.args.size() + tx.namedargs.size())
          continue;

        if ((tx.queryflags & QueryFlags::Functions) == QueryFlags::Methods)
          continue;

        candidates.erase(remove_if(candidates.begin(), candidates.end(), [&](auto &candidate) {
          return get<0>(candidate).fn->owner == variant<Decl*, Stmt*>{decl};
        }), candidates.end());

        FindContext ttx(ctx, tx.name, QueryFlags::Functions);

        find_overloads(ctx, ttx, typescope, parms, namedparms, candidates, results);
      }

      if (decl->kind() == Decl::TypeAlias)
      {
        size_t k = 0;

        auto alias = decl_cast<TypeAliasDecl>(decl);
        auto aliasscope = child_scope(ctx, scope, alias, k, tx.args, tx.namedargs);

        if ((alias->flags & TypeAliasDecl::Builtin) || (alias->flags & TypeAliasDecl::Implicit))
          continue;

        if (k != tx.args.size() + tx.namedargs.size())
          continue;

        auto aliastype = resolve_type(ctx, aliasscope, alias->type);

        FindContext ttx(ctx, aliastype, tx.queryflags & ~QueryFlags::Public);

        find_overloads(ctx, ttx, scopeof_type(ctx, aliastype), parms, namedparms, candidates, results);
      }

      if (decl->kind() == Decl::FieldVar)
      {
        if (auto owner = get<Decl*>(scope.owner); owner->kind() == Decl::Union)
        {
          if (!(decl->flags & Decl::Public) && get_module(decl) != ctx.module)
            continue;

          auto typescope = scope;

          fill_defaultargs(ctx, decl, typescope.typeargs);

          auto field = resolve_type(ctx, typescope, decl_cast<FieldVarDecl>(decl));
          auto uniun = resolve_type(ctx, typescope, decl_cast<UnionDecl>(get<Decl*>(scope.owner)));

          vector<FnSig> ctors;

          FindContext ttx(ctx, field, QueryFlags::Types | QueryFlags::Functions);

          find_overloads(ctx, ttx, scopeof_type(ctx, field), parms, namedparms, candidates, ctors);

          for (auto &fx : ctors)
          {
            auto fn = ctx.mir.make_decl<FunctionDecl>(decl->loc());

            fn->name = Ident::type_union;
            fn->returntype = uniun;
            fn->parms = fx.fn->parms;
            fn->args.push_back(decl);
            fn->args.push_back(fx.fn);
            fn->owner = fx.fn->owner;

            results.push_back(FnSig(fn, std::move(fx.typeargs)));
          }
        }
      }

      if (decl->kind() == Decl::Using)
      {
        if (!(decl->flags & UsingDecl::Resolved))
          continue;

        FindContext ttx(tx, tx.queryflags);

        if (get_module(decl_cast<UsingDecl>(decl)->decl) != ctx.module)
          ttx.queryflags |= QueryFlags::Public;

        switch (auto usein = decl_cast<UsingDecl>(decl); usein->decl->kind())
        {
          case Decl::Module:
            find_overloads(ctx, ttx, usein->decl, parms, namedparms, candidates, results);
            break;

          case Decl::Struct:
          case Decl::Union:
          case Decl::VTable:
          case Decl::Concept:
          case Decl::Enum:
            if (tx.name != decl_cast<TagDecl>(usein->decl)->name)
              ttx.queryflags &= ~QueryFlags::Types;
            find_overloads(ctx, ttx, parent_scope(usein->decl), parms, namedparms, candidates, results);
            break;

          case Decl::TypeAlias:
            if (tx.name != decl_cast<TypeAliasDecl>(usein->decl)->name)
              ttx.queryflags &= ~QueryFlags::Types;
            find_overloads(ctx, ttx, parent_scope(usein->decl), parms, namedparms, candidates, results);
            break;

          case Decl::DeclRef:
            if (tx.name == decl_cast<DeclRefDecl>(usein->decl)->name)
              find_overloads(ctx, ttx, parent_scope(usein->decl), parms, namedparms, candidates, results);
            break;

          case Decl::DeclScoped:
            if (tx.name == decl_cast<DeclRefDecl>(decl_cast<DeclScopedDecl>(usein->decl)->decls.back())->name)
              find_overloads(ctx, ttx, parent_scope(usein->decl), parms, namedparms, candidates, results);
            break;

          case Decl::TypeArg:
            if (auto j = scope.find_type(usein->decl); j != scope.typeargs.end())
              find_overloads(ctx, ttx, scopeof_type(ctx, j->second), parms, namedparms, candidates, results);
            break;

          case Decl::TypeOf:
            if (auto j = resolve_type(ctx, scope, decl_cast<TypeOfDecl>(usein->decl)))
              find_overloads(ctx, ttx, scopeof_type(ctx, j), parms, namedparms, candidates, results);
            break;

          default:
            assert(false);
        }
      }
    }

    tx.decls.clear();
  }

  void find_overloads(LowerContext &ctx, FindContext &tx, vector<Scope> const &stack, vector<MIR::Fragment> const &parms, map<Ident*, MIR::Fragment> const &namedparms, vector<std::tuple<FnSig, size_t>> &candidates, vector<FnSig> &results)
  {
    for (auto sx = stack.rbegin(); sx != stack.rend(); ++sx)
    {
      find_decls(ctx, *sx, tx.name, QueryFlags::Types, tx.decls);

      if (tx.decls.empty())
        continue;

      for (auto &decl : tx.decls)
      {
        if (decl->kind() == Decl::TypeArg)
        {
          if (0 < tx.args.size() || 0 < tx.namedargs.size())
            continue;

          if (auto j = sx->find_type(decl); j != sx->typeargs.end())
          {
            tx = FindContext(ctx, remove_const_type(j->second), tx.queryflags);

            if (auto type = remove_const_type(j->second); is_lambda_type(type))
              tx.decls.push_back(type_cast<TagType>(type)->decl);

            find_overloads(ctx, tx, scopeof_type(ctx, j->second), parms, namedparms, candidates, results);
          }

          break;
        }
      }

      tx.decls.clear();

      break;
    }

    for (auto scope = stack.rbegin(); scope != stack.rend(); ++scope)
    {
      find_overloads(ctx, tx, *scope, parms, namedparms, candidates, results);

      if (is_tag_scope(*scope) && decl_cast<TagDecl>(get<Decl*>(scope->owner))->name == tx.name)
        continue;

      for (auto basescope = base_scope(ctx, *scope, QueryFlags::Public); basescope; basescope = base_scope(ctx, basescope, QueryFlags::Public))
      {
        find_overloads(ctx, tx, basescope, parms, namedparms, candidates, results);
      }
    }

    tx.decls.clear();
  }

  //|///////////////////// resolve_overloads ////////////////////////////////
  void resolve_overloads(LowerContext &ctx, FnSig &match, vector<FnSig> &overloads, vector<MIR::Fragment> const &parms, map<Ident*, MIR::Fragment> const &namedparms)
  {
    if (overloads.size() == 1)
    {
      match = overloads[0];
      return;
    }

    int best = std::numeric_limits<int>::max();

    for (auto &fx : overloads)
    {
      int rank = fx.fn->args.size();

      for (auto sx = Scope(fx.fn); sx; sx = parent_scope(std::move(sx)))
      {
        if (is_tag_scope(sx))
          rank += decl_cast<TagDecl>(get<Decl*>(sx.owner))->args.size();
      }

      for (size_t i = 0, k = 0; i < fx.fn->parms.size(); ++i)
      {
        auto parm = decl_cast<ParmVarDecl>(fx.fn->parms[i]);

        auto rankargs = [&](auto &self, Type const *type, int s) -> void {

          while (true)
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
                for (auto &field : type_cast<TupleType>(type)->fields)
                  self(self, field, (s - 1) / type_cast<TupleType>(type)->fields.size());
                break;

              case Type::Tag:
                if (type_cast<TagType>(type)->args.empty())
                  rank += s - 1;
                for (auto &[decl, arg] : type_cast<TagType>(type)->args)
                  self(self, arg, (s - 1) / type_cast<TagType>(type)->args.size());
                break;

              default:
                rank += s - 1;
                break;
            }

            break;
          }
        };

        auto rankcast = [&](auto &self, Type const *type, MIR::Fragment const &src, int s) -> void {

          auto lhs = remove_qualifiers_type(type);
          auto rhs = remove_qualifiers_type(src.type.type);

          while (is_tag_type(rhs))
          {
            if (lhs->klass() == Type::Tag && type_cast<TagType>(lhs)->decl == type_cast<TagType>(rhs)->decl)
              break;

            rank += s;

            if (!decl_cast<TagDecl>(type_cast<TagType>(rhs)->decl)->basetype)
              break;

            rhs = type_cast<TagType>(rhs)->fields[0];
          }

          if (lhs->klass() == Type::TypeArg)
            rank += s - 1;

          if (is_builtin_type(lhs) && lhs != rhs)
            rank += s - 1;
        };

        if (!is_pack_type(parm->type))
        {
          if (k < parms.size())
          {
            rankcast(rankcast, parm->type, parms[k], 10);
          }
          else if (auto j = namedparms.find(parm->name); j != namedparms.end())
          {
            rankcast(rankcast, parm->type, j->second, 10);
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

          if (is_typearg_type(remove_qualifiers_type(parm->type)))
          {
            auto typearg = type_cast<TypeArgType>(remove_qualifiers_type(parm->type));

            if (!typearg->koncept || decl_cast<ConceptDecl>(typearg->koncept)->name == Ident::kw_var)
              rank += 5;
          }

          if (!((is_pointer_type(parm->type) && !is_const_pointer(parm->type)) ||
                (is_reference_type(parm->type) && !is_const_reference(parm->type)) ||
                (is_pack_type(parm->type) && is_reference_type(type_cast<PackType>(parm->type)->type) && !is_const_type(type_cast<ReferenceType>(type_cast<PackType>(parm->type)->type)->type))))
            rank += 5;
        }

        if (is_pack_type(parm->type))
          rank += 100000000;

        k = is_pack_type(parm->type) ? parms.size() : k + 1;
      }

      if (fx.fn->flags & FunctionDecl::Constructor)
      {
        rank += 1;
      }

      if (fx.fn->flags & FunctionDecl::Defaulted)
      {
        // These builtins may conflict when types are unresolved
        if (fx.fn->builtin == Builtin::Tuple_CopytructorEx || fx.fn->builtin == Builtin::Tuple_AssignmentEx || fx.fn->builtin == Builtin::TupleEqEx || fx.fn->builtin == Builtin::TupleCmpEx)
          rank += 1;
      }

      if (fx.fn->name == Ident::type_union)
      {
        // These builtins may conflict when types are unresolved
        if (decl_cast<FunctionDecl>(fx.fn->args[1])->builtin == Builtin::Tuple_CopytructorEx)
          rank += 1;
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
    vector<std::tuple<FnSig, size_t>> candidates;

    auto typearg = type_cast<TypeArgType>(remove_const_type(remove_reference_type(parm->type)));

    FindContext tx(ctx, decl_cast<ConceptDecl>(typearg->koncept)->name, QueryFlags::Public | QueryFlags::Functions);

    for (auto &arg : decl_cast<ConceptDecl>(typearg->koncept)->args)
    {
      if (auto j = find_if(typearg->args.begin(), typearg->args.end(), [&](auto &k) { return k.first == arg; }); j != typearg->args.end())
      {
        if (auto argtype = resolve_type(ctx, scope, j->second); !is_typearg_type(argtype))
          tx.args.push_back(argtype);
      }
    }

    FnSig refn;

    vector<MIR::Fragment> parms(1);
    map<Ident*, MIR::Fragment> namedparms;

    parms[0].type = rhs;

    if (is_tag_type(rhs.type))
    {
      find_overloads(ctx, tx, type_scope(ctx, rhs.type), parms, namedparms, candidates, overloads);
      find_overloads(ctx, tx, scopeof_type(ctx, rhs.type), parms, namedparms, candidates, overloads);
    }

    auto declscope = Scope(typearg->koncept, outer_scope(scope, typearg->koncept).typeargs);

    find_overloads(ctx, tx, parent_scope(declscope), parms, namedparms, candidates, overloads);

    for (auto &fx: overloads)
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

      break;
    }

    return refn;
  }

  //|///////////////////// find_builtin /////////////////////////////////////

  FnSig find_builtin(LowerContext &ctx, Builtin::Kind kind, Type *T1 = nullptr, Type *T2 = nullptr)
  {
    return Builtin::fn(ctx.translationunit->builtins, kind, T1, T2);
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

    throw logic_error("invalid map_builtin");
  }

  //|///////////////////// find_callee //////////////////////////////////////

  struct Callee
  {
    FnSig fx;
    vector<FnSig> overloads;
    vector<std::tuple<FnSig, size_t>> candidates;

    Callee(std::nullptr_t = nullptr)
    {
      fx.fn = nullptr;
    }

    explicit operator bool() const { return fx.fn; }
  };

  Callee find_callee(LowerContext &ctx, Type *type, vector<MIR::Fragment> const &parms = {}, map<Ident*, MIR::Fragment> const &namedparms = {})
  {
    Callee callee;

    if (is_tag_type(type))
    {
      FindContext tx(ctx, decl_cast<TagDecl>(type_cast<TagType>(type)->decl)->name, QueryFlags::Functions);

      find_overloads(ctx, tx, type_scope(ctx, type), parms, namedparms, callee.candidates, callee.overloads);
    }

    if (callee.overloads.empty())
    {
      FindContext tx(ctx, type);

      find_overloads(ctx, tx, scopeof_type(ctx, type), parms, namedparms, callee.candidates, callee.overloads);
    }

    resolve_overloads(ctx, callee.fx, callee.overloads, parms, namedparms);

    return callee;
  }

  Callee find_callee(LowerContext &ctx, Type *type, Ident *name, vector<MIR::Fragment> const &parms = {}, map<Ident*, MIR::Fragment> const &namedparms = {})
  {
    Callee callee;

    FindContext tx(ctx, name);

    if (is_tag_type(type))
    {
      for (auto scope = type_scope(ctx, type); scope; scope = base_scope(ctx, scope, QueryFlags::Public))
      {
        find_overloads(ctx, tx, scope, parms, namedparms, callee.candidates, callee.overloads);
      }
    }

    if (callee.overloads.empty())
    {
      find_overloads(ctx, tx, scopeof_type(ctx, type), parms, namedparms, callee.candidates, callee.overloads);
    }

    resolve_overloads(ctx, callee.fx, callee.overloads, parms, namedparms);

    return callee;
  }

  Callee find_callee(LowerContext &ctx, vector<Scope> const &stack, UnaryOpExpr::OpCode op, vector<MIR::Fragment> const &parms = {}, map<Ident*, MIR::Fragment> const &namedparms = {})
  {
    Callee callee;

    FindContext tx(ctx, UnaryOpExpr::name(op));

    if (is_tag_type(parms[0].type.type))
    {
      for (auto scope = type_scope(ctx, parms[0].type.type); scope; scope = base_scope(ctx, scope, QueryFlags::Public))
      {
        find_overloads(ctx, tx, scope, parms, namedparms, callee.candidates, callee.overloads);

        if (op == UnaryOpExpr::PreDec || op == UnaryOpExpr::PreInc || op == UnaryOpExpr::PostDec || op == UnaryOpExpr::PostInc)
          break;
      }
    }

    if (callee.overloads.empty())
    {
      find_overloads(ctx, tx, scopeof_type(ctx, parms[0].type.type), parms, namedparms, callee.candidates, callee.overloads);
    }

    if (callee.overloads.empty())
    {
      find_overloads(ctx, tx, stack, parms, namedparms, callee.candidates, callee.overloads);
    }

    resolve_overloads(ctx, callee.fx, callee.overloads, parms, namedparms);

    return callee;
  }

  Callee find_callee(LowerContext &ctx, vector<Scope> const &stack, BinaryOpExpr::OpCode op, vector<MIR::Fragment> const &parms = {}, map<Ident*, MIR::Fragment> const &namedparms = {})
  {
    Callee callee;

    FindContext tx(ctx, BinaryOpExpr::name(op));

    if (is_tag_type(parms[0].type.type))
    {
      for (auto scope = type_scope(ctx, parms[0].type.type); scope; scope = base_scope(ctx, scope, QueryFlags::Public))
      {
        find_overloads(ctx, tx, scope, parms, namedparms, callee.candidates, callee.overloads);

        if (op == BinaryOpExpr::Assign || (BinaryOpExpr::AddAssign <= op && op <= BinaryOpExpr::XorAssign))
          break;
      }
    }

    if (is_tag_type(parms[1].type.type) && parms[1].type.type != parms[0].type.type)
    {
      for (auto scope = type_scope(ctx, parms[1].type.type); scope; scope = base_scope(ctx, scope, QueryFlags::Public))
      {
        if (op == BinaryOpExpr::Assign || (BinaryOpExpr::AddAssign <= op && op <= BinaryOpExpr::XorAssign))
          break;

        find_overloads(ctx, tx, scope, parms, namedparms, callee.candidates, callee.overloads);
      }
    }

    if (callee.overloads.empty())
    {
      find_overloads(ctx, tx, scopeof_type(ctx, parms[0].type.type), parms, namedparms, callee.candidates, callee.overloads);

      if (parms[1].type.type != parms[0].type.type)
        find_overloads(ctx, tx, scopeof_type(ctx, parms[1].type.type), parms, namedparms, callee.candidates, callee.overloads);
    }

    if (callee.overloads.empty())
    {
      find_overloads(ctx, tx, stack, parms, namedparms, callee.candidates, callee.overloads);
    }

    resolve_overloads(ctx, callee.fx, callee.overloads, parms, namedparms);

    return callee;
  }

  Callee find_callee(LowerContext &ctx, vector<Scope> const &stack, Scope const &basescope, DeclRefDecl *declref, vector<MIR::Fragment> const &parms = {}, map<Ident*, MIR::Fragment> const &namedparms = {}, bool is_callop = false)
  {
    Callee callee;

    FindContext tx(ctx, declref->name);

    if (is_callop)
      tx.name = Ident::op_call;

    tx.args = typeargs(ctx, ctx.stack.back(), declref->args);
    tx.namedargs = typeargs(ctx, ctx.stack.back(), declref->namedargs);

    if (basescope)
    {
      tx.queryflags &= ~(QueryFlags::Functions & ~QueryFlags::Methods);

      for (auto scope = basescope; scope; scope = base_scope(ctx, scope, QueryFlags::Public))
      {
        find_overloads(ctx, tx, scope, parms, namedparms, callee.candidates, callee.overloads);
      }

      if (callee.overloads.empty() && is_tag_scope(basescope))
      {
        find_overloads(ctx, tx, parent_scope(basescope), parms, namedparms, callee.candidates, callee.overloads);
      }
    }

    if (callee.overloads.empty())
    {
      find_overloads(ctx, tx, stack, parms, namedparms, callee.candidates, callee.overloads);
    }

    if (callee.overloads.empty() && ctx.labelscope)
    {
      find_overloads(ctx, tx, ctx.labelscope, parms, namedparms, callee.candidates, callee.overloads);
    }

    resolve_overloads(ctx, callee.fx, callee.overloads, parms, namedparms);

    return callee;
  }

  Callee find_callee(LowerContext &ctx, vector<Scope> const &stack, Scope const &basescope, DeclScopedDecl *scoped, vector<MIR::Fragment> const &parms = {}, map<Ident*, MIR::Fragment> const &namedparms = {}, bool is_callop = false)
  {
    Callee callee;

    long querymask = 0;

    if (Scoped declref = find_scoped(ctx, stack, scoped, querymask))
    {
      FindContext tx(ctx, declref.decl->name, QueryFlags::All | querymask);

      if ((tx.name->sv().substr(0, 1) == "~" && scoped->decls[scoped->decls.size() - 2]->kind() == Decl::DeclRef && decl_cast<DeclRefDecl>(scoped->decls[scoped->decls.size() - 2])->name == tx.name->sv().substr(1)) || tx.name->sv() == "~this")
      {
        if (is_type_scope(declref.scope))
        {
          auto type = resolve_type(ctx, declref.scope, get<Decl*>(declref.scope.owner));

          switch (type = remove_const_type(type); type->klass())
          {
            case Type::Builtin:
            case Type::Pointer:
            case Type::Reference:
              tx.decls.push_back(find_builtin(ctx, Builtin::Builtin_Destructor, type).fn);
              break;

            case Type::Array:
              tx.decls.push_back(find_builtin(ctx, Builtin::Array_Destructor, type).fn);
              break;

            case Type::Tuple:
              tx.decls.push_back(find_builtin(ctx, Builtin::Tuple_Destructor, type).fn);
              break;

            case Type::Tag:

              for (auto &decl : type_cast<TagType>(type)->decls)
              {
                if (decl->kind() == Decl::Function && (decl->flags & FunctionDecl::Destructor))
                  tx.decls.push_back(decl);
              }

              if (is_enum_type(type))
                tx.decls.push_back(find_builtin(ctx, Builtin::Builtin_Destructor, type).fn);

              break;

            default:
              break;
          }
        }
      }

      if (tx.name->kind() == Ident::Hash)
      {
        if (is_tag_scope(declref.scope))
        {
          auto tagtype = type_cast<TagType>(resolve_type(ctx, declref.scope, get<Decl*>(declref.scope.owner)));

          if (auto index = find_index(ctx, stack, tagtype->decls, tx.name); index < tagtype->decls.size())
            tx.decls.push_back(tagtype->decls[index]);
        }
      }

      if (auto owner = get_if<Decl*>(&declref.scope.owner); owner && *owner && ((*owner)->kind() == Decl::TypeArg || (*owner)->kind() == Decl::TypeAlias || (*owner)->kind() == Decl::TypeOf))
      {
        declref.scope = ctx.translationunit->builtins;
      }

      tx.args = typeargs(ctx, ctx.stack.back(), declref.decl->args);
      tx.namedargs = typeargs(ctx, ctx.stack.back(), declref.decl->namedargs);

      for (auto sx = declref.scope; sx; sx = base_scope(ctx, sx, QueryFlags::Public))
      {
        find_overloads(ctx, tx, sx, parms, namedparms, callee.candidates, callee.overloads);

        if (callee.overloads.empty())
          continue;

        break;
      }

      resolve_overloads(ctx, callee.fx, callee.overloads, parms, namedparms);
    }

    return callee;
  }

  Callee find_callee(LowerContext &ctx, vector<Scope> const &stack, Scope const &basescope, Decl *callee, vector<MIR::Fragment> const &parms = {}, map<Ident*, MIR::Fragment> const &namedparms = {}, bool is_callop = false)
  {
    ctx.site = callee->loc();

    switch (callee->kind())
    {
      case Decl::DeclRef:
        return find_callee(ctx, stack, basescope, decl_cast<DeclRefDecl>(callee), parms, namedparms, is_callop);

      case Decl::DeclScoped:
        return find_callee(ctx, stack, basescope, decl_cast<DeclScopedDecl>(callee), parms, namedparms, is_callop);

      case Decl::TypeName:
        return find_callee(ctx, remove_const_type(resolve_type(ctx, stack.back(), decl_cast<TypeNameDecl>(callee)->type)), parms, namedparms);

      case Decl::TypeOf:
        return find_callee(ctx, remove_const_type(resolve_type(ctx, stack.back(), decl_cast<TypeOfDecl>(callee))), parms, namedparms);

      default:
        assert(false);
    }

    return {};
  }

  //|///////////////////// diag_callee //////////////////////////////////////
  void diag_callee(LowerContext &ctx, Callee const &callee, vector<MIR::Fragment> const &parms, map<Ident*, MIR::Fragment> const &namedparms)
  {
    if (callee.overloads.size() > 1)
    {
      ctx.diag << "  ambiguous overloads\n";

      for (auto &overload : callee.overloads)
        ctx.diag << Diag::white() << "    " << get_module(overload.fn)->file() << ":" << overload.fn->loc() << ":" << Diag::cyan() << *overload.fn << '\n';
    }

    if (callee.candidates.size() != 0)
    {
      ctx.diag << Diag::white() << "  candidate functions\n";

      for (auto &[candidate, state]: callee.candidates)
      {
        ctx.diag << Diag::white() << "    " << get_module(candidate.fn)->file() << ":" << candidate.fn->loc() << ":" << Diag::cyan() << *candidate.fn << '\n';

        if (state == WrongArgCount)
          ctx.diag << Diag::normal() << "      wrong number of type arguments\n";

        if (state == WrongParmCount)
          ctx.diag << Diag::normal() << "      wrong number of parameters provided\n";

        if (state == MatchExprFailed)
          ctx.diag << Diag::normal() << "      match expression failed\n";

        if (state == WhereExprFailed)
          ctx.diag << Diag::normal() << "      where expression failed\n";

        if (state < candidate.fn->parms.size())
        {
          auto parm = decl_cast<ParmVarDecl>(candidate.fn->parms[state]);

          ctx.diag << Diag::normal() << "      no conversion for parameter " << state + 1 << ", wanted: '"
                   << ((is_reference_type(parm->type) && !is_const_reference(parm->type) && !is_qualarg_reference(parm->type)) ? "&mut " : "")
                   << *remove_const_type(remove_reference_type(parm->type)) << "'\n";
        }
      }
    }

    if (parms.size() != 0 || namedparms.size() != 0)
    {
      ctx.diag << Diag::white() << "  provided parameters\n";

      for (auto &parm : parms)
        ctx.diag << Diag::white() << "    " << &parm - &parms[0] + 1 << ": " << Diag::cyan() << parm.type << '\n';

      for (auto &[name, parm] : namedparms)
        ctx.diag << Diag::white() << "    " << *name << ": " << Diag::cyan() << parm.type << '\n';
    }

    ctx.diag << Diag::normal();
  }

  //|///////////////////// find_destructor //////////////////////////////////
  Callee find_destructor(LowerContext &ctx, Type *type, SourceLocation loc)
  {
    Callee callee;

    if (!is_trivial_destroy_type(type))
    {
      if (is_tag_type(type))
      {
        vector<MIR::Fragment> parms(1);
        map<Ident*, MIR::Fragment> namedparms;

        parms[0].type = type;

        for (auto &decl : type_cast<TagType>(type)->decls)
        {
          if (decl->kind() == Decl::Function && (decl->flags & FunctionDecl::Destructor))
            callee = find_callee(ctx, type, decl_cast<FunctionDecl>(decl)->name, parms, namedparms);
        }

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

    if (fx.fn->returntype)
    {
      Scope scope(fx.fn, fx.typeargs);

      returntype = MIR::Local(resolve_type(ctx, scope, fx.fn->returntype), MIR::Local::LValue);

      if (is_const_type(returntype.type) || is_qualarg_type(returntype.type))
        returntype.type = remove_const_type(returntype.type);

      returntype.defn = fx.fn->returntype;
    }

    if ((!fx.fn->returntype || is_typearg_type(returntype.type)) && fx.fn->body)
    {
      auto &mir = lower(fx, ctx.typetable, ctx.diag);

      if (mir.locals.empty() || !mir.locals[0])
      {
        ctx.diag.error("unable to determine function return type", fx.fn, fx.fn->loc());
        return ctx.voidtype;
      }

      returntype = mir.locals[0];
    }

    if ((fx.fn->flags & FunctionDecl::Builtin) && fx.fn->builtin == Builtin::CallOp)
      returntype.defn = returntype.type;

    returntype.flags &= ~MIR::Local::Const;
    returntype.flags &= ~MIR::Local::XValue;
    returntype.flags &= ~MIR::Local::Literal;
    returntype.flags &= ~MIR::Local::LValue;
    returntype.flags |= MIR::Local::RValue;

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

      case Type::Tuple:

        if (!is_tuple_type(rhs))
          return false;

        if (type_cast<TupleType>(lhs)->fields.size() == type_cast<TupleType>(rhs)->fields.size())
        {
          auto defns = type_cast<TupleType>(lhs)->defns;
          auto fields = type_cast<TupleType>(lhs)->fields;

          for (size_t i = 0; i < fields.size(); ++i)
            if (!promote_type(ctx, fields[i], type_cast<TupleType>(rhs)->fields[i]))
              return false;

          lhs = ctx.typetable.find_or_create<TupleType>(std::move(defns), std::move(fields));

          return true;
        }

        return false;

      default: {

        Scope fx;
        DeduceContext tx;

        tx.allow_const_downcast = true;
        tx.allow_object_downcast = false;
        tx.allow_pointer_downcast = false;

        if (deduce_type(ctx, tx, fx, fx, rhs, lhs))
        {
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
  bool lower_call(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, vector<MIR::Fragment> &parms, map<Ident*, MIR::Fragment> &namedparms, SourceLocation loc);

  //|///////////////////// realise //////////////////////////////////////////
  void realise(LowerContext &ctx, Place dst, MIR::Fragment &expr, long flags = 0)
  {
    if (flags & VarDecl::Const)
      expr.type.flags |= MIR::Local::Const;

    if (expr.value.kind() == MIR::RValue::Call && get<0>(expr.value.get<MIR::RValue::Call>()).fn->name == Ident::type_union)
    {
      auto &[callee, args, loc] = expr.value.get<MIR::RValue::Call>();

      auto tagtype = type_cast<TagType>(callee.fn->returntype);
      size_t kind = find(tagtype->fieldvars.begin(), tagtype->fieldvars.end(), callee.fn->args[0]) - tagtype->fieldvars.begin();

      callee = FnSig(decl_cast<FunctionDecl>(callee.fn->args[1]), std::move(callee.typeargs), callee.throwtype);

      if (callee.fn->flags & FunctionDecl::Builtin)
        expr.value = MIR::RValue::local(MIR::RValue::Val, args[0], loc);

      auto kinddst = ctx.add_temporary(tagtype->fields[0], MIR::Local::LValue | MIR::Local::Reference);
      auto kindres = ctx.add_temporary(tagtype->fields[0], MIR::Local::LValue | MIR::Local::Reference);

      auto datadst = ctx.add_temporary(tagtype->fields[kind], MIR::Local::LValue | MIR::Local::Reference);
      auto datares = ctx.add_temporary(tagtype->fields[kind], MIR::Local::LValue | MIR::Local::Reference);

      switch (dst.op)
      {
        case Place::Val:
          ctx.add_statement(MIR::Statement::assign(kinddst, MIR::RValue::field(MIR::RValue::Ref, dst.local, MIR::RValue::Field{ MIR::RValue::Ref, 0 }, loc)));
          ctx.add_statement(MIR::Statement::construct(kindres, MIR::RValue::literal(ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(kind), loc))));
          ctx.add_statement(MIR::Statement::assign(datadst, MIR::RValue::field(MIR::RValue::Ref, dst.local, MIR::RValue::Field{ MIR::RValue::Ref, kind }, loc)));
          ctx.add_statement(MIR::Statement::construct(datares, std::move(expr.value)));
          break;

        case Place::Fer:
          ctx.add_statement(MIR::Statement::assign(dst.local, MIR::RValue::cast(dst.local - 1, loc)));
          ctx.add_statement(MIR::Statement::assign(kinddst, MIR::RValue::field(MIR::RValue::Ref, dst.local, MIR::RValue::Field{ MIR::RValue::Val, 0 }, loc)));
          ctx.add_statement(MIR::Statement::construct(kindres, MIR::RValue::literal(ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(kind), loc))));
          ctx.add_statement(MIR::Statement::assign(datadst, MIR::RValue::field(MIR::RValue::Ref, dst.local, MIR::RValue::Field{ MIR::RValue::Val, kind }, loc)));
          ctx.add_statement(MIR::Statement::construct(datares, std::move(expr.value)));
          expr.type = resolve_as_value(ctx, expr.type);
          expr.type.flags |= MIR::Local::Reference;
          break;
      }

      return;
    }

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

    expr.type.flags &= ~MIR::Local::Literal;
  }

  //|///////////////////// realise_destructor ///////////////////////////////
  void realise_destructor(LowerContext &ctx, MIR::local_t arg, SourceLocation loc)
  {
    assert(!(ctx.mir.locals[arg].flags & MIR::Local::Reference));

    auto type = ctx.mir.locals[arg].type;

    if (auto callee = find_destructor(ctx, type, loc))
    {
      auto src = ctx.add_local();

      commit_type(ctx, src, type, MIR::Local::Reference);

      auto dst = ctx.add_local();

      commit_type(ctx, dst, ctx.voidtype);

      ctx.push_barrier();
      ctx.retiring_statement(MIR::Statement::storagedead(dst));
      ctx.retiring_statement(MIR::Statement::storagedead(src));
      ctx.retiring_statement(MIR::Statement::assign(dst, MIR::RValue::call(callee.fx, { src }, loc)));
      ctx.retiring_statement(MIR::Statement::assign(src, MIR::RValue::local(MIR::RValue::Ref, arg, loc)));
      ctx.retiring_statement(MIR::Statement::storagelive(dst));
      ctx.retiring_statement(MIR::Statement::storagelive(src));
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
      if (is_struct_type(expr.type.type) || is_union_type(expr.type.type) || is_vtable_type(expr.type.type) || is_array_type(expr.type.type) || is_tuple_type(expr.type.type) || is_lambda_type(expr.type.type) || is_function_type(expr.type.type))
      {
        vector<MIR::Fragment> parms(1);
        map<Ident*, MIR::Fragment> namedparms;

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

      expr.type.flags &= ~MIR::Local::Unaligned;
      expr.type.flags &= ~MIR::Local::Const;
    }

    realise(ctx, dst, expr, flags);
  }

  //|///////////////////// realise_as_value_type ////////////////////////////
  void realise_as_value_type(LowerContext &ctx, Place dst, MIR::Fragment &expr, long flags = 0)
  {
    if (is_tuple_type(expr.type.type))
    {
      if (auto type = resolve_value_type(ctx, expr.type.type); type != expr.type.type)
      {
        vector<MIR::Fragment> parms(1);
        map<Ident*, MIR::Fragment> namedparms;

        parms[0] = std::move(expr);

        auto callee = find_callee(ctx, type, parms, namedparms);

        if (!callee)
        {
          ctx.diag.error("cannot resolve copy constructor", ctx.stack.back(), parms[0].value.loc());
          diag_callee(ctx, callee, parms, namedparms);
          return;
        }

        lower_call(ctx, expr, callee.fx, parms, namedparms, parms[0].value.loc());
      }
    }

    realise_as_value(ctx, dst, expr, flags);
  }

  //|///////////////////// collapse_returns /////////////////////////////////
  void collapse_returns(LowerContext &ctx)
  {
    for (auto i = ctx.barriers.back().firstreturn; i < ctx.returns.size(); ++i)
      ctx.mir.blocks[ctx.returns[i]].terminator.blockid = ctx.currentblockid;

    ctx.returns.resize(ctx.barriers.back().firstreturn);
    ctx.returns.push_back(ctx.currentblockid);
  }

  //|///////////////////// literal_cast /////////////////////////////////////
  bool literal_cast(LowerContext &ctx, MIR::RValue &result, MIR::RValue const &expr, Type const *type)
  {
    assert(expr.kind() == MIR::RValue::Constant);

    auto value = expr.get<MIR::RValue::Constant>();

    if (holds_alternative<BoolLiteralExpr*>(value))
    {
      auto literal = get<BoolLiteralExpr*>(value);

      switch (type->klass())
      {
        case Type::Builtin:

          switch (type_cast<BuiltinType>(type)->kind())
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

        case Type::TypeArg:
          result = literal;
          return true;

        default:
        boolinvalid:
          ctx.diag.error("invalid literal cast", ctx.stack.back(), literal->loc());
          ctx.diag << "  cast type: '" << *type << "' from: '#bool'\n";
          break;
      }
    }

    if (holds_alternative<CharLiteralExpr*>(value))
    {
      auto literal = get<CharLiteralExpr*>(value);

      switch (type->klass())
      {
        case Type::Builtin:

          switch (type_cast<BuiltinType>(type)->kind())
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

        case Type::TypeArg:
          result = literal;
          return true;

        default:
        charinvalid:
          ctx.diag.error("invalid literal cast", ctx.stack.back(), literal->loc());
          ctx.diag << "  cast type: '" << *type << "' from: '#char'\n";
          break;
      }
    }

    if (holds_alternative<IntLiteralExpr*>(value))
    {
      auto literal = get<IntLiteralExpr*>(value);

      switch (type->klass())
      {
        case Type::Builtin:

          switch (type_cast<BuiltinType>(type)->kind())
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
            case BuiltinType::DeclidLiteral:
            case BuiltinType::TypeidLiteral:
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

        case Type::Tag:

          switch (type_cast<TagType>(type)->decl->kind())
          {
            case Decl::Enum:
              result = literal;
              return true;

            default:
              goto intinvalid;
          }

          break;

        case Type::Pointer:
          break;

        case Type::TypeArg:
          result = literal;
          return true;

        default:
        intinvalid:
          ctx.diag.error("invalid literal cast", ctx.stack.back(), literal->loc());
          ctx.diag << "  cast type: '" << *type << "' from: '#int'\n";
          break;
      }
    }

    if (holds_alternative<FloatLiteralExpr*>(value))
    {
      auto literal = get<FloatLiteralExpr*>(value);

      switch (type->klass())
      {
        case Type::Builtin:

          switch (type_cast<BuiltinType>(type)->kind())
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

        case Type::TypeArg:
          result = literal;
          return true;

        default:
        fltinvalid:
          ctx.diag.error("invalid literal cast", ctx.stack.back(), literal->loc());
          ctx.diag << "  cast type: '" << *type << "' from: '#float'\n";
          break;
      }
    }

    if (holds_alternative<PointerLiteralExpr*>(value))
    {
      auto literal = get<PointerLiteralExpr*>(value);

      switch (type->klass())
      {
        case Type::Builtin:

          switch (type_cast<BuiltinType>(type)->kind())
          {
            case BuiltinType::Bool:
              result = ctx.mir.make_expr<BoolLiteralExpr>(false, literal->loc());
              return true;

            default:
              goto ptrinvalid;
          }

          break;

        case Type::Pointer:
        case Type::TypeArg:
          result = literal;
          return true;

        default:
        ptrinvalid:
          ctx.diag.error("invalid literal cast", ctx.stack.back(), literal->loc());
          ctx.diag << "  cast type: '" << *type << "' from: 'null'\n";
          break;
      }
    }

    if (holds_alternative<StringLiteralExpr*>(value) && is_string_type(type))
    {
      result = get<StringLiteralExpr*>(value);

      return true;
    }

    if (holds_alternative<ArrayLiteralExpr*>(value) && is_array_type(type))
    {
      auto literal = get<ArrayLiteralExpr*>(value);

      if (!equals(type_cast<TypeLitType>(type_cast<ArrayType>(type)->size), type_cast<TypeLitType>(resolve_type(ctx, ctx.stack.back(), literal->size))))
        return false;

      auto elemtype = type_cast<ArrayType>(type)->type;

      if (literal->elements.size() != 0 && (
          (is_bool_type(elemtype) && literal->elements[0]->kind() != Expr::BoolLiteral) ||
          (is_char_type(elemtype) && literal->elements[0]->kind() != Expr::CharLiteral) ||
          (is_int_type(elemtype) && literal->elements[0]->kind() != Expr::IntLiteral) ||
          (is_float_type(elemtype) && literal->elements[0]->kind() != Expr::FloatLiteral) ||
          (is_string_type(elemtype) && literal->elements[0]->kind() != Expr::StringLiteral)))
      {
        vector<Expr*> elements;

        for (auto expr : literal->elements)
        {
          MIR::RValue value;

          if (!literal_cast(ctx, value, MIR::RValue::literal(expr), elemtype))
            return false;

          elements.push_back(std::visit([&](auto &v) -> Expr * { return v; }, value.get<MIR::RValue::Constant>()));
        }

        literal = ctx.mir.make_expr<ArrayLiteralExpr>(elements, literal->size, literal->loc());
      }

      result = literal;

      return true;
    }

    if (holds_alternative<CompoundLiteralExpr*>(value) && is_compound_type(type))
    {
      auto literal = get<CompoundLiteralExpr*>(value);

      if (type_cast<CompoundType>(type)->fields.size() != literal->fields.size())
        return false;

      vector<Expr*> elements;

      for (size_t i = 0; i < literal->fields.size(); ++i)
      {
        MIR::RValue value;

        if (!literal_cast(ctx, value, MIR::RValue::literal(literal->fields[i]), type_cast<CompoundType>(type)->fields[i]))
          return false;

        elements.push_back(std::visit([&](auto &v) -> Expr * { return v; }, value.get<MIR::RValue::Constant>()));
      }

      result = ctx.mir.make_expr<CompoundLiteralExpr>(elements, literal->loc());

      return true;
    }

    return false;
  }

  //|///////////////////// lower_lit ////////////////////////////////////////
  bool lower_lit(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, SourceLocation loc)
  {
    auto V = callee.find_type(callee.fn->args[1])->second;

    result.type = find_returntype(ctx, callee);
    result.type.flags = MIR::Local::Const | MIR::Local::Literal;
    result.value = MIR::RValue::literal(type_cast<TypeLitType>(V)->value);

    switch (auto expr = type_cast<TypeLitType>(V)->value; expr->kind())
    {
      case Expr::CharLiteral:
        result.value = ctx.mir.make_expr<CharLiteralExpr>(expr_cast<CharLiteralExpr>(expr)->value(), loc);
        break;

      case Expr::IntLiteral:
        result.value = ctx.mir.make_expr<IntLiteralExpr>(expr_cast<IntLiteralExpr>(expr)->value(), loc);
        break;

      case Expr::FloatLiteral:
        result.value = ctx.mir.make_expr<FloatLiteralExpr>(expr_cast<FloatLiteralExpr>(expr)->value(), loc);
        break;

      default:
        break;
    }

    return true;
  }

  //|///////////////////// lower_ctor ///////////////////////////////////////
  bool lower_ctor(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, MIR::Fragment &expr, SourceLocation loc)
  {
    if (expr.type.flags & MIR::Local::Reference)
    {
      auto arg = ctx.add_temporary();

      realise_as_value(ctx, arg, expr);

      commit_type(ctx, arg, expr.type.type, expr.type.flags);

      expr.value = MIR::RValue::local(MIR::RValue::Val, arg, loc);
    }

    result.type = find_returntype(ctx, callee);
    result.type.flags |= expr.type.flags & (MIR::Local::Const | MIR::Local::Literal);
    result.value = std::move(expr.value);

    return true;
  }

  //|///////////////////// lower_vtor ///////////////////////////////////////
  bool lower_vtor(LowerContext &ctx, MIR::Fragment &result, TagType *thistype, Type *selftype, SourceLocation loc)
  {
    size_t index = 0;
    vector<Expr*> elements;

    if (decl_cast<TagDecl>(thistype->decl)->basetype)
    {
      auto type = thistype->fields[0];

      if (!is_vtable_type(type))
      {
        ctx.diag.error("vtable base must be a vtable", thistype->fieldvars[0], loc);
        return false;
      }

      if (!lower_vtor(ctx, result, type_cast<TagType>(type), selftype, loc))
        return false;

      elements.push_back(std::visit([&](auto &v) -> Expr * { return v; }, result.value.get<MIR::RValue::Constant>()));

      index += 1;
    }

    for ( ; index < thistype->fields.size(); ++index)
    {
      auto type = thistype->fields[index];
      auto fntype = type_cast<FunctionType>(remove_qualifiers_type(type));
      auto decl = decl_cast<FieldVarDecl>(thistype->fieldvars[index]);

      Callee callee;
      vector<MIR::Fragment> parms;
      map<Ident*, MIR::Fragment> namedparms;

      for (auto &parm : type_cast<TupleType>(fntype->paramtuple)->fields)
      {
        MIR::Fragment value = { parm };

        if (is_reference_type(parm))
          value.type = resolve_as_reference(ctx, value.type);

        parms.push_back(value);
      }

      if (decl->flags & VarDecl::SelfImplicit)
      {
        parms[0].type.type = selftype;

        if (is_pointer_type(type_cast<TupleType>(fntype->paramtuple)->fields[0]))
        {
          if (is_const_pointer(type_cast<TupleType>(fntype->paramtuple)->fields[0]))
            parms[0].type = ctx.typetable.find_or_create<ConstType>(parms[0].type.type);

          parms[0].type = ctx.typetable.find_or_create<PointerType>(parms[0].type.type);
        }
      }

      FindContext tx(ctx, decl->name);

      auto impltype = remove_qualifiers_type(selftype);

      for (auto scope = type_scope(ctx, impltype); scope; scope = base_scope(ctx, scope, QueryFlags::Public))
      {
        find_overloads(ctx, tx, scope, parms, namedparms, callee.candidates, callee.overloads);
      }

      find_overloads(ctx, tx, scopeof_type(ctx, impltype), parms, namedparms, callee.candidates, callee.overloads);
      find_overloads(ctx, tx, scopeof_type(ctx, thistype), parms, namedparms, callee.candidates, callee.overloads);
      find_overloads(ctx, tx, ctx.stack, parms, namedparms, callee.candidates, callee.overloads);

      callee.overloads.erase(remove_if(callee.overloads.begin(), callee.overloads.end(), [&](auto &fx){

        if (fx.fn->parms.size() != parms.size())
          return true;

        if (is_throws(ctx, fx, parms, namedparms) && !(fntype->throwtype != ctx.voidtype))
          return true;

        if (find_returntype(ctx, fx).type != fntype->returntype)
          return true;

        return false;

      }), callee.overloads.end());

      if (callee.overloads.size() != 1)
      {
        auto override = find_if(callee.overloads.begin(), callee.overloads.end(), [&](auto &fx) { return (fx.fn->flags & FunctionDecl::Override); });

        if (override != callee.overloads.end())
          callee.overloads.erase(override + 1, callee.overloads.end());
      }

      if (callee.overloads.size() != 1)
      {
        ctx.diag.error("in vtable resolution", ctx.stack.back(), loc);
        ctx.diag.error("cannot resolve vtable function", decl, decl->loc());
        diag_callee(ctx, callee, parms, namedparms);
        continue;
      }

      callee.fx = callee.overloads[0];

      if (fntype->throwtype != ctx.voidtype)
        callee.fx.throwtype = fntype->throwtype;

      if (is_throws(ctx, callee.fx, parms, namedparms, &callee.fx.throwtype))
      {
        if (callee.fx.throwtype != fntype->throwtype)
        {
          ctx.diag.error("unable to resolve throw type", ctx.stack.back(), loc);
          return false;
        }
      }

      elements.push_back(ctx.mir.make_expr<FunctionPointerExpr>(callee.fx, decl->loc()));
    }

    result.type = MIR::Local(thistype, MIR::Local::Const | MIR::Local::Literal);
    result.value = ctx.mir.make_expr<CompoundLiteralExpr>(elements, loc);

    return true;
  }

  bool lower_vtor(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, SourceLocation loc)
  {
    auto thistype = find_returntype(ctx, callee).type;

    auto selftype = thistype;
    for (auto sx = ctx.stack.rbegin(); sx != ctx.stack.rend(); ++sx)
    {
      if (!is_tag_scope(*sx))
        continue;

      selftype = resolve_type(ctx, *sx, get<Decl*>(sx->owner));

      break;
    }

    if (!lower_vtor(ctx, result, type_cast<TagType>(thistype), selftype, loc))
      return false;

    return true;
  }

  //|///////////////////// lower_trait //////////////////////////////////////
  bool lower_trait(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, SourceLocation loc)
  {
    Type *args[2] = {};
    Type *type[2] = {};

    for (size_t i = 0; i < callee.fn->args.size(); ++i)
    {
      args[i] = callee.find_type(callee.fn->args[i])->second;
      type[i] = remove_const_type(args[i]);
    }

    bool match = false;

    switch (callee.fn->builtin)
    {
      case Builtin::is_const:
        match = is_const_type(args[0]) || (is_qualarg_type(args[0]) && (type_cast<QualArgType>(args[0])->qualifiers & QualArgType::Const));
        break;

      case Builtin::is_rvalue:
        match = is_qualarg_type(args[0]) && (type_cast<QualArgType>(args[0])->qualifiers & QualArgType::RValue);
        break;

      case Builtin::is_enum:
        match = is_enum_type(type[0]);
        break;

      case Builtin::is_array:
        match = is_array_type(type[0]);
        break;

      case Builtin::is_tuple:
        match = is_tuple_type(type[0]);
        break;

      case Builtin::is_union:
        match = is_union_type(type[0]);
        break;

      case Builtin::is_struct:
        match = is_struct_type(type[0]);
        break;

      case Builtin::is_vtable:
        match = is_vtable_type(type[0]);
        break;

      case Builtin::is_lambda:
        match = is_lambda_type(type[0]);
        break;

      case Builtin::is_slice:
        match = is_slice_type(type[0]);
        break;

      case Builtin::is_builtin:
        match = is_builtin_type(type[0]);
        break;

      case Builtin::is_pointer:
        match = is_pointference_type(type[0]);
        break;

      case Builtin::is_reference:
        match = is_reference_type(type[0]);
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

      case Builtin::is_unsigned:
        match = !is_signed_type(type[0]);
        break;

      case Builtin::is_floating_point:
        match = is_float_type(type[0]);
        break;

      case Builtin::is_arithmetic:
        match = is_int_type(type[0]) || is_char_type(type[0]) || is_float_type(type[0]);
        break;

      case Builtin::is_same:

        for (size_t i = 0; i < 2; ++i)
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
          return false;
        }

        if (auto typearg = type_cast<TypeArgType>(args[0]); typearg->koncept)
        {
          Scope sig;

          match = match_concept(ctx, ctx.stack.back(), sig, decl_cast<ConceptDecl>(typearg->koncept), typearg->args, type[1]);
        }

        break;

      default:
        assert(false);
    }

    result.type = MIR::Local(ctx.booltype, MIR::Local::Const | MIR::Local::Literal);
    result.value = ctx.mir.make_expr<BoolLiteralExpr>(match, loc);

    return true;
  }

  //|///////////////////// array_len ////////////////////////////////////////
  bool lower_array_len(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, SourceLocation loc)
  {
    auto type = remove_const_type(callee.find_type(callee.fn->args[0])->second);

    while (is_tag_type(type) && decl_cast<TagDecl>(type_cast<TagType>(type)->decl)->basetype && (type_cast<TagType>(type)->decl->flags & TagDecl::PublicBase))
      type = type_cast<TagType>(type)->fields[0];

    if (type_cast<TypeLitType>(type_cast<ArrayType>(type)->size)->value->kind() != Expr::IntLiteral)
      return false;

    result.type = MIR::Local(ctx.usizetype, MIR::Local::Const | MIR::Local::Literal);
    result.value = expr_cast<IntLiteralExpr>(type_cast<TypeLitType>(type_cast<ArrayType>(type)->size)->value);

    return true;
  }

  //|///////////////////// tuple_len ////////////////////////////////////////
  bool lower_tuple_len(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, SourceLocation loc)
  {
    auto type = remove_const_type(callee.find_type(callee.fn->args[0])->second);

    while (is_tag_type(type) && decl_cast<TagDecl>(type_cast<TagType>(type)->decl)->basetype && (type_cast<TagType>(type)->decl->flags & TagDecl::PublicBase))
      type = type_cast<TagType>(type)->fields[0];

    result.type = MIR::Local(ctx.usizetype, MIR::Local::Const | MIR::Local::Literal);
    result.value = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, type_cast<CompoundType>(type)->fields.size()), loc);

    return true;
  }

  //|///////////////////// lower_site ///////////////////////////////////////
  bool lower_site(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, SourceLocation loc)
  {
    vector<Expr*> fields;

    fields.push_back(ctx.mir.make_expr<StringLiteralExpr>(ctx.module->file(), loc));
    fields.push_back(ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(ctx.site_override.lineno != -1 ? ctx.site_override.lineno : ctx.site.lineno), loc));
    fields.push_back(ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(ctx.site_override.charpos != -1 ? ctx.site_override.charpos : ctx.site.charpos), loc));
    fields.push_back(ctx.mir.make_expr<StringLiteralExpr>(ctx.mir.fx.fn ? ctx.mir.fx.fn->name->str() : string(), loc));

    result.type = find_returntype(ctx, callee);
    result.type.flags = MIR::Local::Const | MIR::Local::Literal;
    result.value = ctx.mir.make_expr<CompoundLiteralExpr>(fields, loc);

    return true;
  }

  //|///////////////////// lower_declid /////////////////////////////////////
  bool lower_declid(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, SourceLocation loc)
  {
    Decl *declid = nullptr;

    for (auto sx = ctx.stack.rbegin(); sx != ctx.stack.rend(); ++sx)
    {
      if (auto owner = get_if<Decl*>(&sx->owner); owner && *owner)
      {
        if ((*owner)->kind() == Decl::If)
          continue;

        if ((*owner)->kind() == Decl::Run)
          continue;

        if ((*owner)->kind() == Decl::Function && (decl_cast<FunctionDecl>(*owner)->flags & FunctionDecl::DeclType) == FunctionDecl::RunDecl)
          continue;
      }

      switch (callee.fn->builtin)
      {
        case Builtin::__decl__:
          if (is_decl_scope(*sx))
            declid = get<Decl*>(sx->owner);
          break;

        case Builtin::__function__:
          if (is_fn_scope(*sx))
            declid = get<Decl*>(sx->owner);
          break;

        case Builtin::__module__:
          if (is_module_scope(*sx))
            declid = get<Decl*>(sx->owner);
          break;

        default:
          assert(false);
      }

      if (declid)
        break;
    }

    result.type = find_returntype(ctx, callee);
    result.type.flags = MIR::Local::Const | MIR::Local::Literal;
    result.value = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(0, reinterpret_cast<uintptr_t>(declid)), loc);

    return true;
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
    map<Ident*, MIR::Fragment> namedparms;

    parms[0] = expr;

    auto callee = find_callee(ctx, parms[0].type.type, Ident::op_deref, parms, namedparms);

    if (!callee || (callee.fx.fn->flags & FunctionDecl::Static))
      return false;

    if (!lower_call(ctx, result, callee.fx, parms, namedparms, loc))
      return false;

    return true;
  }

  //|///////////////////// lower_deref //////////////////////////////////////
  bool lower_base_deref(LowerContext &ctx, MIR::Fragment &base, SourceLocation loc)
  {
    switch (base.type.type->klass())
    {
      case Type::Pointer:
        if (!lower_deref(ctx, base, base, loc))
          return false;

        return true;

      case Type::Reference:
        if (base.type.flags & MIR::Local::Reference)
          lower_fer(ctx, base, base);

        base.type = resolve_as_reference(ctx, base.type);
        base.type.defn = remove_const_type(remove_reference_type(base.type.defn));

        return true;

      case Type::Tag:
        if (!lower_deref(ctx, base, base, loc))
          return false;

        return true;

      default:
        return false;
    }
  }

  //|///////////////////// lower_deref //////////////////////////////////////
  bool lower_expr_deref(LowerContext &ctx, MIR::Fragment &expr, SourceLocation loc)
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

  //|///////////////////// lower_deref //////////////////////////////////////
  bool lower_const_deref(LowerContext &ctx, MIR::Fragment &expr, SourceLocation loc)
  {
    if (expr.type.flags & MIR::Local::Const)
    {
      if (is_pointer_type(expr.type.type))
      {
        if (auto rhs = remove_pointer_type(expr.type.type); !is_const_type(rhs))
          expr.type.type = ctx.typetable.find_or_create<PointerType>(ctx.typetable.find_or_create<ConstType>(rhs));
      }

      if (is_reference_type(expr.type.type))
      {
        if (auto rhs = remove_reference_type(expr.type.type); !is_const_type(rhs))
          expr.type.type = ctx.typetable.find_or_create<ReferenceType>(ctx.typetable.find_or_create<ConstType>(rhs));
      }
    }

    return true;
  }

  //|///////////////////// lower_field //////////////////////////////////////
  bool lower_field(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &base, Field &field, SourceLocation loc)
  {
    if (base.value.kind() == MIR::RValue::Constant)
    {
      if (is_compound_type(base.type.type))
      {
        auto literal = get<CompoundLiteralExpr*>(base.value.get<MIR::RValue::Constant>());

        result.type = MIR::Local(field.type, base.type.flags);
        result.value = MIR::RValue::literal(literal->fields[field.index]);

        return true;
      }

      if (is_array_type(base.type.type))
      {
        auto literal = get<ArrayLiteralExpr*>(base.value.get<MIR::RValue::Constant>());

        result.type = MIR::Local(field.type, base.type.flags);
        result.value = MIR::RValue::literal(literal->elements[field.index]);

        return true;
      }
    }

    if (base.value.kind() != MIR::RValue::Variable || get<0>(base.value.get<MIR::RValue::Variable>()) == MIR::RValue::Fer)
    {
      auto arg = ctx.add_temporary();

      realise(ctx, arg, base);

      commit_type(ctx, arg, base.type.type, base.type.flags);

      if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
        realise_destructor(ctx, arg, loc);

      base.value = MIR::RValue::local(MIR::RValue::Val, arg, loc);
    }

    auto &[op, arg, fields, lloc] = base.value.get<MIR::RValue::Variable>();

    fields.push_back(MIR::RValue::Field{ (base.type.flags & MIR::Local::Reference) ? op : MIR::RValue::Ref, field.index });

    result.type = MIR::Local(field.type, field.defn, base.type.flags);

    if (field.flags & VarDecl::Const)
      result.type.flags |= MIR::Local::Const;

    if (field.flags & VarDecl::Mutable)
      result.type.flags &= ~MIR::Local::Const;

    if (base.type.type->flags & Type::Packed)
      result.type.flags |= MIR::Local::Unaligned;

    result.type.flags |= MIR::Local::Reference;
    result.value = MIR::RValue::field(MIR::RValue::Ref, arg, std::move(fields), loc);

#if TRANSATIVE_CONST
    if (!lower_const_deref(ctx, result, loc))
      return false;
#endif

    if (!lower_expr_deref(ctx, result, loc))
      return false;

    return true;
  }

  //|///////////////////// lower_base_cast //////////////////////////////////
  bool lower_base_cast(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &expr, Type *type, SourceLocation loc)
  {
    if (is_tag_type(expr.type.type))
    {
      if (expr.value.kind() == MIR::RValue::Constant)
        lower_ref(ctx, expr, expr);

      while (is_tag_type(expr.type.type))
      {
        if (expr.type.type == type)
          break;

        if (auto field = find_field(ctx, ctx.stack, expr.type.type, Ident::kw_super))
        {
          field.defn = ctx.typetable.var_defn;

          if (!lower_field(ctx, expr, expr, field, loc))
            return false;

          continue;
        }

        break;
      }
    }

    if (expr.type.type == ctx.ptrliteraltype)
    {
      if (expr.value.kind() == MIR::RValue::Constant)
        expr.type.type = type;
    }

    if (expr.type.type != type)
    {
      auto arg = ctx.add_temporary();

      realise_as_value(ctx, arg, expr);

      commit_type(ctx, arg, expr.type.type, expr.type.flags);

      expr.type = MIR::Local(type, (expr.type.flags & ~MIR::Local::LValue) | MIR::Local::RValue);
      expr.value = MIR::RValue::cast(arg, loc);
    }

    result.type = expr.type;
    result.value = expr.value;

    return true;
  }

  //|///////////////////// lower_impl_type //////////////////////////////////
  bool lower_impl_type(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &expr, Type *type, SourceLocation loc)
  {
    auto lhs = remove_const_type(remove_pointference_type(type));

    if (!lower_vtor(ctx, result, type_cast<TagType>(lhs), expr.type.type, loc))
      return false;

    if (is_pointer_type(type))
    {
      if (!(result.type.flags & MIR::Local::Reference))
        lower_ref(ctx, result, result);

      result.type = resolve_as_value(ctx, result.type);
    }

    return true;
  }

  //|///////////////////// lower_lambda_decay ///////////////////////////////
  bool lower_lambda_decay(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &expr, Scope const &scope, Type *type, SourceLocation loc)
  {
    FnSig callop;

    auto lhs = remove_const_type(remove_pointference_type(type));
    auto rhs = remove_const_type(remove_pointference_type(expr.type.type));

    if (!deduce_calltype(ctx, scope, callop, type_cast<FunctionType>(lhs), rhs))
    {
      ctx.diag.error("type mismatch", ctx.stack.back(), loc);
      ctx.diag << "  function type: '" << *rhs << "' wanted: '" << *lhs << "'\n";
      return false;
    }

    if (!is_pointference_type(type))
      expr.type.flags |= MIR::Local::Reference;
    else
      expr.type.flags &= ~MIR::Local::Reference;

    expr.type.flags &= ~MIR::Local::RValue;

    result.type = MIR::Local(type, expr.type.flags);
    result.value = MIR::RValue::literal(ctx.mir.make_expr<FunctionPointerExpr>(callop, loc));

    return true;
  }

  //|///////////////////// lower_function_cast /////////////////////////
  bool lower_function_cast(LowerContext &ctx, MIR::Fragment &result, Scope const &scope, FunctionType *fntype, Decl *decl, SourceLocation loc)
  {
    vector<MIR::Fragment> parms;
    map<Ident*, MIR::Fragment> namedparms;

    for (auto &parm : type_cast<TupleType>(fntype->paramtuple)->fields)
    {
      MIR::Fragment value = { parm };

      if (is_reference_type(parm))
        value.type = resolve_as_reference(ctx, value.type);

      parms.push_back(value);
    }

    auto callee = find_callee(ctx, ctx.stack, scope, decl, parms, namedparms);

    callee.overloads.erase(remove_if(callee.overloads.begin(), callee.overloads.end(), [&](auto &fx){

      if (fx.fn->parms.size() != parms.size())
        return true;

      if (is_throws(ctx, fx, parms, namedparms) && !(fntype->throwtype != ctx.voidtype))
        return true;

      if (find_returntype(ctx, fx).type != fntype->returntype)
        return true;

      return false;

    }), callee.overloads.end());

    if (callee.overloads.size() != 1)
    {
      ctx.diag.error("unable to resolve function cast", ctx.stack.back(), loc);
      diag_callee(ctx, callee, parms, namedparms);
      return false;
    }

    callee.fx = callee.overloads[0];

    if (fntype->throwtype != ctx.voidtype)
      callee.fx.throwtype = fntype->throwtype;

    if (is_throws(ctx, callee.fx, parms, namedparms, &callee.fx.throwtype))
    {
      if (callee.fx.throwtype != fntype->throwtype)
      {
        ctx.diag.error("unable to resolve throw type", ctx.stack.back(), loc);
        return false;
      }
    }

    result.type = MIR::Local(fntype, MIR::Local::Const | MIR::Local::Reference);
    result.value = MIR::RValue::literal(ctx.mir.make_expr<FunctionPointerExpr>(callee.fx, loc));

    return true;
  }

  //|///////////////////// lower_label //////////////////////////////////////
  bool lower_label(LowerContext &ctx, vector<size_t> &result, Type *type, Expr *label)
  {
    MIR::Fragment value;

    switch (label->kind())
    {
      case Expr::DeclRef: {
        vector<MIR::Fragment> parms;
        map<Ident*, MIR::Fragment> namedparms;

        if (auto callee = find_callee(ctx, ctx.stack, type_scope(ctx, type), expr_cast<DeclRefExpr>(label)->decl, parms, namedparms); callee)
        {
          if (!lower_call(ctx, value, callee.fx, parms, namedparms, label->loc()))
            return false;

          break;
        }
      }

      [[fallthrough]];

      default:

        if (is_tag_type(type))
          ctx.labelscope = type_scope(ctx, type);

        if (!lower_expr(ctx, value, label))
          return false;

        ctx.labelscope = {};
    }

    if (is_constant(ctx, value) && get_if<BoolLiteralExpr*>(&value.value.get<MIR::RValue::Constant>()))
    {
      auto literal = get<BoolLiteralExpr*>(value.value.get<MIR::RValue::Constant>());

      if (!is_int_type(type) && value.type.type != type)
      {
        ctx.diag.error("type mismatch on case label", ctx.stack.back(), label->loc());
        ctx.diag << "  label type: '" << *value.type.type << "' wanted: '" << *type << "'\n";
        return false;
      }

      result.push_back(literal->value());

      return true;
    }

    if (is_constant(ctx, value) && get_if<CharLiteralExpr*>(&value.value.get<MIR::RValue::Constant>()))
    {
      auto literal = get<CharLiteralExpr*>(value.value.get<MIR::RValue::Constant>());

      if (!is_int_type(type) && !is_char_type(type) && value.type.type != type)
      {
        ctx.diag.error("type mismatch on case label", ctx.stack.back(), label->loc());
        ctx.diag << "  label type: '" << *value.type.type << "' wanted: '" << *type << "'\n";
        return false;
      }

      result.push_back(literal->value().value);

      return true;
    }

    if (is_constant(ctx, value) && get_if<IntLiteralExpr*>(&value.value.get<MIR::RValue::Constant>()))
    {
      auto literal = get<IntLiteralExpr*>(value.value.get<MIR::RValue::Constant>());

      if (!is_int_type(type) && !is_char_type(type) && value.type.type != type)
      {
        ctx.diag.error("type mismatch on case label", ctx.stack.back(), label->loc());
        ctx.diag << "  label type: '" << *value.type.type << "' wanted: '" << *type << "'\n";
        return false;
      }

      result.push_back(literal->value().sign * literal->value().value);

      return true;
    }

    if (is_constant(ctx, value) && is_tuple_type(value.type.type))
    {
      auto tuple = get<CompoundLiteralExpr*>(value.value.get<MIR::RValue::Constant>());

      if (!is_int_type(type) && !is_char_type(type) && !(type_cast<TupleType>(value.type.type)->fields[0] == type && type_cast<TupleType>(value.type.type)->fields[1] == type))
      {
        ctx.diag.error("type mismatch on case range", ctx.stack.back(), label->loc());
        ctx.diag << "  label type: '" << *value.type.type << "' wanted: '" << *type << "'\n";
        return false;
      }

      Numeric::Int beg = {};
      Numeric::Int end = {};

      if (tuple->fields.size() == 2 && tuple->fields[0]->kind() == Expr::CharLiteral && tuple->fields[1]->kind() == Expr::CharLiteral)
      {
        beg = expr_cast<CharLiteralExpr>(tuple->fields[0])->value();
        end = expr_cast<CharLiteralExpr>(tuple->fields[1])->value();
      }

      if (tuple->fields.size() == 3 && tuple->fields[0]->kind() == Expr::CharLiteral && tuple->fields[1]->kind() == Expr::CharLiteral && tuple->fields[2]->kind() == Expr::VoidLiteral)
      {
        beg = expr_cast<CharLiteralExpr>(tuple->fields[0])->value();
        end = expr_cast<CharLiteralExpr>(tuple->fields[1])->value() + Numeric::int_literal(1);
      }

      if (tuple->fields.size() == 2 && tuple->fields[0]->kind() == Expr::IntLiteral && tuple->fields[1]->kind() == Expr::IntLiteral)
      {
        beg = expr_cast<IntLiteralExpr>(tuple->fields[0])->value();
        end = expr_cast<IntLiteralExpr>(tuple->fields[1])->value();
      }

      if (tuple->fields.size() == 3 && tuple->fields[0]->kind() == Expr::IntLiteral && tuple->fields[1]->kind() == Expr::IntLiteral && tuple->fields[2]->kind() == Expr::VoidLiteral)
      {
        beg = expr_cast<IntLiteralExpr>(tuple->fields[0])->value();
        end = expr_cast<IntLiteralExpr>(tuple->fields[1])->value() + Numeric::int_literal(1);
      }

      if (end <= beg || end - beg > Numeric::int_literal(256))
      {
        ctx.diag.error("invalid label range", ctx.stack.back(), label->loc());
        return false;
      }

      for (auto i = beg; i != end; i = i + Numeric::int_literal(1))
      {
        result.push_back(i.sign * i.value);
      }

      return true;
    }

    ctx.diag.error("invalid label expression", ctx.stack.back(), label->loc());

    return false;
  }

  //|///////////////////// lower_pack ///////////////////////////////////////
  bool lower_pack(LowerContext &ctx, MIR::Fragment &result, Scope const &scope, ParmVarDecl *parm, vector<MIR::Fragment> &exprs, size_t k, size_t n, SourceLocation loc)
  {
    auto tup = ctx.add_temporary();

    auto parmtype = resolve_type_as_value(ctx, scope, parm);
    auto tupletype = type_cast<TupleType>(remove_reference_type(parmtype));

    for (size_t i = k, index = 0; i < n; ++i, ++index)
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
        lower_base_cast(ctx, exprs[i], exprs[i], type, loc);

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
  bool lower_unpack(LowerContext &ctx, vector<MIR::Fragment> &parms, Expr *expr, SourceLocation loc)
  {
    MIR::Fragment base;

    if (!lower_expr(ctx, base, expr))
      return false;

    if (base.value.kind() != MIR::RValue::Constant)
    {
      auto arg = ctx.add_temporary();

      realise_as_reference(ctx, arg, base);

      commit_type(ctx, arg, base.type.type, base.type.flags);

      base.type = ctx.mir.locals[arg];
      base.value = MIR::RValue::local(MIR::RValue::Val, arg, loc);
    }

    if (!is_compound_type(base.type.type) && !is_array_type(base.type.type))
    {
      ctx.diag.error("compound type required", ctx.stack.back(), loc);
      return false;
    }

    auto values = vector<MIR::Fragment>();

    if (is_compound_type(base.type.type))
    {
      auto pack = type_cast<CompoundType>(base.type.type);

      for (size_t index = 0; index < pack->fields.size(); ++index)
      {
        values.push_back(base);

        auto field = find_field(ctx, pack, index);

        if (!lower_field(ctx, values.back(), values.back(), field, loc))
          return false;
      }
    }

    if (is_array_type(base.type.type))
    {
      auto pack = type_cast<ArrayType>(base.type.type);

      if (pack->size->klass() != Type::TypeLit || type_cast<TypeLitType>(pack->size)->value->kind() != Expr::IntLiteral)
      {
        ctx.diag.error("invalid array literal size", ctx.stack.back(), loc);
        return false;
      }

      for (size_t index = 0; index < array_len(pack); ++index)
      {
        values.push_back(base);

        auto field = find_field(ctx, pack, index);

        if (!lower_field(ctx, values.back(), values.back(), field, loc))
          return false;
      }
    }

    for (auto &value : values)
    {
      if (expr->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(expr)->op() == UnaryOpExpr::Fwd)
      {
        if ((value.type.flags & MIR::Local::XValue) && !(value.type.flags & MIR::Local::Const))
          value.type.flags = (value.type.flags & ~MIR::Local::XValue) | MIR::Local::RValue | MIR::Local::MoveRef;
      }

      if (!(value.type.flags & MIR::Local::MutRef) && !(expr->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(expr)->op() == UnaryOpExpr::Fwd))
      {
        if (!(value.type.flags & MIR::Local::RValue))
          value.type.flags |= MIR::Local::Const;
      }

      parms.push_back(std::move(value));
    }

    return true;
  }

  //|///////////////////// lower_expand /////////////////////////////////////
  bool lower_expand(LowerContext &ctx, vector<MIR::Fragment> &parms, Expr *expr, SourceLocation loc)
  {
    size_t iterations = size_t(-1);

    vector<Expr*> stack(1, expr);

    while (!stack.empty())
    {
      auto expr = stack.back();
      stack.pop_back();

      switch (expr->kind())
      {
        case Expr::Paren:
          stack.push_back(expr_cast<ParenExpr>(expr)->subexpr);
          break;

        case Expr::Named:
          stack.push_back(expr_cast<NamedExpr>(expr)->subexpr);
          break;

        case Expr::UnaryOp:
          stack.push_back(expr_cast<UnaryOpExpr>(expr)->subexpr);
          break;

        case Expr::BinaryOp:
          stack.push_back(expr_cast<BinaryOpExpr>(expr)->lhs);
          stack.push_back(expr_cast<BinaryOpExpr>(expr)->rhs);
          break;

        case Expr::Call:
          for (auto &parm : expr_cast<CallExpr>(expr)->parms)
            stack.push_back(parm);
          if (expr_cast<CallExpr>(expr)->base)
            stack.push_back(expr_cast<CallExpr>(expr)->base);
          break;

        case Expr::DeclRef:
          if (expr_cast<DeclRefExpr>(expr)->base)
            stack.push_back(expr_cast<DeclRefExpr>(expr)->base);
          break;

        case Expr::ExprRef:
          stack.push_back(expr_cast<ExprRefExpr>(expr)->subexpr);
          break;

        default:
          break;
      }

      if (auto declref = is_declrefdecl_expr(expr))
      {
        auto name = declref->name;

        if (name->kind() == Ident::Hash)
          name = static_cast<HashIdent*>(name)->value();

        if (auto vardecl = find_vardecl(ctx, ctx.stack, name); vardecl && is_pack_type(vardecl->type))
        {
          size_t len = 0;

          if (auto type = resolve_type(ctx, ctx.stack.back(), decl_cast<VarDecl>(vardecl)); is_tuple_type(type))
            len = tuple_len(type_cast<TupleType>(type));

          if (iterations == size_t(-1))
            iterations = len;

          if (iterations != len)
          {
            ctx.diag.error("inconsistent tuple sizes", ctx.stack.back(), loc);
            return false;
          }
        }
      }
    }

    if (iterations == size_t(-1))
    {
      ctx.diag.error("no expansion found", ctx.stack.back(), loc);
      return false;
    }

    auto old_expansion = ctx.pack_expansion;

    for (ctx.pack_expansion = 0; ctx.pack_expansion < iterations; ++ctx.pack_expansion)
    {
      if (expr->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(expr)->op() == UnaryOpExpr::Unpack)
      {
        if (!lower_unpack(ctx, parms, expr_cast<UnaryOpExpr>(expr)->subexpr, expr->loc()))
          return false;

        continue;
      }

      MIR::Fragment parm;

      if (!lower_expr(ctx, parm, expr))
        return false;

      parms.push_back(std::move(parm));
    }

    ctx.pack_expansion = old_expansion;

    return true;
  }

  //|///////////////////// lower_parms //////////////////////////////////////
  bool lower_parms(LowerContext &ctx, vector<MIR::Fragment> &parms, map<Ident*, MIR::Fragment> &namedparms, vector<Expr*> const &exprs, SourceLocation loc)
  {
    for (auto expr : exprs)
    {
      Ident *name = nullptr;

      if (expr->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(expr)->op() == UnaryOpExpr::Unpack)
      {
        expr = expr_cast<UnaryOpExpr>(expr)->subexpr;

        if (expr->kind() == Expr::Paren)
        {
          if (!lower_expand(ctx, parms, expr_cast<ParenExpr>(expr)->subexpr, expr->loc()))
            return false;
        }
        else
        {
          if (!lower_unpack(ctx, parms, expr, expr->loc()))
            return false;
        }

        continue;
      }

      MIR::Fragment parm;

      if (expr->kind() == Expr::Named)
      {
        name = expr_cast<NamedExpr>(expr)->name;
        expr = expr_cast<NamedExpr>(expr)->subexpr;
      }

      if (!lower_expr(ctx, parm, expr))
        return false;

      if (!(parm.type.flags & MIR::Local::MutRef) && !(expr->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(expr)->op() == UnaryOpExpr::Fwd))
      {
        if (!(parm.type.flags & MIR::Local::RValue))
          parm.type.flags |= MIR::Local::Const;
      }

      if (name)
        namedparms.emplace(name, std::move(parm));
      else
        parms.push_back(std::move(parm));
    }

    return true;
  }

  //|///////////////////// lower_call ///////////////////////////////////////
  bool lower_call(LowerContext &ctx, MIR::Fragment &result, FnSig &callee, vector<MIR::Fragment> &parms, map<Ident*, MIR::Fragment> &namedparms, SourceLocation loc)
  {
    if (callee.fn->flags & FunctionDecl::Deleted)
    {
      ctx.diag.error("call of deleted function", ctx.stack.back(), loc);
      return false;
    }

    // throw type

    if (is_throws(ctx, callee, parms, namedparms, &callee.throwtype))
    {
      if (!ctx.errorarg)
      {
        ctx.diag.error("throwing call outside try block", ctx.stack.back(), loc);
        return false;
      }

      if (is_typearg_type(callee.throwtype))
        callee.throwtype = ctx.mir.locals[ctx.errorarg].type;

      if (callee.throwtype != ctx.mir.locals[ctx.errorarg].type)
      {
        ctx.diag.error("throw type mismatch", ctx.stack.back(), loc);
        ctx.diag << "  throw type: '" << *callee.throwtype << "' wanted: '" << *ctx.mir.locals[ctx.errorarg].type << "'\n";
        return false;
      }
    }

    // bake parameters

    auto scope = Scope(callee.fn, std::move(callee.typeargs));

    for (size_t i = 0, k = 0; i < callee.fn->parms.size(); ++i)
    {
      scope.goalpost = callee.fn->parms[i];

      auto parm = decl_cast<ParmVarDecl>(callee.fn->parms[i]);
      auto parmtype = resolve_type_as_reference(ctx, scope, parm);

      if (parm->flags & VarDecl::Literal)
      {
        if (is_pack_type(parm->type))
        {
          parms.erase(parms.begin() + k, parms.begin() + k + tuple_len(type_cast<TupleType>(parmtype)));
        }

        else if (k < parms.size())
        {
          parms.erase(parms.begin() + k);
        }

        continue;
      }

      if (is_pack_type(parm->type))
      {
        auto n = k + tuple_len(type_cast<TupleType>(parmtype));

        parms.insert(parms.begin() + k, MIR::Fragment());

        lower_pack(ctx, parms[k], scope, parm, parms, k + 1, n + 1, loc);

        parms.erase(parms.begin() + k + 1, parms.begin() + n + 1);

        parmtype = parms[k].type.type;
      }

      if (parms.size() <= k)
      {
        if (auto j = namedparms.find(parm->name); j != namedparms.end())
        {
          parms.push_back(std::move(j->second));
        }

        else if (auto j = find_if(namedparms.begin(), namedparms.end(), [&](auto &k) { auto name = k.first->sv(); return name.back() == '?' && parm->name && name.substr(0, name.size()-1) == parm->name->sv(); }); j != namedparms.end())
        {
          parms.push_back(std::move(j->second));
        }

        else if (parm->defult)
        {
          MIR::Fragment expr;

          vector<Scope> stack;
          seed_stack(stack, scope);

          swap(stack, ctx.stack);
          swap(loc, ctx.site_override);

          if (!lower_expr(ctx, expr, parm->defult))
          {
            swap(ctx.stack, stack);
            return false;
          }

          if (expr.type.type != parmtype)
          {
            if (!deduce_type(ctx, ctx.stack.back(), scope, parm, expr.type))
            {
              ctx.diag.error("type mismatch", ctx.stack.back(), parm->defult->loc());
              ctx.diag << "  parameter type: '" << *expr.type.type << "' wanted: '" << *parm->type << "'\n";
              swap(ctx.stack, stack);
              return false;
            }

            parmtype = resolve_type_as_reference(ctx, scope, parm);
          }

          parms.push_back(std::move(expr));

          swap(ctx.site_override, loc);
          swap(ctx.stack, stack);
        }
      }

      if (is_refn_type(ctx, parm))
      {
        if (auto refn = find_refn(ctx, scope, parm, parms[k].type); refn.fn)
        {
          vector<MIR::Fragment> callparms(1);
          map<Ident*, MIR::Fragment> callnamedparms;

          callparms[0] = std::move(parms[k]);

          lower_call(ctx, parms[k], refn, callparms, callnamedparms, callparms[0].value.loc());

          parmtype = parms[k].type.type;
        }
      }

      if (is_impl_type(ctx, parmtype, parms[k].type))
      {
        if (!lower_impl_type(ctx, parms[k], parms[k], parmtype, parms[k].value.loc()))
          return false;
      }

      if (is_lambda_decay(ctx, parmtype, parms[k].type.type))
      {
        if (!lower_lambda_decay(ctx, parms[k], parms[k], scope, parmtype, parms[k].value.loc()))
          return false;
      }

      if (is_base_cast(ctx, parmtype, parms[k].type.type))
      {
        if (!lower_base_cast(ctx, parms[k], parms[k], parmtype, parms[k].value.loc()))
          return false;
      }

      parms[k].type.type = parmtype;

      k += 1;
    }

    callee = FnSig(callee.fn, std::move(scope.typeargs), callee.throwtype);

    // handle const builtins

    if (callee.fn->flags & FunctionDecl::Builtin)
    {
      switch (callee.fn->builtin)
      {
        case Builtin::Type_Void:
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
        case Builtin::Type_DeclidLiteral:
        case Builtin::Type_TypeidLiteral:
        case Builtin::Type_PtrLiteral:
        case Builtin::Type_Ptr:
        case Builtin::Type_Ref:
        case Builtin::Type_Enum:
          lower_ctor(ctx, result, callee, parms[0], loc);
          return true;

        case Builtin::Type_Lit:
          lower_lit(ctx, result, callee, loc);
          return true;

        case Builtin::VTable_Constructor:
          lower_vtor(ctx, result, callee, loc);
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
        case Builtin::is_enum:
        case Builtin::is_array:
        case Builtin::is_tuple:
        case Builtin::is_union:
        case Builtin::is_struct:
        case Builtin::is_vtable:
        case Builtin::is_lambda:
        case Builtin::is_slice:
        case Builtin::is_builtin:
        case Builtin::is_pointer:
        case Builtin::is_reference:
        case Builtin::is_trivial_copy:
        case Builtin::is_trivial_assign:
        case Builtin::is_trivial_destroy:
        case Builtin::is_integral:
        case Builtin::is_unsigned:
        case Builtin::is_floating_point:
        case Builtin::is_arithmetic:
        case Builtin::is_same:
        case Builtin::is_match:
          lower_trait(ctx, result, callee, loc);
          return true;

        case Builtin::__site__:
          lower_site(ctx, result, callee, loc);
          return true;

        case Builtin::__decl__:
        case Builtin::__function__:
        case Builtin::__module__:
          lower_declid(ctx, result, callee, loc);
          return true;

        default:
          break;
      }
    }

    // return type

    result.type = find_returntype(ctx, callee);

    if (is_function_type(result.type.type))
      ctx.diag.error("cannot return a function type", ctx.stack.back(), loc);

    if (is_unresolved_type(result.type.type))
      ctx.diag.error("unresolved return type", ctx.stack.back(), loc);

    if (is_reference_type(result.type.defn))
    {
      result.type = resolve_as_reference(ctx, result.type);

      if ((result.type.flags & MIR::Local::XValue) && !(result.type.flags & MIR::Local::Const))
        result.type.flags = (result.type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;

      if ((callee.fn->flags & FunctionDecl::Builtin) && callee.fn->builtin == Builtin::ArrayIndex)
        result.type.flags |= (parms[0].type.flags & MIR::Local::RValue);

      result.type.defn = remove_const_type(remove_reference_type(result.type.defn));
    }

    // constant fold

    if (callee.fn->flags & FunctionDecl::Const)
    {
      if (all_of(parms.begin(), parms.end(), [](auto &k) { return k.type.flags & MIR::Local::Literal; }) && is_literal_copy_type(result.type.type) && !(result.type.flags & MIR::Local::Reference))
      {
        vector<EvalResult> arglist;

        for (auto &parm : parms)
        {
          EvalResult arg;

          arg.type = parm.type.type;
          arg.value = std::visit([&](auto &v) -> Expr * { return v; }, parm.value.get<MIR::RValue::Constant>());

          arglist.push_back(arg);
        }

        if (auto expr = evaluate(ctx.stack.back(), callee, result.type.type, arglist, ctx.typetable, ctx.diag, loc))
        {
          lower_expr(ctx, result, expr.value);

          result.type.type = expr.type;

          return true;
        }
      }

      if ((callee.fn->flags & FunctionDecl::DeclType) == FunctionDecl::ConstDecl)
        ctx.diag.error("non literal value", ctx.stack.back(), loc);
    }

    // resolve call

    vector<MIR::local_t> arglist;

    for (auto const &[parm, expr] : zip(callee.parameters(), parms))
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

    if (!lower_expr_deref(ctx, result, loc))
      return false;

    if (callee.fn->flags & FunctionDecl::NoReturn)
      ctx.unreachable = Unreachable::Yes;

    return true;
  }

  //|///////////////////// lower_cast ///////////////////////////////////////
  bool lower_cast(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &expr, Type *type, SourceLocation loc)
  {
    vector<MIR::Fragment> parms(1);
    map<Ident*, MIR::Fragment> namedparms;

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
  bool lower_new(LowerContext &ctx, MIR::Fragment &result, Type *type, vector<MIR::Fragment> &parms, map<Ident*, MIR::Fragment> &namedparms, SourceLocation loc)
  {
    if (type->klass() == Type::TypeLit)
    {
      result.type = type;
      return true;
    }

    if (parms.size() == 1 && namedparms.size() == 0 && parms[0].type.type == type && (parms[0].type.flags & MIR::Local::RValue))
    {
      result = std::move(parms[0]);
      return true;
    }

    auto callee = find_callee(ctx, type, parms, namedparms);

    if (!callee)
    {
      ctx.diag.error("cannot resolve constructor", ctx.stack.back(), loc);
      ctx.diag << "  for type: " << *type << '\n';
      diag_callee(ctx, callee, parms, namedparms);
      return false;
    }

    if (!lower_call(ctx, result, callee.fx, parms, namedparms, loc))
      return false;

    return true;
  }

  //|///////////////////// lower_new ////////////////////////////////////////
  bool lower_new(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &address, Type *type, vector<MIR::Fragment> &parms, map<Ident*, MIR::Fragment> &namedparms, SourceLocation loc)
  {
    auto dst = ctx.add_temporary();
    auto res = ctx.add_temporary();

    realise_as_value(ctx, dst, address);

    commit_type(ctx, dst, address.type.type, address.type.flags);

    if (!lower_new(ctx, result, type, parms, namedparms, loc))
      return false;

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
    }

    return true;
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
    }

    return true;
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
    result.type = MIR::Local(ctx.ptrliteraltype, MIR::Local::Literal | MIR::Local::RValue);
    result.value = ptrliteral;
  }

  //|///////////////////// lower_fnptr //////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, FunctionPointerExpr *functionpointer)
  {
    result.type = MIR::Local(ctx.ptrliteraltype, MIR::Local::Literal | MIR::Local::RValue);
    result.value = functionpointer;
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
    auto elemtype = ctx.typetable.var_defn;

    if (arrayliteral->coercedtype)
    {
      elemtype = resolve_type(ctx, arrayliteral->coercedtype);
    }

    auto size = resolve_type(ctx, arrayliteral->size);

    if (size->klass() != Type::TypeLit || type_cast<TypeLitType>(size)->value->kind() != Expr::IntLiteral)
    {
      ctx.diag.error("invalid array literal size", ctx.stack.back(), arrayliteral->loc());
      return;
    }

    if (all_of(arrayliteral->elements.begin(), arrayliteral->elements.end(), [](auto expr) { return is_literal_expr(expr); }))
    {
      if (elemtype == ctx.typetable.var_defn && arrayliteral->elements.size() != 0)
      {
        elemtype = find_type(ctx, ctx.stack, arrayliteral->elements[0]).type;

        if (!elemtype)
          return;
      }

      for (auto &element : arrayliteral->elements)
      {
        if ((is_bool_type(elemtype) && element->kind() != Expr::BoolLiteral) ||
            (is_char_type(elemtype) && (element->kind() != Expr::IntLiteral && element->kind() != Expr::CharLiteral)) ||
            (is_int_type(elemtype) && element->kind() != Expr::IntLiteral) ||
            (is_float_type(elemtype) && element->kind() != Expr::FloatLiteral) ||
            (is_string_type(elemtype) && element->kind() != Expr::StringLiteral) ||
            (is_array_type(elemtype) && (element->kind() != Expr::ArrayLiteral || expr_cast<IntLiteralExpr>(type_cast<TypeLitType>(expr_cast<ArrayLiteralExpr>(element)->size)->value)->value().value != array_len(type_cast<ArrayType>(elemtype)))) ||
            (is_compound_type(elemtype) && (element->kind() != Expr::CompoundLiteral || expr_cast<CompoundLiteralExpr>(element)->fields.size() != type_cast<CompoundType>(elemtype)->fields.size())))
        {
          ctx.diag.error("literal type incompatible with required type", ctx.stack.back(), element->loc());
          ctx.diag << "  required type: '" << *elemtype << "'\n";
          return;
        }
      }

      result.type = MIR::Local(ctx.typetable.find_or_create<ArrayType>(elemtype, size), MIR::Local::Const | MIR::Local::Literal);
      result.value = arrayliteral;
      return;
    }

    vector<MIR::Fragment> values;
    map<Ident*, MIR::Fragment> namedvalues;

    if (!lower_parms(ctx, values, namedvalues, arrayliteral->elements, arrayliteral->loc()))
      return;

    for (auto &value : values)
    {
      promote_type(ctx, elemtype, value.type.type);
    }

    if (values.size() != arrayliteral->elements.size())
    {
      size = ctx.typetable.find_or_create<TypeLitType>(ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, values.size()), arrayliteral->loc()));
    }

    auto type = ctx.typetable.find_or_create<ArrayType>(elemtype, size);

    if (all_of(values.begin(), values.end(), [](auto &value) { return value.type.flags & MIR::Local::Literal; }))
    {
      vector<Expr*> elements(values.size());

      for (size_t index = 0; index < values.size(); ++index)
      {
        elements[index] = std::visit([&](auto &v) { return static_cast<Expr*>(v); }, values[index].value.get<MIR::RValue::Constant>());
      }

      result.type = MIR::Local(type, MIR::Local::Const | MIR::Local::Literal);
      result.value = ctx.mir.make_expr<ArrayLiteralExpr>(elements, size, arrayliteral->loc());

      return;
    }

    auto arg = ctx.add_temporary();
    auto len = expr_cast<IntLiteralExpr>(type_cast<TypeLitType>(size)->value)->value().value;

    auto typeref = ctx.typetable.find_or_create<ReferenceType>(elemtype);

    for (size_t index = 0; index < values.size(); ++index)
    {
      auto dst = ctx.add_temporary();
      auto res = ctx.add_temporary();

      MIR::Fragment address;
      address.type = MIR::Local(typeref, MIR::Local::LValue);
      address.value = MIR::RValue::field(MIR::RValue::Ref, arg, MIR::RValue::Field{ MIR::RValue::Ref, index }, arrayliteral->loc());

      realise_as_value(ctx, dst, address);

      commit_type(ctx, dst, address.type.type, address.type.flags);

      MIR::Fragment result;
      vector<MIR::Fragment> parms(1);
      map<Ident*, MIR::Fragment> namedparms;

      parms[0] = std::move(values[index]);

      if (!lower_new(ctx, result, elemtype, parms, namedparms, parms[0].value.loc()))
        return;

      realise_as_value(ctx, Place(Place::Fer, res), result);

      commit_type(ctx, res, result.type.type, result.type.flags);
    }

    if (values.size() < len)
    {
      auto inc = find_builtin(ctx, Builtin::PreInc, typeref);
      auto cmp = find_builtin(ctx, Builtin::NE, typeref);

      auto dst = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto res = ctx.add_temporary();
      auto end = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto dsr = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto dsi = ctx.add_temporary(typeref, MIR::Local::LValue | MIR::Local::Reference);
      auto flg = ctx.add_temporary(ctx.booltype, MIR::Local::LValue);

      ctx.add_statement(MIR::Statement::assign(dst, MIR::RValue::field(MIR::RValue::Ref, arg, MIR::RValue::Field{ MIR::RValue::Ref, 1 }, arrayliteral->loc())));
      ctx.add_statement(MIR::Statement::assign(end, MIR::RValue::field(MIR::RValue::Ref, arg, MIR::RValue::Field{ MIR::RValue::Ref, len }, arrayliteral->loc())));
      ctx.add_statement(MIR::Statement::assign(dsr, MIR::RValue::local(MIR::RValue::Ref, dst, arrayliteral->loc())));

      auto block_head = ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

      MIR::Fragment result;
      vector<MIR::Fragment> parms(1);
      map<Ident*, MIR::Fragment> namedparms;

      parms[0].type = elemtype;
      parms[0].value = MIR::RValue::field(MIR::RValue::Val, arg, MIR::RValue::Field{ MIR::RValue::Ref, 0 }, arrayliteral->loc());

      if (!lower_new(ctx, result, elemtype, parms, namedparms, arrayliteral->loc()))
        return;

      realise_as_value(ctx, Place(Place::Fer, res), result);

      commit_type(ctx, res, result.type.type, result.type.flags);

      ctx.add_statement(MIR::Statement::assign(dsi, MIR::RValue::call(inc, { dsr }, arrayliteral->loc())));
      ctx.add_statement(MIR::Statement::assign(flg, MIR::RValue::call(cmp, { dst, end }, arrayliteral->loc())));
      ctx.add_block(MIR::Terminator::switcher(flg, ctx.currentblockid + 1, block_head + 1));
    }

    commit_type(ctx, arg, type, MIR::Local::RValue);

    if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
      realise_destructor(ctx, arg, arrayliteral->loc());

    result.type = MIR::Local(type, MIR::Local::RValue | MIR::Local::Reference);
    result.value = MIR::RValue::local(MIR::RValue::Ref, arg, arrayliteral->loc());
  }

  //|///////////////////// lower_compound ///////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, CompoundLiteralExpr *compoundliteral)
  {
    vector<Type*> defns;
    vector<Type*> fields;

    vector<MIR::Fragment> values;
    map<Ident*, MIR::Fragment> namedvalues;

    if (!lower_parms(ctx, values, namedvalues, compoundliteral->fields, compoundliteral->loc()))
      return;

    for (size_t index = 0; index < values.size(); ++index)
    {
      defns.push_back(resolve_defn(ctx, values[index].type.defn));
      fields.push_back(values[index].type.type);
    }

    auto type = ctx.typetable.find_or_create<TupleType>(std::move(defns), std::move(fields));

    if (all_of(values.begin(), values.end(), [](auto &k) { return k.type.flags & MIR::Local::Literal; }))
    {
      vector<Expr*> elements(values.size());

      for (size_t index = 0; index < values.size(); ++index)
      {
        elements[index] = std::visit([&](auto &v) { return static_cast<Expr*>(v); }, values[index].value.get<MIR::RValue::Constant>());
      }

      result.type = MIR::Local(type, MIR::Local::Const | MIR::Local::Literal);
      result.value = ctx.mir.make_expr<CompoundLiteralExpr>(elements, compoundliteral->loc());

      return;
    }

    auto arg = ctx.add_temporary();

    for (size_t index = 0; index < values.size(); ++index)
    {
      auto dst = ctx.add_temporary();
      auto res = ctx.add_temporary();

      MIR::Fragment address;
      address.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(type->fields[index]), MIR::Local::LValue);
      address.value = MIR::RValue::field(MIR::RValue::Ref, arg, MIR::RValue::Field{ MIR::RValue::Ref, index }, compoundliteral->loc());

      realise_as_value(ctx, dst, address);

      commit_type(ctx, dst, address.type.type, address.type.flags);

      realise_as_value(ctx, Place(Place::Fer, res), values[index]);

      commit_type(ctx, res, values[index].type.type, values[index].type.flags);
    }

    commit_type(ctx, arg, type, MIR::Local::RValue);

    if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
      realise_destructor(ctx, arg, compoundliteral->loc());

    result.type = MIR::Local(type, MIR::Local::RValue | MIR::Local::Reference);
    result.value = MIR::RValue::local(MIR::RValue::Ref, arg, compoundliteral->loc());
  }

  //|///////////////////// lower_paren //////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, ParenExpr *paren)
  {
    assert(paren->subexpr);

    lower_expr(ctx, result, paren->subexpr);
  }

  //|///////////////////// lower_vardecl ////////////////////////////////////
  bool lower_expr(LowerContext &ctx, MIR::Fragment &result, VarDecl *vardecl, SourceLocation loc)
  {
    auto j = ctx.locals.find(vardecl);

    if (j == ctx.locals.end())
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

            if (is_pack_type(vardecl->type) && ctx.pack_expansion != size_t(-1))
            {
              if (auto field = find_field(ctx, type_cast<TupleType>(result.type.type), ctx.pack_expansion))
              {
                if (!lower_field(ctx, result, result, field, loc))
                  return false;
              }
            }

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
        if (ctx.mir.fx.fn)
        {
          MIR::Fragment base;

          if (ctx.mir.fx.fn->flags & FunctionDecl::Constructor)
          {
            base.type = ctx.mir.locals[0];
            base.value = MIR::RValue::local(MIR::RValue::Ref, 0, loc);
          }
          else
          {
            auto arg = ctx.mir.fx.throwtype ? 2 : 1;
            base.type = resolve_as_reference(ctx, ctx.mir.locals[arg]);
            base.value = MIR::RValue::local(MIR::RValue::Val, arg, loc);
          }

          if (auto field = find_field(ctx, ctx.stack, base.type.type, decl_cast<FieldVarDecl>(vardecl)->name))
          {
            if (!lower_field(ctx, result, base, field, loc))
              return false;

            return true;
          }
        }
      }

      if (ctx.suppressed.find(vardecl) == ctx.suppressed.end())
        ctx.diag.error("variable not defined in this context", ctx.stack.back(), loc);

      ctx.suppressed[vardecl] = true;

      return false;
    }

    auto arg = j->second;
    result.type = MIR::Local(ctx.mir.locals[arg].type, vardecl->type, MIR::Local::LValue | MIR::Local::Reference);
    result.value = MIR::RValue::local(MIR::RValue::Ref, arg, loc);

    if (ctx.mir.locals[arg].flags & MIR::Local::Const)
      result.type.flags |= MIR::Local::Const;

    if (is_pack_type(vardecl->type))
    {
      lower_fer(ctx, result, result);

      result.type = resolve_as_reference(ctx, result.type);

      if (ctx.pack_expansion != size_t(-1))
      {
        if (auto field = find_field(ctx, type_cast<TupleType>(result.type.type), ctx.pack_expansion))
        {
          if (!lower_field(ctx, result, result, field, loc))
            return false;
        }
      }
    }

    if (!lower_expr_deref(ctx, result, loc))
      return false;

    return true;
  }

  //|///////////////////// lower_declref /////////////////////////////////////
  bool lower_expr(LowerContext &ctx, MIR::Fragment &result, MIR::Fragment &base, DeclRefExpr *declref)
  {
    Scope basescope;
    vector<MIR::Fragment> parms(1);
    map<Ident*, MIR::Fragment> namedparms;

    parms[0] = std::move(base);

    for (;;)
    {
      auto name = decl_cast<DeclRefDecl>(declref->decl)->name;

#if !ASSOCIATED_DEREF
      while (is_pointference_type(parms[0].type.type))
        if (!lower_base_deref(ctx, parms[0], declref->loc()))
          return false;
#endif

      basescope = type_scope(ctx, parms[0].type.type);

      if (decl_cast<DeclRefDecl>(declref->decl)->argless)
      {
        if (name->kind() == Ident::Index || name->kind() == Ident::Hash)
        {
          if (auto field = find_field(ctx, ctx.stack, parms[0].type.type, name))
          {
            if (!lower_field(ctx, result, parms[0], field, declref->loc()))
              return false;

            return true;
          }

          ctx.diag.error("cannot resolve function reference", ctx.stack.back(), declref->loc());
          return false;
        }

        for (auto type = parms[0].type.type; is_tag_type(type); )
        {
          auto tagtype = type_cast<TagType>(type);

          if (auto field = find_field(ctx, ctx.stack, tagtype, name))
          {
            if ((field.flags & Decl::Public) || get_module(tagtype->decl) == ctx.module)
            {
              while (parms[0].type.type != type)
              {
                if (auto field = find_field(ctx, ctx.stack, parms[0].type.type, Ident::kw_super))
                {
                  lower_field(ctx, parms[0], parms[0], field, declref->loc());
                }
              }

              lower_field(ctx, result, parms[0], field, declref->loc());

              return true;
            }
          }

          if (!decl_cast<TagDecl>(tagtype->decl)->basetype || !(tagtype->decl->flags & TagDecl::PublicBase))
            break;

          type = tagtype->fields[0];
        }
      }

      auto callee = find_callee(ctx, ctx.stack, basescope, declref->decl, parms, namedparms);

      if (!callee)
      {
#if ASSOCIATED_DEREF
        auto base = parms[0];

        if (lower_base_deref(ctx, base, declref->loc()))
        {
          callee = find_callee(ctx, ctx.stack, type_scope(ctx, base.type.type), declref->decl, parms, namedparms);

          if (!callee)
          {
            parms[0] = std::move(base);
            continue;
          }
        }
#else
        if (lower_base_deref(ctx, parms[0], declref->loc()))
          continue;
#endif

        ctx.diag.error("cannot resolve function reference", ctx.stack.back(), declref->loc());
        diag_callee(ctx, callee, parms, namedparms);
        return false;
      }

      if (!lower_call(ctx, result, callee.fx, parms, namedparms, declref->loc()))
        return false;

      return true;
    }
  }

  //|///////////////////// lower_declref /////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, DeclRefExpr *declref)
  {
    Scope basescope;
    vector<MIR::Fragment> parms;
    map<Ident*, MIR::Fragment> namedparms;

    if (declref->base)
    {
      parms.resize(1);

      if (!lower_expr(ctx, parms[0], declref->base))
        return;
    }

    if (declref->decl->kind() == Decl::DeclRef)
    {
      auto name = decl_cast<DeclRefDecl>(declref->decl)->name;

      if (declref->base)
      {
        lower_expr(ctx, result, parms[0], declref);

        return;
      }

      if (decl_cast<DeclRefDecl>(declref->decl)->argless)
      {
        if (auto vardecl = find_vardecl(ctx, ctx.stack, name))
        {
          lower_expr(ctx, result, vardecl, declref->loc());

          return;
        }
      }
    }

    auto callee = find_callee(ctx, ctx.stack, basescope, declref->decl, parms, namedparms);

    if (!callee)
    {
      ctx.diag.error("cannot resolve function reference", ctx.stack.back(), declref->loc());
      diag_callee(ctx, callee, parms, namedparms);
      return;
    }

    if (callee.fx.fn->flags & FunctionDecl::Constructor)
      ctx.diag.error("cannot call constructor without parenthesis", ctx.stack.back(), declref->loc());

    lower_call(ctx, result, callee.fx, parms, namedparms, declref->loc());
  }

  //|///////////////////// lower_exprref ////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, ExprRefExpr *exprref)
  {
    if (!lower_expr(ctx, result, exprref->subexpr))
      return;

    if (exprref->qualifiers & ExprRefExpr::Mut)
    {
      if (result.type.flags & MIR::Local::Const)
        ctx.diag.error("invalid mut reference type", ctx.stack.back(), exprref->subexpr->loc());

      result.type.flags |= MIR::Local::MutRef;
    }

    if (exprref->qualifiers & ExprRefExpr::Move)
    {
      result.type.flags = (result.type.flags & ~MIR::Local::LValue) | MIR::Local::RValue | MIR::Local::MoveRef;

      if (is_tuple_type(result.type.type))
      {
        auto defns = type_cast<TupleType>(result.type.type)->defns;
        auto fields = type_cast<TupleType>(result.type.type)->fields;

        for (size_t i = 0; i < fields.size(); ++i)
        {
          if (is_reference_type(defns[i]))
          {
            fields[i] = remove_reference_type(fields[i]);

            if (!(is_const_type(fields[i]) || (is_qualarg_type(fields[i]) && (type_cast<QualArgType>(fields[i])->qualifiers & QualArgType::Const))))
              fields[i] = ctx.typetable.find_or_create<QualArgType>(QualArgType::RValue, remove_const_type(fields[i]));

            fields[i] = ctx.typetable.find_or_create<ReferenceType>(fields[i]);
          }
        }

        result.type.type = ctx.typetable.find_or_create<TupleType>(std::move(defns), std::move(fields));
      }
    }

    if (exprref->qualifiers & ExprRefExpr::Impl)
    {
      result.type.flags |= MIR::Local::ImplRef;
    }
  }

  //|///////////////////// lower_unaryop ////////////////////////////////////
  bool lower_expr(LowerContext &ctx, MIR::Fragment &result, UnaryOpExpr::OpCode unaryop, vector<MIR::Fragment> &parms, map<Ident*, MIR::Fragment> &namedparms, SourceLocation loc)
  {
    if (unaryop == UnaryOpExpr::Unpack)
    {
      ctx.diag.error("invalid unpack", ctx.stack.back(), loc);

      return false;
    }

    if (unaryop == UnaryOpExpr::Ref && (parms[0].type.flags & MIR::Local::Literal))
    {
      if (is_array_type(parms[0].type.type) || is_compound_type(parms[0].type.type))
        lower_ref(ctx, parms[0], parms[0]); // This really should be a LiteralPointerExpr
    }

    if (unaryop == UnaryOpExpr::Ref && (parms[0].type.flags & MIR::Local::Reference))
    {
      result = std::move(parms[0]);

      result.type = resolve_as_value(ctx, result.type);

      if (result.type.flags & MIR::Local::Unaligned)
        ctx.diag.error("cannot reference unaligned field", ctx.stack.back(), loc);

      return true;
    }

    if (unaryop == UnaryOpExpr::Fer && is_reference_type(parms[0].type.type))
    {
      result = std::move(parms[0]);

      if (result.type.flags & MIR::Local::Reference)
        lower_fer(ctx, result, result);

      result.type = resolve_as_reference(ctx, result.type);

      return true;
    }

    if (unaryop == UnaryOpExpr::Fwd && (parms[0].value.kind() == MIR::RValue::Call || (parms[0].value.kind() == MIR::RValue::Variable && get<0>(parms[0].value.get<MIR::RValue::Variable>()) == MIR::RValue::Fer)))
    {
      result = std::move(parms[0]);

      if (result.type.flags & MIR::Local::Reference)
      {
        result.type = resolve_as_value(ctx, result.type);

        result.type.defn = ctx.typetable.find_or_create<ReferenceType>(result.type.defn);
      }

      return true;
    }

    if (unaryop == UnaryOpExpr::Fwd && (parms[0].type.flags & MIR::Local::Reference))
    {
      result = std::move(parms[0]);

      if ((result.type.flags & MIR::Local::XValue) && !(result.type.flags & MIR::Local::Const))
        result.type.flags = (result.type.flags & ~MIR::Local::XValue) | MIR::Local::RValue | MIR::Local::MoveRef;

      return true;
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

      if ((parms[0].type.flags & MIR::Local::RValue) && (is_builtin_type(parms[0].type.type) || is_pointer_type(parms[0].type.type)))
      {
        ctx.diag.error("invalid increment on rvalue expression", ctx.stack.back(), loc);
        return false;
      }

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

        return true;
      }
    }

    if (!callee && unaryop == UnaryOpExpr::LNot)
    {
      if (!lower_cast(ctx, parms[0], parms[0], ctx.booltype, parms[0].value.loc()))
        return false;

      callee.fx = Builtin::fn(ctx.translationunit->builtins, Builtin::LNot);
    }

    if (!callee)
    {
      ctx.diag.error("cannot resolve operator reference", ctx.stack.back(), loc);
      diag_callee(ctx, callee, parms, namedparms);
      return false;
    }

    if (!lower_call(ctx, result, callee.fx, parms, namedparms, loc))
      return false;

    return true;
  }

  //|///////////////////// lower_unaryop ////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, UnaryOpExpr *unaryop)
  {
    vector<MIR::Fragment> parms(1);
    map<Ident*, MIR::Fragment> namedparms;

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
  bool lower_expr(LowerContext &ctx, MIR::Fragment &result, BinaryOpExpr::OpCode binaryop, vector<MIR::Fragment> &parms, map<Ident*, MIR::Fragment> &namedparms, SourceLocation loc)
  {
    auto callee = find_callee(ctx, ctx.stack, binaryop, parms, namedparms);

    if ((!callee || !(callee.fx.fn->flags & FunctionDecl::Builtin)) && binaryop == BinaryOpExpr::Assign)
    {
      auto base_type = [&](Type *type) { while (is_tag_type(type) && decl_cast<TagDecl>(type_cast<TagType>(type)->decl)->basetype) type = type_cast<TagType>(type)->fields[0]; return type; };

      if (is_impl_type(ctx, parms[0].type.type, parms[1].type))
      {
        if (!lower_impl_type(ctx, parms[1], parms[1], parms[0].type.type, parms[1].value.loc()))
          return false;
      }

      if (!(parms[0].type.flags & MIR::Local::Const) && is_pointference_type(parms[0].type.type) && is_pointference_type(base_type(parms[1].type.type)))
      {
        auto lhs = parms[0].type.type;
        auto rhs = base_type(parms[1].type.type);

        if (is_tag_type(parms[1].type.type))
          lower_base_cast(ctx, parms[1], parms[1], rhs, loc);

        while (is_pointference_type(lhs) && is_pointference_type(rhs))
        {
          lhs = remove_pointference_type(lhs);
          rhs = remove_pointference_type(rhs);

          if (is_const_type(lhs))
          {
            lhs = remove_const_type(lhs);
            rhs = remove_const_type(rhs);
          }
        }

        while (lhs != rhs && is_tag_type(rhs) && decl_cast<TagDecl>(type_cast<TagType>(rhs)->decl)->basetype)
          rhs = type_cast<TagType>(rhs)->fields[0];

        promote_type(ctx, rhs, lhs);

        if (lhs == rhs || (lhs == ctx.voidtype && !is_const_type(rhs)))
          callee.fx = Builtin::fn(ctx.translationunit->builtins, Builtin::Assign, parms[0].type.type);
      }
    }

    if ((!callee || !(callee.fx.fn->flags & FunctionDecl::Builtin)) && (binaryop == BinaryOpExpr::LT || binaryop == BinaryOpExpr::GT || binaryop == BinaryOpExpr::LE || binaryop == BinaryOpExpr::GE || binaryop == BinaryOpExpr::EQ || binaryop == BinaryOpExpr::NE || binaryop == BinaryOpExpr::Cmp))
    {
      auto base_type = [&](Type *type) {
        while (is_tag_type(type) && decl_cast<TagDecl>(type_cast<TagType>(type)->decl)->basetype && (type_cast<TagType>(type)->decl->flags & TagDecl::PublicBase))
          type = type_cast<TagType>(type)->fields[0];

        return type;
      };

      if (is_pointference_type(parms[0].type.type) && is_pointference_type(parms[1].type.type))
      {
        auto n = 0;
        auto lhs = parms[0].type.type;
        auto rhs = parms[1].type.type;

        while (is_pointference_type(lhs) && is_pointference_type(rhs))
        {
          lhs = remove_const_type(remove_pointference_type(lhs));
          rhs = remove_const_type(remove_pointference_type(rhs));
          n += 1;
        }

        if (lhs != rhs)
        {
          lhs = base_type(lhs);
          rhs = base_type(rhs);
        }

        if (lhs == rhs)
        {
          for (auto k = 0; k < n; ++k)
            lhs = ctx.typetable.find_or_create<PointerType>(ctx.typetable.find_or_create<ConstType>(lhs));

          callee.fx = map_builtin(ctx, binaryop, lhs);
        }
      }
    }

    if ((!callee || !(callee.fx.fn->flags & FunctionDecl::Builtin)) && (binaryop == BinaryOpExpr::Add || binaryop == BinaryOpExpr::Sub))
    {
      if (is_reference_type(parms[0].type.type) && (parms[1].type.type == ctx.intliteraltype || parms[1].type.type == ctx.usizetype))
      {
        parms[0].type.type = ctx.typetable.find_or_create<PointerType>(remove_reference_type(parms[0].type.type));

        callee = find_callee(ctx, ctx.stack, binaryop, parms, namedparms);
      }
    }

    if (!callee && (BinaryOpExpr::AddAssign <= binaryop && binaryop <= BinaryOpExpr::XorAssign))
    {
      auto op = static_cast<BinaryOpExpr::OpCode>(binaryop - BinaryOpExpr::AddAssign); // TODO: fragile!

      auto lhs = parms[0];

      if (!lower_expr(ctx, result, op, parms, namedparms, loc))
        return false;

      parms[0] = std::move(lhs);
      parms[1] = std::move(result);

      callee = find_callee(ctx, ctx.stack, BinaryOpExpr::Assign, parms, namedparms);
    }

    if (binaryop == BinaryOpExpr::Assign || (BinaryOpExpr::AddAssign <= binaryop && binaryop <= BinaryOpExpr::XorAssign))
    {
      if (is_tuple_type(parms[0].type.type))
      {
        auto tupletype = type_cast<TupleType>(parms[0].type.type);

        if (any_of(tupletype->defns.begin(), tupletype->defns.end(), [](auto defn) { return is_reference_type(defn); }))
        {
          for (size_t i = 0; i < tupletype->fields.size(); ++i)
          {
            if (is_const_reference(tupletype->fields[i]))
            {
              ctx.diag.error("invalid assignment to const field", ctx.stack.back(), loc);
              return false;
            }
          }

          parms[0].type.flags &= ~MIR::Local::RValue;
        }
      }

      if (callee && is_struct_type(parms[0].type.type) && callee.fx.fn->owner != variant<Decl*, Stmt*>{type_cast<TagType>(parms[0].type.type)->decl})
      {
        ctx.diag.error("invalid assignment to base expression", ctx.stack.back(), loc);
        return false;
      }

      if (callee && (parms[0].type.flags & MIR::Local::RValue) && !is_qualarg_reference(decl_cast<ParmVarDecl>(callee.fx.fn->parms[0])->type))
      {
        ctx.diag.error("invalid assignment to rvalue expression", ctx.stack.back(), loc);
        return false;
      }

      if (binaryop == BinaryOpExpr::Assign && is_reference_type(parms[0].type.type) && (is_pointer_type(parms[1].type.type) || is_null_type(parms[1].type.type)))
      {
        ctx.diag.error("invalid assignment to reference type", ctx.stack.back(), loc);
        return false;
      }
    }

    if (callee && (callee.fx.fn->builtin == Builtin::Tuple_CopytructorEx || callee.fx.fn->builtin == Builtin::Tuple_AssignmentEx || callee.fx.fn->builtin == Builtin::TupleEqEx || callee.fx.fn->builtin == Builtin::TupleCmpEx))
    {
      auto lhs = type_cast<TupleType>(callee.fx.find_type(callee.fx.fn->args[0])->second);
      auto rhs = type_cast<TupleType>(callee.fx.find_type(callee.fx.fn->args[1])->second);

      if (is_indefinite_type(rhs))
      {
        auto defns = rhs->defns;
        auto fields = rhs->fields;

        for (size_t k = 0; k < fields.size(); ++k)
        {
          promote_type(ctx, fields[k], remove_const_type(remove_reference_type(lhs->fields[k])));
        }

        callee.fx.set_type(callee.fx.fn->args[1], ctx.typetable.find_or_create<TupleType>(std::move(defns), std::move(fields)));
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

    if (!callee && binaryop == BinaryOpExpr::Match)
    {
      callee = find_callee(ctx, ctx.stack, BinaryOpExpr::EQ, parms, namedparms);
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

    if (!callee && (binaryop == BinaryOpExpr::LT || binaryop == BinaryOpExpr::GT || binaryop == BinaryOpExpr::LE || binaryop == BinaryOpExpr::GE || binaryop == BinaryOpExpr::EQ || binaryop == BinaryOpExpr::NE || binaryop == BinaryOpExpr::Cmp))
    {
      auto base_type = [&](Type *type) {
        while (is_tag_type(type) && decl_cast<TagDecl>(type_cast<TagType>(type)->decl)->basetype && (type_cast<TagType>(type)->decl->flags & TagDecl::PublicBase))
          type = type_cast<TagType>(type)->fields[0];

        return type;
      };

      if (is_tag_type(parms[0].type.type) || is_tag_type(parms[1].type.type))
      {
        auto lhs = base_type(parms[0].type.type);
        auto rhs = base_type(parms[1].type.type);

        if (lhs != parms[0].type.type || rhs != parms[1].type.type)
        {
          lower_base_cast(ctx, parms[0], parms[0], lhs, loc);
          lower_base_cast(ctx, parms[1], parms[1], rhs, loc);

          if (lower_expr(ctx, result, binaryop, parms, namedparms, loc))
            return true;
        }
      }
    }

    if (!callee)
    {
      ctx.diag.error("cannot resolve operator reference", ctx.stack.back(), loc);
      diag_callee(ctx, callee, parms, namedparms);
      return false;
    }

    if (!lower_call(ctx, result, callee.fx, parms, namedparms, loc))
      return false;

    return true;
  }

  //|///////////////////// lower_binaryop ///////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, BinaryOpExpr *binaryop)
  {
    vector<MIR::Fragment> parms(2);
    map<Ident*, MIR::Fragment> namedparms;

    if (binaryop->op() == BinaryOpExpr::Assign)
    {
      if (auto declref = is_declrefdecl_expr(binaryop->lhs); declref && expr_cast<DeclRefExpr>(binaryop->lhs)->base)
      {
        if (!lower_expr(ctx, parms[0], expr_cast<DeclRefExpr>(binaryop->lhs)->base))
          return;

        if (!lower_expr(ctx, parms[1], binaryop->rhs))
          return;

        auto rm = ctx.push_barrier();

        MIR::Fragment base = parms[0];

        for (;;)
        {
          auto name = Ident::from(declref->name->str() + '=');

          while (is_pointference_type(parms[0].type.type))
            if (!lower_base_deref(ctx, parms[0], binaryop->lhs->loc()))
              return;

          if (auto callee = find_callee(ctx, parms[0].type.type, name, parms, namedparms); callee)
          {
            lower_call(ctx, result, callee.fx, parms, namedparms, binaryop->loc());

            return;
          }

          if (lower_base_deref(ctx, parms[0], binaryop->lhs->loc()))
            continue;

          break;
        }

        ctx.rollback_barrier(rm);

        lower_expr(ctx, parms[0], base, expr_cast<DeclRefExpr>(binaryop->lhs));

        lower_expr(ctx, result, binaryop->op(), parms, namedparms, binaryop->loc());

        return;
      }
    }

    if (!lower_expr(ctx, parms[0], binaryop->lhs))
      return;

    if (binaryop->op() == BinaryOpExpr::Mul || binaryop->op() == BinaryOpExpr::Div)
    {
      if (is_int_literal(ctx, parms[0]) && get<IntLiteralExpr*>(parms[0].value.get<MIR::RValue::Constant>())->value().value == 0)
      {
        result.type = MIR::Local(ctx.intliteraltype, MIR::Local::Const | MIR::Local::Literal);
        result.value = std::move(parms[0].value);
        return;
      }
    }

    if (binaryop->op() == BinaryOpExpr::LAnd || binaryop->op() == BinaryOpExpr::LOr)
    {
      auto rm = ctx.push_barrier();

      MIR::Fragment lhs = parms[0];

      if (!is_bool_type(lhs.type.type))
      {
        lower_cast(ctx, lhs, lhs, ctx.booltype, binaryop->lhs->loc());
      }

      if (ctx.is_expression)
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

      auto ssm = ctx.push_barrier();

      if (!lower_expr(ctx, parms[1], binaryop->rhs))
        return;

      MIR::Fragment rhs = parms[1];

      if (!is_bool_type(rhs.type.type))
      {
        lower_cast(ctx, rhs, rhs, ctx.booltype, binaryop->rhs->loc());
      }

      realise_as_value(ctx, dst, rhs);

      ctx.retire_barrier(ssm);

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

          ctx.mir.blocks[block_lhs].terminator = MIR::Terminator::switcher(dst, block_lhs + 1, ctx.currentblockid);
        }

        commit_type(ctx, dst, ctx.booltype, MIR::Local::RValue);

        result.type = MIR::Local(ctx.booltype, MIR::Local::RValue);
        result.value = MIR::RValue::local(MIR::RValue::Val, dst, binaryop->loc());

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

    auto block_cond = ctx.add_block(MIR::Terminator::switcher(cond, ctx.currentblockid + 1));

    bool by_value = false;

    MIR::Fragment lhs;

    if (!lower_expr(ctx, lhs, ternaryop->lhs))
      return;

    ctx.unreachable = Unreachable::No;

    if (!(lhs.type.flags & MIR::Local::Reference) || !(find_type(ctx, ctx.stack, ternaryop->rhs).flags & MIR::Local::Reference))
      by_value = true;

    if (by_value)
      realise_as_value(ctx, dst, lhs);
    else
      realise(ctx, dst, lhs);

    auto block_true = ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    ctx.mir.blocks[block_cond].terminator.targets.emplace_back(0, ctx.currentblockid);

    MIR::Fragment rhs;

    if (!lower_expr(ctx, rhs, ternaryop->rhs))
      return;

    ctx.unreachable = Unreachable::No;

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
          Scope fx;
          DeduceContext tx;

          if (deduce_type(ctx, tx, ctx.stack.back(), fx, lhs.type.type, rhs.type.type))
            rhs.type.type = lhs.type.type;

          if (lhs.type.type != rhs.type.type)
          {
            Scope fx;
            DeduceContext tx;

            if (deduce_type(ctx, tx, ctx.stack.back(), fx, rhs.type.type, lhs.type.type))
              lhs.type.type = rhs.type.type;
          }
        }
      }
    }

    if (lhs.type.type != rhs.type.type || (lhs.type.flags & MIR::Local::Reference) != (rhs.type.flags & MIR::Local::Reference) ||
       (is_reference_type(lhs.type.type) && is_reference_type(rhs.type.type) && (lhs.type.flags & MIR::Local::RValue) != (rhs.type.flags & MIR::Local::RValue)) ||
       (!by_value && (lhs.type.flags & MIR::Local::RValue) != (rhs.type.flags & MIR::Local::RValue)))
    {
      ctx.diag.error("ternary operands differing types", ctx.stack.back(), ternaryop->loc());
      ctx.diag << "  lhs type: '" << *lhs.type.type << "' rhs type: '" << *rhs.type.type << "'\n";
      return;
    }

    commit_type(ctx, dst, lhs.type.type, lhs.type.flags | rhs.type.flags);

    ctx.mir.locals[dst].flags &= ~MIR::Local::XValue;

    if (!(ctx.mir.locals[dst].flags & MIR::Local::Reference))
      realise_destructor(ctx, dst, ternaryop->loc());

    result.type = ctx.mir.locals[dst];
    result.type.defn = ctx.typetable.var_defn;
    result.value = MIR::RValue::local(MIR::RValue::Val, dst, ternaryop->loc());
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
      TypeOfDecl decl(call->expr, call->loc());

      type = resolve_type(ctx, ctx.stack.back(), &decl);
    }

    if (is_incomplete_type(type))
    {
      ctx.diag.error("incomplete type for sizeof", ctx.stack.back(), call->loc());
      return;
    }

    if (is_unresolved_type(type))
    {
      ctx.diag.error("unresolved type for sizeof", ctx.stack.back(), call->loc());
      return;
    }

    result.type = MIR::Local(ctx.intliteraltype, MIR::Local::Const | MIR::Local::Literal);
    result.value = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, sizeof_type(type)), call->loc());
  }

  //|///////////////////// lower_alignof ///////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, AlignofExpr *call)
  {
    auto align = size_t(-1);

    if (call->type)
    {
      auto type = resolve_type(ctx, call->type);

      if (is_incomplete_type(type))
      {
        ctx.diag.error("incomplete type for alignof", ctx.stack.back(), call->loc());
        return;
      }

      if (is_unresolved_type(type))
      {
        ctx.diag.error("unresolved type for alignof", ctx.stack.back(), call->loc());
        return;
      }

      align = alignof_type(type);
    }

    if (call->decl && call->decl->kind() == Decl::DeclRef)
    {
      if (auto vardecl = find_vardecl(ctx, ctx.stack, decl_cast<DeclRefDecl>(call->decl)->name); vardecl)
      {
        if (auto type = resolve_type(ctx, ctx.stack.back(), decl_cast<VarDecl>(vardecl)))
          align = alignof_type(type);
      }
    }

    if (call->decl && call->decl->kind() == Decl::DeclScoped)
    {
      long queryflags = 0;

      if (Scoped declref = find_scoped(ctx, ctx.stack, decl_cast<DeclScopedDecl>(call->decl), queryflags))
      {
        if (is_type_scope(declref.scope))
        {
          auto type = resolve_type(ctx, declref.scope, get<Decl*>(declref.scope.owner));

          if (is_compound_type(type))
          {
            if (auto field = find_field(ctx, ctx.stack, type, declref.decl->name))
              align = alignof_type(field.type);
          }
        }
      }
    }

    if (align == size_t(-1))
    {
      ctx.diag.error("invalid field for alignof", ctx.stack.back(), call->loc());
      return;
    }

    result.type = MIR::Local(ctx.intliteraltype, MIR::Local::Const | MIR::Local::Literal);
    result.value = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, align), call->loc());
  }

  //|///////////////////// lower_offsetof ///////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, OffsetofExpr *call)
  {
    auto offset = size_t(-1);

    if (call->decl->kind() == Decl::DeclScoped)
    {
      long queryflags = 0;

      if (Scoped declref = find_scoped(ctx, ctx.stack, decl_cast<DeclScopedDecl>(call->decl), queryflags))
      {
        if (is_type_scope(declref.scope))
        {
          auto type = resolve_type(ctx, declref.scope, get<Decl*>(declref.scope.owner));

          if (is_compound_type(type))
          {
            if (auto field = find_field(ctx, ctx.stack, type, declref.decl->name))
              offset = offsetof_field(type_cast<CompoundType>(type), field.index);
          }
        }
      }
    }

    if (offset == size_t(-1))
    {
      ctx.diag.error("invalid field for offsetof", ctx.stack.back(), call->loc());
      return;
    }

    result.type = MIR::Local(ctx.intliteraltype, MIR::Local::Const | MIR::Local::Literal);
    result.value = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(1, offset), call->loc());
  }

  //|///////////////////// lower_instanceof /////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, InstanceofExpr *call)
  {
    Type *lhs = call->type;
    Type *rhs = resolve_type(ctx, call->instance);

    bool match = false;

    rhs = remove_const_type(rhs);

    if (is_tag_type(lhs) && is_tag_type(rhs))
    {
      while (is_tag_type(rhs))
      {
        if (type_cast<TagType>(lhs)->decl == type_cast<TagType>(rhs)->decl)
        {
          match = true;

          for (size_t i = 0; i != type_cast<TagType>(lhs)->args.size(); ++i)
          {
            if (is_unresolved_type(type_cast<TagType>(lhs)->args[i].second))
              continue;

            if (resolve_type(ctx, type_cast<TagType>(lhs)->args[i].second) != type_cast<TagType>(rhs)->args[i].second)
              match = false;
          }

          break;
        }

        if (!decl_cast<TagDecl>(type_cast<TagType>(rhs)->decl)->basetype || !(type_cast<TagType>(rhs)->decl->flags & TagDecl::PublicBase))
          break;

        rhs = type_cast<TagType>(rhs)->fields[0];
      }
    }

    result.type = MIR::Local(ctx.booltype, MIR::Local::Const | MIR::Local::Literal);
    result.value = ctx.mir.make_expr<BoolLiteralExpr>(match, call->loc());
  }

  //|///////////////////// lower_typeid /////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, TypeidExpr *call)
  {
    Type *typid = nullptr;

    if (call->decl->kind() == Decl::TypeOf)
    {
      typid = resolve_type(ctx, ctx.stack.back(), decl_cast<TypeOfDecl>(call->decl));
    }

    if (call->decl->kind() == Decl::TypeName)
    {
      typid = resolve_type(ctx, ctx.stack.back(), decl_cast<TypeNameDecl>(call->decl)->type);
    }

    if (call->decl->kind() == Decl::DeclRef)
    {
      auto declref = decl_cast<DeclRefDecl>(call->decl);

      if (declref->argless)
      {
        if (auto vardecl = find_vardecl(ctx, ctx.stack, declref->name); vardecl)
        {
          typid = resolve_type(ctx, ctx.stack.back(), decl_cast<VarDecl>(vardecl));
        }
      }

      if (!typid)
      {
        typid = resolve_type(ctx, ctx.stack.back(), nullptr, decl_cast<DeclRefDecl>(call->decl));
      }
    }

    if (call->decl->kind() == Decl::DeclScoped)
    {
      long queryflags = 0;

      if (Scoped declref = find_scoped(ctx, ctx.stack, decl_cast<DeclScopedDecl>(call->decl), queryflags))
      {
        if (declref.decl->argless)
        {
          vector<Decl*> decls;

          for (auto sx = declref.scope; sx; sx = base_scope(ctx, sx, QueryFlags::Public))
          {
            find_decls(ctx, sx, declref.decl->name, QueryFlags::Variables | QueryFlags::Fields, decls);

            if (decls.empty())
              continue;

            break;
          }

          if (decls.size() == 1)
          {
            if (is_var_decl(decls[0]))
              typid = resolve_type(ctx, declref.scope, decl_cast<VarDecl>(decls[0]));
          }
        }

        if (is_type_scope(declref.scope))
        {
          auto type = resolve_type(ctx, declref.scope, get<Decl*>(declref.scope.owner));

          if (is_compound_type(type))
          {
            if (declref.decl->name->kind() == Ident::Index || declref.decl->name->kind() == Ident::Hash)
            {
              if (auto field = find_field(ctx, ctx.stack, type, declref.decl->name))
                typid = field.type;
            }
          }

          if (is_enum_type(type))
          {
            if (declref.decl->name == Ident::kw_super)
              typid = type_cast<TagType>(type)->fields[0];
          }
        }
      }

      if (!typid)
      {
        typid = resolve_type(ctx, ctx.stack.back(), nullptr, decl_cast<DeclScopedDecl>(call->decl));
      }
    }

    if (!typid)
    {
      ctx.diag.error("typeid not found", ctx.stack.back(), call->loc());
      return;
    }

    result.type = MIR::Local(ctx.typeidliteraltype, MIR::Local::Const | MIR::Local::Literal);
    result.value = ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(0, reinterpret_cast<uintptr_t>(typid)), call->loc());
  }

  //|///////////////////// lower_cast ///////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, CastExpr *cast)
  {
    auto casttype = resolve_type(ctx, cast->type);

    if (is_function_type(casttype) && is_declref_expr(cast->expr))
    {
      lower_function_cast(ctx, result, ctx.stack.back(), type_cast<FunctionType>(casttype), expr_cast<DeclRefExpr>(cast->expr)->decl, cast->loc());

      return;
    }

    MIR::Fragment source;

    if (!lower_expr(ctx, source, cast->expr))
      return;

    if (is_qualarg_type(cast->type))
    {
      // use cast<&&typeof(U)>(value) to propegate qualifiers

      result = std::move(source);

      long qualifiers = 0;
      if (is_qualarg_type(casttype))
        qualifiers = type_cast<QualArgType>(casttype)->qualifiers;

      if (is_const_type(casttype))
        result.type.flags = result.type.flags | MIR::Local::Const;

      if (qualifiers & QualArgType::RValue)
        result.type.flags = (result.type.flags & ~MIR::Local::LValue) | MIR::Local::RValue;

      return;
    }

    casttype = remove_const_type(casttype);

    if (source.type.flags & MIR::Local::Literal)
    {
      if (literal_cast(ctx, result.value, source.value, casttype))
      {
        result.type = MIR::Local(casttype, MIR::Local::Const | MIR::Local::Literal);

        return;
      }

      if (is_pointer_type(casttype) && is_int_literal(ctx, source))
        source.type = ctx.usizetype;
    }

    if (is_function_type(remove_qualifiers_type(casttype)) && is_lambda_type(source.type.type))
    {
      lower_lambda_decay(ctx, result, source, ctx.stack.back(), casttype, cast->loc());

      return;
    }

    while (is_tag_type(source.type.type))
    {
      if (source.type.type == casttype)
        break;

      if (is_reference_type(cast->type) && source.type.type == remove_const_type(remove_reference_type(casttype)))
        break;

      if (auto field = find_field(ctx, ctx.stack, source.type.type, Ident::kw_super))
      {
        field.defn = ctx.typetable.var_defn;

        lower_field(ctx, source, source, field, cast->loc());

        continue;
      }

      break;
    }

    if (source.type.type == casttype)
    {
      result = std::move(source);

      return;
    }

    auto arg = ctx.add_temporary();

    if (is_reference_type(cast->type) && (source.type.flags & MIR::Local::Reference))
    {
      // use &&cast<T mut &>(value) to cast away const, retain rvalue
      // use &&cast<T &&>(value) to cast, retain rvalue and const

      result.type = resolve_as_reference(ctx, casttype);
      result.type.defn = remove_const_type(remove_reference_type(cast->type));

      result.type.flags |= source.type.flags & MIR::Local::RValue;
      result.type.flags |= source.type.flags & MIR::Local::XValue;

      if (is_qualarg_reference(cast->type))
        result.type.flags |= source.type.flags & MIR::Local::Const;

      realise_as_reference(ctx, arg, source);
    }
    else
    {
      if (!is_builtin_type(source.type.type) && !is_enum_type(source.type.type) && !is_pointer_type(source.type.type) && !is_reference_type(source.type.type))
      {
        ctx.diag.error("invalid cast", ctx.stack.back(), cast->loc());
        ctx.diag << "  cast type: '" << *casttype << "' from: '" << *source.type.type << "'\n";
        return;
      }

      result.type = MIR::Local(casttype, ctx.typetable.var_defn, MIR::Local::RValue);

      realise_as_value(ctx, arg, source);
    }

    commit_type(ctx, arg, source.type.type, source.type.flags);

    result.value = MIR::RValue::cast(arg, cast->loc());
  }

  //|///////////////////// lower_newexpr ////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, NewExpr *call)
  {
    MIR::Fragment address;
    vector<MIR::Fragment> parms;
    map<Ident*, MIR::Fragment> namedparms;

    if (!lower_expr(ctx, address, call->address))
      return;

    auto type = remove_const_type(resolve_type(ctx, call->type));

    if (!((is_pointer_type(address.type.type) && (type_cast<PointerType>(address.type.type)->type == type || is_void_type(type_cast<PointerType>(address.type.type)->type))) ||
          (is_reference_type(address.type.type) && (type_cast<ReferenceType>(address.type.type)->type == type || is_void_type(type_cast<ReferenceType>(address.type.type)->type)))))
    {
      ctx.diag.error("address type mismatch", ctx.stack.back(), call->loc());
      ctx.diag << "  address type: '" << *address.type.type << "' wanted: '" << *type << " mut *'\n";
      return;
    }

    if (!lower_parms(ctx, parms, namedparms, call->parms, call->loc()))
      return;

    lower_new(ctx, result, address, type, parms, namedparms, call->loc());
  }

  //|///////////////////// lower_call ///////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, CallExpr *call)
  {
    Scope basescope;
    vector<MIR::Fragment> parms;
    map<Ident*, MIR::Fragment> namedparms;

    if (call->base)
    {
      parms.resize(1);

      if (!lower_expr(ctx, parms[0], call->base))
        return;
    }

    if (!lower_parms(ctx, parms, namedparms, call->parms, call->loc()))
      return;

    for (;;)
    {
      bool is_callop = false;

      if (call->callee->kind() == Decl::DeclRef)
      {
        auto name = decl_cast<DeclRefDecl>(call->callee)->name;

        if (call->base)
        {
#if !ASSOCIATED_DEREF
          while (is_pointference_type(parms[0].type.type))
            if (!lower_base_deref(ctx, parms[0], call->loc()))
              return;

          if (call->base->kind() == Expr::Paren && expr_cast<ParenExpr>(call->base)->subexpr->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(expr_cast<ParenExpr>(call->base)->subexpr)->op() == UnaryOpExpr::Fwd)
          {
            if ((parms[0].type.flags & MIR::Local::XValue) && !(parms[0].type.flags & MIR::Local::Const))
              parms[0].type.flags = (parms[0].type.flags & ~MIR::Local::XValue) | MIR::Local::RValue | MIR::Local::MoveRef;
          }
#endif
          basescope = type_scope(ctx, parms[0].type.type);

          if (decl_cast<DeclRefDecl>(call->callee)->argless)
          {
            for (auto type = parms[0].type.type; is_tag_type(type); )
            {
              auto tagtype = type_cast<TagType>(type);

              if (auto field = find_field(ctx, ctx.stack, tagtype, name))
              {
                if ((field.flags & Decl::Public) || get_module(tagtype->decl) == ctx.module)
                {
                  while (parms[0].type.type != type)
                  {
                    if (auto field = find_field(ctx, ctx.stack, parms[0].type.type, Ident::kw_super))
                    {
                      lower_field(ctx, parms[0], parms[0], field, call->loc());
                    }
                  }

                  if (!lower_field(ctx, parms[0], parms[0], field, call->loc()))
                    return;

                  is_callop = true;

                  break;
                }
              }

              if (!decl_cast<TagDecl>(tagtype->decl)->basetype || !(tagtype->decl->flags & TagDecl::PublicBase))
                break;

              type = tagtype->fields[0];
            }

            if (is_lambda_type(parms[0].type.type))
              is_callop = true;
          }
        }

        else if (decl_cast<DeclRefDecl>(call->callee)->argless)
        {
          if (auto vardecl = find_vardecl(ctx, ctx.stack, name))
          {
            parms.insert(parms.begin(), MIR::Fragment());

            if (!lower_expr(ctx, parms[0], vardecl, call->loc()))
              return;

            is_callop = true;
          }
        }

        if (is_callop)
        {
          for (;;)
          {
            if (lower_base_deref(ctx, parms[0], call->loc()))
              continue;

            basescope = type_scope(ctx, parms[0].type.type);

            break;
          }

          if (is_function_type(remove_qualifiers_type(parms[0].type.type)))
          {
            auto fntype = type_cast<FunctionType>(remove_qualifiers_type(parms[0].type.type));

            for (size_t k = 1; k < std::min(parms.size(), type_cast<TupleType>(fntype->paramtuple)->fields.size() + 1); ++k)
            {
              auto lhs = parms[k].type.type;
              auto rhs = remove_const_type(remove_reference_type(type_cast<TupleType>(fntype->paramtuple)->fields[k - 1]));

              while (is_tag_type(lhs))
              {
                if (rhs->klass() == Type::Tag && type_cast<TagType>(rhs)->decl == type_cast<TagType>(lhs)->decl)
                  break;

                if (!decl_cast<TagDecl>(type_cast<TagType>(lhs)->decl)->basetype || !(type_cast<TagType>(lhs)->decl->flags & TagDecl::PublicBase))
                  break;

                lhs = type_cast<TagType>(lhs)->fields[0];
              }

              lower_base_cast(ctx, parms[k], parms[k], lhs, parms[k].value.loc());
            }
          }

          if (is_lambda_type(parms[0].type.type) && !(type_cast<TagType>(parms[0].type.type)->decl->flags & LambdaDecl::Captures))
          {
            auto arg = ctx.add_variable();

            realise(ctx, arg, parms[0]);

            commit_type(ctx, arg, parms[0].type.type, parms[0].type.flags);

            if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
              realise_destructor(ctx, arg, call->loc());

            parms.erase(parms.begin());
          }
        }
      }

      auto callee = find_callee(ctx, ctx.stack, basescope, call->callee, parms, namedparms, is_callop);

      if (!callee && is_callop && !call->base)
      {
        is_callop = false;

        if (!(is_decl_scope(basescope) && get<Decl*>(basescope.owner)->kind() == Decl::Lambda && !(get<Decl*>(basescope.owner)->flags & LambdaDecl::Captures)))
          parms.erase(parms.begin());

        callee = find_callee(ctx, ctx.stack, Scope(), call->callee, parms, namedparms, is_callop);
      }

      if (!callee)
      {
#if ASSOCIATED_DEREF
        if (call->base)
        {
          auto base = parms[0];

          if (lower_base_deref(ctx, base, call->loc()))
          {
            callee = find_callee(ctx, ctx.stack, type_scope(ctx, base.type.type), call->callee, parms, namedparms, is_callop);

            if (!callee)
            {
              parms[0] = std::move(base);
              continue;
            }
          }
        }
#else
        if (call->base && lower_base_deref(ctx, parms[0], call->loc()))
          continue;
#endif

        if (!callee)
        {
          ctx.diag.error("cannot resolve function reference", ctx.stack.back(), call->loc());
          diag_callee(ctx, callee, parms, namedparms);
          return;
        }
      }

      lower_call(ctx, result, callee.fx, parms, namedparms, call->loc());

      return;
    }
  }

  //|///////////////////// lower_requires ///////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, RequiresExpr *reqires)
  {
    Diag diag(ctx.diag.leader());

    auto fx = FnSig(decl_cast<FunctionDecl>(reqires->decl), ctx.stack.back().typeargs);

    LowerContext cttx(ctx.typetable, diag);

    seed_stack(cttx.stack, Scope(fx.fn, fx.typeargs));

    cttx.mir.fx = fx;
    cttx.translationunit = decl_cast<TranslationUnitDecl>(get<Decl*>(cttx.stack[0].owner));
    cttx.module = decl_cast<ModuleDecl>(get<Decl*>(cttx.stack[1].owner));
    cttx.symbols = ctx.symbols;

    cttx.add_local();

    for (auto &parm : fx.parameters())
    {
      cttx.stack.back().goalpost = parm;

      lower_decl(cttx, decl_cast<ParmVarDecl>(parm));
    }

    cttx.stack.back().goalpost = nullptr;

    if (cttx.diag.has_errored())
      ctx.diag << cttx.diag;

    lower_statement(cttx, fx.fn->body);

    backfill(cttx, cttx.mir);

    result.type = MIR::Local(ctx.booltype, MIR::Local::Const | MIR::Local::Literal);
    result.value = ctx.mir.make_expr<BoolLiteralExpr>(!cttx.diag.has_errored(), reqires->loc());
  }

  //|///////////////////// lower_lambda /////////////////////////////////////
  void lower_expr(LowerContext &ctx, MIR::Fragment &result, LambdaExpr *lambda)
  {
    Callee callee;
    vector<MIR::Fragment> parms;
    map<Ident*, MIR::Fragment> namedparms;

    auto typescope = child_scope(ctx.stack.back(), lambda->decl);

    for (auto &capture : decl_cast<LambdaDecl>(lambda->decl)->captures)
    {
      MIR::Fragment result;

      if (!lower_expr(ctx, result, decl_cast<LambdaVarDecl>(capture)->value))
        return;

      if (is_qualarg_reference(decl_cast<LambdaVarDecl>(capture)->type))
      {
        if ((result.type.flags & (MIR::Local::RValue | MIR::Local::Const)) == MIR::Local::RValue)
          result.type.type = ctx.typetable.find_or_create<QualArgType>(QualArgType::RValue, result.type.type);

        if (result.type.flags & MIR::Local::Const)
          result.type.type = ctx.typetable.find_or_create<ConstType>(result.type.type);
      }

      typescope.set_type(decl_cast<LambdaVarDecl>(capture)->arg, result.type.type);

      parms.push_back(std::move(result));
    }

    FindContext tx(ctx, decl_cast<LambdaDecl>(lambda->decl)->name, QueryFlags::Functions);

    find_overloads(ctx, tx, typescope, parms, namedparms, callee.candidates, callee.overloads);

    resolve_overloads(ctx, callee.fx, callee.overloads, parms, namedparms);

    if (!callee)
    {
      ctx.diag.error("cannot resolve constructor", ctx.stack.back(), lambda->loc());
      diag_callee(ctx, callee, parms, namedparms);
      return;
    }

    lower_call(ctx, result, callee.fx, parms, namedparms, lambda->loc());
  }

  //|///////////////////// lower_expr ///////////////////////////////////////
  bool lower_expr(LowerContext &ctx, MIR::Fragment &result, Expr *expr)
  {
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

      case Expr::PointerLiteral:
        lower_expr(ctx, result, expr_cast<PointerLiteralExpr>(expr));
        break;

      case Expr::FunctionPointer:
        lower_expr(ctx, result, expr_cast<FunctionPointerExpr>(expr));
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

      case Expr::ExprRef:
        lower_expr(ctx, result, expr_cast<ExprRefExpr>(expr));
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

      case Expr::Offsetof:
        lower_expr(ctx, result, expr_cast<OffsetofExpr>(expr));
        break;

      case Expr::Instanceof:
        lower_expr(ctx, result, expr_cast<InstanceofExpr>(expr));
        break;

      case Expr::Typeid:
        lower_expr(ctx, result, expr_cast<TypeidExpr>(expr));
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

      case Expr::Fragment:
        ctx.diag.error("invalid fragment", ctx.stack.back(), expr->loc());
        break;

      default:
        assert(false);
    }

    assert(result.value || ctx.diag.has_errored());

    return !!result.value;
  }

  //|///////////////////// lower_vardecl ////////////////////////////////////
  void lower_decl(LowerContext &ctx, VarDecl *vardecl, MIR::Fragment &value)
  {
    if (vardecl->flags & VarDecl::Literal)
    {
      if (!(value.type.flags & MIR::Local::Literal))
      {
        ctx.diag.error("non literal value", ctx.stack.back(), vardecl->loc());
        return;
      }

      if (vardecl->pattern)
      {
        switch (vardecl->pattern->kind())
        {
          case Decl::TuplePattern:

            for (auto &binding : decl_cast<TuplePatternDecl>(vardecl->pattern)->bindings)
            {
              MIR::Fragment field = value;

              if (!lower_expr(ctx, field, field, expr_cast<DeclRefExpr>(decl_cast<StmtVarDecl>(binding)->value)))
                return;

              lower_decl(ctx, decl_cast<VarDecl>(binding), field);
            }

            break;

          default:
            assert(false);
        }
      }

      ctx.symbols[vardecl] = value;

      return;
    }

    if (vardecl->flags & VarDecl::Static)
    {
      auto arg = ctx.add_local();

      if (is_reference_type(vardecl->type))
        ctx.diag.error("invalid reference type", ctx.stack.back(), vardecl->loc());

      ctx.mir.statics.emplace_back(arg, std::move(value.value));

      if (!(vardecl->flags & VarDecl::Const))
        value.type.flags &= ~MIR::Local::Const;

      if (vardecl->flags & VarDecl::ThreadLocal)
        value.type.flags |= MIR::Local::ThreadLocal;

      if (vardecl->flags & VarDecl::CacheAligned)
        value.type.flags |= MIR::Local::CacheAligned;

      if (vardecl->flags & VarDecl::PageAligned)
        value.type.flags |= MIR::Local::PageAligned;

      value.type.flags |= MIR::Local::LValue;
      value.type.flags &= ~MIR::Local::XValue;
      value.type.flags &= ~MIR::Local::RValue;
      value.type.flags &= ~MIR::Local::Literal;

      commit_type(ctx, arg, value.type.type, value.type.flags);

      ctx.mir.add_varinfo(arg, vardecl);

      ctx.locals[vardecl] = arg;
      ctx.symbols[vardecl].type = ctx.mir.locals[arg];

      return;
    }

    size_t arg = 0;

    if (vardecl == ctx.mir.fx.fn->retvar)
    {
      if ((!ctx.mir.locals[0] || ctx.mir.locals[0].type == value.type.type) && !(value.type.flags & MIR::Local::Reference))
        ctx.nrvo = vardecl;
    }

    if (vardecl != ctx.nrvo)
      arg = ctx.add_variable();

    if (is_reference_type(vardecl->type))
    {
      if ((!is_qualarg_reference(vardecl->type) && !is_const_reference(vardecl->type)) && (value.type.flags & MIR::Local::Const))
        ctx.diag.error("cannot bind to const reference", ctx.stack.back(), vardecl->loc());

      realise_as_reference(ctx, arg, value, vardecl->flags & VarDecl::Const);

      if (is_const_reference(vardecl->type))
        value.type.flags |= MIR::Local::Const;

      value.type = resolve_as_value(ctx, value.type);
    }
    else
    {
      realise_as_value_type(ctx, arg, value, vardecl->flags & VarDecl::Const);
    }

    if (vardecl->pattern)
    {
      switch (vardecl->pattern->kind())
      {
        case Decl::TuplePattern:

          for (auto &binding : decl_cast<TuplePatternDecl>(vardecl->pattern)->bindings)
          {
            MIR::Fragment field;

            field.type = value.type;
            field.type.defn = vardecl->type;
            field.type.flags = MIR::Local::LValue | MIR::Local::Reference;
            field.value = MIR::RValue::local(MIR::RValue::Ref, arg, binding->loc());

            if (!lower_expr_deref(ctx, field, binding->loc()))
              return;

            if (!lower_expr(ctx, field, field, expr_cast<DeclRefExpr>(decl_cast<StmtVarDecl>(binding)->value)))
              return;

            if (!(field.type.flags & MIR::Local::Reference))
              ctx.diag.error("non reference binding", ctx.stack.back(), binding->loc());

            lower_decl(ctx, decl_cast<VarDecl>(binding), field);
          }

          break;

        default:
          assert(false);
      }
    }

    value.type.flags |= MIR::Local::LValue;
    value.type.flags &= ~MIR::Local::XValue;
    value.type.flags &= ~MIR::Local::RValue;

    commit_type(ctx, arg, value.type.type, value.type.flags);

    if (arg != 0 && !(ctx.mir.locals[arg].flags & MIR::Local::Reference))
      realise_destructor(ctx, arg, vardecl->loc());

    ctx.mir.add_varinfo(arg, vardecl);

    ctx.locals[vardecl] = arg;
    ctx.symbols[vardecl].type = ctx.mir.locals[arg];
  }

  //|///////////////////// lower_voidvar ////////////////////////////////////
  void lower_decl(LowerContext &ctx, VoidVarDecl *voidvar)
  {
    MIR::Fragment value;

    value.type = resolve_type(ctx, voidvar->type);
    value.type.flags = MIR::Local::LValue;

    if (voidvar->flags & VarDecl::Static)
    {
      value.value = MIR::RValue::literal(ctx.mir.make_expr<VoidLiteralExpr>(voidvar->loc()));
    }

    lower_decl(ctx, voidvar, value);
  }

  //|///////////////////// lower_stmtvar ////////////////////////////////////
  void lower_decl(LowerContext &ctx, StmtVarDecl *stmtvar)
  {
    MIR::Fragment value;

    if (!lower_expr(ctx, value, stmtvar->value))
    {
      ctx.suppressed[stmtvar] = true;

      return;
    }

    if (stmtvar->flags & VarDecl::Literal)
    {
      lower_decl(ctx, stmtvar, value);

      return;
    }

    if (stmtvar->flags & VarDecl::Static)
    {
      if (!(value.type.flags & MIR::Local::Literal))
        ctx.diag.error("non literal static value", ctx.stack.back(), stmtvar->loc());

      lower_decl(ctx, stmtvar, value);

      return;
    }

    if (is_unresolved_type(value.type.type))
    {
      ctx.diag.error("unresolved type for variable", ctx.stack.back(), stmtvar->loc());
      ctx.diag << "  variable type : '" << *value.type.type << "'\n";
      return;
    }

    if (value.type.type == ctx.ptrliteraltype && (value.type.flags & MIR::Local::Literal))
    {
      // infer_pointer_type(ctx, value.type, stmtvar);

      ctx.diag.error("unable to infer pointer type", ctx.stack.back(), stmtvar->loc());
      return;
    }

    if (is_reference_type(stmtvar->type) && !is_qualarg_reference(stmtvar->type))
    {
#if STRICT_BINDING
      if (!(value.type.flags & MIR::Local::Reference))
        ctx.diag.error("non reference type", ctx.stack.back(), stmtvar->loc());

      if (value.type.flags & MIR::Local::RValue)
        ctx.diag.error("cannot bind to rvalue reference", ctx.stack.back(), stmtvar->loc());
#else
      if (!is_const_reference(stmtvar->type) && (value.type.flags & MIR::Local::RValue))
        ctx.diag.error("cannot bind to mutable rvalue reference", ctx.stack.back(), stmtvar->loc());
#endif
    }

#if REFERENCE_DECAY
    if (!is_reference_type(stmtvar->type))
    {
      if (is_return_reference(ctx, stmtvar->value) && !(value.type.flags & MIR::Local::Const))
        value.type.type = ctx.typetable.find_or_create<PointerType>(remove_reference_type(value.type.type));
    }
#endif

    lower_decl(ctx, stmtvar, value);
  }

  //|///////////////////// lower_parmvar ////////////////////////////////////
  void lower_decl(LowerContext &ctx, ParmVarDecl *parmvar)
  {
    auto arg = ctx.add_local();

    ctx.mir.locals[arg].type = resolve_type_as_value(ctx, ctx.stack.back(), parmvar);
    ctx.mir.locals[arg].defn = remove_const_type(parmvar->type);
    ctx.mir.locals[arg].flags = MIR::Local::LValue;

    if (parmvar->flags & VarDecl::Const)
      ctx.mir.locals[arg].flags |= MIR::Local::Const;

    ctx.mir.add_varinfo(arg, parmvar);

    ctx.locals[parmvar] = arg;
    ctx.symbols[parmvar].type = ctx.mir.locals[arg];
  }

  //|///////////////////// lower_errorvar ///////////////////////////////////
  void lower_decl(LowerContext &ctx, ErrorVarDecl *errorvar)
  {
    auto arg = ctx.add_variable();

    ctx.mir.locals[arg].type = resolve_type(ctx, errorvar->type);
    ctx.mir.locals[arg].flags = MIR::Local::LValue;

    ctx.mir.add_varinfo(arg, errorvar);

    ctx.errorarg = arg;
    ctx.locals[errorvar] = arg;
    ctx.symbols[errorvar].type = ctx.mir.locals[arg];
  }

  //|///////////////////// lower_thisvar ////////////////////////////////////
  void lower_decl(LowerContext &ctx, ThisVarDecl *thisvar)
  {
    assert(ctx.mir.fx.fn->flags & FunctionDecl::Constructor);

    ctx.mir.add_varinfo(0, thisvar);

    ctx.locals[thisvar] = 0;
    ctx.symbols[thisvar].type = ctx.mir.locals[0];

    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<TagType>(ctx.mir.locals[0].type);

    if (is_struct_type(thistype) || is_union_type(thistype) || is_lambda_type(thistype) || is_enum_type(thistype))
    {
      auto sm = ctx.push_barrier();

      size_t index = 0;

      if (auto j = find_if(fn->inits.begin(), fn->inits.end(), [&](auto &k) { return decl_cast<InitialiserDecl>(k)->name == Ident::kw_this; }); j != fn->inits.end())
      {
        auto init = decl_cast<InitialiserDecl>(*j);

        MIR::Fragment address;
        address.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(thistype), MIR::Local::LValue);
        address.value = MIR::RValue::local(MIR::RValue::Ref, 0, fn->loc());

        MIR::Fragment result;
        vector<MIR::Fragment> parms;
        map<Ident*, MIR::Fragment> namedparms;

        ctx.mir.add_lineinfo(ctx.currentblockid, ctx.currentblock.statements.size(), init->loc().lineno);

        if (!lower_parms(ctx, parms, namedparms, init->parms, init->loc()))
          return;

        lower_new(ctx, result, address, thistype, parms, namedparms, init->loc());

        index = thistype->fields.size();
      }

      for (; index < thistype->fields.size(); ++index)
      {
        auto type = remove_const_type(thistype->fields[index]);
        auto decl = decl_cast<FieldVarDecl>(thistype->fieldvars[index]);

        MIR::Fragment address;
        address.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(type), MIR::Local::LValue);
        address.value = MIR::RValue::field(MIR::RValue::Ref, 0, MIR::RValue::Field{ MIR::RValue::Ref, index }, decl->loc());

        MIR::Fragment result;
        vector<MIR::Fragment> parms;
        map<Ident*, MIR::Fragment> namedparms;

        if (auto j = find_if(fn->inits.begin(), fn->inits.end(), [&](auto &k) { return decl_cast<InitialiserDecl>(k)->name == decl->name; }); j != fn->inits.end())
        {
          auto init = decl_cast<InitialiserDecl>(*j);

          if (init->flags & InitialiserDecl::VoidInit)
            continue;

          ctx.mir.add_lineinfo(ctx.currentblockid, ctx.currentblock.statements.size(), init->loc().lineno);

          if (is_union_type(thistype) && index != 0)
          {
            auto kinddst = ctx.add_temporary(thistype->fields[0], MIR::Local::LValue | MIR::Local::Reference);
            auto kindres = ctx.add_temporary(thistype->fields[0], MIR::Local::LValue | MIR::Local::Reference);

            ctx.add_statement(MIR::Statement::assign(kinddst, MIR::RValue::field(MIR::RValue::Ref, 0, MIR::RValue::Field{ MIR::RValue::Ref, 0 }, fn->loc())));
            ctx.add_statement(MIR::Statement::construct(kindres, MIR::RValue::literal(ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(index), fn->loc()))));
          }

          if (!lower_parms(ctx, parms, namedparms, init->parms, init->loc()))
            return;

          lower_new(ctx, result, address, type, parms, namedparms, init->loc());
        }
        else
        {
          if (is_enum_type(thistype))
            continue;

          if (is_union_type(thistype) && index != 0)
            continue;

          if (decl->defult)
          {
            parms.resize(1);

            if (!lower_expr(ctx, parms[0], decl->defult))
              return;
          }

          lower_new(ctx, result, address, type, parms, namedparms, fn->loc());
        }
      }

      ctx.retire_barrier(sm);
    }
  }

  //|///////////////////// lower_deinitialisers /////////////////////////////
  void lower_deinitialisers(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<CompoundType>(resolve_as_reference(ctx, ctx.mir.locals[1]).type);

    auto sm = ctx.push_barrier();

    auto res = ctx.add_temporary(ctx.voidtype, MIR::Local::LValue);

    if (is_struct_type(thistype) || is_tuple_type(thistype) || is_lambda_type(thistype))
    {
      for (size_t index = thistype->fields.size(); index-- != 0; )
      {
        auto type = thistype->fields[index];

        if (auto callee = find_destructor(ctx, type, fn->loc()))
        {
          auto src = ctx.add_temporary(type, MIR::Local::Reference);

          ctx.add_statement(MIR::Statement::assign(src, MIR::RValue::field(MIR::RValue::Ref, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc())));
          ctx.add_statement(MIR::Statement::assign(res, MIR::RValue::call(callee.fx, { src }, fn->loc())));
        }
      }
    }

    if (is_union_type(thistype))
    {
      auto kind = ctx.add_temporary(thistype->fields[0]);

      ctx.add_statement(MIR::Statement::assign(kind, MIR::RValue::field(MIR::RValue::Val, 1, MIR::RValue::Field{ MIR::RValue::Val, 0 }, fn->loc())));

      auto endblock = ctx.currentblockid + thistype->fields.size();
      auto switcher = ctx.add_block(MIR::Terminator::switcher(kind, endblock));

      for (size_t index = 1; index < thistype->fields.size(); ++index)
      {
        auto type = thistype->fields[index];

        if (auto callee = find_destructor(ctx, type, fn->loc()))
        {
          auto src = ctx.add_temporary(type, MIR::Local::Reference);

          ctx.add_statement(MIR::Statement::assign(src, MIR::RValue::field(MIR::RValue::Ref, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc())));
          ctx.add_statement(MIR::Statement::assign(res, MIR::RValue::call(callee.fx, { src }, fn->loc())));
        }

        ctx.mir.blocks[switcher].terminator.targets.emplace_back(index, ctx.currentblockid);
        ctx.add_block(MIR::Terminator::gotoer(endblock));
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

    if (is_tuple_type(thistype))
    {
      for (size_t index = 0; index < thistype->fields.size(); ++index)
      {
        auto type = remove_const_type(thistype->fields[index]);

        MIR::Fragment address;
        address.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(type), MIR::Local::LValue);
        address.value = MIR::RValue::field(MIR::RValue::Ref, 0, MIR::RValue::Field{ MIR::RValue::Ref, index }, fn->loc());

        MIR::Fragment result;
        vector<MIR::Fragment> parms;
        map<Ident*, MIR::Fragment> namedparms;

        if (!lower_new(ctx, result, address, type, parms, namedparms, fn->loc()))
          return;
      }
    }

    if (is_struct_type(thistype))
    {
      MIR::Fragment allocator;

      if (fn->parms.size() == 1)
      {
        if (!lower_expr(ctx, allocator, decl_cast<ParmVarDecl>(fn->parms[0]), fn->loc()))
          return;
      }

      for (size_t index = 0; index < thistype->fields.size(); ++index)
      {
        auto type = remove_const_type(thistype->fields[index]);
        auto decl = decl_cast<FieldVarDecl>(type_cast<TagType>(thistype)->fieldvars[index]);

        MIR::Fragment address;
        address.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(type), MIR::Local::LValue);
        address.value = MIR::RValue::field(MIR::RValue::Ref, 0, MIR::RValue::Field{ MIR::RValue::Ref, index }, fn->loc());

        MIR::Fragment result;
        vector<MIR::Fragment> parms;
        map<Ident*, MIR::Fragment> namedparms;

        if (decl->defult)
        {
          parms.resize(1);

          if (!lower_expr(ctx, parms[0], decl->defult))
            return;
        }

        if (allocator)
          namedparms.emplace(Ident::kw_opt_allocator, allocator);

        if (!lower_new(ctx, result, address, type, parms, namedparms, fn->loc()))
          return;
      }
    }

    if (is_lambda_type(thistype))
    {
      for (size_t index = 0; index < thistype->fields.size(); ++index)
      {
        auto type = remove_const_type(thistype->fields[index]);

        MIR::Fragment address;
        address.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(type), MIR::Local::LValue);
        address.value = MIR::RValue::field(MIR::RValue::Ref, 0, MIR::RValue::Field{ MIR::RValue::Ref, index }, fn->loc());

        MIR::Fragment result;
        vector<MIR::Fragment> parms(1);
        map<Ident*, MIR::Fragment> namedparms;

        parms[0].type = resolve_as_reference(ctx, ctx.mir.locals[index + 1]);
        parms[0].value = MIR::RValue::local(MIR::RValue::Val, index + 1, fn->loc());

        if (is_reference_type(decl_cast<VarDecl>(type_cast<TagType>(thistype)->fieldvars[index])->type))
          parms[0].type = resolve_as_value(ctx, parms[0].type);

        if (parms[0].type.flags & MIR::Local::XValue)
          parms[0].type.flags = (parms[0].type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;

        if (!lower_new(ctx, result, address, type, parms, namedparms, fn->loc()))
          return;
      }
    }

    if (is_union_type(thistype))
    {
      auto kinddst = ctx.add_temporary(thistype->fields[0], MIR::Local::LValue | MIR::Local::Reference);
      auto kindres = ctx.add_temporary(thistype->fields[0], MIR::Local::LValue | MIR::Local::Reference);

      ctx.add_statement(MIR::Statement::assign(kinddst, MIR::RValue::field(MIR::RValue::Ref, 0, MIR::RValue::Field{ MIR::RValue::Ref, 0 }, fn->loc())));
      ctx.add_statement(MIR::Statement::construct(kindres, MIR::RValue::literal(ctx.mir.make_expr<IntLiteralExpr>(Numeric::int_literal(0), fn->loc()))));
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

    if (is_struct_type(thistype) || is_tuple_type(thistype) || is_lambda_type(thistype))
    {
      for (size_t index = 0; index < thistype->fields.size(); ++index)
      {
        auto type = remove_const_type(thistype->fields[index]);

        MIR::Fragment address;
        address.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(type), MIR::Local::LValue);
        address.value = MIR::RValue::field(MIR::RValue::Ref, 0, MIR::RValue::Field{ MIR::RValue::Ref, index }, fn->loc());

        MIR::Fragment result;
        vector<MIR::Fragment> parms(1);
        map<Ident*, MIR::Fragment> namedparms;

        auto rhsfield = find_field(ctx, type_cast<CompoundType>(thattype.type), index);

        parms[0].type = MIR::Local(rhsfield.type, rhsfield.defn, thattype.flags);
        parms[0].value = MIR::RValue::field(MIR::RValue::Ref, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

        if (fn->builtin == Builtin::Tuple_Copytructor || fn->builtin == Builtin::Tuple_CopytructorEx)
          lower_expr_deref(ctx, parms[0], fn->loc());

        if ((thattype.flags & MIR::Local::XValue) && (parms[0].type.flags & MIR::Local::XValue) && !(rhsfield.flags & MIR::Local::Const))
          parms[0].type.flags = (parms[0].type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;

        if (allocator)
          namedparms.emplace(Ident::kw_opt_allocator, allocator);

        if (!lower_new(ctx, result, address, type, parms, namedparms, fn->loc()))
          return;
      }
    }

    if (is_union_type(thistype))
    {
      auto kind = ctx.add_temporary(thistype->fields[0]);
      auto kinddst = ctx.add_temporary(thistype->fields[0], MIR::Local::LValue | MIR::Local::Reference);
      auto kindres = ctx.add_temporary(thistype->fields[0], MIR::Local::LValue | MIR::Local::Reference);

      ctx.add_statement(MIR::Statement::assign(kind, MIR::RValue::field(MIR::RValue::Val, 1, MIR::RValue::Field{ MIR::RValue::Val, 0 }, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(kinddst, MIR::RValue::field(MIR::RValue::Ref, 0, MIR::RValue::Field{ MIR::RValue::Ref, 0 }, fn->loc())));
      ctx.add_statement(MIR::Statement::construct(kindres, MIR::RValue::field(MIR::RValue::Val, 1, MIR::RValue::Field{ MIR::RValue::Val, 0 }, fn->loc())));

      auto endblock = ctx.currentblockid + thistype->fields.size();
      auto switcher = ctx.add_block(MIR::Terminator::switcher(kind, endblock));

      for (size_t index = 1; index < thistype->fields.size(); ++index)
      {
        auto type = remove_const_type(thistype->fields[index]);

        MIR::Fragment address;
        address.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(type), MIR::Local::LValue);
        address.value = MIR::RValue::field(MIR::RValue::Ref, 0, MIR::RValue::Field{ MIR::RValue::Ref, index }, fn->loc());

        MIR::Fragment result;
        vector<MIR::Fragment> parms(1);
        map<Ident*, MIR::Fragment> namedparms;

        parms[0].type = MIR::Local(type, thattype.flags);
        parms[0].value = MIR::RValue::field(MIR::RValue::Ref, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

        if ((thattype.flags & MIR::Local::XValue) && parms[0].type.flags & MIR::Local::XValue)
          parms[0].type.flags = (parms[0].type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;

        if (allocator)
          namedparms.emplace(Ident::kw_opt_allocator, allocator);

        if (!lower_new(ctx, result, address, type, parms, namedparms, fn->loc()))
          return;

        ctx.mir.blocks[switcher].terminator.targets.emplace_back(index, ctx.currentblockid);
        ctx.add_block(MIR::Terminator::gotoer(endblock));
      }
    }
  }

  //|///////////////////// lower_default_assignment /////////////////////////
  void lower_default_assignment(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<CompoundType>(resolve_as_reference(ctx, ctx.mir.locals[1]).type);
    auto thattype = resolve_as_reference(ctx, ctx.mir.locals[2]);

    if (is_struct_type(thistype) || is_tuple_type(thistype) || is_lambda_type(thistype))
    {
      for (size_t index = 0; index < thistype->fields.size(); ++index)
      {
        MIR::Fragment result;

        vector<MIR::Fragment> parms(2);
        map<Ident*, MIR::Fragment> namedparms;

        auto lhsfield = find_field(ctx, thistype, index);

        parms[0].type = MIR::Local(lhsfield.type, lhsfield.defn, MIR::Local::LValue | MIR::Local::Reference);
        parms[0].value = MIR::RValue::field(MIR::RValue::Ref, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

        if (fn->builtin == Builtin::Tuple_Assignment || fn->builtin == Builtin::Tuple_AssignmentEx)
          lower_expr_deref(ctx, parms[0], fn->loc());

        auto rhsfield = find_field(ctx, type_cast<CompoundType>(thattype.type), index);

        parms[1].type = MIR::Local(rhsfield.type, rhsfield.defn, thattype.flags);
        parms[1].value = MIR::RValue::field(MIR::RValue::Ref, 2, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

        if (fn->builtin == Builtin::Tuple_Assignment || fn->builtin == Builtin::Tuple_AssignmentEx)
          lower_expr_deref(ctx, parms[1], fn->loc());

        if ((thattype.flags & MIR::Local::XValue) && (parms[1].type.flags & MIR::Local::XValue) && !(rhsfield.flags & MIR::Local::Const))
          parms[1].type.flags = (parms[1].type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;

        if (!lower_expr(ctx, result, BinaryOpExpr::Assign, parms, namedparms, fn->loc()))
          return;

        auto res = ctx.add_temporary();

        realise(ctx, Place(Place::Val, res), result);

        commit_type(ctx, res, result.type.type, result.type.flags);
      }
    }

    if (is_union_type(thistype))
    {
      auto typeref = ctx.typetable.find_or_create<ReferenceType>(thistype);

      auto cmp = find_builtin(ctx, Builtin::EQ, typeref);
      auto tstlhs = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto tstrhs = ctx.add_temporary(typeref, MIR::Local::LValue);
      auto tstflg = ctx.add_temporary(ctx.booltype, MIR::Local::LValue);

      ctx.add_statement(MIR::Statement::assign(tstlhs, MIR::RValue::local(MIR::RValue::Val, 1, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(tstrhs, MIR::RValue::local(MIR::RValue::Val, 2, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(tstflg, MIR::RValue::call(cmp, { tstlhs, tstrhs }, fn->loc())));

      auto tstblock = ctx.add_block(MIR::Terminator::switcher(tstflg, ctx.currentblockid + 1));

      lower_deinitialisers(ctx);

      auto kind = ctx.add_temporary(thistype->fields[0]);
      auto kinddst = ctx.add_temporary(thistype->fields[0], MIR::Local::LValue | MIR::Local::Reference);
      auto kindres = ctx.add_temporary(thistype->fields[0], MIR::Local::LValue | MIR::Local::Reference);

      ctx.add_statement(MIR::Statement::assign(kind, MIR::RValue::field(MIR::RValue::Val, 2, MIR::RValue::Field{ MIR::RValue::Val, 0 }, fn->loc())));
      ctx.add_statement(MIR::Statement::assign(kinddst, MIR::RValue::field(MIR::RValue::Ref, 1, MIR::RValue::Field{ MIR::RValue::Val, 0 }, fn->loc())));
      ctx.add_statement(MIR::Statement::construct(kindres, MIR::RValue::field(MIR::RValue::Val, 2, MIR::RValue::Field{ MIR::RValue::Val, 0 }, fn->loc())));

      auto endblock = ctx.currentblockid + thistype->fields.size();
      auto switcher = ctx.add_block(MIR::Terminator::switcher(kind, endblock));

      for (size_t index = 1; index < thistype->fields.size(); ++index)
      {
        auto type = thistype->fields[index];

        MIR::Fragment address;
        address.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(type), MIR::Local::LValue);
        address.value = MIR::RValue::field(MIR::RValue::Ref, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

        MIR::Fragment result;
        vector<MIR::Fragment> parms(1);
        map<Ident*, MIR::Fragment> namedparms;

        parms[0].type = MIR::Local(type, thattype.flags);
        parms[0].value = MIR::RValue::field(MIR::RValue::Ref, 2, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

        if ((thattype.flags & MIR::Local::XValue) && (parms[0].type.flags & MIR::Local::XValue))
          parms[0].type.flags = (parms[0].type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;

        if (!lower_new(ctx, result, address, type, parms, namedparms, fn->loc()))
          return;

        ctx.mir.blocks[switcher].terminator.targets.emplace_back(index, ctx.currentblockid);
        ctx.add_block(MIR::Terminator::gotoer(endblock));
      }

      ctx.mir.blocks[tstblock].terminator.targets.emplace_back(1, ctx.currentblockid);
    }

    ctx.add_statement(MIR::Statement::assign(0, MIR::RValue::local(MIR::RValue::Val, 1, fn->loc())));
  }

  //|///////////////////// lower_default_equality ///////////////////////////
  void lower_default_equality(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<CompoundType>(resolve_as_reference(ctx, ctx.mir.locals[1]).type);
    auto thattype = type_cast<CompoundType>(resolve_as_reference(ctx, ctx.mir.locals[2]).type);

    if (is_struct_type(thistype) || is_tuple_type(thistype) || is_lambda_type(thistype))
    {
      for (size_t index = 0; index < thistype->fields.size(); ++index)
      {
        MIR::Fragment result;
        vector<MIR::Fragment> parms(2);
        map<Ident*, MIR::Fragment> namedparms;

        auto lhsfield = find_field(ctx, thistype, index);

        parms[0].type = MIR::Local(lhsfield.type, lhsfield.defn, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
        parms[0].value = MIR::RValue::field(MIR::RValue::Ref, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

        lower_expr_deref(ctx, parms[0], fn->loc());

        auto rhsfield = find_field(ctx, thattype, index);

        parms[1].type = MIR::Local(rhsfield.type, rhsfield.defn, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
        parms[1].value = MIR::RValue::field(MIR::RValue::Ref, 2, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

        lower_expr_deref(ctx, parms[1], fn->loc());

        if (!lower_expr(ctx, result, BinaryOpExpr::EQ, parms, namedparms, fn->loc()))
          return;

        realise(ctx, Place(Place::Val, 0), result);

        commit_type(ctx, 0, result.type.type, result.type.flags);

        ctx.add_block(MIR::Terminator::switcher(0, ctx.currentblockid + thistype->fields.size() - index, ctx.currentblockid + 1));
      }

      if (thistype->fields.empty())
      {
        ctx.add_statement(MIR::Statement::assign(0, ctx.mir.make_expr<BoolLiteralExpr>(true, fn->loc())));
      }
    }

    if (is_union_type(thistype))
    {
      ctx.diag.error("non-trivial union operator cannot be defaulted", fn, fn->loc());
    }
  }

  //|///////////////////// lower_default_compare ////////////////////////////
  void lower_default_compare(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = type_cast<CompoundType>(resolve_as_reference(ctx, ctx.mir.locals[1]).type);
    auto thattype = type_cast<CompoundType>(resolve_as_reference(ctx, ctx.mir.locals[2]).type);

    if (is_struct_type(thistype) || is_tuple_type(thistype) || is_lambda_type(thistype))
    {
      for (size_t index = 0; index < thistype->fields.size(); ++index)
      {
        MIR::Fragment result;
        vector<MIR::Fragment> parms(2);
        map<Ident*, MIR::Fragment> namedparms;

        auto lhsfield = find_field(ctx, thistype, index);

        parms[0].type = MIR::Local(lhsfield.type, lhsfield.defn, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
        parms[0].value = MIR::RValue::field(MIR::RValue::Ref, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

        lower_expr_deref(ctx, parms[0], fn->loc());

        auto rhsfield = find_field(ctx, thattype, index);

        parms[1].type = MIR::Local(rhsfield.type, rhsfield.defn, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
        parms[1].value = MIR::RValue::field(MIR::RValue::Ref, 2, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

        lower_expr_deref(ctx, parms[1], fn->loc());

        if (!lower_expr(ctx, result, BinaryOpExpr::Cmp, parms, namedparms, fn->loc()))
          return;

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

    if (is_union_type(thistype))
    {
      ctx.diag.error("non-trivial union operator cannot be defaulted", fn, fn->loc());
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
      map<Ident*, MIR::Fragment> namedparms;

      if (!lower_new(ctx, result, type, parms, namedparms, fn->loc()))
        return;

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
      map<Ident*, MIR::Fragment> namedparms;

      parms[0].type = MIR::Local(type, thattype.flags);
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, src, fn->loc());

      if ((thattype.flags & MIR::Local::XValue) && (parms[0].type.flags & MIR::Local::XValue))
        parms[0].type.flags = (parms[0].type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;

      if (!lower_new(ctx, result, type, parms, namedparms, fn->loc()))
        return;

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
      map<Ident*, MIR::Fragment> namedparms;

      parms[0].type = MIR::Local(type, MIR::Local::LValue | MIR::Local::Reference);
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, dst, fn->loc());

      parms[1].type = MIR::Local(type, thattype.flags);
      parms[1].value = MIR::RValue::local(MIR::RValue::Val, src, fn->loc());

      if ((thattype.flags & MIR::Local::XValue) && (parms[1].type.flags & MIR::Local::XValue))
        parms[1].type.flags = (parms[1].type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;

      if (!lower_expr(ctx, result, BinaryOpExpr::Assign, parms, namedparms, fn->loc()))
        return;

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
      map<Ident*, MIR::Fragment> namedparms;

      parms[0].type = MIR::Local(type, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, rhs, fn->loc());

      parms[1].type = MIR::Local(type, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
      parms[1].value = MIR::RValue::local(MIR::RValue::Val, lhs, fn->loc());

      if (!lower_expr(ctx, result, BinaryOpExpr::EQ, parms, namedparms, fn->loc()))
        return;

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
      map<Ident*, MIR::Fragment> namedparms;

      parms[0].type = MIR::Local(type, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, rhs, fn->loc());

      parms[1].type = MIR::Local(type, MIR::Local::LValue | MIR::Local::Const | MIR::Local::Reference);
      parms[1].value = MIR::RValue::local(MIR::RValue::Val, lhs, fn->loc());

      if (!lower_expr(ctx, result, BinaryOpExpr::Cmp, parms, namedparms, fn->loc()))
        return;

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

    for (size_t index = 0; index < thistype->fields.size(); ++index)
    {
      auto type = remove_const_type(thistype->fields[index]);

      MIR::Fragment address;
      address.type = MIR::Local(ctx.typetable.find_or_create<ReferenceType>(type), MIR::Local::LValue);
      address.value = MIR::RValue::field(MIR::RValue::Ref, 0, MIR::RValue::Field{ MIR::RValue::Ref, index }, fn->loc());

      MIR::Fragment result;
      vector<MIR::Fragment> parms(1);
      map<Ident*, MIR::Fragment> namedparms;

      parms[0].type = resolve_as_reference(ctx, type_cast<TupleType>(thattype.type)->fields[index]);
      parms[0].value = MIR::RValue::field(MIR::RValue::Val, 1, MIR::RValue::Field{ MIR::RValue::Val, index }, fn->loc());

      if ((thattype.flags & MIR::Local::XValue) && (parms[0].type.flags & MIR::Local::XValue))
        parms[0].type.flags = (parms[0].type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;

      if (!lower_new(ctx, result, address, type, parms, namedparms, fn->loc()))
        return;
    }
  }

  //|///////////////////// lower_literal_copytructor ////////////////////////
  void lower_literal_copytructor(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = ctx.mir.locals[0].type;

    auto val = ctx.stack.back().find_type(fn->parms[0])->second;
    auto src = ctx.add_temporary(thistype, MIR::Local::LValue | MIR::Local::Reference);

    assert(src == 1);

    MIR::Fragment result;
    result.type = MIR::Local(thistype, MIR::Local::Const | MIR::Local::Literal);
    result.value = MIR::RValue::literal(type_cast<TypeLitType>(val)->value);

    realise_as_reference(ctx, src, result);

    commit_type(ctx, src, result.type.type, result.type.flags);

    lower_trivial_copytructor(ctx);
  }

  //|///////////////////// lower_literal_assignment /////////////////////////
  void lower_literal_assignment(LowerContext &ctx)
  {
    auto fn = ctx.mir.fx.fn;
    auto thistype = resolve_as_reference(ctx, ctx.mir.locals[1]).type;

    auto val = ctx.stack.back().find_type(fn->parms[1])->second;
    auto src = ctx.add_temporary(thistype, MIR::Local::LValue | MIR::Local::Reference);

    assert(src == 2);

    MIR::Fragment result;
    result.type = MIR::Local(thistype, MIR::Local::Const | MIR::Local::Literal);
    result.value = MIR::RValue::literal(type_cast<TypeLitType>(val)->value);

    realise_as_reference(ctx, src, result);

    commit_type(ctx, src, result.type.type, result.type.flags);

    lower_trivial_assignment(ctx);
  }

  //|///////////////////// lower_defaulted_body /////////////////////////////
  void lower_defaulted_body(LowerContext &ctx)
  {
    auto sm = ctx.push_barrier();

    if (ctx.diag.has_errored())
      return;

    switch (ctx.mir.fx.fn->builtin)
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
        lower_deinitialisers(ctx);
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

      case Builtin::Tuple_CopytructorEx:
        lower_default_copytructor(ctx);
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
        lower_deinitialisers(ctx);
        break;

      case Builtin::Literal_Copytructor:
        lower_literal_copytructor(ctx);
        break;

      case Builtin::Literal_Assignment:
        lower_literal_assignment(ctx);
        break;

      default:
        ctx.diag.error("invalid defaulted function", ctx.mir.fx.fn, ctx.mir.fx.fn->loc());
    }

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_injection_statement ////////////////////////
  void lower_injection_statement(LowerContext &ctx, InjectionStmt *injection)
  {
    auto args = std::vector<MIR::local_t>();

    auto fragment = expr_cast<FragmentExpr>(injection->expr);

    for (auto &expr : fragment->args)
    {
      MIR::Fragment result;
      if (!lower_expr(ctx, result, expr))
        return;

      auto arg = ctx.add_temporary();

      realise_as_value(ctx, arg, result);

      commit_type(ctx, arg, result.type.type, result.type.flags);

      if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
        realise_destructor(ctx, arg, expr->loc());

      args.push_back(arg);
    }

    ctx.add_statement(MIR::Statement::assign(0, MIR::RValue::injection(fragment, args, injection->loc())));
  }

  //|///////////////////// lower_declaration_statement //////////////////////
  void lower_declaration_statement(LowerContext &ctx, DeclStmt *stmt)
  {
    switch (stmt->decl->kind())
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
      case Decl::Union:
      case Decl::VTable:
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

      if (result.value.kind() == MIR::RValue::Call && is_call_inhibited(ctx, result))
      {
        ctx.rollback_barrier(sm);
        return;
      }

      if (result.value.kind() == MIR::RValue::Call && is_call_nodiscard(ctx, result))
      {
        ctx.diag.error("discarding result on nodiscard function", ctx.stack.back(), stmt->loc());
      }

      auto arg = ctx.add_variable();

      realise(ctx, arg, result);

      commit_type(ctx, arg, result.type.type, result.type.flags);

      if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
        realise_destructor(ctx, arg, stmt->loc());

      if (ctx.unreachable)
        ctx.add_block(MIR::Terminator::unreachable());
    }

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_if_statement ///////////////////////////////
  void lower_if_statement(LowerContext &ctx, IfStmt *ifs)
  {
    auto sm = ctx.push_barrier();
    auto sp = ctx.push_scope(ifs, ctx.stack.back().typeargs);

    for (auto &init : ifs->inits)
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

    auto cond = ctx.add_local();

    realise_as_value(ctx, cond, condition);

    commit_type(ctx, cond, condition.type.type, condition.type.flags);

    auto block_cond = ctx.add_block(MIR::Terminator::switcher(cond, ctx.currentblockid + 1));

    Unreachable unreachable[2] = { Unreachable::No, Unreachable::No};

    lower_statement(ctx, ifs->stmts[0]);

    auto block_true = ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    ctx.mir.blocks[block_cond].terminator.targets.emplace_back(0, ctx.currentblockid);

    swap(ctx.unreachable, unreachable[0]);

    if (ifs->stmts[1])
    {
      lower_statement(ctx, ifs->stmts[1]);

      ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

      ctx.mir.blocks[block_true].terminator.blockid = ctx.currentblockid;

      swap(ctx.unreachable, unreachable[1]);
    }

    if (is_true_constant(ctx, condition))
      unreachable[1] = Unreachable::Yes;

    if (is_false_constant(ctx, condition))
      unreachable[0] = Unreachable::Yes;

    if (unreachable[0] && unreachable[1])
    {
      collapse_returns(ctx);

      ctx.unreachable = std::min(unreachable[0], unreachable[1]);
    }

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_if_statement ///////////////////////////////
  void lower_static_if_statement(LowerContext &ctx, IfStmt *ifs)
  {
    auto sm = ctx.push_barrier();
    auto sp = ctx.push_scope(ifs, ctx.stack.back().typeargs);

    for (auto &init : ifs->inits)
    {
      ctx.stack.back().goalpost = init;

      lower_statement(ctx, init);
    }

    ctx.stack.back().goalpost = nullptr;

    if (eval(ctx, ctx.stack.back(), ctx.symbols, ifs->cond) == 1)
    {
      lower_statement(ctx, ifs->stmts[0]);
    }
    else
    {
      if (ifs->stmts[1])
        lower_statement(ctx, ifs->stmts[1]);
    }

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_for_statement //////////////////////////////
  void lower_for_statement(LowerContext &ctx, ForStmt *fors)
  {
    auto sm = ctx.push_barrier();
    auto sp = ctx.push_scope(fors, ctx.stack.back().typeargs);

    vector<tuple<StmtVarDecl*, MIR::local_t, MIR::local_t, MIR::local_t>> ranges;

    for (auto &init : fors->inits)
    {
      ctx.stack.back().goalpost = init;

      if (init->kind() == Stmt::Declaration)
      {
        auto var = decl_cast<StmtVarDecl>(stmt_cast<DeclStmt>(init)->decl);

        if (var->flags & VarDecl::Range)
        {
          MIR::Fragment range;

          auto arg = ctx.add_variable();

          if (!lower_expr(ctx, range, var->value))
            return;

          realise(ctx, arg, range);

          commit_type(ctx, arg, range.type.type, range.type.flags);

          if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
            realise_destructor(ctx, arg, var->value->loc());

          ctx.mir.add_varinfo(arg, var);

          auto beg = ctx.add_variable();

          {
            MIR::Fragment iterator;

            vector<MIR::Fragment> parms(1);
            map<Ident*, MIR::Fragment> namedparms;

            parms[0].type = ctx.mir.locals[arg];
            parms[0].type.flags &= ~(MIR::Local::MutRef | MIR::Local::MoveRef);
            parms[0].value = MIR::RValue::local(MIR::RValue::Val, arg, var->loc());

            if (!lower_expr(ctx, iterator, UnaryOpExpr::Begin, parms, namedparms, var->loc()))
              return;

            realise(ctx, beg, iterator);

            iterator.type.flags |= MIR::Local::LValue;
            iterator.type.flags &= ~MIR::Local::XValue;
            iterator.type.flags &= ~MIR::Local::RValue;

            commit_type(ctx, beg, iterator.type.type, iterator.type.flags);

            if (!(ctx.mir.locals[beg].flags & MIR::Local::Reference))
              realise_destructor(ctx, beg, var->loc());
          }

          auto end = ctx.add_variable();

          {
            MIR::Fragment iterator;

            vector<MIR::Fragment> parms(1);
            map<Ident*, MIR::Fragment> namedparms;

            parms[0].type = ctx.mir.locals[arg];
            parms[0].type.flags &= ~(MIR::Local::MutRef | MIR::Local::MoveRef);
            parms[0].value = MIR::RValue::local(MIR::RValue::Val, arg, var->loc());

            if (!lower_expr(ctx, iterator, UnaryOpExpr::End, parms, namedparms, var->loc()))
              return;

            realise(ctx, end, iterator);

            iterator.type.flags |= MIR::Local::LValue;
            iterator.type.flags &= ~MIR::Local::XValue;
            iterator.type.flags &= ~MIR::Local::RValue;

            commit_type(ctx, end, iterator.type.type, iterator.type.flags);

            if (!(ctx.mir.locals[end].flags & MIR::Local::Reference))
              realise_destructor(ctx, end, var->loc());
          }

          ranges.push_back({ var, arg, beg, end});

          continue;
        }
      }

      lower_statement(ctx, init);
    }

    ctx.stack.back().goalpost = nullptr;

    ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    auto block_loop = ctx.currentblockid;

    auto ssm = ctx.push_barrier();

    MIR::Fragment condition;
    vector<MIR::block_t> block_conds;

    for (auto &[rangevar, arg, beg, end] : ranges)
    {
      MIR::Fragment compare;

      vector<MIR::Fragment> parms(2);
      map<Ident*, MIR::Fragment> namedparms;

      parms[0].type = ctx.mir.locals[beg];
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, beg, rangevar->loc());

      parms[1].type = ctx.mir.locals[end];
      parms[1].value = MIR::RValue::local(MIR::RValue::Val, end, rangevar->loc());

      if (!lower_expr(ctx, compare, BinaryOpExpr::NE, parms, namedparms, fors->loc()))
        return;

      auto cond = ctx.add_local();

      realise_as_value(ctx, cond, compare);

      commit_type(ctx, cond, compare.type.type, compare.type.flags);

      ctx.retire_barrier(ssm);

      block_conds.push_back(ctx.add_block(MIR::Terminator::switcher(cond, ctx.currentblockid + 1)));
    }

    for (auto &[rangevar, arg, beg, end] : ranges)
    {
      MIR::Fragment value;

      vector<MIR::Fragment> parms(2);
      map<Ident*, MIR::Fragment> namedparms;

      parms[0].type = ctx.mir.locals[arg];
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, arg, rangevar->loc());

      parms[1].type = ctx.mir.locals[beg];
      parms[1].value = MIR::RValue::local(MIR::RValue::Val, beg, rangevar->loc());

      if (!lower_expr(ctx, value, BinaryOpExpr::Index, parms, namedparms, rangevar->loc()))
        return;

      lower_decl(ctx, rangevar, value);
    }

    if (fors->cond)
    {
      if (!lower_expr(ctx, condition, fors->cond))
        return;

      if (!is_bool_type(condition.type.type))
      {
        if (!lower_cast(ctx, condition, condition, ctx.booltype, fors->cond->loc()))
          return;
      }

      auto cond = ctx.add_local();

      realise_as_value(ctx, cond, condition);

      commit_type(ctx, cond, condition.type.type, condition.type.flags);

      ctx.retire_barrier(ssm);

      block_conds.push_back(ctx.add_block(MIR::Terminator::switcher(cond, ctx.currentblockid + 1)));
    }

    lower_statement(ctx, fors->stmt);

    ctx.retire_barrier(ssm);

    ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    if (ctx.barriers.back().firstcontinue != ctx.continues.size())
      ctx.unreachable = Unreachable::No;

    auto block_step = ctx.currentblockid;

    for (auto &[rangevar, arg, beg, end] : ranges)
    {
      ctx.add_statement(MIR::Statement::storageloop(arg));
    }

    for (auto &[rangevar, arg, beg, end] : ranges)
    {
      MIR::Fragment increment;

      vector<MIR::Fragment> parms(1);
      map<Ident*, MIR::Fragment> namedparms;

      parms[0].type = ctx.mir.locals[beg];
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, beg, rangevar->loc());

      if (!lower_expr(ctx, increment, UnaryOpExpr::PreInc, parms, namedparms, fors->loc()))
        return;

      auto res = ctx.add_temporary();

      realise(ctx, res, increment);

      commit_type(ctx, res, increment.type.type, increment.type.flags);

      if (!(ctx.mir.locals[res].flags & MIR::Local::Reference))
        realise_destructor(ctx, res, fors->loc());
    }

    for (auto &iter : fors->iters)
    {
      lower_statement(ctx, iter);
    }

    for (auto &init : fors->inits)
    {
      if (init->kind() == Stmt::Declaration && !(stmt_cast<DeclStmt>(init)->decl->flags & VarDecl::Range))
      {
        ctx.add_statement(MIR::Statement::storageloop(ctx.locals[stmt_cast<DeclStmt>(init)->decl]));
      }
    }

    ctx.add_block(MIR::Terminator::gotoer(block_loop));

    for (auto &block_cond : block_conds)
      ctx.mir.blocks[block_cond].terminator.targets.emplace_back(0, ctx.currentblockid);

    for (auto i = ctx.barriers.back().firstcontinue; i < ctx.continues.size(); ++i)
      ctx.mir.blocks[ctx.continues[i]].terminator.blockid = block_step;

    ctx.continues.resize(ctx.barriers.back().firstcontinue);

    for (auto i = ctx.barriers.back().firstbreak; i < ctx.breaks.size(); ++i)
      ctx.mir.blocks[ctx.breaks[i]].terminator.blockid = ctx.currentblockid;

    if ((!fors->cond || (fors->cond && is_true_constant(ctx, condition))) && ranges.empty() && ctx.barriers.back().firstbreak == ctx.breaks.size())
      ctx.unreachable = Unreachable::Yes;
    else
      ctx.unreachable = Unreachable::No;

    ctx.breaks.resize(ctx.barriers.back().firstbreak);

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_rof_statement //////////////////////////////
  void lower_rof_statement(LowerContext &ctx, RofStmt *rofs)
  {
    auto sm = ctx.push_barrier();
    auto sp = ctx.push_scope(rofs, ctx.stack.back().typeargs);

    vector<tuple<StmtVarDecl*, MIR::local_t, MIR::local_t, MIR::local_t>> ranges;

    for (auto &init : rofs->inits)
    {
      ctx.stack.back().goalpost = init;

      if (init->kind() == Stmt::Declaration)
      {
        auto var = decl_cast<StmtVarDecl>(stmt_cast<DeclStmt>(init)->decl);

        if (var->flags & VarDecl::Range)
        {
          MIR::Fragment range;

          auto arg = ctx.add_variable();

          if (!lower_expr(ctx, range, var->value))
            return;

          realise(ctx, arg, range);

          commit_type(ctx, arg, range.type.type, range.type.flags);

          if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
            realise_destructor(ctx, arg, var->value->loc());

          ctx.mir.add_varinfo(arg, var);

          auto beg = ctx.add_variable();

          {
            MIR::Fragment iterator;

            vector<MIR::Fragment> parms(1);
            map<Ident*, MIR::Fragment> namedparms;

            parms[0].type = ctx.mir.locals[arg];
            parms[0].type.flags &= ~(MIR::Local::MutRef | MIR::Local::MoveRef);
            parms[0].value = MIR::RValue::local(MIR::RValue::Val, arg, var->loc());

            if (!lower_expr(ctx, iterator, UnaryOpExpr::Begin, parms, namedparms, var->loc()))
              return;

            realise(ctx, beg, iterator);

            iterator.type.flags |= MIR::Local::LValue;
            iterator.type.flags &= ~MIR::Local::XValue;
            iterator.type.flags &= ~MIR::Local::RValue;

            commit_type(ctx, beg, iterator.type.type, iterator.type.flags);

            if (!(ctx.mir.locals[beg].flags & MIR::Local::Reference))
              realise_destructor(ctx, beg, var->loc());
          }

          auto end = ctx.add_variable();

          {
            MIR::Fragment iterator;

            vector<MIR::Fragment> parms(1);
            map<Ident*, MIR::Fragment> namedparms;

            parms[0].type = ctx.mir.locals[arg];
            parms[0].type.flags &= ~(MIR::Local::MutRef | MIR::Local::MoveRef);
            parms[0].value = MIR::RValue::local(MIR::RValue::Val, arg, var->loc());

            if (!lower_expr(ctx, iterator, UnaryOpExpr::End, parms, namedparms, var->loc()))
              return;

            realise(ctx, end, iterator);

            iterator.type.flags |= MIR::Local::LValue;
            iterator.type.flags &= ~MIR::Local::XValue;
            iterator.type.flags &= ~MIR::Local::RValue;

            commit_type(ctx, end, iterator.type.type, iterator.type.flags);

            if (!(ctx.mir.locals[end].flags & MIR::Local::Reference))
              realise_destructor(ctx, end, var->loc());

            ctx.mir.add_varinfo(end, var);
          }

          ranges.push_back({ var, arg, beg, end });

          continue;
        }
      }

      lower_statement(ctx, init);
    }

    ctx.stack.back().goalpost = nullptr;

    ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    auto block_loop = ctx.currentblockid;

    auto ssm = ctx.push_barrier();

    MIR::Fragment condition;
    vector<MIR::block_t> block_conds;

    for (auto &[rangevar, arg, beg, end] : ranges)
    {
      MIR::Fragment compare;

      vector<MIR::Fragment> parms(2);
      map<Ident*, MIR::Fragment> namedparms;

      parms[0].type = ctx.mir.locals[beg];
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, beg, rangevar->loc());

      parms[1].type = ctx.mir.locals[end];
      parms[1].value = MIR::RValue::local(MIR::RValue::Val, end, rangevar->loc());

      if (!lower_expr(ctx, compare, BinaryOpExpr::EQ, parms, namedparms, rofs->loc()))
        return;

      auto cond = ctx.add_local();

      realise_as_value(ctx, cond, compare);

      commit_type(ctx, cond, compare.type.type, compare.type.flags);

      ctx.retire_barrier(ssm);

      block_conds.push_back(ctx.add_block(MIR::Terminator::switcher(cond, ctx.currentblockid + 1, ctx.currentblockid + 1)));
    }

    for (auto &[rangevar, arg, beg, end] : ranges)
    {
      MIR::Fragment decrement;

      vector<MIR::Fragment> parms(1);
      map<Ident*, MIR::Fragment> namedparms;

      parms[0].type = ctx.mir.locals[end];
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, end, rangevar->loc());

      if (!lower_expr(ctx, decrement, UnaryOpExpr::PreDec, parms, namedparms, rofs->loc()))
        return;

      auto res = ctx.add_temporary();

      realise(ctx, res, decrement);

      commit_type(ctx, res, decrement.type.type, decrement.type.flags);

      if (!(ctx.mir.locals[res].flags & MIR::Local::Reference))
        realise_destructor(ctx, res, rofs->loc());
    }

    for (auto &[rangevar, arg, beg, end] : ranges)
    {
      MIR::Fragment value;

      vector<MIR::Fragment> parms(2);
      map<Ident*, MIR::Fragment> namedparms;

      parms[0].type = ctx.mir.locals[arg];
      parms[0].value = MIR::RValue::local(MIR::RValue::Val, arg, rangevar->loc());

      parms[1].type = ctx.mir.locals[end];
      parms[1].value = MIR::RValue::local(MIR::RValue::Val, end, rangevar->loc());

      if (!lower_expr(ctx, value, BinaryOpExpr::Index, parms, namedparms, rangevar->loc()))
        return;

      lower_decl(ctx, rangevar, value);
    }

    if (rofs->cond)
    {
      if (!lower_expr(ctx, condition, rofs->cond))
        return;

      if (!is_bool_type(condition.type.type))
      {
        if (!lower_cast(ctx, condition, condition, ctx.booltype, rofs->cond->loc()))
          return;
      }

      auto cond = ctx.add_local();

      realise_as_value(ctx, cond, condition);

      commit_type(ctx, cond, condition.type.type, condition.type.flags);

      ctx.retire_barrier(ssm);

      block_conds.push_back(ctx.add_block(MIR::Terminator::switcher(cond, ctx.currentblockid + 1, ctx.currentblockid + 1)));
    }

    for (auto &iter : rofs->iters)
    {
      lower_statement(ctx, iter);
    }

    lower_statement(ctx, rofs->stmt);

    ctx.retire_barrier(ssm);

    ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    auto block_step = ctx.currentblockid;

    for (auto &[rangevar, arg, beg, end] : ranges)
    {
      ctx.add_statement(MIR::Statement::storageloop(arg));
      ctx.add_statement(MIR::Statement::storageloop(end));
    }

    for (auto &init : rofs->inits)
    {
      if (init->kind() == Stmt::Declaration && !(stmt_cast<DeclStmt>(init)->decl->flags & VarDecl::Range))
      {
        ctx.add_statement(MIR::Statement::storageloop(ctx.locals[stmt_cast<DeclStmt>(init)->decl]));
      }
    }

    ctx.add_block(MIR::Terminator::gotoer(block_loop));

    for (auto &block_cond : block_conds)
      ctx.mir.blocks[block_cond].terminator.blockid = ctx.currentblockid;

    for (auto i = ctx.barriers.back().firstcontinue; i < ctx.continues.size(); ++i)
      ctx.mir.blocks[ctx.continues[i]].terminator.blockid = block_step;

    ctx.continues.resize(ctx.barriers.back().firstcontinue);

    if ((!rofs->cond || (rofs->cond && is_false_constant(ctx, condition))) && ranges.empty() && ctx.barriers.back().firstbreak == ctx.breaks.size())
      ctx.unreachable = Unreachable::Yes;
    else
      ctx.unreachable = Unreachable::No;

    for (auto i = ctx.barriers.back().firstbreak; i < ctx.breaks.size(); ++i)
      ctx.mir.blocks[ctx.breaks[i]].terminator.blockid = ctx.currentblockid;

    ctx.breaks.resize(ctx.barriers.back().firstbreak);

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_for_statement //////////////////////////////
  void lower_static_for_statement(LowerContext &ctx, ForStmt *fors)
  {
    auto sm = ctx.push_barrier();
    auto sp = ctx.push_scope(fors, ctx.stack.back().typeargs);

    size_t iterations = size_t(-1);
    map<Ident*, StmtVarDecl*> vars;
    vector<tuple<StmtVarDecl*, MIR::Fragment>> ranges;

    for (auto &init : fors->inits)
    {
      ctx.stack.back().goalpost = init;

      if (init->kind() == Stmt::Declaration)
      {
        auto var = decl_cast<StmtVarDecl>(stmt_cast<DeclStmt>(init)->decl);

        if (var->flags & VarDecl::Range)
        {
          MIR::Fragment range;

          if (!lower_expr(ctx, range, var->value))
            return;

          if (range.value.kind() != MIR::RValue::Constant)
          {
            auto arg = ctx.add_temporary();

            realise_as_reference(ctx, arg, range);

            commit_type(ctx, arg, range.type.type, range.type.flags);

            range.type = ctx.mir.locals[arg];
            range.value = MIR::RValue::local(MIR::RValue::Val, arg, var->value->loc());
          }

          if (is_compound_type(range.type.type))
          {
            iterations = min(iterations, type_cast<CompoundType>(range.type.type)->fields.size());

            ranges.push_back({ var, range });

            continue;
          }

          if (is_array_type(range.type.type))
          {
            iterations = min(iterations, array_len(type_cast<ArrayType>(range.type.type)));

            ranges.push_back({ var, range });

            continue;
          }

          ctx.diag.error("unsupported static for initialiser", ctx.stack.back(), var->value->loc());

          continue;
        }

        vars.emplace(var->name, var);
      }

      lower_statement(ctx, init);
    }

    ctx.stack.back().goalpost = nullptr;

    for (size_t index = 0; index < iterations; ++index)
    {
      auto ssm = ctx.push_barrier();

      for (auto &range : ranges)
      {
        MIR::Fragment value = get<1>(range);

        if (is_compound_type(value.type.type))
        {
          auto field = find_field(ctx, type_cast<CompoundType>(value.type.type), index);

          if (!lower_field(ctx, value, value, field, get<0>(range)->loc()))
            return;

          if (get<0>(range)->value->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(get<0>(range)->value)->op() == UnaryOpExpr::Fwd)
          {
            if ((value.type.flags & MIR::Local::XValue) && !(value.type.flags & MIR::Local::Const))
              value.type.flags = (value.type.flags & ~MIR::Local::XValue) | MIR::Local::RValue | MIR::Local::MoveRef;
          }

          lower_decl(ctx, get<0>(range), value);

          continue;
        }

        if (is_array_type(value.type.type))
        {
          auto field = find_field(ctx, type_cast<ArrayType>(value.type.type), index);

          if (!lower_field(ctx, value, value, field, get<0>(range)->loc()))
            return;

          lower_decl(ctx, get<0>(range), value);

          continue;
        }

        assert(false);
      }

      if (fors->cond)
      {
        if (eval(ctx, ctx.stack.back(), ctx.symbols, fors->cond) != 1)
        {
          ctx.retire_barrier(ssm);

          break;
        }
      }

      lower_statement(ctx, fors->stmt);

      ctx.retire_barrier(ssm);

      ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

      for (auto i = ctx.barriers.back().firstcontinue; i < ctx.continues.size(); ++i)
        ctx.mir.blocks[ctx.continues[i]].terminator.blockid = ctx.currentblockid;

      if (ctx.barriers.back().firstcontinue != ctx.continues.size())
        ctx.unreachable = Unreachable::No;

      ctx.continues.resize(ctx.barriers.back().firstcontinue);

      for (auto &iter : fors->iters)
      {
        auto expr = stmt_cast<ExprStmt>(iter)->expr;

        if (expr->kind() == Expr::UnaryOp && is_declrefdecl_expr(expr_cast<UnaryOpExpr>(expr)->subexpr) && !expr_cast<DeclRefExpr>(expr_cast<UnaryOpExpr>(expr)->subexpr)->base)
        {
          auto unaryop = expr_cast<UnaryOpExpr>(expr);
          auto declref = decl_cast<DeclRefDecl>(expr_cast<DeclRefExpr>(unaryop->subexpr)->decl);

          if (auto var = vars.find(declref->name); var != vars.end() && (var->second->flags & VarDecl::Literal))
          {
            if (lower_const(ctx, unaryop, ctx.symbols.find(var->second)->second))
              continue;
          }
        }

        if (expr->kind() == Expr::BinaryOp && is_declrefdecl_expr(expr_cast<BinaryOpExpr>(expr)->lhs) && !expr_cast<DeclRefExpr>(expr_cast<BinaryOpExpr>(expr)->lhs)->base)
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

      if (ctx.unreachable)
        break;

      if (ctx.diag.has_errored())
        return;

      ctx.unreachable = Unreachable::No;
    }

    for (auto i = ctx.barriers.back().firstbreak; i < ctx.breaks.size(); ++i)
      ctx.mir.blocks[ctx.breaks[i]].terminator.blockid = ctx.currentblockid;

    if (ctx.barriers.back().firstbreak != ctx.breaks.size())
      ctx.unreachable = Unreachable::No;

    ctx.breaks.resize(ctx.barriers.back().firstbreak);

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_while_statement ////////////////////////////
  void lower_while_statement(LowerContext &ctx, WhileStmt *wile)
  {
    auto sm = ctx.push_barrier();
    auto sp = ctx.push_scope(wile, ctx.stack.back().typeargs);

    for (auto &init : wile->inits)
    {
      ctx.stack.back().goalpost = init;

      lower_statement(ctx, init);
    }

    ctx.stack.back().goalpost = nullptr;

    ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    auto block_loop = ctx.currentblockid;

    auto ssm = ctx.push_barrier();

    MIR::Fragment condition;

    for (auto &iter : wile->iters)
    {
      lower_statement(ctx, iter);
    }

    if (!lower_expr(ctx, condition, wile->cond))
      return;

    if (!is_bool_type(condition.type.type))
    {
      if (!lower_cast(ctx, condition, condition, ctx.booltype, wile->cond->loc()))
        return;
    }

    auto cond = ctx.add_local();

    realise_as_value(ctx, cond, condition);

    commit_type(ctx, cond, condition.type.type, condition.type.flags);

    ctx.retire_barrier(ssm);

    auto block_cond = ctx.add_block(MIR::Terminator::switcher(cond, ctx.currentblockid + 1));

    lower_statement(ctx, wile->stmt);

    ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    auto block_step = ctx.currentblockid;

    for (auto &init : wile->inits)
    {
      if (init->kind() == Stmt::Declaration)
      {
        ctx.add_statement(MIR::Statement::storageloop(ctx.locals[stmt_cast<DeclStmt>(init)->decl]));
      }
    }

    ctx.add_block(MIR::Terminator::gotoer(block_loop));

    ctx.mir.blocks[block_cond].terminator.targets.emplace_back(0, ctx.currentblockid);

    for (auto i = ctx.barriers.back().firstcontinue; i < ctx.continues.size(); ++i)
      ctx.mir.blocks[ctx.continues[i]].terminator.blockid = block_step;

    ctx.continues.resize(ctx.barriers.back().firstcontinue);

    if (is_true_constant(ctx, condition) && ctx.barriers.back().firstbreak == ctx.breaks.size())
      ctx.unreachable = Unreachable::Yes;
    else
      ctx.unreachable = Unreachable::No;

    for (auto i = ctx.barriers.back().firstbreak; i < ctx.breaks.size(); ++i)
      ctx.mir.blocks[ctx.breaks[i]].terminator.blockid = ctx.currentblockid;

    ctx.breaks.resize(ctx.barriers.back().firstbreak);

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_switch_statement ///////////////////////////
  void lower_switch_statement(LowerContext &ctx, SwitchStmt *swtch)
  {
    auto sm = ctx.push_barrier();
    auto sp = ctx.push_scope(swtch, ctx.stack.back().typeargs);

    for (auto &init : swtch->inits)
    {
      ctx.stack.back().goalpost = init;

      lower_statement(ctx, init);
    }

    ctx.stack.back().goalpost = nullptr;

    ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    MIR::Fragment base;
    MIR::Fragment condition;

    if (!lower_expr(ctx, condition, swtch->cond))
      return;

    if (is_bool_type(condition.type.type))
    {
      lower_base_cast(ctx, condition, condition, ctx.usizetype, swtch->cond->loc());
    }

    if (is_union_type(condition.type.type))
    {
      auto arg = ctx.add_variable();

      realise(ctx, arg, condition);

      commit_type(ctx, arg, condition.type.type, condition.type.flags);

      if (!(ctx.mir.locals[arg].flags & MIR::Local::Reference))
        realise_destructor(ctx, arg, swtch->cond->loc());

      condition.type = ctx.mir.locals[arg];
      condition.value = MIR::RValue::local(MIR::RValue::Val, arg, swtch->cond->loc());

      auto field = find_field(ctx, type_cast<CompoundType>(condition.type.type), 0);

      if (!lower_field(ctx, condition, condition, field, swtch->cond->loc()))
        return;

      base.type = ctx.mir.locals[arg];
      base.value = MIR::RValue::local(MIR::RValue::Val, arg, swtch->cond->loc());

      if ((base.type.flags & MIR::Local::XValue) && !(base.type.flags & MIR::Local::Const))
        base.type.flags = (base.type.flags & ~MIR::Local::XValue) | MIR::Local::RValue;
    }

    auto is_native = is_int_type(condition.type.type) || is_char_type(condition.type.type) || is_enum_type(condition.type.type);

    auto cond = ctx.add_temporary();

    if (is_native)
      realise_as_value(ctx, cond, condition);
    else
      realise_as_reference(ctx, cond, condition);

    commit_type(ctx, cond, condition.type.type, condition.type.flags);

    if (!(ctx.mir.locals[cond].flags & MIR::Local::Reference))
      realise_destructor(ctx, cond, swtch->cond->loc());

    Unreachable unreachable = Unreachable::Yes;

    vector<MIR::block_t> block_conds;
    vector<MIR::block_t> block_bodys;
    unordered_map<size_t, MIR::block_t> block_labels;

    auto block_cond = ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid));

    if (is_native)
    {
      ctx.mir.blocks[block_cond].terminator = MIR::Terminator::switcher(cond, block_cond);
    }

    auto ssm = ctx.push_barrier();

    vector<Decl*> decls;
    find_decls(ctx, ctx.stack.back(), swtch->decls, decls);

    for (auto &decl : decls)
    {
      if (decl->kind() != Decl::Case)
      {
        ctx.diag.error("invalid case in switch", ctx.stack.back(), decl->loc());
        continue;
      }

      auto casse = decl_cast<CaseDecl>(decl);

      if (is_native)
      {
        if (casse->label)
        {
          vector<size_t> labels;

          if (!lower_label(ctx, labels, condition.type.type, casse->label))
            return;

          for (auto &parm : casse->parms)
          {
            auto casevar = decl_cast<CaseVarDecl>(parm);

            if (!base)
            {
              ctx.diag.error("case parameter requires union condition", ctx.stack.back(), decl->loc());
              return;
            }

            if (labels.size() != 1)
            {
              ctx.diag.error("case parameter requires unique label", ctx.stack.back(), decl->loc());
              return;
            }

            MIR::Fragment value;

            if (casevar->value)
            {
              if (!lower_expr(ctx, value, casevar->value))
                return;
            }
            else
            {
              auto field = find_field(ctx, type_cast<CompoundType>(base.type.type), labels[0]);

              if (!lower_field(ctx, value, base, field, casevar->loc()))
                return;
            }

            lower_decl(ctx, casevar, value);
          }

          for (auto label : labels)
          {
            if (block_labels.find(label) != block_labels.end())
              ctx.diag.error("duplicate label in switch", ctx.stack.back(), decl->loc());

            ctx.mir.blocks[block_cond].terminator.targets.emplace_back(label, ctx.currentblockid);

            block_labels.emplace(label, ctx.currentblockid);
          }
        }
        else
        {
          if (ctx.mir.blocks[block_cond].terminator.blockid != block_cond)
            ctx.diag.error("duplicate else in switch", ctx.stack.back(), decl->loc());

          for (auto &parm : casse->parms)
          {
            MIR::Fragment value;

            value.type = ctx.mir.locals[cond];
            value.value = MIR::RValue::local(MIR::RValue::Val, cond, decl->loc());

            lower_decl(ctx, decl_cast<CaseVarDecl>(parm), value);
          }

          ctx.mir.blocks[block_cond].terminator.blockid = ctx.currentblockid;
        }
      }
      else
      {
        ctx.mir.blocks[block_cond].terminator.blockid = ctx.currentblockid;

        if (casse->label)
        {
          MIR::Fragment testcase;

          vector<MIR::Fragment> parms(2);
          map<Ident*, MIR::Fragment> namedparms;

          if (!lower_expr(ctx, parms[0], casse->label))
            return;

          if (!is_constant(ctx, parms[0]))
            ctx.diag.error("case not a literal value", ctx.stack.back(), decl->loc());

          if (casse->parms.size() != 0)
            ctx.diag.error("case parameter requires union condition", ctx.stack.back(), decl->loc());

          parms[1].type = ctx.mir.locals[cond];
          parms[1].value = MIR::RValue::local(MIR::RValue::Val, cond, decl->loc());

          if (!lower_expr(ctx, testcase, BinaryOpExpr::Match, parms, namedparms, decl->loc()))
            return;

          auto flg = ctx.add_variable();

          realise_as_value(ctx, flg, testcase);

          commit_type(ctx, flg, testcase.type.type, testcase.type.flags);

          block_conds.push_back(block_cond = ctx.add_block(MIR::Terminator::switcher(flg, ctx.currentblockid)));
        }
        else
        {
          for (auto &parm : casse->parms)
          {
            MIR::Fragment value;

            value.type = ctx.mir.locals[cond];
            value.value = MIR::RValue::local(MIR::RValue::Val, cond, decl->loc());

            lower_decl(ctx, decl_cast<CaseVarDecl>(parm), value);
          }
        }

        if (casse->body)
        {
          for (auto block_cond : block_conds)
            ctx.mir.blocks[block_cond].terminator.targets.emplace_back(1, ctx.currentblockid);

          block_conds.clear();
        }
      }

      if (casse->body)
      {
        ctx.stack.emplace_back(casse, ctx.stack.back().typeargs);

        lower_statement(ctx, casse->body);

        ctx.stack.pop_back();

        ctx.retire_barrier(ssm);

        block_bodys.push_back(ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1)));

        unreachable = std::min(unreachable, ctx.unreachable);
      }

      ctx.unreachable = Unreachable::No;
    }

    if (ctx.mir.blocks[block_cond].terminator.blockid == block_cond)
      unreachable = Unreachable::No;

    if (ctx.mir.blocks[block_cond].terminator.blockid == block_cond)
      ctx.mir.blocks[block_cond].terminator.blockid = ctx.currentblockid;

    for (auto block_body : block_bodys)
      ctx.mir.blocks[block_body].terminator.blockid = ctx.currentblockid;

    for (auto i = ctx.barriers.back().firstgoto; i < ctx.gotos.size(); ++i)
    {
      auto [blk, label] = ctx.gotos[i];

      if (auto declref = is_declrefdecl_expr(label); declref && declref->name == Ident::kw_else)
      {
        ctx.mir.blocks[blk].terminator.blockid = ctx.mir.blocks[block_cond].terminator.blockid;

        continue;
      }

      vector<size_t> labels;

      if (!lower_label(ctx, labels, condition.type.type, label))
        return;

      if (labels.size() != 1)
        ctx.diag.error("invalid label in goto", ctx.stack.back(), label->loc());

      auto j = block_labels.find(labels[0]);

      if (j == block_labels.end())
        ctx.diag.error("unknown label in goto", ctx.stack.back(), label->loc());

      if (j != block_labels.end())
        ctx.mir.blocks[blk].terminator.blockid = get<1>(*j);
    }

    ctx.gotos.resize(ctx.barriers.back().firstgoto);

    if (unreachable)
    {
      ctx.unreachable = unreachable;
    }

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_goto_statement /////////////////////////////
  void lower_goto_statement(LowerContext &ctx, GotoStmt *gotoo)
  {
    ctx.gotos.push_back(std::make_tuple(ctx.currentblockid, gotoo->label));
    ctx.unreachable = Unreachable::Unwind;
  }

  //|///////////////////// lower_try_statement //////////////////////////////
  void lower_try_statement(LowerContext &ctx, TryStmt *trys)
  {
    auto sm = ctx.push_barrier();

    lower_decl(ctx, decl_cast<ErrorVarDecl>(trys->errorvar));

    Unreachable unreachable[2] = { Unreachable::No, Unreachable::Yes};

    lower_statement(ctx, trys->body);

    auto block_body = ctx.add_block(MIR::Terminator::gotoer(ctx.currentblockid + 1));

    swap(ctx.unreachable, unreachable[0]);

    if (ctx.barriers.back().firstthrow != ctx.throws.size())
    {
      unreachable[1] = Unreachable::No;

      for (auto i = ctx.barriers.back().firstthrow; i < ctx.throws.size(); ++i)
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

      ctx.unreachable = std::min(unreachable[0], unreachable[1]);
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

    Scope fx;

    if (!deduce_type(ctx, ctx.stack.back(), fx, ctx.mir.locals[ctx.errorarg].type, result.type))
    {
      ctx.diag.error("type mismatch", ctx.stack.back(), throwe->loc());
      ctx.diag << "  throw type: '" << *result.type.type << "' wanted: '" << *ctx.mir.locals[ctx.errorarg].type << "'\n";
      return;
    }

    ctx.throws.push_back(ctx.currentblockid);
    ctx.add_block(MIR::Terminator::thrower(ctx.errorarg, ctx.currentblockid));
    ctx.unreachable = Unreachable::Unwind;

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_break_statement ////////////////////////////
  void lower_break_statement(LowerContext &ctx, BreakStmt *brek)
  {
    ctx.breaks.push_back(ctx.currentblockid);
    ctx.unreachable = Unreachable::Unwind;
  }

  //|///////////////////// lower_continue_statement /////////////////////////
  void lower_continue_statement(LowerContext &ctx, ContinueStmt *continu)
  {
    ctx.continues.push_back(ctx.currentblockid);
    ctx.unreachable = Unreachable::Unwind;
  }

  //|///////////////////// lower_return_statement ///////////////////////////
  void lower_return_statement(LowerContext &ctx, ReturnStmt *retrn)
  {
    auto sm = ctx.push_barrier();

    if (retrn->expr)
    {
      MIR::Fragment result;

      if (ctx.mir.locals[0] && is_tag_type(ctx.mir.locals[0].type))
        ctx.labelscope = type_scope(ctx, ctx.mir.locals[0].type);

      if (!lower_expr(ctx, result, retrn->expr))
        return;

      ctx.labelscope = {};

      if (is_return_reference(ctx, retrn->expr))
      {
        result.type = resolve_as_value(ctx, result.type);

        result.type.defn = ctx.typetable.find_or_create<ReferenceType>(result.type.defn);
      }

      if (retrn->expr->kind() == Expr::CompoundLiteral)
      {
        auto defns = type_cast<TupleType>(result.type.type)->defns;
        auto fields = type_cast<TupleType>(result.type.type)->fields;

        for (size_t i = 0; i < expr_cast<CompoundLiteralExpr>(retrn->expr)->fields.size(); ++i)
        {
          if (is_return_reference(ctx, expr_cast<CompoundLiteralExpr>(retrn->expr)->fields[i]))
            defns[i] = ctx.typetable.find_or_create<ReferenceType>(defns[i]);
        }

        result.type.type = ctx.typetable.find_or_create<TupleType>(std::move(defns), std::move(fields));
      }

      if (ctx.mir.locals[0])
      {
        if (!deduce_returntype(ctx, ctx.stack.back(), ctx.mir.fx.fn, ctx.mir.locals[0], result.type))
        {
          vector<MIR::Fragment> parms(1);
          map<Ident*, MIR::Fragment> namedparms;

          parms[0] = std::move(result);

          if (!lower_new(ctx, result, ctx.mir.locals[0].type, parms, namedparms, retrn->expr->loc()))
            return;
        }

        if (is_lambda_decay(ctx, ctx.mir.locals[0].type, result.type.type))
        {
          if (!lower_lambda_decay(ctx, result, result, ctx.stack.back(), ctx.mir.locals[0].type, retrn->expr->loc()))
            return;
        }

        if (is_base_cast(ctx, ctx.mir.locals[0].type, result.type.type))
        {
          if (!lower_base_cast(ctx, result, result, ctx.mir.locals[0].type, retrn->expr->loc()))
            return;
        }
      }

      // Implicit move from local
      if (!is_reference_type(result.type.type) && result.value.kind() == MIR::RValue::Variable && !(result.type.flags & MIR::Local::Const))
      {
        auto &[op, arg, fields, loc] = result.value.get<MIR::RValue::Variable>();

        if (op == MIR::RValue::Ref && all_of(fields.begin(), fields.end(), [](auto k){ return k.op != MIR::RValue::Val; }))
          result.type.flags |= MIR::Local::RValue;
      }

      if (!ctx.nrvo)
      {
        realise_as_value(ctx, 0, result);

        commit_type(ctx, 0, result.type.type, result.type.flags);

        ctx.mir.locals[0].defn = result.type.defn;

        if (!(ctx.mir.locals[0].flags & MIR::Local::RValue))
          ctx.mir.locals[0].flags |= MIR::Local::LValue;

        if (!is_reference_type(ctx.mir.locals[0].type))
          ctx.mir.locals[0].flags &= ~(MIR::Local::LValue | MIR::Local::RValue);

        ctx.mir.locals[0].flags &= ~MIR::Local::XValue;
        ctx.mir.locals[0].flags &= ~MIR::Local::MutRef;
        ctx.mir.locals[0].flags &= ~MIR::Local::MoveRef;
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
    ctx.unreachable = Unreachable::Unwind;

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_compound_statement /////////////////////////
  void lower_compound_statement(LowerContext &ctx, CompoundStmt *compound)
  {
    auto sm = ctx.push_barrier();
    auto sp = ctx.push_scope(compound, ctx.stack.back().typeargs);

    for (auto &stmt : compound->stmts)
    {
      ctx.stack.back().goalpost = stmt;

      lower_statement(ctx, stmt);

      if (ctx.unreachable)
        break;
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

    ctx.retire_barrier(sm);
  }

  //|///////////////////// lower_statement //////////////////////////////////
  void lower_statement(LowerContext &ctx, Stmt *stmt)
  {
    ctx.mir.add_lineinfo(ctx.currentblockid, ctx.currentblock.statements.size(), stmt->loc().lineno);

    switch (stmt->kind())
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

      case Stmt::Switch:
        lower_switch_statement(ctx, stmt_cast<SwitchStmt>(stmt));
        break;

      case Stmt::Goto:
        lower_goto_statement(ctx, stmt_cast<GotoStmt>(stmt));
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

      case Stmt::Injection:
        lower_injection_statement(ctx, stmt_cast<InjectionStmt>(stmt));
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

    realise(ctx, 0, result);

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

    if (fx.throwtype)
    {
      ctx.errorarg = ctx.add_local();

      commit_type(ctx, ctx.errorarg, fx.throwtype);
    }

    ctx.mir.throws = fx.throwtype;

    ctx.mir.args_beg = ctx.mir.locals.size();

    for (auto &parm : fx.parameters())
    {
      ctx.stack.back().goalpost = parm;

      lower_decl(ctx, decl_cast<ParmVarDecl>(parm));
    }

    if (fn->flags & FunctionDecl::Destructor)
    {
      ctx.mir.locals[1].type = ctx.typetable.find_or_create<ReferenceType>(remove_const_type(remove_reference_type(ctx.mir.locals[1].type)));
    }

    ctx.stack.back().goalpost = nullptr;

    ctx.mir.args_end = ctx.mir.locals.size();

    ctx.mir.add_lineinfo(ctx.currentblockid, ctx.currentblock.statements.size(), fn->loc().lineno);

    if (fn->body)
    {
      lower_statement(ctx, fn->body);

      if (!ctx.mir.locals[0].type)
      {
        commit_type(ctx, 0, ctx.voidtype);
      }

      if (!ctx.breaks.empty())
        ctx.diag.error("unhandled break statement", ctx.stack.back(), fn->loc());

      if (!ctx.continues.empty())
        ctx.diag.error("unhandled continue statement", ctx.stack.back(), fn->loc());

      if (!ctx.gotos.empty())
        ctx.diag.error("unhandled goto statement", ctx.stack.back(), fn->loc());

      if (!ctx.unreachable && ctx.mir.locals[0].type != ctx.voidtype && !(ctx.mir.fx.fn->flags & FunctionDecl::Constructor))
        ctx.diag.error("missing return statement", ctx.stack.back(), fn->loc());

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

      for (auto &retn : ctx.returns)
        ctx.mir.blocks[retn].terminator.blockid = ctx.currentblockid;
    }

    if (fn->body && fn->body->kind() == Stmt::Compound)
      ctx.mir.add_lineinfo(ctx.currentblockid, ctx.currentblock.statements.size(), stmt_cast<CompoundStmt>(fn->body)->endloc.lineno);

    ctx.add_block(MIR::Terminator::returner());
  }

  //|///////////////////// diag_mismatch ////////////////////////////////////

  void diag_mismatch(LowerContext &ctx, const char *name, MIR::local_t arg, Type *wanted)
  {
    ctx.diag << "  " << name << ": '" << Diag::white() << *ctx.mir.locals[arg].type << Diag::normal() << "' wanted: '" << Diag::white() << *wanted << Diag::normal() << "'\n";
  }

  void diag_mismatch(LowerContext &ctx, const char *name, Type *vartype, MIR::local_t arg)
  {
    ctx.diag << "  " << name << ": '" << Diag::white() << *vartype << Diag::normal() << "' wanted: '" << Diag::white() << *ctx.mir.locals[arg].type << Diag::normal() << "'";

    for (auto &block : ctx.mir.blocks)
    {
      for (auto &statement : block.statements)
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

  bool promote(LowerContext &ctx, MIR::local_t id, Type *type, long flags = 0)
  {
    type = remove_const_type(type);

    if (ctx.mir.locals[id].flags & MIR::Local::Reference)
      type = remove_pointference_type(type);

    if (ctx.mir.locals[id].flags & MIR::Local::Const)
      type = remove_const_type(type);

    if (ctx.mir.locals[id].type == type)
      return true;

    if (ctx.mir.args_beg <= id && id < ctx.mir.args_end)
    {
      switch (ctx.mir.fx.fn->flags & FunctionDecl::DeclType)
      {
        case FunctionDecl::MatchDecl:
          break;

        case FunctionDecl::LambdaDecl:

          if (auto lambdadecl = decl_cast<LambdaDecl>(get<Decl*>(ctx.mir.fx.fn->owner)); lambdadecl->flags & LambdaDecl::Quick)
            break;

          return false;

        default:
          return false;
      }
    }

#if 0
  cout << "promote _" << id << ": " << *ctx.mir.locals[id].type << " to " << *type << endl;
#endif

    if (!promote_type(ctx, ctx.mir.locals[id].type, type))
      return false;

    ctx.mir.locals[id].flags |= flags;

    if (is_concrete_type(ctx.mir.locals[id].type))
    {
      for (auto &block : ctx.mir.blocks)
      {
        for (auto &statement : block.statements)
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

              if (!promote(ctx, statement.dst, vartype))
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
              auto scope = Scope(callee.fn, std::move(callee.typeargs));

              for (auto const &[parm, arg] : zip(callee.parameters(), args))
              {
                scope.goalpost = parm;

                if (!deduce_type(ctx, callee.fn, scope, decl_cast<ParmVarDecl>(parm), ctx.mir.locals[arg]))
                {
                  ctx.diag.error("type mismatch", ctx.mir.fx.fn, loc);
                  diag_mismatch(ctx, "parameter type", arg, decl_cast<ParmVarDecl>(parm)->type);
                }
              }
#if 0
              for (auto &expr : callee.fn->constraints)
              {
                switch (expr->kind())
                {
                  case Expr::Where:
                    if (eval(ctx, scope, expr_cast<WhereExpr>(expr)->expr) != 1)
                    {
                      ctx.diag.error("invalid call resolution", ctx.mir.fx.fn, loc);

                      for (auto const &[parm, arg] : zip(callee.parameters(), args))
                        diag_mismatch(ctx, "parameter type", arg, decl_cast<ParmVarDecl>(parm)->type);

                      return false;
                    }
                    break;

                  default:
                    break;
                }
              }
#endif
              callee = FnSig(callee.fn, std::move(scope.typeargs), callee.throwtype);

              if (auto returntype = find_returntype(ctx, callee).type; is_concrete_type(returntype))
              {
                if (statement.kind == MIR::Statement::Construct)
                  returntype = ctx.typetable.find_or_create<ReferenceType>(returntype);

                if (!promote(ctx, statement.dst, returntype))
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
    if (mir.fx.fn->flags & FunctionDecl::Defaulted)
      return;

    for (size_t iteration = 0; iteration < 3; ++iteration)
    {
      if (ctx.diag.has_errored())
        return;

      for (auto block = mir.blocks.rbegin(); block != mir.blocks.rend(); ++block)
      {
        for (auto statement = block->statements.rbegin(); statement != block->statements.rend(); ++statement)
        {
          auto dst = mir.locals[statement->dst];

          if (statement->kind == MIR::Statement::Construct)
            dst.flags &= ~MIR::Local::Reference;

          if (statement->src.kind() == MIR::RValue::Variable)
          {
            auto &[op, arg, fields, loc] = statement->src.get<MIR::RValue::Variable>();

            if (is_concrete_type(dst.type) && is_indefinite_type(mir.locals[arg].type))
            {
              auto lhs = resolve_as_value(ctx, dst).type;
              auto rhs = mir.locals[arg].type;

              if (op == MIR::RValue::Ref)
                lhs = remove_pointference_type(remove_const_type(lhs));

              if (op == MIR::RValue::Fer)
                lhs = ctx.typetable.find_or_create<ReferenceType>(lhs);

              for (auto &field : fields)
              {
                if (field.op == MIR::RValue::Val)
                  rhs = remove_pointference_type(rhs);

                switch (rhs = remove_const_type(rhs); rhs->klass())
                {
                  case Type::Tag:
                  case Type::Tuple:
                    rhs = type_cast<CompoundType>(rhs)->fields[field.index];
                    break;

                  case Type::Array:
                    rhs = type_cast<ArrayType>(rhs)->type;
                    break;

                  default:
                    assert(false);
                }
              }

              if (remove_qualifiers_type(lhs) != remove_qualifiers_type(rhs))
              {
                if (fields.size() == 1)
                {
                  if (is_array_type(mir.locals[arg].type))
                  {
                    auto arraytype = type_cast<ArrayType>(mir.locals[arg].type);
                    auto arrayelem = arraytype->type;

                    promote_type(ctx, arrayelem, lhs);

                    lhs = ctx.typetable.find_or_create<ArrayType>(arrayelem, arraytype->size);
                  }

                  if (is_tuple_type(mir.locals[arg].type))
                  {
                    auto tupletype = type_cast<TupleType>(mir.locals[arg].type);

                    auto tupledefns = tupletype->defns;
                    auto tuplefields = tupletype->fields;

                    promote_type(ctx, tuplefields[fields[0].index], lhs);

                    lhs = ctx.typetable.find_or_create<TupleType>(std::move(tupledefns), std::move(tuplefields));
                  }
                }

                if (!promote(ctx, arg, lhs))
                {
                  ctx.diag.error("type mismatch", ctx.mir.fx.fn, loc);
                  diag_mismatch(ctx, "variable type", arg, lhs);
                }
              }
            }
          }

          if (statement->src.kind() == MIR::RValue::Call)
          {
            auto &[callee, args, loc] = statement->src.get<MIR::RValue::Call>();

            if (any_of(args.begin(), args.end(), [&](auto arg) { return is_indefinite_type(mir.locals[arg].type); }))
            {
              auto scope = Scope(callee.fn, callee.typeargs);

              if (callee.fn->returntype)
              {
                if (is_reference_type(callee.fn->returntype) && !(dst.flags & MIR::Local::Reference) && is_pointer_type(dst.type))
                  dst.type = ctx.typetable.find_or_create<ReferenceType>(remove_pointer_type(dst.type));

                deduce_type(ctx, callee.fn, scope, callee.fn->returntype, dst);

                callee = FnSig(callee.fn, scope.typeargs, callee.throwtype);
              }

              for (auto const &[parm, arg] : zip(callee.parameters(), args))
              {
                scope.goalpost = parm;

                if (is_indefinite_type(mir.locals[arg].type))
                {
                  auto parmtype = resolve_type_as_value(ctx, scope, decl_cast<ParmVarDecl>(parm));

                  if (!promote(ctx, arg, parmtype))
                  {
                    ctx.diag.error("type mismatch", ctx.mir.fx.fn, loc);
                    diag_mismatch(ctx, "parameter type", arg, parmtype);
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  //|///////////////////// solidify /////////////////////////////////////////
  void solidify(LowerContext &ctx, MIR &mir)
  {
    bool changed = false;

    for (size_t arg = 0; arg != mir.locals.size(); ++arg)
    {
      auto dst = mir.locals[arg];

      if (dst.type == ctx.intliteraltype)
        changed |= promote(ctx, arg, type(Builtin::Type_I32));

      if (dst.type == ctx.floatliteraltype)
        changed |= promote(ctx, arg, type(Builtin::Type_F64));

      //if (dst.type->klass() == Type::Array && type_cast<ArrayType>(dst.type)->type == ctx.intliteraltype)
      //  changed |= promote(ctx, arg, ctx.typetable.find_or_create<ArrayType>(type(Builtin::Type_I32), type_cast<ArrayType>(dst.type)->size));
      //
      //if (dst.type->klass() == Type::Array && type_cast<ArrayType>(dst.type)->type == ctx.floatliteraltype)
      //  changed |= promote(ctx, arg, ctx.typetable.find_or_create<ArrayType>(type(Builtin::Type_F64), type_cast<ArrayType>(dst.type)->size));
    }

    if (ctx.diag.has_errored())
      return;

    if (changed)
    {
      backfill(ctx, mir);
    }
  }
}


//|--------------------- Lower ----------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// lower //////////////////////////////////////////////
MIR const &lower(FnSig const &fx, TypeTable &typetable, Diag &diag)
{
  if (auto j = Cache::lookup(fx))
  {
    if (!diag.has_errored() && j->diag.has_errored())
      diag << j->diag;

    return j->mir;
  }

  LowerContext ctx(typetable, diag);

  if (!Cache::begin(fx))
  {
    ctx.diag.error("unable to lower function", fx.fn, fx.fn->loc());

    return Cache::commit(fx, std::move(ctx.mir), ctx.diag);
  }

  seed_stack(ctx.stack, Scope(fx.fn, fx.typeargs));

  ctx.mir.fx = fx;
  ctx.translationunit = decl_cast<TranslationUnitDecl>(get<Decl*>(ctx.stack[0].owner));
  ctx.module = decl_cast<ModuleDecl>(get<Decl*>(ctx.stack[1].owner));

  lower_function(ctx, fx);

#if 0
  dump_mir(ctx.mir);
#endif

  backfill(ctx, ctx.mir);

  return Cache::commit(fx, std::move(ctx.mir), ctx.diag);
}

//|///////////////////// lower //////////////////////////////////////////////
MIR lower(Scope const &scope, Expr *expr, unordered_map<Decl*, MIR::Fragment> const &symbols, TypeTable &typetable, Diag &diag)
{
  LowerContext ctx(typetable, diag);

  seed_stack(ctx.stack, scope);

  ctx.translationunit = decl_cast<TranslationUnitDecl>(get<Decl*>(ctx.stack[0].owner));
  ctx.module = decl_cast<ModuleDecl>(get<Decl*>(ctx.stack[1].owner));
  ctx.is_expression = true;
  ctx.symbols = symbols;

  lower_expression(ctx, expr);

#if 0
  dump_mir(ctx.mir);
#endif

  return std::move(ctx.mir);
}

//|///////////////////// lower //////////////////////////////////////////////
MIR lower(FnSig const &fx, TypeTable &typetable, Diag &diag, long flags)
{
  LowerContext ctx(typetable, diag);

  ctx.mir = lower(fx, typetable, ctx.diag);

  if (ctx.diag.has_errored())
    return ctx.mir;

  if (!is_concrete_type(ctx.mir.locals[0].type))
    ctx.diag.error("unresolved return type", fx.fn, fx.fn->loc());

  solidify(ctx, ctx.mir);

  return std::move(ctx.mir);
}
