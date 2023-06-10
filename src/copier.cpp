//
// typer.cpp
//
// Copyright (c) 2020-2023 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "typer.h"
#include "diag.h"
#include "query.h"
#include "numeric.h"
#include "sema.h"
#include <iostream>
#include <algorithm>

using namespace std;

namespace
{
  struct CopierContext
  {
    Diag &diag;

    vector<Expr*> const &substitutions;

    unordered_map<Decl*, Decl*> typetable;

    CopierContext(vector<Expr*> const &substitutions, Diag &diag)
      : diag(diag), substitutions(substitutions)
    {
    }

    Expr *get(size_t substitution)
    {
      assert(substitution < substitutions.size());

      return substitutions[substitution];
    }
  };

  Type *copier_type(CopierContext &ctx, Type *type);
  Expr *copier_expr(CopierContext &ctx, Expr *expr);
  Decl *copier_decl(CopierContext &ctx, Decl *decl);
  Stmt *copier_stmt(CopierContext &ctx, Stmt *stmt);

  //|///////////////////// copyier_name /////////////////////////////////////
  Ident *copier_name(CopierContext &ctx, Ident *name)
  {
    if (!name)
      return nullptr;

    if (name->kind() == Ident::Dollar)
    {
      auto expr = ctx.get(static_cast<DollarIdent*>(name)->value());

      if (expr->kind() == Expr::StringLiteral)
      {
        return Ident::from(expr_cast<StringLiteralExpr>(expr)->value());
      }

      if (expr->kind() == Expr::IntLiteral)
      {
        return Ident::make_index_ident(expr_cast<IntLiteralExpr>(expr)->value().value);
      }

      if (expr->kind() == Expr::Cast && expr_cast<CastExpr>(expr)->type == Builtin::type(Builtin::Type_DeclidLiteral))
      {
        auto declid = reinterpret_cast<Decl*>(expr_cast<IntLiteralExpr>(expr_cast<CastExpr>(expr)->expr)->value().value);

        switch (declid->kind())
        {
          case Decl::Module:
            return decl_cast<ModuleDecl>(declid)->name;

          case Decl::Function:
            return decl_cast<FunctionDecl>(declid)->name;

          case Decl::Struct:
          case Decl::Union:
          case Decl::VTable:
          case Decl::Concept:
          case Decl::Enum:
            return decl_cast<TagDecl>(declid)->name;

          case Decl::VoidVar:
          case Decl::StmtVar:
          case Decl::ParmVar:
          case Decl::FieldVar:
          case Decl::ThisVar:
          case Decl::ErrorVar:
            return decl_cast<VarDecl>(declid)->name;

          case Decl::EnumConstant:
            return decl_cast<EnumConstantDecl>(declid)->name;

          case Decl::TypeAlias:
            return decl_cast<TypeAliasDecl>(declid)->name;

          case Decl::TypeArg:
            return decl_cast<TypeArgDecl>(declid)->name;

          default:
            break;
        }
      }
    }

    return name;
  }

  //|///////////////////// typeref //////////////////////////////////////////
  Type *copier_type(CopierContext &ctx, TypeRefType *typeref)
  {
    assert(typeref->args.empty());

    if (typeref->decl->kind() == Decl::DeclRef && decl_cast<DeclRefDecl>(typeref->decl)->argless)
    {
      auto name = decl_cast<DeclRefDecl>(typeref->decl)->name;

      if (name->kind() == Ident::Dollar)
      {
        auto expr = ctx.get(static_cast<DollarIdent*>(name)->value());

        if (expr->kind() == Expr::Cast && expr_cast<CastExpr>(expr)->type == Builtin::type(Builtin::Type_TypeidLiteral))
        {
          return reinterpret_cast<Type*>(expr_cast<IntLiteralExpr>(expr_cast<CastExpr>(expr)->expr)->value().value);
        }
      }
    }

    if (auto j = ctx.typetable.find(typeref->decl); j != ctx.typetable.end())
      return new TypeRefType(j->second);

    return new TypeRefType(copier_decl(ctx, typeref->decl));
  }

  //|///////////////////// copyier_type /////////////////////////////////////
  Type *copier_type(CopierContext &ctx, Type *type)
  {
    switch (type->klass())
    {
      case Type::Builtin:
        return type;

      case Type::Const:
        return new ConstType(copier_type(ctx, type_cast<ConstType>(type)->type));

      case Type::QualArg:
        return new QualArgType(copier_type(ctx, type_cast<QualArgType>(type)->type), type_cast<QualArgType>(type)->qualifiers);

      case Type::Pointer:
        return new PointerType(copier_type(ctx, type_cast<PointerType>(type)->type));

      case Type::Reference:
        return new ReferenceType(copier_type(ctx, type_cast<ReferenceType>(type)->type));

      case Type::Array:
        return new ArrayType(copier_type(ctx, type_cast<ArrayType>(type)->type), copier_type(ctx, type_cast<ArrayType>(type)->size));

      case Type::Tuple: {
        auto fields = type_cast<TupleType>(type)->fields;
        for (auto &field : fields)
          field = copier_type(ctx, field);
        return new TupleType(fields);
      }

      case Type::Function: {
        auto returntype = copier_type(ctx, type_cast<FunctionType>(type)->returntype);
        auto paramtuple = copier_type(ctx, type_cast<FunctionType>(type)->paramtuple);
        auto throwtype = copier_type(ctx, type_cast<FunctionType>(type)->throwtype);
        return new FunctionType(returntype, paramtuple, throwtype);
      }

      case Type::TypeRef:
        return copier_type(ctx, type_cast<TypeRefType>(type));

      case Type::TypeLit:
        return new TypeLitType(copier_expr(ctx, type_cast<TypeLitType>(type)->value));

      case Type::TypeArg:
        return type;

      default:
        assert(false);
    }

    return type;
  }

  //|///////////////////// arrayliteral /////////////////////////////////////
  Expr *copier_expr(CopierContext &ctx, ArrayLiteralExpr *arrayliteral)
  {
    std::vector<Expr*> elements;

    for (auto &element : arrayliteral->elements)
    {
      elements.push_back(copier_expr(ctx, element));
    }

    return new ArrayLiteralExpr(elements, copier_type(ctx, arrayliteral->size), arrayliteral->loc());
  }

  //|///////////////////// compoundliteral //////////////////////////////////
  Expr *copier_expr(CopierContext &ctx, CompoundLiteralExpr *compoundliteral)
  {
    std::vector<Expr*> fields;

    for (auto &field: compoundliteral->fields)
    {
      fields.push_back(copier_expr(ctx, field));
    }

    return new CompoundLiteralExpr(fields, compoundliteral->loc());
  }

  //|///////////////////// exprref_expression ///////////////////////////////
  Expr *copier_expr(CopierContext &ctx, ExprRefExpr *exprref)
  {
    return new ExprRefExpr(copier_expr(ctx, exprref->expr), exprref->qualifiers, exprref->loc());
  }

  //|///////////////////// paren_expression /////////////////////////////////
  Expr *copier_expr(CopierContext &ctx, ParenExpr *paren)
  {
    return new ParenExpr(copier_expr(ctx, paren->subexpr), paren->loc());
  }

  //|///////////////////// unary_expression /////////////////////////////////
  Expr *copier_expr(CopierContext &ctx, UnaryOpExpr *unaryop)
  {
    return new UnaryOpExpr(unaryop->op(), copier_expr(ctx, unaryop->subexpr), unaryop->loc());
  }

  //|///////////////////// binary_expression ////////////////////////////////
  Expr *copier_expr(CopierContext &ctx, BinaryOpExpr *binaryop)
  {
    return new BinaryOpExpr(binaryop->op(), copier_expr(ctx, binaryop->lhs), copier_expr(ctx, binaryop->rhs), binaryop->loc());
  }

  //|///////////////////// ternary_expression ///////////////////////////////
  Expr *copier_expr(CopierContext &ctx, TernaryOpExpr *ternaryop)
  {
    return new TernaryOpExpr(copier_expr(ctx, ternaryop->cond), copier_expr(ctx, ternaryop->lhs), copier_expr(ctx, ternaryop->rhs), ternaryop->loc());
  }

  //|///////////////////// call_expression //////////////////////////////////
  Expr *copier_expr(CopierContext &ctx, CallExpr *call)
  {
    auto result = new CallExpr(copier_decl(ctx, call->callee), call->loc());

    for (auto &parm : call->parms)
      result->parms.push_back(copier_expr(ctx, parm));

    for (auto &[name, parm] : call->namedparms)
      result->namedparms.emplace(name, copier_expr(ctx, parm));

    if (call->base)
      result->base = copier_expr(ctx, call->base);

    return result;
  }

  //|///////////////////// sizeof_expression ////////////////////////////////
  Expr *copier_expr(CopierContext &ctx, SizeofExpr *call)
  {
    if (call->type)
    {
      return new SizeofExpr(copier_type(ctx, call->type), call->loc());
    }

    if (call->expr)
    {
      return new SizeofExpr(copier_expr(ctx, call->expr), call->loc());
    }

    return call;
  }

  //|///////////////////// alignof_expression ///////////////////////////////
  Expr *copier_expr(CopierContext &ctx, AlignofExpr *call)
  {
    if (call->type)
    {
      return new AlignofExpr(copier_type(ctx, call->type), call->loc());
    }

    if (call->decl)
    {
      return new AlignofExpr(copier_decl(ctx, call->decl), call->loc());
    }

    return call;
  }

  //|///////////////////// offsetof_expression //////////////////////////////
  Expr *copier_expr(CopierContext &ctx, OffsetofExpr *call)
  {
    return new OffsetofExpr(copier_decl(ctx, call->decl), call->loc());
  }

  //|///////////////////// instanceof_expression ////////////////////////////
  Expr *copier_expr(CopierContext &ctx, InstanceofExpr *call)
  {
    return new InstanceofExpr(copier_type(ctx, call->type), copier_type(ctx, call->instance), call->loc());
  }

  //|///////////////////// throws_expression ////////////////////////////////
  Expr *copier_expr(CopierContext &ctx, ThrowsExpr *call)
  {
    return new ThrowsExpr(copier_expr(ctx, call->expr), call->loc());
  }

  //|///////////////////// typeid_expression ////////////////////////////////
  Expr *copier_expr(CopierContext &ctx, TypeidExpr *call)
  {
    return new TypeidExpr(copier_decl(ctx, call->decl), call->loc());
  }

  //|///////////////////// cast_expression //////////////////////////////////
  Expr *copier_expr(CopierContext &ctx, CastExpr *call)
  {
    return new CastExpr(copier_type(ctx, call->type), copier_expr(ctx, call->expr), call->loc());
  }

  //|///////////////////// new_expression ///////////////////////////////////
  Expr *copier_expr(CopierContext &ctx, NewExpr *call)
  {
    auto result = new NewExpr(copier_type(ctx, call->type), copier_expr(ctx, call->address), call->loc());

    for (auto &parm : call->parms)
      result->parms.push_back(copier_expr(ctx, parm));

    for (auto &[name, parm] : call->namedparms)
      result->namedparms.emplace(name, copier_expr(ctx, parm));

    return result;
  }

  //|///////////////////// requires_expression //////////////////////////////
  Expr *copier_expr(CopierContext &ctx, RequiresExpr *requires)
  {
    return new RequiresExpr(copier_decl(ctx, requires->decl), requires->loc());
  }

  //|///////////////////// match_expression /////////////////////////////////
  Expr *copier_expr(CopierContext &ctx, MatchExpr *match)
  {
    return new MatchExpr(copier_decl(ctx, match->decl), match->loc());
  }

  //|///////////////////// lambda_expression ////////////////////////////////
  Expr *copier_expr(CopierContext &ctx, LambdaExpr *lambda)
  {
    return new LambdaExpr(copier_decl(ctx, lambda->decl), lambda->loc());
  }

  //|///////////////////// declref_expression ///////////////////////////////
  Expr *copier_expr(CopierContext &ctx, DeclRefExpr *declexpr)
  {
    if (declexpr->base)
    {
      return new DeclRefExpr(copier_expr(ctx, declexpr->base), copier_decl(ctx, declexpr->decl), declexpr->loc());
    }

    if (declexpr->decl->kind() == Decl::DeclRef && decl_cast<DeclRefDecl>(declexpr->decl)->argless)
    {
      auto name = decl_cast<DeclRefDecl>(declexpr->decl)->name;

      if (name->kind() == Ident::Dollar)
      {
        return ctx.get(static_cast<DollarIdent*>(name)->value());
      }
    }

    return new DeclRefExpr(copier_decl(ctx, declexpr->decl), declexpr->loc());
  }

  //|///////////////////// fragment_expression //////////////////////////////
  Expr *copier_expr(CopierContext &ctx, FragmentExpr *fragment)
  {
    vector<Expr*> args;
    for (auto &arg : fragment->args)
      args.push_back(arg);

    vector<Decl*> decls;
    for (auto &decl : fragment->decls)
      decls.push_back(copier_decl(ctx, decl));

    return new FragmentExpr(std::move(args), std::move(decls), fragment->loc());
  }

  //|///////////////////// copier_expr ///////////////////////////////////////
  Expr *copier_expr(CopierContext &ctx, Expr *expr)
  {
    switch (expr->kind())
    {
      case Expr::BoolLiteral:
      case Expr::CharLiteral:
      case Expr::IntLiteral:
      case Expr::FloatLiteral:
      case Expr::StringLiteral:
      case Expr::PointerLiteral:
      case Expr::FunctionPointer:
        return expr;

      case Expr::ArrayLiteral:
        return copier_expr(ctx, expr_cast<ArrayLiteralExpr>(expr));

      case Expr::CompoundLiteral:
        return copier_expr(ctx, expr_cast<CompoundLiteralExpr>(expr));

      case Expr::ExprRef:
        return copier_expr(ctx, expr_cast<ExprRefExpr>(expr));

      case Expr::Paren:
        return copier_expr(ctx, expr_cast<ParenExpr>(expr));

      case Expr::UnaryOp:
        return copier_expr(ctx, expr_cast<UnaryOpExpr>(expr));

      case Expr::BinaryOp:
        return copier_expr(ctx, expr_cast<BinaryOpExpr>(expr));

      case Expr::TernaryOp:
        return copier_expr(ctx, expr_cast<TernaryOpExpr>(expr));

      case Expr::Call:
        return copier_expr(ctx, expr_cast<CallExpr>(expr));

      case Expr::Sizeof:
        return copier_expr(ctx, expr_cast<SizeofExpr>(expr));

      case Expr::Alignof:
        return copier_expr(ctx, expr_cast<AlignofExpr>(expr));

      case Expr::Offsetof:
        return copier_expr(ctx, expr_cast<OffsetofExpr>(expr));

      case Expr::Instanceof:
        return copier_expr(ctx, expr_cast<InstanceofExpr>(expr));

      case Expr::Throws:
        return copier_expr(ctx, expr_cast<ThrowsExpr>(expr));

      case Expr::Typeid:
        return copier_expr(ctx, expr_cast<TypeidExpr>(expr));

      case Expr::Cast:
        return copier_expr(ctx, expr_cast<CastExpr>(expr));

      case Expr::New:
        return copier_expr(ctx, expr_cast<NewExpr>(expr));

      case Expr::Requires:
        return copier_expr(ctx, expr_cast<RequiresExpr>(expr));

      case Expr::Match:
        return copier_expr(ctx, expr_cast<MatchExpr>(expr));

      case Expr::Lambda:
        return copier_expr(ctx, expr_cast<LambdaExpr>(expr));

      case Expr::DeclRef:
        return copier_expr(ctx, expr_cast<DeclRefExpr>(expr));

      case Expr::Fragment:
        return copier_expr(ctx, expr_cast<FragmentExpr>(expr));

      default:
        assert(false);
    }

    return nullptr;
  }

  //|///////////////////// IdentPattern /////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, IdentPatternDecl *pattern)
  {
    auto result = new IdentPatternDecl(pattern->loc());

    result->flags = pattern->flags;
    result->name = copier_name(ctx, pattern->name);

    return result;
  }

  //|///////////////////// TuplePattern /////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, TuplePatternDecl *pattern)
  {
    auto result = new TuplePatternDecl(pattern->loc());

    result->flags = pattern->flags;

    for (auto &binding : pattern->bindings)
      result->bindings.push_back(copier_decl(ctx, binding));

    return result;
  }


  //|///////////////////// voidvar //////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, VoidVarDecl *var)
  {
    auto result = new VoidVarDecl(var->loc());

    result->flags = var->flags;
    result->name = copier_name(ctx, var->name);
    result->type = copier_type(ctx, var->type);

    if (var->pattern)
      result->pattern = copier_decl(ctx, var->pattern);

    return result;
  }

  //|///////////////////// stmtvar //////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, StmtVarDecl *var)
  {
    auto result = new StmtVarDecl(var->loc());

    result->flags = var->flags;
    result->name = copier_name(ctx, var->name);
    result->type = copier_type(ctx, var->type);
    result->value = copier_expr(ctx, var->value);

    if (var->pattern)
      result->pattern = copier_decl(ctx, var->pattern);

    return result;
  }

  //|///////////////////// parmvar //////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, ParmVarDecl *var)
  {
    auto result = new ParmVarDecl(var->loc());

    result->flags = var->flags;
    result->name = copier_name(ctx, var->name);
    result->type = copier_type(ctx, var->type);

    if (var->defult)
      result->defult = copier_expr(ctx, var->defult);

    return result;
  }

  //|///////////////////// thisvar //////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, ThisVarDecl *var)
  {
    auto result = new ThisVarDecl(var->loc());

    result->flags = var->flags;
    result->name = copier_name(ctx, var->name);
    result->type = copier_type(ctx, var->type);

    return result;
  }

  //|///////////////////// errorvar /////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, ErrorVarDecl *var)
  {
    auto result = new ErrorVarDecl(var->loc());

    result->flags = var->flags;
    result->name = copier_name(ctx, var->name);
    result->type = copier_type(ctx, var->type);

    return result;
  }

  //|///////////////////// lambdavar ////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, LambdaVarDecl *var)
  {
    auto result = new LambdaVarDecl(var->loc());

    result->flags = var->flags;
    result->name = copier_name(ctx, var->name);
    result->type = copier_type(ctx, var->type);
    result->arg = copier_decl(ctx, var->arg);
    result->value = copier_expr(ctx, var->value);

    return result;
  }

  //|///////////////////// casevar //////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, CaseVarDecl *var)
  {
    auto result = new CaseVarDecl(var->loc());

    result->flags = var->flags;
    result->name = copier_name(ctx, var->name);
    result->type = copier_type(ctx, var->type);

    if (var->pattern)
      result->pattern = copier_decl(ctx, var->pattern);

    if (var->value)
      result->value = copier_expr(ctx, var->value);

    return result;
  }

  //|///////////////////// typearg //////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, TypeArgDecl *typearg)
  {
    auto result = new TypeArgDecl(typearg->loc());

    result->flags = typearg->flags;
    result->name = copier_name(ctx, typearg->name);

    if (typearg->defult)
      result->defult = copier_type(ctx, typearg->defult);

    return result;
  }

  //|///////////////////// declref //////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, DeclRefDecl *declref)
  {
    auto result = new DeclRefDecl(declref->loc());

    result->flags = declref->flags;
    result->name = copier_name(ctx, declref->name);

    for (auto &arg : declref->args)
      result->args.push_back(copier_type(ctx, arg));

    for (auto &[name, arg] : declref->namedargs)
      result->namedargs.emplace(name, copier_type(ctx, arg));

    result->argless = declref->argless;

    return result;
  }

  //|///////////////////// declscoped ///////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, DeclScopedDecl *declref)
  {
    auto result = new DeclScopedDecl(declref->loc());

    result->flags = declref->flags;

    for (auto &decl : declref->decls)
      result->decls.push_back(copier_decl(ctx, decl));

    if (result->decls[0]->kind() == Decl::DeclRef && decl_cast<DeclRefDecl>(result->decls[0])->argless)
    {
      auto name = decl_cast<DeclRefDecl>(result->decls[0])->name;

      if (name->kind() == Ident::Dollar)
      {
        auto expr = ctx.get(static_cast<DollarIdent*>(name)->value());

        if (expr->kind() == Expr::Cast && expr_cast<CastExpr>(expr)->type == Builtin::type(Builtin::Type_TypeidLiteral))
        {
          result->decls[0] = new TypeNameDecl(reinterpret_cast<Type*>(expr_cast<IntLiteralExpr>(expr_cast<CastExpr>(expr)->expr)->value().value), result->decls[0]->loc());
        }
      }
    }

    return result;
  }

  //|///////////////////// typename /////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, TypeNameDecl *declref)
  {
    auto result = new TypeNameDecl(declref->loc());

    result->flags = declref->flags;
    result->type = copier_type(ctx, declref->type);

    return result;
  }

  //|///////////////////// typeof ///////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, TypeOfDecl *typedecl)
  {
    auto result = new TypeOfDecl(typedecl->loc());

    result->flags = typedecl->flags;

    result->expr = copier_expr(ctx, typedecl->expr);

    return result;
  }

  //|///////////////////// typealias ////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, TypeAliasDecl *typealias)
  {
    auto result = new TypeAliasDecl(typealias->loc());

    result->flags = typealias->flags;
    result->name = copier_name(ctx, typealias->name);

    for (auto &arg : typealias->args)
      result->args.push_back(copier_decl(ctx, arg));

    result->type = copier_type(ctx, typealias->type);

    return result;
  }

  //|///////////////////// tagdecl //////////////////////////////////////////
  void copier_decl(CopierContext &ctx, TagDecl *result, TagDecl *tagdecl)
  {
    ctx.typetable.emplace(tagdecl, result);

    result->flags = tagdecl->flags;
    result->name = copier_name(ctx, tagdecl->name);

    for (auto &arg : tagdecl->args)
      result->args.push_back(copier_decl(ctx, arg));

    if (tagdecl->basetype)
      result->basetype = copier_type(ctx, tagdecl->basetype);

    for (auto &decl : tagdecl->decls)
      result->decls.push_back(copier_decl(ctx, decl));
  }

  //|///////////////////// struct ///////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, StructDecl *strct)
  {
    auto result = new StructDecl(strct->loc());

    copier_decl(ctx, result, decl_cast<TagDecl>(strct));

    return result;
  }

  //|///////////////////// union ////////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, UnionDecl *unnion)
  {
    auto result = new UnionDecl(unnion->loc());

    copier_decl(ctx, result, decl_cast<TagDecl>(unnion));

    return result;
  }

  //|///////////////////// vtable ///////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, VTableDecl *vtable)
  {
    auto result = new VTableDecl(vtable->loc());

    copier_decl(ctx, result, decl_cast<TagDecl>(vtable));

    return result;
  }

  //|///////////////////// concept //////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, ConceptDecl *koncept)
  {
    auto result = new ConceptDecl(koncept->loc());

    copier_decl(ctx, result, decl_cast<TagDecl>(koncept));

    return result;
  }

  //|///////////////////// requires /////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, RequiresDecl *reqires)
  {
    auto result = new RequiresDecl(reqires->loc());

    result->flags = reqires->flags;

    result->fn = copier_decl(ctx, reqires->fn);

    if (reqires->requirestype)
      result->requirestype = copier_type(ctx, reqires->requirestype);

    return result;
  }

  //|///////////////////// lambda ///////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, LambdaDecl *lambda)
  {
    auto result = new LambdaDecl(lambda->loc());

    copier_decl(ctx, result, decl_cast<TagDecl>(lambda));

    for (auto &decl : lambda->decls)
      if (decl == lambda->fn)
        result->fn = result->decls[&decl - &lambda->decls[0]];

    for (auto &capture : lambda->captures)
      result->captures.push_back(copier_decl(ctx, capture));

    return result;
  }

  //|///////////////////// enum /////////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, EnumDecl *enumm)
  {
    auto result = new EnumDecl(enumm->loc());

    copier_decl(ctx, result, decl_cast<TagDecl>(enumm));

    return result;
  }

  //|///////////////////// constant /////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, EnumConstantDecl *constant)
  {
    auto result = new EnumConstantDecl(constant->loc());

    result->flags = constant->flags;
    result->name = copier_name(ctx, constant->name);

    if (constant->value)
      result->value = copier_expr(ctx, constant->value);

    return result;
  }

  //|///////////////////// field ////////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, FieldVarDecl *field)
  {
    auto result = new FieldVarDecl(field->loc());

    result->flags = field->flags;
    result->name = copier_name(ctx, field->name);
    result->type = copier_type(ctx, field->type);

    if (field->defult)
      result->defult = copier_expr(ctx, field->defult);

    return result;
  }

  //|///////////////////// initialiser //////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, InitialiserDecl *init)
  {
    auto result = new InitialiserDecl(init->loc());

    result->flags = init->flags;
    result->name = copier_name(ctx, init->name);

    for (auto &parm : init->parms)
      result->parms.push_back(copier_expr(ctx, parm));

    for (auto &[name, parm] : init->namedparms)
      result->namedparms.emplace(name, copier_expr(ctx, parm));

    return result;
  }

  //|///////////////////// case /////////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, CaseDecl *casse)
  {
    auto result = new CaseDecl(casse->loc());

    result->flags = casse->flags;

    if (casse->label)
      result->label = copier_expr(ctx, casse->label);

    if (casse->parm)
      result->parm = copier_decl(ctx, casse->parm);

    if (casse->body)
      result->body = copier_stmt(ctx, casse->body);

    return result;
  }

  //|///////////////////// import ///////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, ImportDecl *imprt)
  {
    auto result = new ImportDecl(imprt->loc());

    result->flags = imprt->flags;
    result->decl = imprt->decl;
    result->alias = imprt->alias;

    for (auto &usein : imprt->usings)
      result->usings.push_back(copier_decl(ctx, usein));

    return result;
  }

  //|///////////////////// using ////////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, UsingDecl *usein)
  {
    auto result = new UsingDecl(usein->loc());

    result->flags = usein->flags;
    result->decl = usein->decl;

    return result;
  }

  //|///////////////////// function /////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, FunctionDecl *fn)
  {
    auto result = new FunctionDecl(fn->loc());

    result->flags = fn->flags;
    result->name = copier_name(ctx, fn->name);
    result->builtin = fn->builtin;

    for (auto &arg : fn->args)
      result->args.push_back(copier_decl(ctx, arg));

    for (auto &parm : fn->parms)
      result->parms.push_back(copier_decl(ctx, parm));

    if (fn->throws)
      result->throws = copier_type(ctx, fn->throws);

    if (fn->returntype)
      result->returntype = copier_type(ctx, fn->returntype);

    if (fn->match)
      result->match = copier_expr(ctx, fn->match);

    if (fn->where)
      result->where = copier_expr(ctx, fn->where);

    for (auto &init : fn->inits)
      result->inits.push_back(copier_decl(ctx, init));

    if (fn->body)
      result->body = copier_stmt(ctx, fn->body);

    return result;
  }

  //|///////////////////// run //////////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, RunDecl *run)
  {
    auto result = new RunDecl(run->loc());

    result->flags = run->flags;
    result->fn = copier_decl(ctx, run->fn);

    return result;
  }

  //|///////////////////// if ///////////////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, IfDecl *ifd)
  {
    auto result = new IfDecl(ifd->loc());

    result->flags = ifd->flags;
    result->cond = copier_expr(ctx, ifd->cond);

    for (auto &decl : ifd->decls)
      result->decls.push_back(copier_decl(ctx, decl));

    if (ifd->elseif)
      result->elseif = copier_decl(ctx, ifd->elseif);

    return result;
  }

  //|///////////////////// copier_decl ///////////////////////////////////////
  Decl *copier_decl(CopierContext &ctx, Decl *decl)
  {
    switch (decl->kind())
    {
      case Decl::IdentPattern:
        decl = copier_decl(ctx, decl_cast<IdentPatternDecl>(decl));
        break;

      case Decl::TuplePattern:
        decl = copier_decl(ctx, decl_cast<TuplePatternDecl>(decl));
        break;

      case Decl::VoidVar:
        decl = copier_decl(ctx, decl_cast<VoidVarDecl>(decl));
        break;

      case Decl::StmtVar:
        decl = copier_decl(ctx, decl_cast<StmtVarDecl>(decl));
        break;

      case Decl::ParmVar:
        decl = copier_decl(ctx, decl_cast<ParmVarDecl>(decl));
        break;

      case Decl::ThisVar:
        decl = copier_decl(ctx, decl_cast<ThisVarDecl>(decl));
        break;

      case Decl::ErrorVar:
        decl = copier_decl(ctx, decl_cast<ErrorVarDecl>(decl));
        break;

      case Decl::LambdaVar:
        decl = copier_decl(ctx, decl_cast<LambdaVarDecl>(decl));
        break;

      case Decl::CaseVar:
        decl = copier_decl(ctx, decl_cast<CaseVarDecl>(decl));
        break;

      case Decl::TypeArg:
        decl = copier_decl(ctx, decl_cast<TypeArgDecl>(decl));
        break;

      case Decl::DeclRef:
        decl = copier_decl(ctx, decl_cast<DeclRefDecl>(decl));
        break;

      case Decl::DeclScoped:
        decl = copier_decl(ctx, decl_cast<DeclScopedDecl>(decl));
        break;

      case Decl::TypeName:
        decl = copier_decl(ctx, decl_cast<TypeNameDecl>(decl));
        break;

      case Decl::TypeOf:
        decl = copier_decl(ctx, decl_cast<TypeOfDecl>(decl));
        break;

      case Decl::TypeAlias:
        decl = copier_decl(ctx, decl_cast<TypeAliasDecl>(decl));
        break;

      case Decl::Struct:
        decl = copier_decl(ctx, decl_cast<StructDecl>(decl));
        break;

      case Decl::Union:
        decl = copier_decl(ctx, decl_cast<UnionDecl>(decl));
        break;

      case Decl::VTable:
        decl = copier_decl(ctx, decl_cast<VTableDecl>(decl));
        break;

      case Decl::Concept:
        decl = copier_decl(ctx, decl_cast<ConceptDecl>(decl));
        break;

      case Decl::Requires:
        decl = copier_decl(ctx, decl_cast<RequiresDecl>(decl));
        break;

      case Decl::Lambda:
        decl = copier_decl(ctx, decl_cast<LambdaDecl>(decl));
        break;

      case Decl::Enum:
        decl = copier_decl(ctx, decl_cast<EnumDecl>(decl));
        break;

      case Decl::EnumConstant:
        decl = copier_decl(ctx, decl_cast<EnumConstantDecl>(decl));
        break;

      case Decl::FieldVar:
        decl = copier_decl(ctx, decl_cast<FieldVarDecl>(decl));
        break;

      case Decl::Initialiser:
        decl = copier_decl(ctx, decl_cast<InitialiserDecl>(decl));
        break;

      case Decl::Case:
        decl = copier_decl(ctx, decl_cast<CaseDecl>(decl));
        break;

      case Decl::Import:
        decl = copier_decl(ctx, decl_cast<ImportDecl>(decl));
        break;

      case Decl::Using:
        decl = copier_decl(ctx, decl_cast<UsingDecl>(decl));
        break;

      case Decl::Function:
        decl = copier_decl(ctx, decl_cast<FunctionDecl>(decl));
        break;

      case Decl::Run:
        decl = copier_decl(ctx, decl_cast<RunDecl>(decl));
        break;

      case Decl::If:
        decl = copier_decl(ctx, decl_cast<IfDecl>(decl));
        break;

      default:
        assert(false);
    }

    return decl;
  }

  //|///////////////////// injection_statement //////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, InjectionStmt *injection)
  {
    auto result = new InjectionStmt(injection->loc());

    result->expr = copier_expr(ctx, injection->expr);

    return result;
  }

  //|///////////////////// declaration_statement ////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, DeclStmt *declstmt)
  {
    auto result = new DeclStmt(declstmt->loc());

    result->decl = copier_decl(ctx, declstmt->decl);

    return result;
  }

  //|///////////////////// expression_statement /////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, ExprStmt *exprstmt)
  {
    auto result = new ExprStmt(exprstmt->loc());

    if (exprstmt->expr)
      result->expr = copier_expr(ctx, exprstmt->expr);

    return result;
  }

  //|///////////////////// if_statement /////////////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, IfStmt *ifs)
  {
    auto result = new IfStmt(ifs->loc());

    result->flags = ifs->flags;

    for (auto &init : ifs->inits)
      result->inits.push_back(copier_stmt(ctx, init));

    result->cond = copier_expr(ctx, ifs->cond);

    if (ifs->stmts[0])
      result->stmts[0] = copier_stmt(ctx, ifs->stmts[0]);

    if (ifs->stmts[1])
      result->stmts[1] = copier_stmt(ctx, ifs->stmts[1]);

    return result;
  }

  //|///////////////////// for_statement ////////////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, ForStmt *fors)
  {
    auto result = new ForStmt(fors->loc());

    result->flags = fors->flags;

    for (auto &init : fors->inits)
      result->inits.push_back(copier_stmt(ctx, init));

    if (fors->cond)
      result->cond = copier_expr(ctx, fors->cond);

    result->stmt = copier_stmt(ctx, fors->stmt);

    for (auto &iter : fors->iters)
      result->iters.push_back(copier_stmt(ctx, iter));

    return result;
  }

  //|///////////////////// rof_statement ////////////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, RofStmt *rofs)
  {
    auto result = new RofStmt(rofs->loc());

    result->flags = rofs->flags;

    for (auto &init : rofs->inits)
      result->inits.push_back(copier_stmt(ctx, init));

    if (rofs->cond)
      result->cond = copier_expr(ctx, rofs->cond);

    result->stmt = copier_stmt(ctx, rofs->stmt);

    for (auto &iter : rofs->iters)
      result->iters.push_back(copier_stmt(ctx, iter));

    return result;
  }

  //|///////////////////// while_statement //////////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, WhileStmt *wile)
  {
    auto result = new WhileStmt(wile->loc());

    for (auto &init : wile->inits)
      result->inits.push_back(copier_stmt(ctx, init));

    for (auto &iter : wile->iters)
      result->iters.push_back(copier_stmt(ctx, iter));

    result->cond = copier_expr(ctx, wile->cond);
    result->stmt = copier_stmt(ctx, wile->stmt);

    return result;
  }

  //|///////////////////// switch_statement /////////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, SwitchStmt *swtch)
  {
    auto result = new SwitchStmt(swtch->loc());

    for (auto &init : swtch->inits)
      result->inits.push_back(copier_stmt(ctx, init));

    result->cond = copier_expr(ctx, swtch->cond);

    for (auto &decl : swtch->decls)
      result->decls.push_back(copier_decl(ctx, decl));

    return result;
  }

  //|///////////////////// goto_statement ///////////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, GotoStmt *gotoo)
  {
    auto result = new GotoStmt(gotoo->loc());

    if (gotoo->label)
      result->label = copier_expr(ctx, gotoo->label);

    return result;
  }

  //|///////////////////// try_statement ////////////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, TryStmt *trys)
  {
    auto result = new TryStmt(trys->loc());

    result->body = copier_stmt(ctx, trys->body);
    result->errorvar = copier_decl(ctx, trys->errorvar);
    result->handler = copier_stmt(ctx, trys->handler);

    return result;
  }

  //|///////////////////// throw_statement //////////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, ThrowStmt *throwe)
  {
    auto result = new ThrowStmt(throwe->loc());

    result->expr = copier_expr(ctx, throwe->expr);

    return result;
  }

  //|///////////////////// break_statement //////////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, BreakStmt *brek)
  {
    return new BreakStmt(brek->loc());
  }

  //|///////////////////// continue_statement /////////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, ContinueStmt *continu)
  {
    return new ContinueStmt(continu->loc());
  }

  //|///////////////////// return_statement /////////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, ReturnStmt *retrn)
  {
    auto result = new ReturnStmt(retrn->loc());

    if (retrn->expr)
      result->expr = copier_expr(ctx, retrn->expr);

    return result;
  }

  //|///////////////////// compound_statement ///////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, CompoundStmt *compound)
  {
    auto result = new CompoundStmt(compound->loc());

    for (auto &stmt : compound->stmts)
      result->stmts.push_back(copier_stmt(ctx, stmt));

    result->endloc = compound->endloc;

    return result;
  }

  //|///////////////////// copier_stmt //////////////////////////////////////
  Stmt *copier_stmt(CopierContext &ctx, Stmt *stmt)
  {
    switch (stmt->kind())
    {
      case Stmt::Null:
        stmt = new NullStmt(stmt->loc());
        break;

      case Stmt::Declaration:
        stmt = copier_stmt(ctx, stmt_cast<DeclStmt>(stmt));
        break;

      case Stmt::Expression:
        stmt = copier_stmt(ctx, stmt_cast<ExprStmt>(stmt));
        break;

      case Stmt::If:
        stmt = copier_stmt(ctx, stmt_cast<IfStmt>(stmt));
        break;

      case Stmt::For:
        stmt = copier_stmt(ctx, stmt_cast<ForStmt>(stmt));
        break;

      case Stmt::Rof:
        stmt = copier_stmt(ctx, stmt_cast<RofStmt>(stmt));
        break;

      case Stmt::While:
        stmt = copier_stmt(ctx, stmt_cast<WhileStmt>(stmt));
        break;

      case Stmt::Switch:
        stmt = copier_stmt(ctx, stmt_cast<SwitchStmt>(stmt));
        break;

      case Stmt::Goto:
        stmt = copier_stmt(ctx, stmt_cast<GotoStmt>(stmt));
        break;

      case Stmt::Try:
        stmt = copier_stmt(ctx, stmt_cast<TryStmt>(stmt));
        break;

      case Stmt::Throw:
        stmt = copier_stmt(ctx, stmt_cast<ThrowStmt>(stmt));
        break;

      case Stmt::Break:
        stmt = copier_stmt(ctx, stmt_cast<BreakStmt>(stmt));
        break;

      case Stmt::Continue:
        stmt = copier_stmt(ctx, stmt_cast<ContinueStmt>(stmt));
        break;

      case Stmt::Injection:
        stmt = copier_stmt(ctx, stmt_cast<InjectionStmt>(stmt));
        break;

      case Stmt::Return:
        stmt = copier_stmt(ctx, stmt_cast<ReturnStmt>(stmt));
        break;

      case Stmt::Compound:
        stmt = copier_stmt(ctx, stmt_cast<CompoundStmt>(stmt));
        break;

      default:
        assert(false);
    }

    return stmt;
  }
}

//|--------------------- Copier ---------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// copier /////////////////////////////////////////////
Decl *copier(Decl *root, vector<Expr*> const &substitutions, Diag &diag)
{
  CopierContext ctx(substitutions, diag);

  return copier_decl(ctx, root);
}
