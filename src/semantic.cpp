//
// semantic.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "semantic.h"
#include "diag.h"
#include "query.h"
#include "interp.h"
#include "numeric.h"
#include "sema.h"
#include <iostream>
#include <algorithm>

using namespace std;

namespace
{
  struct SemanticContext
  {
    Diag &diag;

    string file;

    vector<Scope> stack;

    TypeTable typetable;
    unordered_map<Decl*, MIR::Fragment> symbols;

    SemanticContext(Diag &diag)
      : diag(diag)
    {
    }
  };

  void semantic_expr(SemanticContext &ctx, Expr *expr, Sema &sema);
  void semantic_decl(SemanticContext &ctx, Decl *decl, Sema &sema);
  void semantic_statement(SemanticContext &ctx, Stmt *stmt, Sema &sema);

  //|///////////////////// eval /////////////////////////////////////////////
  int eval(SemanticContext &ctx, Scope const &scope, Expr *expr)
  {
    auto result = evaluate(scope, expr, ctx.symbols, ctx.typetable, ctx.diag, expr->loc());

    if (ctx.diag.has_errored())
      return -1;

    if (result.type != Builtin::type(Builtin::Type_Bool))
    {
      if (result.type == Builtin::type(Builtin::Type_IntLiteral))
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

  //|///////////////////// arrayliteral /////////////////////////////////////
  void semantic_expr(SemanticContext &ctx, ArrayLiteralExpr *arrayliteral, Sema &sema)
  {
    for(auto &element : arrayliteral->elements)
    {
      semantic_expr(ctx, element, sema);
    }
  }

  //|///////////////////// paren_expression /////////////////////////////////
  void semantic_expr(SemanticContext &ctx, ParenExpr *paren, Sema &sema)
  {
    semantic_expr(ctx, paren->subexpr, sema);
  }

  //|///////////////////// unary_expression /////////////////////////////////
  void semantic_expr(SemanticContext &ctx, UnaryOpExpr *unaryop, Sema &sema)
  {
    semantic_expr(ctx, unaryop->subexpr, sema);
  }

  //|///////////////////// binary_expression ////////////////////////////////
  void semantic_expr(SemanticContext &ctx, BinaryOpExpr *binaryop, Sema &sema)
  {
    semantic_expr(ctx, binaryop->lhs, sema);
    semantic_expr(ctx, binaryop->rhs, sema);
  }

  //|///////////////////// ternary_expression ///////////////////////////////
  void semantic_expr(SemanticContext &ctx, TernaryOpExpr *ternaryop, Sema &sema)
  {
    semantic_expr(ctx, ternaryop->cond, sema);
    semantic_expr(ctx, ternaryop->lhs, sema);
    semantic_expr(ctx, ternaryop->rhs, sema);
  }

  //|///////////////////// call_expression //////////////////////////////////
  void semantic_expr(SemanticContext &ctx, CallExpr *call, Sema &sema)
  {
    for(auto &parm : call->parms)
    {
      semantic_expr(ctx, parm, sema);
    }

    for(auto &[name, parm] : call->namedparms)
    {
      semantic_expr(ctx, parm, sema);
    }

    if (call->base)
    {
      semantic_expr(ctx, call->base, sema);
    }

    semantic_decl(ctx, call->callee, sema);
  }

  //|///////////////////// sizeof_expression ////////////////////////////////
  void semantic_expr(SemanticContext &ctx, SizeofExpr *call, Sema &sema)
  {
    if (call->expr)
    {
      semantic_expr(ctx, call->expr, sema);
    }
  }

  //|///////////////////// alignof_expression ///////////////////////////////
  void semantic_expr(SemanticContext &ctx, AlignofExpr *call, Sema &sema)
  {
    if (call->expr)
    {
      semantic_expr(ctx, call->expr, sema);
    }
  }

  //|///////////////////// cast_expression //////////////////////////////////
  void semantic_expr(SemanticContext &ctx, CastExpr *cast, Sema &sema)
  {
    if (!cast->type)
    {
      cast->type = sema.make_typearg(sema.make_typearg("var", cast->loc()));
    }

    semantic_expr(ctx, cast->expr, sema);
  }

  //|///////////////////// new_expression ///////////////////////////////////
  void semantic_expr(SemanticContext &ctx, NewExpr *call, Sema &sema)
  {
    semantic_expr(ctx, call->address, sema);

    for(auto &parm : call->parms)
    {
      semantic_expr(ctx, parm, sema);
    }

    for(auto &[name, parm] : call->namedparms)
    {
      semantic_expr(ctx, parm, sema);
    }
  }

  //|///////////////////// lambda_expression ////////////////////////////////
  void semantic_expr(SemanticContext &ctx, LambdaExpr *lambda, Sema &sema)
  {
    semantic_decl(ctx, lambda->decl, sema);
  }

  //|///////////////////// declref_expression ///////////////////////////////
  void semantic_expr(SemanticContext &ctx, DeclRefExpr *declexpr, Sema &sema)
  {
    if (declexpr->base)
    {
      semantic_expr(ctx, declexpr->base, sema);
    }

    semantic_decl(ctx, declexpr->decl, sema);
  }

  //|///////////////////// expression ///////////////////////////////////////
  void semantic_expr(SemanticContext &ctx, Expr *expr, Sema &sema)
  {
    switch (expr->kind())
    {
      case Expr::BoolLiteral:
      case Expr::CharLiteral:
      case Expr::IntLiteral:
      case Expr::FloatLiteral:
      case Expr::StringLiteral:
      case Expr::PtrLiteral:
        break;

      case Expr::ArrayLiteral:
        semantic_expr(ctx, expr_cast<ArrayLiteralExpr>(expr), sema);
        break;

      case Expr::Paren:
        semantic_expr(ctx, expr_cast<ParenExpr>(expr), sema);
        break;

      case Expr::UnaryOp:
        semantic_expr(ctx, expr_cast<UnaryOpExpr>(expr), sema);
        break;

      case Expr::BinaryOp:
        semantic_expr(ctx, expr_cast<BinaryOpExpr>(expr), sema);
        break;

      case Expr::TernaryOp:
        semantic_expr(ctx, expr_cast<TernaryOpExpr>(expr), sema);
        break;

      case Expr::Call:
        semantic_expr(ctx, expr_cast<CallExpr>(expr), sema);
        break;

      case Expr::Sizeof:
        semantic_expr(ctx, expr_cast<SizeofExpr>(expr), sema);
        break;

      case Expr::Alignof:
        semantic_expr(ctx, expr_cast<AlignofExpr>(expr), sema);
        break;

      case Expr::Cast:
        semantic_expr(ctx, expr_cast<CastExpr>(expr), sema);
        break;

      case Expr::New:
        semantic_expr(ctx, expr_cast<NewExpr>(expr), sema);
        break;

      case Expr::Lambda:
        semantic_expr(ctx, expr_cast<LambdaExpr>(expr), sema);
        break;

      case Expr::DeclRef:
        semantic_expr(ctx, expr_cast<DeclRefExpr>(expr), sema);
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// voidvar //////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, VoidVarDecl *var, Sema &sema)
  {
  }

  //|///////////////////// stmtvar //////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, StmtVarDecl *var, Sema &sema)
  {
    semantic_expr(ctx, var->value, sema);
  }

  //|///////////////////// parmvar //////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, ParmVarDecl *var, Sema &sema)
  {
    if (var->defult)
    {
      semantic_expr(ctx, var->defult, sema);
    }
  }

  //|///////////////////// thisvar //////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, ThisVarDecl *var, Sema &sema)
  {
  }

  //|///////////////////// errorvar /////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, ErrorVarDecl *var, Sema &sema)
  {
  }

  //|///////////////////// rangevar /////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, RangeVarDecl *var, Sema &sema)
  {
    semantic_expr(ctx, var->range, sema);
  }

  //|///////////////////// typeof ///////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, TypeOfDecl *typedecl, Sema &sema)
  {
    semantic_expr(ctx, typedecl->expr, sema);
  }

  //|///////////////////// typealias ////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, TypeAliasDecl *typealias, Sema &sema)
  {
    ctx.stack.emplace_back(typealias);

    for(auto &arg : typealias->args)
    {
      semantic_decl(ctx, arg, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// tagdecl //////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, TagDecl *tag, Sema &sema)
  {
    for(auto &arg : tag->args)
    {
      semantic_decl(ctx, arg, sema);
    }

    if (tag->args.size() != 0)
    {
      // implicit self alias

      auto selfalias = sema.alias_declaration(tag->loc());

      selfalias->name = tag->name;
      selfalias->type = sema.make_typeref(tag);
      selfalias->flags |= TypeAliasDecl::Implicit;

      tag->decls.insert(tag->decls.begin(), selfalias);
    }

    for(auto &decl : tag->decls)
    {
      semantic_decl(ctx, decl, sema);
    }
  }

  //|///////////////////// struct ///////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, StructDecl *strct, Sema &sema)
  {
    ctx.stack.emplace_back(strct);

    if (strct->basetype)
    {
      // base as first field

      auto basefield = sema.field_declaration(strct->loc());

      basefield->name = "super";
      basefield->flags = VarDecl::Public;
      basefield->type = strct->basetype;

      strct->decls.insert(strct->decls.begin(), basefield);
    }

    semantic_decl(ctx, decl_cast<TagDecl>(strct), sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// concept //////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, ConceptDecl *concep, Sema &sema)
  {
    ctx.stack.emplace_back(concep);

    semantic_decl(ctx, decl_cast<TagDecl>(concep), sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// struct ///////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, LambdaDecl *lambda, Sema &sema)
  {
    auto fn = decl_cast<FunctionDecl>(lambda->fn);

    {
      auto ctor = sema.function_declaration(fn->loc());

      ctor->name = lambda->name;
      ctor->flags |= FunctionDecl::Public;
      ctor->flags |= FunctionDecl::Constructor;
      ctor->flags |= FunctionDecl::Defaulted;

      lambda->decls.push_back(ctor);
    }

    {
      auto ctor = sema.function_declaration(fn->loc());

      ctor->name = lambda->name;
      ctor->flags |= FunctionDecl::Public;
      ctor->flags |= FunctionDecl::Constructor;
      ctor->flags |= FunctionDecl::Defaulted;

      auto thatvar = sema.parm_declaration(fn->loc());
      thatvar->type = sema.make_reference(sema.make_const(sema.make_typeref(lambda)));

      ctor->parms.push_back(thatvar);

      lambda->decls.push_back(ctor);
    }

    {
      auto copy = sema.function_declaration(fn->loc());

      copy->name = "=";
      copy->flags |= FunctionDecl::Public;
      copy->flags |= FunctionDecl::Defaulted;

      auto thisvar = sema.parm_declaration(fn->loc());
      thisvar->type = sema.make_reference(sema.make_typeref(lambda));

      copy->parms.push_back(thisvar);

      auto thatvar = sema.parm_declaration(fn->loc());
      thatvar->type = sema.make_reference(sema.make_const(sema.make_typeref(lambda)));

      copy->parms.push_back(thatvar);

      copy->returntype = sema.make_reference(sema.make_typeref(lambda));

      lambda->decls.push_back(copy);
    }

    {
      auto dtor = sema.function_declaration(fn->loc());

      dtor->name = "~" + lambda->name;
      dtor->flags |= FunctionDecl::Public;
      dtor->flags |= FunctionDecl::Destructor;
      dtor->flags |= FunctionDecl::Defaulted;

      lambda->decls.push_back(dtor);
    }

    if (lambda->captures.size() == 0)
    {
      auto body = stmt_cast<CompoundStmt>(fn->body);
      auto stmt = sema.declaration_statement(fn->loc());

      auto thisvar = sema.voidvar_declaration(fn->loc());
      thisvar->name = lambda->name;
      thisvar->type = sema.make_typeref(lambda);

      stmt->decl = thisvar;

      body->stmts.insert(body->stmts.begin(), stmt);
    }
    else
    {
      auto thisvar = sema.parm_declaration(fn->loc());
      thisvar->name = lambda->name;
      thisvar->type = sema.make_reference(sema.make_const(sema.make_typeref(lambda)));

      fn->parms.insert(fn->parms.begin(), thisvar);
    }

    ctx.stack.emplace_back(lambda);

    semantic_decl(ctx, decl_cast<TagDecl>(lambda), sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// enum /////////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, EnumDecl *enumm, Sema &sema)
  {
    {
      auto basefield = sema.field_declaration(enumm->loc());

      basefield->type = enumm->basetype;

      if (!basefield->type)
        basefield->type = type(Builtin::Type_ISize);

      enumm->decls.push_back(basefield);
    }

    ctx.stack.emplace_back(enumm);

    semantic_decl(ctx, decl_cast<TagDecl>(enumm), sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// enum constant ////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, EnumConstantDecl *constant, Sema &sema)
  {
    if (constant->value)
    {
      semantic_expr(ctx, constant->value, sema);
    }
  }

  //|///////////////////// field ////////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, FieldVarDecl *field, Sema &sema)
  {
  }

  //|///////////////////// initialiser //////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, InitialiserDecl *init, Sema &sema)
  {
    if (init->parms.size() == 1 && init->parms[0]->kind() == Expr::DeclRef)
    {
      if (auto call = expr_cast<DeclRefExpr>(init->parms[0]); call->decl->kind() == Decl::DeclRef)
      {
        if (auto declref = decl_cast<DeclRefDecl>(call->decl); declref->name == "void")
        {
          init->flags |= InitialiserDecl::VoidInit;
        }
      }
    }

    for(auto &parm : init->parms)
    {     
      semantic_expr(ctx, parm, sema);
    }

    for(auto &[name, parm] : init->namedparms)
    {
      semantic_expr(ctx, parm, sema);
    }

    semantic_decl(ctx, init->decl, sema);
  }

  //|///////////////////// import ///////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, ImportDecl *imprt, Sema &sema)
  {
    auto &name = decl_cast<DeclRefDecl>(imprt->decl)->name;

    auto submodule = false;
    auto path = decl_cast<DeclRefDecl>(imprt->decl)->name;

    if (auto j = path.find('.'); j != path.npos)
    {
#ifdef _WIN32
      std::replace(path.begin(), path.end(), '.', '\\');
#else
      std::replace(path.begin(), path.end(), '.', '/');
#endif

      if (path.substr(0, j) == imprt->alias)
        submodule = true;
    }

    path += ".zaa";

    auto module = sema.lookup_module(name);

    if (!module)
    {
      module = sema.module_declaration(name, path);

      load(module, sema, ctx.diag);

      semantic(module, sema, ctx.diag);
    }

    if (submodule)
    {
      auto umbrella = sema.lookup_module(imprt->alias);

      if (!umbrella)
      {
        umbrella = sema.module_declaration(imprt->alias, imprt->alias + '/' + imprt->alias + ".zaa");
      }

      auto j = find_if(umbrella->decls.begin(), umbrella->decls.end(), [&](auto &decl) { return decl->kind() == Decl::Using && decl_cast<UsingDecl>(decl)->decl == imprt->decl; });

      if (j == umbrella->decls.end())
      {
        auto umbrella_using = sema.using_declaration({});

        umbrella_using->decl = module;
        umbrella_using->flags |= UsingDecl::Public;

        umbrella->decls.push_back(umbrella_using);
      }

      module = umbrella;
    }

    imprt->decl = module;

    ctx.stack.emplace_back(imprt);

    for(auto &usein : imprt->usings)
    {
      semantic_decl(ctx, usein, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// using ////////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, UsingDecl *usein, Sema &sema)
  {
  }

  //|///////////////////// function /////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, FunctionDecl *fn, Sema &sema)
  {
    ctx.stack.emplace_back(fn);

    for(auto &arg : fn->args)
    {
      semantic_decl(ctx, arg, sema);
    }

    for(auto &init: fn->inits)
    {
      semantic_decl(ctx, init, sema);
    }

    if (auto owner = get_if<Decl*>(&fn->owner); owner && is_tag_decl(*owner))
    {
      if (fn->parms.size() != 0)
      {
        auto parm = decl_cast<ParmVarDecl>(fn->parms[0]);

        if (auto basetype = remove_const_type(remove_reference_type(parm->type)); basetype->klass() == Type::TypeRef)
        {
          if (auto typeref = type_cast<TypeRefType>(basetype); typeref->decl->kind() == Decl::DeclRef)
          {
            if (decl_cast<DeclRefDecl>(typeref->decl)->name == "this")
            {
              parm->name = "this";
              typeref->decl = *owner;
            }
          }
        }
      }

      if (fn->flags & FunctionDecl::Constructor)
      {
        // constructor

        if (fn->body)
        {
          auto body = stmt_cast<CompoundStmt>(fn->body);
          auto stmt = sema.declaration_statement(fn->loc());

          auto thisvar = sema.thisvar_declaration(fn->loc());
          thisvar->name = "this";
          thisvar->type = sema.make_typeref(decl_cast<TagDecl>(*owner));

          stmt->decl = thisvar;

          body->stmts.insert(body->stmts.begin(), stmt);
        }

        fn->returntype = sema.make_typeref(decl_cast<TagDecl>(*owner));

        if (fn->flags & FunctionDecl::Defaulted)
        {
          if (fn->parms.size() > 1)
          {
            ctx.diag.error("invalid defaulted constructor", ctx.file, fn->loc());
          }

          fn->builtin = fn->parms.empty() ? Builtin::Default_Constructor : Builtin::Default_Copytructor;
        }
      }

      if (fn->flags & FunctionDecl::Destructor)
      {
        // destructor

        auto thisvar = sema.parm_declaration(fn->loc());
        thisvar->name = "this";
        thisvar->type = sema.make_reference(sema.make_typeref(decl_cast<TagDecl>(*owner)));

        fn->parms.push_back(thisvar);

        fn->returntype = type(Builtin::Type_Void);

        if (fn->flags & FunctionDecl::Defaulted)
        {
          if (fn->parms.size() != 1)
          {
            ctx.diag.error("invalid defaulted destructor", ctx.file, fn->loc());
          }

          fn->builtin = Builtin::Default_Destructor;
        }
      }
    }

    if (fn->name == "=")
    {
      if (fn->flags & FunctionDecl::Defaulted)
      {
        if (fn->parms.size() != 2)
        {
          ctx.diag.error("invalid assignment operator parameters", ctx.file, fn->loc());
          return;
        }

        if (!fn->returntype)
        {
          ctx.diag.error("invalid assignment operator return type", ctx.file, fn->loc());
          return;
        }

        fn->builtin = Builtin::Default_Assignment;
      }
    }

    if (fn->name == "==")
    {
      if (fn->flags & FunctionDecl::Defaulted)
      {
        if (fn->parms.size() != 2)
        {
          ctx.diag.error("invalid equality operator parameters", ctx.file, fn->loc());
          return;
        }

        if (!fn->returntype)
        {
          ctx.diag.error("invalid equality operator return type", ctx.file, fn->loc());
          return;
        }

        fn->builtin = Builtin::Default_Equality;
      }
    }

    if (fn->name == "<=>")
    {
      if (fn->flags & FunctionDecl::Defaulted)
      {
        if (fn->parms.size() != 2)
        {
          ctx.diag.error("invalid compare operator parameters", ctx.file, fn->loc());
          return;
        }

        if (!fn->returntype)
        {
          ctx.diag.error("invalid compare operator return type", ctx.file, fn->loc());
          return;
        }

        fn->builtin = Builtin::Default_Compare;
      }
    }

    for(auto &parm : fn->parms)
    {
      semantic_decl(ctx, parm, sema);
    }

    if (fn->body)
    {
      semantic_statement(ctx, fn->body, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// if ///////////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, IfDecl *ifd, Sema &sema)
  {
    semantic_expr(ctx, ifd->cond, sema);

    for(auto &decl : ifd->decls)
    {
      semantic_decl(ctx, decl, sema);
    }

    if (ifd->elseif)
    {
      semantic_decl(ctx, ifd->elseif, sema);
    }
  }

  //|///////////////////// declaration //////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, Decl *decl, Sema &sema)
  {
    decl->owner = ctx.stack.back().owner;

    switch(decl->kind())
    {
      case Decl::VoidVar:
        semantic_decl(ctx, decl_cast<VoidVarDecl>(decl), sema);
        break;

      case Decl::StmtVar:
        semantic_decl(ctx, decl_cast<StmtVarDecl>(decl), sema);
        break;

      case Decl::ParmVar:
        semantic_decl(ctx, decl_cast<ParmVarDecl>(decl), sema);
        break;

      case Decl::ThisVar:
        semantic_decl(ctx, decl_cast<ThisVarDecl>(decl), sema);
        break;

      case Decl::ErrorVar:
        semantic_decl(ctx, decl_cast<ErrorVarDecl>(decl), sema);
        break;

      case Decl::RangeVar:
        semantic_decl(ctx, decl_cast<RangeVarDecl>(decl), sema);
        break;

      case Decl::TypeArg:
        break;

      case Decl::DeclRef:
      case Decl::DeclScoped:
        break;

      case Decl::TypeOf:
        semantic_decl(ctx, decl_cast<TypeOfDecl>(decl), sema);
        break;

      case Decl::TypeAlias:
        semantic_decl(ctx, decl_cast<TypeAliasDecl>(decl), sema);
        break;

      case Decl::Struct:
        semantic_decl(ctx, decl_cast<StructDecl>(decl), sema);
        break;

      case Decl::Concept:
        semantic_decl(ctx, decl_cast<ConceptDecl>(decl), sema);
        break;

      case Decl::Lambda:
        semantic_decl(ctx, decl_cast<LambdaDecl>(decl), sema);
        break;

      case Decl::Enum:
        semantic_decl(ctx, decl_cast<EnumDecl>(decl), sema);
        break;

      case Decl::EnumConstant:
        semantic_decl(ctx, decl_cast<EnumConstantDecl>(decl), sema);
        break;

      case Decl::FieldVar:
        semantic_decl(ctx, decl_cast<FieldVarDecl>(decl), sema);
        break;

      case Decl::Initialiser:
        semantic_decl(ctx, decl_cast<InitialiserDecl>(decl), sema);
        break;

      case Decl::Import:
        semantic_decl(ctx, decl_cast<ImportDecl>(decl), sema);
        break;

      case Decl::Using:
        semantic_decl(ctx, decl_cast<UsingDecl>(decl), sema);
        break;

      case Decl::Function:
        semantic_decl(ctx, decl_cast<FunctionDecl>(decl), sema);
        break;

      case Decl::If:
        semantic_decl(ctx, decl_cast<IfDecl>(decl), sema);
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// declaration_statement ////////////////////////////
  void semantic_declaration_statement(SemanticContext &ctx, DeclStmt *stmt, Sema &sema)
  {
    if (stmt->decl->kind() == Decl::StmtVar)
    {
      if (auto var = decl_cast<StmtVarDecl>(stmt->decl); var->value->kind() == Expr::Call)
      {
        if (auto call = expr_cast<CallExpr>(var->value); call->parms.size() == 1 && call->parms[0]->kind() == Expr::DeclRef)
        {
          if (auto declref = expr_cast<DeclRefExpr>(call->parms[0]); declref->decl->kind() == Decl::DeclRef && decl_cast<DeclRefDecl>(declref->decl)->name == "void")
          {
            auto callee = decl_cast<DeclRefDecl>(call->callee);

            if (var->flags & VarDecl::Const)
            {
              ctx.diag.error("void var cannot be const");
            }

            auto voidvar = sema.voidvar_declaration(var->loc());

            voidvar->name = var->name;
            voidvar->type = sema.make_typeref(callee);

            stmt->decl = voidvar;
          }
        }
      }
    }

    ctx.stack.emplace_back(stmt);

    semantic_decl(ctx, stmt->decl, sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// expression_statement /////////////////////////////
  void semantic_expression_statement(SemanticContext &ctx, ExprStmt *stmt, Sema &sema)
  {
    if (stmt->expr)
    {
      semantic_expr(ctx, stmt->expr, sema);
    }
  }

  //|///////////////////// if_statement /////////////////////////////////////
  void semantic_if_statement(SemanticContext &ctx, IfStmt *ifs, Sema &sema)
  {
    ctx.stack.emplace_back(ifs);

    for(auto &init : ifs->inits)
    {
      semantic_statement(ctx, init, sema);
    }

    if (ifs->stmts[0])
    {
      semantic_statement(ctx, ifs->stmts[0], sema);
    }

    if (ifs->stmts[1])
    {
      semantic_statement(ctx, ifs->stmts[1], sema);
    }

    semantic_expr(ctx, ifs->cond, sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// for_statement ////////////////////////////////////
  void semantic_for_statement(SemanticContext &ctx, ForStmt *fors, Sema &sema)
  {
    ctx.stack.emplace_back(fors);

    for(auto &init : fors->inits)
    {
      semantic_statement(ctx, init, sema);
    }

    semantic_statement(ctx, fors->stmt, sema);

    for(auto &iter: fors->iters)
    {
      semantic_statement(ctx, iter, sema);
    }

    if (fors->cond)
    {
      semantic_expr(ctx, fors->cond, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// rof_statement ////////////////////////////////////
  void semantic_rof_statement(SemanticContext &ctx, RofStmt *rofs, Sema &sema)
  {
    ctx.stack.emplace_back(rofs);

    for(auto &init : rofs->inits)
    {
      semantic_statement(ctx, init, sema);
    }

    if (rofs->cond)
    {
      semantic_expr(ctx, rofs->cond, sema);
    }

    semantic_statement(ctx, rofs->stmt, sema);

    for(auto &iter: rofs->iters)
    {
      semantic_statement(ctx, iter, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// while_statement //////////////////////////////////
  void semantic_while_statement(SemanticContext &ctx, WhileStmt *wile, Sema &sema)
  {
    ctx.stack.emplace_back(wile);

    for(auto &init : wile->inits)
    {
      semantic_statement(ctx, init, sema);
    }

    semantic_expr(ctx, wile->cond, sema);

    semantic_statement(ctx, wile->stmt, sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// try_statement ////////////////////////////////////
  void semantic_try_statement(SemanticContext &ctx, TryStmt *trys, Sema &sema)
  {
    if (auto handler = stmt_cast<CompoundStmt>(trys->handler))
    {
      auto stmt = sema.declaration_statement(trys->loc());

      stmt->decl = trys->errorvar;

      handler->stmts.insert(handler->stmts.begin(), stmt);
    }

    ctx.stack.emplace_back(trys);

    semantic_statement(ctx, trys->body, sema);
    semantic_statement(ctx, trys->handler, sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// throw_statement //////////////////////////////////
  void semantic_throw_statement(SemanticContext &ctx, ThrowStmt *throwe, Sema &sema)
  {
    semantic_expr(ctx, throwe->expr, sema);
  }

  //|///////////////////// break_statement //////////////////////////////////
  void semantic_break_statement(SemanticContext &ctx, BreakStmt *breck, Sema &sema)
  {
  }

  //|///////////////////// continue_statement //////////////////////////////////
  void semantic_continue_statement(SemanticContext &ctx, ContinueStmt *continu, Sema &sema)
  {
  }

  //|///////////////////// return_statement /////////////////////////////////
  void semantic_return_statement(SemanticContext &ctx, ReturnStmt *retrn, Sema &sema)
  {
    if (retrn->expr)
    {
      semantic_expr(ctx, retrn->expr, sema);
    }
  }

  //|///////////////////// compound_statement ///////////////////////////////
  void semantic_compound_statement(SemanticContext &ctx, CompoundStmt *compound, Sema &sema)
  {
    ctx.stack.emplace_back(compound);

    for(auto &stmt : compound->stmts)
    {
      semantic_statement(ctx, stmt, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// statement ////////////////////////////////////////
  void semantic_statement(SemanticContext &ctx, Stmt *stmt, Sema &sema)
  {
    stmt->owner = ctx.stack.back().owner;

    switch(stmt->kind())
    {
      case Stmt::Null:
        break;

      case Stmt::Declaration:
        semantic_declaration_statement(ctx, stmt_cast<DeclStmt>(stmt), sema);
        break;

      case Stmt::Expression:
        semantic_expression_statement(ctx, stmt_cast<ExprStmt>(stmt), sema);
        break;

      case Stmt::If:
        semantic_if_statement(ctx, stmt_cast<IfStmt>(stmt), sema);
        break;

      case Stmt::For:
        semantic_for_statement(ctx, stmt_cast<ForStmt>(stmt), sema);
        break;

      case Stmt::Rof:
        semantic_rof_statement(ctx, stmt_cast<RofStmt>(stmt), sema);
        break;

      case Stmt::While:
        semantic_while_statement(ctx, stmt_cast<WhileStmt>(stmt), sema);
        break;

      case Stmt::Try:
        semantic_try_statement(ctx, stmt_cast<TryStmt>(stmt), sema);
        break;

      case Stmt::Throw:
        semantic_throw_statement(ctx, stmt_cast<ThrowStmt>(stmt), sema);
        break;

      case Stmt::Break:
        semantic_break_statement(ctx, stmt_cast<BreakStmt>(stmt), sema);
        break;

      case Stmt::Continue:
        semantic_continue_statement(ctx, stmt_cast<ContinueStmt>(stmt), sema);
        break;

      case Stmt::Return:
        semantic_return_statement(ctx, stmt_cast<ReturnStmt>(stmt), sema);
        break;

      case Stmt::Compound:
        semantic_compound_statement(ctx, stmt_cast<CompoundStmt>(stmt), sema);
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// semantic_toplevel_declaration ////////////////////
  void semantic_toplevel_declaration(SemanticContext &ctx, Decl *decl, Sema &sema)
  {
    if (decl->kind() == Decl::If)
    {
      auto ifd = decl_cast<IfDecl>(decl);

      ifd->owner = ctx.stack.back().owner;

      semantic_expr(ctx, ifd->cond, sema);

      switch (eval(ctx, ctx.stack.back(), ifd->cond))
      {
        case 1:
          ifd->flags |= IfDecl::ResolvedTrue;

          for(auto &decl : ifd->decls)
          {
            semantic_toplevel_declaration(ctx, decl, sema);
          }

          break;

        case 0:
          ifd->flags |= IfDecl::ResolvedFalse;

          if (ifd->elseif)
          {
            semantic_toplevel_declaration(ctx, ifd->elseif, sema);
          }

          break;

        case -1:
          break;
      }

      return;
    }

    semantic_decl(ctx, decl, sema);
  }

  //|///////////////////// module ///////////////////////////////////////////
  void semantic_module(SemanticContext &ctx, ModuleDecl *module, Sema &sema)
  {
    ctx.file = module->file();

    ctx.stack.emplace_back(module);

    for(auto &decl : module->decls)
    {
      semantic_toplevel_declaration(ctx, decl, sema);
    }

    ctx.stack.pop_back();
  }
}

//|--------------------- Semantic -------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// semantic ///////////////////////////////////////////
void semantic(ModuleDecl *module, Sema &sema, Diag &diag)
{
  SemanticContext ctx(diag);

  ctx.stack.emplace_back(get<Decl*>(module->owner));

  semantic_module(ctx, module, sema);

  ctx.stack.pop_back();
}