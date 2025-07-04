//
// semantic.cpp
//
// Copyright (c) 2020-2024 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "semantic.h"
#include "diag.h"
#include "query.h"
#include "visitor.h"
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
    vector<FunctionDecl*> fnstack;

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

  //|///////////////////// find_vardecl /////////////////////////////////////
  VarDecl *find_vardecl(SemanticContext &ctx, vector<Scope> const &stack, Ident *name, long queryflags)
  {
    vector<Decl*> decls;

    for (auto sx = stack.rbegin(); sx != stack.rend(); ++sx)
    {
      find_decls(*sx, name, queryflags, decls);

      if (decls.empty())
      {
        if (is_fn_scope(*sx))
        {
          auto fn = decl_cast<FunctionDecl>(get<Decl*>(sx->owner));

          if ((fn->flags & FunctionDecl::DeclType) == FunctionDecl::LambdaDecl)
            find_decls(parent_scope(*sx), name, QueryFlags::Fields, decls);

          break;
        }

        continue;
      }

      break;
    }

    if (decls.size() == 1)
    {
      return decl_cast<VarDecl>(decls[0]);
    }

    return nullptr;
  }

  //|///////////////////// detect_captures //////////////////////////////////
  std::vector<Decl*> detect_captures(SemanticContext &ctx, LambdaDecl *lambda, Sema &sema)
  {
    struct VarVisitor : public Visitor
    {
      std::vector<Ident*> unknowns;
      std::vector<std::vector<Ident*>> knowns;

      VarVisitor()
      {
        knowns.push_back({});
      }

      virtual void visit(Ident *name) override
      {
        if (std::none_of(knowns.begin(), knowns.end(), [&](auto &known) { return std::find(known.begin(), known.end(), name) != known.end(); }))
        {
          if (std::find(unknowns.begin(), unknowns.end(), name) == unknowns.end())
            unknowns.push_back(name);
        }
      }

      virtual void visit(VarDecl *vardecl) override
      {
        Visitor::visit(vardecl);

        knowns.back().push_back(vardecl->name);
      }

      virtual void visit(Stmt *stmt) override
      {
        if (stmt->kind() == Stmt::Compound)
          knowns.push_back({});

        Visitor::visit(stmt);

        if (stmt->kind() == Stmt::Compound)
          knowns.pop_back();
      }

      using Visitor::visit;
    };

    VarVisitor visitor;
    std::vector<Decl*> captures;

    visitor.visit(lambda->fn);

    for (auto &name : visitor.unknowns)
    {
      if (find_vardecl(ctx, ctx.stack, name, QueryFlags::Variables | QueryFlags::Parameters))
      {
        auto loc = lambda->loc();
        auto var = sema.capture_declaration(loc);

        var->arg = sema.make_typearg(Ident::from("_" + to_string(captures.size() + 1)), loc);

        var->name = name;
        var->type = sema.make_reference(sema.make_qualarg(sema.make_typearg(var->arg)));
        var->value = sema.make_declref_expression(sema.make_declref(var->name, loc), loc);

        captures.push_back(var);
      }
    }

    return captures;
  }

  //|///////////////////// decl_type ////////////////////////////////////////
  Type *decl_type(SemanticContext &ctx, Decl *decl, Sema &sema)
  {
    return sema.make_typeref(decl);
  }

  //|///////////////////// type /////////////////////////////////////////////
  void semantic_type(SemanticContext &ctx, Type *type, Sema &sema)
  {
    switch (type->klass())
    {
      case Type::Builtin:
        break;

      case Type::Const:
        semantic_type(ctx, type_cast<ConstType>(type)->type, sema);
        break;

      case Type::Pointer:
        semantic_type(ctx, type_cast<PointerType>(type)->type, sema);
        break;

      case Type::Reference:
        semantic_type(ctx, type_cast<ReferenceType>(type)->type, sema);
        break;

      case Type::Array:
        semantic_type(ctx, type_cast<ArrayType>(type)->type, sema);
        semantic_type(ctx, type_cast<ArrayType>(type)->size, sema);
        break;

      case Type::Tuple:
        for (auto &field : type_cast<TupleType>(type)->fields)
          semantic_type(ctx, field, sema);
        break;

      case Type::Function:
        semantic_type(ctx, type_cast<FunctionType>(type)->returntype, sema);
        semantic_type(ctx, type_cast<FunctionType>(type)->paramtuple, sema);
        semantic_type(ctx, type_cast<FunctionType>(type)->throwtype, sema);
        break;

      case Type::Pack:
        semantic_type(ctx, type_cast<PackType>(type)->type, sema);
        break;

      case Type::Unpack:
        semantic_type(ctx, type_cast<UnpackType>(type)->type, sema);
        break;

      case Type::QualArg:
        semantic_type(ctx, type_cast<QualArgType>(type)->type, sema);
        break;

      case Type::TypeLit:
        semantic_expr(ctx, type_cast<TypeLitType>(type)->value, sema);
        break;

      case Type::TypeRef:
        switch (type_cast<TypeRefType>(type)->decl->kind())
        {
          case Decl::DeclRef:
          case Decl::DeclScoped:
          case Decl::TypeOf:
            semantic_decl(ctx, type_cast<TypeRefType>(type)->decl, sema);
            break;

          default:
            break;
        }
        break;

      case Type::TypeArg:
      case Type::Tag:
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// arrayliteral /////////////////////////////////////
  void semantic_expr(SemanticContext &ctx, ArrayLiteralExpr *arrayliteral, Sema &sema)
  {
    for (auto &element : arrayliteral->elements)
    {
      semantic_expr(ctx, element, sema);
    }
  }

  //|///////////////////// compoundliteral //////////////////////////////////
  void semantic_expr(SemanticContext &ctx, CompoundLiteralExpr *compoundliteral, Sema &sema)
  {
    for (auto &field: compoundliteral->fields)
    {
      semantic_expr(ctx, field, sema);
    }
  }

  //|///////////////////// exprref_expression /////////////////////////////////
  void semantic_expr(SemanticContext &ctx, ExprRefExpr *exprref, Sema &sema)
  {
    semantic_expr(ctx, exprref->expr, sema);
  }

  //|///////////////////// paren_expression /////////////////////////////////
  void semantic_expr(SemanticContext &ctx, ParenExpr *paren, Sema &sema)
  {
    semantic_expr(ctx, paren->subexpr, sema);
  }

  //|///////////////////// named_expression /////////////////////////////////
  void semantic_expr(SemanticContext &ctx, NamedExpr *named, Sema &sema)
  {
    semantic_expr(ctx, named->subexpr, sema);
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
    if (call->base)
    {
      semantic_expr(ctx, call->base, sema);
    }

    for (auto &parm : call->parms)
    {
      semantic_expr(ctx, parm, sema);
    }

    semantic_decl(ctx, call->callee, sema);
  }

  //|///////////////////// sizeof_expression ////////////////////////////////
  void semantic_expr(SemanticContext &ctx, SizeofExpr *call, Sema &sema)
  {
    if (call->type)
    {
      semantic_type(ctx, call->type, sema);
    }

    if (call->expr)
    {
      semantic_expr(ctx, call->expr, sema);
    }
  }

  //|///////////////////// alignof_expression ///////////////////////////////
  void semantic_expr(SemanticContext &ctx, AlignofExpr *call, Sema &sema)
  {
    if (call->type)
    {
      semantic_type(ctx, call->type, sema);
    }

    if (call->decl)
    {
      semantic_decl(ctx, call->decl, sema);
    }
  }

  //|///////////////////// offsetof_expression //////////////////////////////
  void semantic_expr(SemanticContext &ctx, OffsetofExpr *call, Sema &sema)
  {
    semantic_decl(ctx, call->decl, sema);
  }

  //|///////////////////// instanceof_expression ////////////////////////////
  void semantic_expr(SemanticContext &ctx, InstanceofExpr *call, Sema &sema)
  {
    semantic_type(ctx, call->type, sema);
    semantic_type(ctx, call->instance, sema);
  }

  //|///////////////////// typeid_expression ////////////////////////////////
  void semantic_expr(SemanticContext &ctx, TypeidExpr *call, Sema &sema)
  {
    semantic_decl(ctx, call->decl, sema);
  }

  //|///////////////////// cast_expression //////////////////////////////////
  void semantic_expr(SemanticContext &ctx, CastExpr *cast, Sema &sema)
  {
    if (!cast->type)
    {
      cast->type = sema.make_typearg(sema.make_typearg(Ident::kw_var, cast->loc()));
    }

    semantic_type(ctx, cast->type, sema);

    semantic_expr(ctx, cast->expr, sema);
  }

  //|///////////////////// new_expression ///////////////////////////////////
  void semantic_expr(SemanticContext &ctx, NewExpr *call, Sema &sema)
  {
    semantic_type(ctx, call->type, sema);

    semantic_expr(ctx, call->address, sema);

    for (auto &parm : call->parms)
    {
      semantic_expr(ctx, parm, sema);
    }
  }

  //|///////////////////// requires_expression //////////////////////////////
  void semantic_expr(SemanticContext &ctx, RequiresExpr *reqires, Sema &sema)
  {
    semantic_decl(ctx, reqires->decl, sema);
  }

  //|///////////////////// where_expression /////////////////////////////////
  void semantic_expr(SemanticContext &ctx, WhereExpr *where, Sema &sema)
  {
    semantic_expr(ctx, where->expr, sema);
  }

  //|///////////////////// match_expression /////////////////////////////////
  void semantic_expr(SemanticContext &ctx, MatchExpr *match, Sema &sema)
  {
    semantic_decl(ctx, match->decl, sema);
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

  //|///////////////////// fragment_expression //////////////////////////////
  void semantic_expr(SemanticContext &ctx, FragmentExpr *fragment, Sema &sema)
  {
    for (auto &arg : fragment->args)
    {
      semantic_expr(ctx, arg, sema);
    }
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
      case Expr::PointerLiteral:
      case Expr::FunctionPointer:
        break;

      case Expr::ArrayLiteral:
        semantic_expr(ctx, expr_cast<ArrayLiteralExpr>(expr), sema);
        break;

      case Expr::CompoundLiteral:
        semantic_expr(ctx, expr_cast<CompoundLiteralExpr>(expr), sema);
        break;

      case Expr::ExprRef:
        semantic_expr(ctx, expr_cast<ExprRefExpr>(expr), sema);
        break;

      case Expr::Paren:
        semantic_expr(ctx, expr_cast<ParenExpr>(expr), sema);
        break;

      case Expr::Named:
        semantic_expr(ctx, expr_cast<NamedExpr>(expr), sema);
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

      case Expr::Offsetof:
        semantic_expr(ctx, expr_cast<OffsetofExpr>(expr), sema);
        break;

      case Expr::Instanceof:
        semantic_expr(ctx, expr_cast<InstanceofExpr>(expr), sema);
        break;

      case Expr::Typeid:
        semantic_expr(ctx, expr_cast<TypeidExpr>(expr), sema);
        break;

      case Expr::Cast:
        semantic_expr(ctx, expr_cast<CastExpr>(expr), sema);
        break;

      case Expr::New:
        semantic_expr(ctx, expr_cast<NewExpr>(expr), sema);
        break;

      case Expr::Requires:
        semantic_expr(ctx, expr_cast<RequiresExpr>(expr), sema);
        break;

      case Expr::Where:
        semantic_expr(ctx, expr_cast<WhereExpr>(expr), sema);
        break;

      case Expr::Match:
        semantic_expr(ctx, expr_cast<MatchExpr>(expr), sema);
        break;

      case Expr::Lambda:
        semantic_expr(ctx, expr_cast<LambdaExpr>(expr), sema);
        break;

      case Expr::DeclRef:
        semantic_expr(ctx, expr_cast<DeclRefExpr>(expr), sema);
        break;

      case Expr::Fragment:
        semantic_expr(ctx, expr_cast<FragmentExpr>(expr), sema);
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// voidvar //////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, VoidVarDecl *var, Sema &sema)
  {
    if (var->flags & VarDecl::Const)
    {
      ctx.diag.error("void var cannot be const", ctx.file, var->loc());
    }

    semantic_type(ctx, var->type, sema);
  }

  //|///////////////////// stmtvar //////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, StmtVarDecl *var, Sema &sema)
  {
    semantic_type(ctx, var->type, sema);

    semantic_expr(ctx, var->value, sema);
  }

  //|///////////////////// parmvar //////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, ParmVarDecl *var, Sema &sema)
  {
    semantic_type(ctx, var->type, sema);

    if (var->defult)
    {
      // default parameters are semantically owned by the functions parent scope

      ctx.stack.push_back(parent_scope(get<Decl*>(var->owner)));

      semantic_expr(ctx, var->defult, sema);

      ctx.stack.pop_back();
    }
  }

  //|///////////////////// thisvar //////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, ThisVarDecl *var, Sema &sema)
  {
    semantic_type(ctx, var->type, sema);
  }

  //|///////////////////// errorvar /////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, ErrorVarDecl *var, Sema &sema)
  {
    semantic_type(ctx, var->type, sema);
  }

  //|///////////////////// declref //////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, DeclRefDecl *declref, Sema &sema)
  {
    for (auto &arg : declref->args)
    {
      semantic_type(ctx, arg, sema);
    }

    for (auto &[name, arg] : declref->namedargs)
    {
      semantic_type(ctx, arg, sema);
    }
  }

  //|///////////////////// declscoped ///////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, DeclScopedDecl *declref, Sema &sema)
  {
    for (auto &decl : declref->decls)
    {
      semantic_decl(ctx, decl, sema);
    }
  }

  //|///////////////////// typename /////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, TypeNameDecl *declref, Sema &sema)
  {
    semantic_type(ctx, declref->type, sema);
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

    for (auto &arg : typealias->args)
    {
      semantic_decl(ctx, arg, sema);
    }

    semantic_type(ctx, typealias->type, sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// tagdecl //////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, TagDecl *tagdecl, Sema &sema)
  {
    for (auto &arg : tagdecl->args)
    {
      semantic_decl(ctx, arg, sema);
    }

    if (tagdecl->args.size() != 0)
    {
      // implicit self alias

      auto selfalias = sema.alias_declaration(tagdecl->loc());

      selfalias->name = tagdecl->name;
      selfalias->flags |= TypeAliasDecl::Implicit;
      selfalias->type = decl_type(ctx, tagdecl, sema);

      tagdecl->decls.insert(tagdecl->decls.begin(), selfalias);
    }

    if (tagdecl->basetype)
    {
      semantic_type(ctx, tagdecl->basetype, sema);
    }

    for (size_t i = 0; i < tagdecl->decls.size(); ++i)
    {
      semantic_decl(ctx, tagdecl->decls[i], sema);
    }

    for (auto &decl : tagdecl->decls)
    {
      if (!(tagdecl->flags & Decl::Public))
        decl->flags |= Decl::Public;
    }

    for (auto attr : tagdecl->attributes)
    {
      auto attribute = decl_cast<AttributeDecl>(attr);

      if (attribute->name == "packed")
        tagdecl->flags |= Type::Packed;

      if (attribute->name == "align")
      {
        size_t align = 0;
        std::from_chars(attribute->options.data()+1, attribute->options.data() + attribute->options.size() - 1, align, 10);

        if ((align & (align - 1)) != 0)
          ctx.diag.error("non power-of-two struct alignment", ctx.file, tagdecl->loc());

        tagdecl->alignment = align;
      }
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

      basefield->name = Ident::kw_super;
      basefield->type = strct->basetype;

      if (strct->flags & TagDecl::PublicBase)
        basefield->flags = VarDecl::Public;

      strct->decls.insert(strct->decls.begin(), basefield);
    }

    semantic_decl(ctx, decl_cast<TagDecl>(strct), sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// union ////////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, UnionDecl *unnion, Sema &sema)
  {
    ctx.stack.emplace_back(unnion);

    semantic_decl(ctx, decl_cast<TagDecl>(unnion), sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// vtable ///////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, VTableDecl *vtable, Sema &sema)
  {
    ctx.stack.emplace_back(vtable);

    auto vtabletype = decl_type(ctx, vtable, sema);

    if (vtable->basetype)
    {
      // base as first field

      auto basefield = sema.field_declaration(vtable->loc());

      basefield->name = Ident::kw_super;
      basefield->type = vtable->basetype;

      if (vtable->flags & TagDecl::PublicBase)
        basefield->flags = VarDecl::Public;

      vtable->decls.insert(vtable->decls.begin(), basefield);
    }

    for (auto &decl : vtable->decls)
    {
      if (decl->kind() == Decl::Function)
      {
        auto fn = decl_cast<FunctionDecl>(decl);

        auto field = sema.field_declaration(fn->loc());

        field->name = fn->name;
        field->flags |= fn->flags & FunctionDecl::Public;

        vector<Type*> params;
        for (auto &parm : fn->parms)
          params.push_back(decl_cast<ParmVarDecl>(parm)->type);

        if (fn->parms.size() != 0)
        {
          if (auto basetype = remove_qualifiers_type(params[0]); basetype->klass() == Type::TypeRef)
          {
            if (auto typeref = type_cast<TypeRefType>(basetype); typeref->decl->kind() == Decl::DeclRef)
            {
              if (decl_cast<DeclRefDecl>(typeref->decl)->name == Ident::kw_this)
              {
                field->flags |= VarDecl::SelfImplicit;
                typeref->decl = sema.make_declref(Ident::kw_void, typeref->decl->loc());
              }
            }
          }
        }

        auto throwtype = Builtin::type(Builtin::Type_Void);

        if (fn->throws)
          throwtype = fn->throws;

        field->type = sema.make_reference(sema.make_const(sema.make_fntype(fn->returntype, sema.make_tuple(params), throwtype)));

        decl = field;
      }
    }

    {
      auto ctor = sema.function_declaration(vtable->loc());

      ctor->name = vtable->name;
      ctor->flags |= FunctionDecl::Public;
      ctor->flags |= FunctionDecl::Const;
      ctor->flags |= FunctionDecl::Constructor;
      ctor->flags |= FunctionDecl::Builtin;
      ctor->builtin = Builtin::VTable_Constructor;

      vtable->decls.push_back(ctor);
    }

    {
      auto ctor = sema.function_declaration(vtable->loc());

      ctor->name = vtable->name;
      ctor->flags |= FunctionDecl::Public;
      ctor->flags |= FunctionDecl::Constructor;
      ctor->flags |= FunctionDecl::Defaulted;
      ctor->builtin = Builtin::Default_Copytructor;

      auto thatvar = sema.parm_declaration(vtable->loc());
      thatvar->type = sema.make_reference(sema.make_const(vtabletype));

      ctor->parms.push_back(thatvar);

      vtable->decls.push_back(ctor);
    }

    {
      auto copy = sema.function_declaration(vtable->loc());

      copy->name = Ident::op_assign;
      copy->flags |= FunctionDecl::Public;
      copy->flags |= FunctionDecl::Defaulted;
      copy->builtin = Builtin::Default_Assignment;

      auto thisvar = sema.parm_declaration(vtable->loc());
      thisvar->type = sema.make_reference(vtabletype);

      copy->parms.push_back(thisvar);

      auto thatvar = sema.parm_declaration(vtable->loc());
      thatvar->type = sema.make_reference(sema.make_const(vtabletype));

      copy->parms.push_back(thatvar);

      copy->returntype = sema.make_reference(vtabletype);

      vtable->decls.push_back(copy);
    }

    {
      auto dtor = sema.function_declaration(vtable->loc());

      dtor->name = Ident::from("~#vtable");
      dtor->flags |= FunctionDecl::Public;
      dtor->flags |= FunctionDecl::Destructor;
      dtor->flags |= FunctionDecl::Defaulted;
      dtor->builtin = Builtin::Default_Destructor;

      vtable->decls.push_back(dtor);
    }

    semantic_decl(ctx, decl_cast<TagDecl>(vtable), sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// concept //////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, ConceptDecl *concep, Sema &sema)
  {
    ctx.stack.emplace_back(concep);

    semantic_decl(ctx, decl_cast<TagDecl>(concep), sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// requires /////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, RequiresDecl *reqires, Sema &sema)
  {
    ctx.stack.emplace_back(reqires);

    semantic_decl(ctx, reqires->fn, sema);

    if (reqires->requirestype)
    {
      semantic_type(ctx, reqires->requirestype, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// lambda ///////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, LambdaDecl *lambda, Sema &sema)
  {
    auto fn = decl_cast<FunctionDecl>(lambda->fn);

    auto lambdatype = decl_type(ctx, lambda, sema);

    if (lambda->flags & LambdaDecl::Capture)
    {
      lambda->captures = detect_captures(ctx, lambda, sema);
    }

    if (lambda->captures.size() != 0)
    {
      lambda->flags |= LambdaDecl::Captures;

      for (auto &capture : lambda->captures)
      {
        auto field = sema.field_declaration(capture->loc());
        field->name = decl_cast<LambdaVarDecl>(capture)->name;
        field->flags = capture->flags;
        field->type = decl_cast<LambdaVarDecl>(capture)->type;

        lambda->decls.push_back(field);
        lambda->args.push_back(decl_cast<LambdaVarDecl>(capture)->arg);
      }
    }

    {
      auto ctor = sema.function_declaration(fn->loc());

      ctor->name = lambda->name;
      ctor->flags |= FunctionDecl::Public;
      ctor->flags |= FunctionDecl::Constructor;
      ctor->flags |= FunctionDecl::Defaulted;
      ctor->builtin = Builtin::Default_Constructor;

      for (auto &capture : lambda->captures)
      {
        auto var = sema.parm_declaration(capture->loc());
        var->name = decl_cast<LambdaVarDecl>(capture)->name;
        var->type = sema.make_reference(sema.make_qualarg(remove_qualifiers_type(decl_cast<LambdaVarDecl>(capture)->type)));

        ctor->parms.push_back(var);
      }

      lambda->decls.push_back(ctor);
    }

    {
      auto ctor = sema.function_declaration(fn->loc());

      ctor->name = lambda->name;
      ctor->flags |= FunctionDecl::Public;
      ctor->flags |= FunctionDecl::Constructor;
      ctor->flags |= FunctionDecl::Defaulted;
      ctor->builtin = Builtin::Default_Copytructor;

      auto thatvar = sema.parm_declaration(fn->loc());
      thatvar->type = sema.make_reference(sema.make_qualarg(lambdatype));

      ctor->parms.push_back(thatvar);

      lambda->decls.push_back(ctor);
    }

    {
      auto copy = sema.function_declaration(fn->loc());

      copy->name = Ident::op_assign;
      copy->flags |= FunctionDecl::Public;
      copy->flags |= FunctionDecl::Defaulted;
      copy->builtin = Builtin::Default_Assignment;

      auto thisvar = sema.parm_declaration(fn->loc());
      thisvar->type = sema.make_reference(lambdatype);

      copy->parms.push_back(thisvar);

      auto thatvar = sema.parm_declaration(fn->loc());
      thatvar->type = sema.make_reference(sema.make_qualarg(lambdatype));

      copy->parms.push_back(thatvar);

      copy->returntype = sema.make_reference(lambdatype);

      lambda->decls.push_back(copy);
    }

    {
      auto dtor = sema.function_declaration(fn->loc());

      dtor->name = Ident::from("~#lambda");
      dtor->flags |= FunctionDecl::Public;
      dtor->flags |= FunctionDecl::Destructor;
      dtor->flags |= FunctionDecl::Defaulted;
      dtor->builtin = Builtin::Default_Destructor;

      lambda->decls.push_back(dtor);
    }

    if (lambda->captures.empty())
    {
      auto body = stmt_cast<CompoundStmt>(fn->body);
      auto stmt = sema.declaration_statement(fn->loc());

      auto thisvar = sema.voidvar_declaration(fn->loc());
      thisvar->name = lambda->name;
      thisvar->type = lambdatype;

      stmt->decl = thisvar;

      body->stmts.insert(body->stmts.begin(), stmt);
    }
    else
    {
      auto thisvar = sema.parm_declaration(fn->loc());
      thisvar->name = lambda->name;
      thisvar->type = sema.make_reference(sema.make_qualarg(lambdatype));

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

      basefield->name = Ident::type_enum;
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
    constant->flags |= Decl::Public;

    if (constant->value)
    {
      semantic_expr(ctx, constant->value, sema);
    }
  }

  //|///////////////////// field ////////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, FieldVarDecl *field, Sema &sema)
  {
    if (!field->type)
    {
      field->type = type(Builtin::Type_Void);
    }

    semantic_type(ctx, field->type, sema);

    if (field->defult)
    {
      semantic_expr(ctx, field->defult, sema);
    }
  }

  //|///////////////////// initialiser //////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, InitialiserDecl *init, Sema &sema)
  {
    if (init->parms.size() == 1 && init->parms[0]->kind() == Expr::DeclRef)
    {
      if (auto call = expr_cast<DeclRefExpr>(init->parms[0]); call->decl->kind() == Decl::DeclRef)
      {
        if (auto declref = decl_cast<DeclRefDecl>(call->decl); declref->name == Ident::kw_void)
        {
          init->flags |= InitialiserDecl::VoidInit;
        }
      }
    }

    for (auto &parm : init->parms)
    {     
      semantic_expr(ctx, parm, sema);
    }
  }

  //|///////////////////// case /////////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, CaseDecl *casse, Sema &sema)
  {
    ctx.stack.emplace_back(casse);

    if (casse->label)
    {
      semantic_expr(ctx, casse->label, sema);
    }

    if (casse->parm)
    {
      semantic_decl(ctx, casse->parm, sema);
    }

    if (casse->body)
    {
      semantic_statement(ctx, casse->body, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// casevar //////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, CaseVarDecl *var, Sema &sema)
  {
    semantic_type(ctx, var->type, sema);

    if (var->value)
    {
      semantic_expr(ctx, var->value, sema);
    }
  }

  //|///////////////////// import ///////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, ImportDecl *imprt, Sema &sema)
  {
    auto name = decl_cast<DeclRefDecl>(imprt->decl)->name;

    auto module = sema.lookup_module(name);

    if (!module)
    {
      module = sema.module_declaration(name);

      if (!load(module, sema, ctx.diag))
        ctx.diag.error("opening file '" + module->file() + "'", ctx.file, imprt->loc());

      semantic(module, sema, ctx.diag);
    }

    if (auto i = imprt->alias->sv().find('.'); i != string_view::npos)
    {
      auto subname = Ident::from(name->sv().substr(0, name->sv().length() - (imprt->alias->sv().length() - i)));

      auto umbrella = sema.lookup_module(subname);

      if (!umbrella)
      {
        umbrella = sema.module_declaration(subname);

        load(umbrella, sema, ctx.diag);

        semantic(umbrella, sema, ctx.diag);
      }

      auto j = find_if(umbrella->decls.begin(), umbrella->decls.end(), [&](auto &decl) { return decl->kind() == Decl::Using && decl_cast<UsingDecl>(decl)->decl == module; });

      if (j == umbrella->decls.end())
      {
        auto umbrella_using = sema.using_declaration({});

        umbrella_using->decl = module;
        umbrella_using->flags |= UsingDecl::Public;
        umbrella_using->flags |= UsingDecl::Resolved;

        umbrella->decls.push_back(umbrella_using);
      }

      imprt->decl = umbrella;
      imprt->alias = Ident::from(imprt->alias->sv().substr(0, i));
    }
    else
    {
      imprt->decl = module;
    }

    ctx.stack.emplace_back(imprt);

    for (auto &usein : imprt->usings)
    {
      if (decl_cast<UsingDecl>(usein)->decl->kind() == Decl::DeclRef && decl_cast<DeclRefDecl>(decl_cast<UsingDecl>(usein)->decl)->name == string_view("*"))
      {
        decl_cast<UsingDecl>(usein)->decl = module;
        usein->owner = imprt->owner;
        continue;
      }

      semantic_decl(ctx, usein, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// using ////////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, UsingDecl *usein, Sema &sema)
  {
    if (!(usein->flags & UsingDecl::Resolved))
      semantic_decl(ctx, usein->decl, sema);
  }

  //|///////////////////// function /////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, FunctionDecl *fn, Sema &sema)
  {
    ctx.stack.emplace_back(fn);
    ctx.fnstack.emplace_back(fn);

    for (auto &arg : fn->args)
    {
      semantic_decl(ctx, arg, sema);
    }

    if (auto owner = get_if<Decl*>(&fn->owner); owner && is_tag_decl(*owner))
    {
      if (fn->parms.size() != 0)
      {
        auto parm = decl_cast<ParmVarDecl>(fn->parms[0]);

        if (auto basetype = remove_qualifiers_type(parm->type); basetype->klass() == Type::TypeRef)
        {
          if (auto typeref = type_cast<TypeRefType>(basetype); typeref->decl->kind() == Decl::DeclRef)
          {
            if (decl_cast<DeclRefDecl>(typeref->decl)->name == Ident::kw_this)
            {
              if (!parm->name)
                parm->name = Ident::kw_this;

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
          thisvar->name = Ident::kw_this;
          thisvar->type = sema.make_typeref(*owner);

          stmt->decl = thisvar;

          body->stmts.insert(body->stmts.begin(), stmt);
        }

        fn->returntype = decl_type(ctx, *owner, sema);

        if ((*owner)->kind() == Decl::Struct || (*owner)->kind() == Decl::Union || (*owner)->kind() == Decl::Enum)
        {
          fn->name = decl_cast<TagDecl>(*owner)->name;

          if (fn->flags & FunctionDecl::Defaulted)
          {
            if (fn->parms.size() == 0 || (fn->parms.size() == 1 && decl_cast<ParmVarDecl>(fn->parms[0])->name == Ident::kw_allocator))
            {
              fn->builtin = Builtin::Default_Constructor;
            }

            else if (fn->parms.size() == 1 || (fn->parms.size() == 2 && decl_cast<ParmVarDecl>(fn->parms[1])->name == Ident::kw_allocator))
            {
              if (!is_reference_type(decl_cast<ParmVarDecl>(fn->parms[0])->type))
                ctx.diag.error("non-reference first parameter", ctx.file, fn->loc());

              if (fn->parms[0]->flags & ParmVarDecl::Literal)
                fn->builtin = Builtin::Literal_Copytructor;
              else
                fn->builtin = Builtin::Default_Copytructor;
            }
            else
            {
              ctx.diag.error("invalid defaulted constructor parameters", ctx.file, fn->loc());
            }
          }
        }
      }

      if (fn->flags & FunctionDecl::Destructor)
      {
        // destructor

        auto thisvar = sema.parm_declaration(fn->loc());
        thisvar->name = Ident::kw_this;
        thisvar->type = sema.make_reference(sema.make_const(decl_type(ctx, *owner, sema)));

        fn->parms.push_back(thisvar);

        fn->returntype = type(Builtin::Type_Void);

        if ((*owner)->kind() == Decl::Struct || (*owner)->kind() == Decl::Union)
        {
          if (decl_cast<TagDecl>(*owner)->name)
            fn->name = Ident::from("~" + decl_cast<TagDecl>(*owner)->name->str());

          if (fn->flags & FunctionDecl::Defaulted)
          {
            if (fn->parms.size() != 1)
              ctx.diag.error("invalid defaulted destructor parameters", ctx.file, fn->loc());

            fn->builtin = Builtin::Default_Destructor;
          }
        }
      }
    }

    if (fn->name == Ident::op_assign)
    {
      if (fn->flags & FunctionDecl::Defaulted)
      {
        if (fn->parms.size() != 2)
          ctx.diag.error("invalid defaulted assignment operator parameters", ctx.file, fn->loc());

        if (!is_reference_type(decl_cast<ParmVarDecl>(fn->parms[0])->type) || is_const_reference(decl_cast<ParmVarDecl>(fn->parms[0])->type))
          ctx.diag.error("non-reference first parameter", ctx.file, fn->loc());

        if (!is_reference_type(decl_cast<ParmVarDecl>(fn->parms[1])->type))
          ctx.diag.error("non-reference second parameter", ctx.file, fn->loc());

        if (!fn->returntype)
          ctx.diag.error("missing return type", ctx.file, fn->loc());

        if (fn->parms[1]->flags & ParmVarDecl::Literal)
          fn->builtin = Builtin::Literal_Assignment;
        else
          fn->builtin = Builtin::Default_Assignment;
      }
    }

    if (fn->name == Ident::op_equality)
    {
      if (fn->flags & FunctionDecl::Defaulted)
      {
        if (fn->parms.size() != 2)
          ctx.diag.error("invalid defaulted equality operator parameters", ctx.file, fn->loc());

        if (!is_reference_type(decl_cast<ParmVarDecl>(fn->parms[0])->type))
          ctx.diag.error("non-reference first parameter", ctx.file, fn->loc());

        if (!is_reference_type(decl_cast<ParmVarDecl>(fn->parms[1])->type))
          ctx.diag.error("non-reference second parameter", ctx.file, fn->loc());

        if (!fn->returntype)
          ctx.diag.error("missing return type", ctx.file, fn->loc());

        fn->builtin = Builtin::Default_Equality;
      }
    }

    if (fn->name == Ident::op_compare)
    {
      if (fn->flags & FunctionDecl::Defaulted)
      {
        if (fn->parms.size() != 2)
          ctx.diag.error("invalid defaulted compare operator parameters", ctx.file, fn->loc());

        if (!is_reference_type(decl_cast<ParmVarDecl>(fn->parms[0])->type))
          ctx.diag.error("non-reference first parameter", ctx.file, fn->loc());

        if (!is_reference_type(decl_cast<ParmVarDecl>(fn->parms[1])->type))
          ctx.diag.error("non-reference second parameter", ctx.file, fn->loc());

        if (!fn->returntype)
          ctx.diag.error("missing return type", ctx.file, fn->loc());

        fn->builtin = Builtin::Default_Compare;
      }
    }

    if (fn->flags & FunctionDecl::Defaulted)
    {
      if (fn->builtin == 0)
        ctx.diag.error("invalid defaulted function", ctx.file, fn->loc());
    }

    for (auto attr : fn->attributes)
    {
      auto attribute = decl_cast<AttributeDecl>(attr);

      if (attribute->name == "noreturn")
      {
        fn->flags |= FunctionDecl::NoReturn;
      }

      if (attribute->name == "conditional")
      {
        auto id = sema.make_declref(Ident::from(attribute->options.substr(1, attribute->options.length() - 2)), fn->loc());

        if (eval(ctx, ctx.stack.back(), sema.make_declref_expression(id, fn->loc())) == 0)
          fn->flags |= FunctionDecl::Inhibited;
      }

      if (attribute->name == "safe")
      {
        fn->flags |= FunctionDecl::Safe;
      }

      if (attribute->name == "unsafe")
      {
        fn->flags |= FunctionDecl::Unsafe;
      }

      if (attribute->name == "lifetime")
      {
        fn->flags |= FunctionDecl::Lifetimed;

        fn->lifetimes = parse_lifetime(attribute->options, attribute->loc());
      }

      if (attribute->name == "noinline")
      {
        fn->flags |= FunctionDecl::NoInline;
      }

      if (attribute->name == "nodiscard")
      {
        fn->flags |= FunctionDecl::NoDiscard;
      }

      if (attribute->name == "weak")
      {
        fn->flags |= FunctionDecl::Weak;
      }
    }

    for (auto &parm : fn->parms)
    {
      semantic_decl(ctx, parm, sema);
    }

    if (fn->throws)
    {
      semantic_type(ctx, fn->throws, sema);
    }

    for (auto &expr : fn->constraints)
    {
      semantic_expr(ctx, expr, sema);
    }

    for (auto &init : fn->inits)
    {
      semantic_decl(ctx, init, sema);
    }

    if (fn->body)
    {
      semantic_statement(ctx, fn->body, sema);
    }

    ctx.fnstack.pop_back();
    ctx.stack.pop_back();
  }

  //|///////////////////// run //////////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, RunDecl *run, Sema &sema)
  {
    run->flags |= Decl::Public;

    semantic_decl(ctx, run->fn, sema);
  }

  //|///////////////////// if ///////////////////////////////////////////////
  void semantic_decl(SemanticContext &ctx, IfDecl *ifd, Sema &sema)
  {
    ifd->flags |= Decl::Public;

    semantic_expr(ctx, ifd->cond, sema);

    for (size_t i = 0; i < ifd->decls.size(); ++i)
    {
      semantic_decl(ctx, ifd->decls[i], sema);
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

    switch (decl->kind())
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

      case Decl::TypeArg:
        break;

      case Decl::DeclRef:
        semantic_decl(ctx, decl_cast<DeclRefDecl>(decl), sema);
        break;

      case Decl::DeclScoped:
        semantic_decl(ctx, decl_cast<DeclScopedDecl>(decl), sema);
        break;

      case Decl::TypeName:
        semantic_decl(ctx, decl_cast<TypeNameDecl>(decl), sema);
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

      case Decl::Union:
        semantic_decl(ctx, decl_cast<UnionDecl>(decl), sema);
        break;

      case Decl::VTable:
        semantic_decl(ctx, decl_cast<VTableDecl>(decl), sema);
        break;

      case Decl::Concept:
        semantic_decl(ctx, decl_cast<ConceptDecl>(decl), sema);
        break;

      case Decl::Requires:
        semantic_decl(ctx, decl_cast<RequiresDecl>(decl), sema);
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

      case Decl::Case:
        semantic_decl(ctx, decl_cast<CaseDecl>(decl), sema);
        break;

      case Decl::CaseVar:
        semantic_decl(ctx, decl_cast<CaseVarDecl>(decl), sema);
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

      case Decl::Run:
        semantic_decl(ctx, decl_cast<RunDecl>(decl), sema);
        break;

      case Decl::If:
        semantic_decl(ctx, decl_cast<IfDecl>(decl), sema);
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// injection_statement //////////////////////////////
  void semantic_injection_statement(SemanticContext &ctx, InjectionStmt *injection, Sema &sema)
  {
    semantic_expr(ctx, injection->expr, sema);
  }

  //|///////////////////// declaration_statement ////////////////////////////
  void semantic_declaration_statement(SemanticContext &ctx, DeclStmt *declstmt, Sema &sema)
  {
    if (declstmt->decl->kind() == Decl::StmtVar)
    {
      switch (auto var = decl_cast<StmtVarDecl>(declstmt->decl); var->value->kind())
      {
        case Expr::Call:

          if (auto call = expr_cast<CallExpr>(var->value); !call->base && call->parms.size() == 1 && call->parms[0]->kind() == Expr::DeclRef)
          {
            if (auto declref = expr_cast<DeclRefExpr>(call->parms[0]); declref->decl->kind() == Decl::DeclRef && decl_cast<DeclRefDecl>(declref->decl)->name == Ident::kw_void)
            {
              auto voidvar = sema.voidvar_declaration(var->loc());

              voidvar->name = var->name;
              voidvar->flags = var->flags;
              voidvar->type = sema.make_typeref(call->callee);
              voidvar->pattern = var->pattern;

              declstmt->decl = voidvar;
            }
          }

          break;

        case Expr::ArrayLiteral:

          if (auto arrayliteral = expr_cast<ArrayLiteralExpr>(var->value); arrayliteral->coercedtype && arrayliteral->elements.size() == 1 && arrayliteral->elements[0]->kind() == Expr::DeclRef)
          {
            if (auto declref = expr_cast<DeclRefExpr>(arrayliteral->elements[0]); declref->decl->kind() == Decl::DeclRef && decl_cast<DeclRefDecl>(declref->decl)->name == Ident::kw_void)
            {
              auto voidvar = sema.voidvar_declaration(var->loc());

              voidvar->name = var->name;
              voidvar->flags = var->flags;
              voidvar->type = sema.make_array(arrayliteral->coercedtype, arrayliteral->size);
              voidvar->pattern = var->pattern;

              declstmt->decl = voidvar;
            }
          }

          break;

        default:
          break;
      }
    }

    ctx.stack.emplace_back(declstmt);

    semantic_decl(ctx, declstmt->decl, sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// expression_statement /////////////////////////////
  void semantic_expression_statement(SemanticContext &ctx, ExprStmt *exprstmt, Sema &sema)
  {
    if (exprstmt->expr)
    {
      semantic_expr(ctx, exprstmt->expr, sema);
    }
  }

  //|///////////////////// if_statement /////////////////////////////////////
  void semantic_if_statement(SemanticContext &ctx, IfStmt *ifs, Sema &sema)
  {
    ctx.stack.emplace_back(ifs);

    for (auto &init : ifs->inits)
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

    for (auto &init : fors->inits)
    {
      semantic_statement(ctx, init, sema);
    }

    semantic_statement(ctx, fors->stmt, sema);

    for (auto &iter : fors->iters)
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

    for (auto &init : rofs->inits)
    {
      semantic_statement(ctx, init, sema);
    }

    if (rofs->cond)
    {
      semantic_expr(ctx, rofs->cond, sema);
    }

    semantic_statement(ctx, rofs->stmt, sema);

    for (auto &iter : rofs->iters)
    {
      semantic_statement(ctx, iter, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// while_statement //////////////////////////////////
  void semantic_while_statement(SemanticContext &ctx, WhileStmt *wile, Sema &sema)
  {
    ctx.stack.emplace_back(wile);

    for (auto &init : wile->inits)
    {
      semantic_statement(ctx, init, sema);
    }

    for (auto &iter : wile->iters)
    {
      semantic_statement(ctx, iter, sema);
    }

    semantic_expr(ctx, wile->cond, sema);

    semantic_statement(ctx, wile->stmt, sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// switch_statement /////////////////////////////////
  void semantic_switch_statement(SemanticContext &ctx, SwitchStmt *swtch, Sema &sema)
  {
    ctx.stack.emplace_back(swtch);

    for (auto &init : swtch->inits)
    {
      semantic_statement(ctx, init, sema);
    }

    semantic_expr(ctx, swtch->cond, sema);

    for (size_t i = 0; i < swtch->decls.size(); ++i)
    {
      semantic_decl(ctx, swtch->decls[i], sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// goto_statement //////////////////////////////////
  void semantic_goto_statement(SemanticContext &ctx, GotoStmt *gotoo, Sema &sema)
  {
    semantic_expr(ctx, gotoo->label, sema);
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

      if (auto fn = !ctx.fnstack.empty() ? ctx.fnstack.back() : nullptr)
      {
        VarDecl *vardecl = nullptr;

        if (retrn->expr->kind() == Expr::DeclRef && expr_cast<DeclRefExpr>(retrn->expr)->decl->kind() == Decl::DeclRef)
        {
          auto declref = decl_cast<DeclRefDecl>(expr_cast<DeclRefExpr>(retrn->expr)->decl);

          if (!expr_cast<DeclRefExpr>(retrn->expr)->base && declref->argless)
          {
            vardecl = find_vardecl(ctx, ctx.stack, declref->name, QueryFlags::Variables);
          }
        }

        if (fn->retcnt == 0)
          fn->retvar = vardecl;

        if (fn->retvar != vardecl)
          fn->retvar = nullptr;

        fn->retcnt += 1;
      }
    }
  }

  //|///////////////////// compound_statement ///////////////////////////////
  void semantic_compound_statement(SemanticContext &ctx, CompoundStmt *compound, Sema &sema)
  {
    ctx.stack.emplace_back(compound);

    for (auto &stmt : compound->stmts)
    {
      semantic_statement(ctx, stmt, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// statement ////////////////////////////////////////
  void semantic_statement(SemanticContext &ctx, Stmt *stmt, Sema &sema)
  {
    stmt->owner = ctx.stack.back().owner;

    switch (stmt->kind())
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

      case Stmt::Switch:
        semantic_switch_statement(ctx, stmt_cast<SwitchStmt>(stmt), sema);
        break;

      case Stmt::Goto:
        semantic_goto_statement(ctx, stmt_cast<GotoStmt>(stmt), sema);
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

      case Stmt::Injection:
        semantic_injection_statement(ctx, stmt_cast<InjectionStmt>(stmt), sema);
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

      ifd->flags |= Decl::Public;
      ifd->owner = ctx.stack.back().owner;

      semantic_expr(ctx, ifd->cond, sema);

      ctx.stack.back().goalpost = ifd->root;

      switch (eval(ctx, ctx.stack.back(), ifd->cond))
      {
        case 1:
          ifd->flags |= IfDecl::ResolvedTrue;

          for (size_t i = 0; i < ifd->decls.size(); ++i)
          {
            semantic_toplevel_declaration(ctx, ifd->decls[i], sema);
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

    for (size_t i = 0; i < module->decls.size(); ++i)
    {
      semantic_toplevel_declaration(ctx, module->decls[i], sema);
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

void semantic(Scope const &scope, Decl *decl, Sema &sema, Diag &diag)
{
  SemanticContext ctx(diag);

  ctx.stack.emplace_back(scope);

  semantic_decl(ctx, decl, sema);

  ctx.stack.pop_back();
}
