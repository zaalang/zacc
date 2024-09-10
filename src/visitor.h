//
// visitor.h
//
// Copyright (c) 2023-2023 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "ast.h"
#include "query.h"

struct Visitor
{
  virtual void visit(Ident *name)
  {
  }

  virtual void visit(VarDecl *vardecl)
  {
    switch (vardecl->kind())
    {
      case Decl::StmtVar:
        visit(decl_cast<StmtVarDecl>(vardecl)->value);
        break;

      default:
        break;
    }
  }

  virtual void visit(Expr *expr)
  {
    switch (expr->kind())
    {
      case Expr::ArrayLiteral:
        for (auto &element : expr_cast<ArrayLiteralExpr>(expr)->elements)
          visit(element);
        break;

      case Expr::CompoundLiteral:
        for (auto &field : expr_cast<CompoundLiteralExpr>(expr)->fields)
          visit(field);
        break;

      case Expr::ExprRef:
        visit(expr_cast<ExprRefExpr>(expr)->expr);
        break;

      case Expr::Paren:
        visit(expr_cast<ParenExpr>(expr)->subexpr);
        break;

      case Expr::Named:
        visit(expr_cast<NamedExpr>(expr)->subexpr);
        break;

      case Expr::UnaryOp:
        visit(expr_cast<UnaryOpExpr>(expr)->subexpr);
        break;

      case Expr::BinaryOp:
        visit(expr_cast<BinaryOpExpr>(expr)->lhs);
        visit(expr_cast<BinaryOpExpr>(expr)->rhs);
        break;

      case Expr::TernaryOp:
        visit(expr_cast<TernaryOpExpr>(expr)->cond);
        visit(expr_cast<TernaryOpExpr>(expr)->lhs);
        visit(expr_cast<TernaryOpExpr>(expr)->rhs);
        break;

      case Expr::Call:
        if (expr_cast<CallExpr>(expr)->base)
          visit(expr_cast<CallExpr>(expr)->base);
        for (auto &parm: expr_cast<CallExpr>(expr)->parms)
          visit(parm);
        if (auto decl = expr_cast<CallExpr>(expr)->callee; decl->kind() == Decl::DeclRef)
          if (!expr_cast<CallExpr>(expr)->base)
            visit(decl_cast<DeclRefDecl>(decl)->name);
        break;

      case Expr::Sizeof:
        if (expr_cast<SizeofExpr>(expr)->expr)
          visit(expr_cast<SizeofExpr>(expr)->expr);
        break;

      case Expr::Cast:
        if (expr_cast<CastExpr>(expr)->expr)
          visit(expr_cast<CastExpr>(expr)->expr);
        break;

      case Expr::New:
        visit(expr_cast<NewExpr>(expr)->address);
        for (auto &parm: expr_cast<NewExpr>(expr)->parms)
          visit(parm);
        break;

      case Expr::DeclRef:
        if (expr_cast<DeclRefExpr>(expr)->base)
          visit(expr_cast<DeclRefExpr>(expr)->base);
        if (auto decl = expr_cast<DeclRefExpr>(expr)->decl; decl->kind() == Decl::DeclRef)
          if (!expr_cast<DeclRefExpr>(expr)->base)
            visit(decl_cast<DeclRefDecl>(decl)->name);
        break;

      case Expr::Lambda:
        visit(decl_cast<LambdaDecl>(expr_cast<LambdaExpr>(expr)->decl)->fn);
        break;

      default:
        break;
    }
  }

  virtual void visit(Stmt *stmt)
  {
    switch (stmt->kind())
    {
      case Stmt::Null:
        break;

      case Stmt::Declaration:
        if (auto decl = stmt_cast<DeclStmt>(stmt)->decl; is_var_decl(decl))
          visit(decl_cast<VarDecl>(decl));
        break;

      case Stmt::Expression:
        if (stmt_cast<ExprStmt>(stmt)->expr)
          visit(stmt_cast<ExprStmt>(stmt)->expr);
        break;

      case Stmt::If:
        if (stmt_cast<IfStmt>(stmt)->cond)
          visit(stmt_cast<IfStmt>(stmt)->cond);
        for (auto &init : stmt_cast<IfStmt>(stmt)->inits)
          visit(init);
        if (stmt_cast<IfStmt>(stmt)->stmts[0])
          visit(stmt_cast<IfStmt>(stmt)->stmts[0]);
        if (stmt_cast<IfStmt>(stmt)->stmts[1])
          visit(stmt_cast<IfStmt>(stmt)->stmts[1]);
        break;

      case Stmt::For:
        if (stmt_cast<ForStmt>(stmt)->cond)
          visit(stmt_cast<ForStmt>(stmt)->cond);
        for (auto &init : stmt_cast<ForStmt>(stmt)->inits)
          visit(init);
        for (auto &iter : stmt_cast<ForStmt>(stmt)->iters)
          visit(iter);
        visit(stmt_cast<ForStmt>(stmt)->stmt);
        break;

      case Stmt::Rof:
        if (stmt_cast<RofStmt>(stmt)->cond)
          visit(stmt_cast<RofStmt>(stmt)->cond);
        for (auto &init : stmt_cast<RofStmt>(stmt)->inits)
          visit(init);
        for (auto &iter : stmt_cast<RofStmt>(stmt)->iters)
          visit(iter);
        visit(stmt_cast<RofStmt>(stmt)->stmt);
        break;

      case Stmt::While:
        if (stmt_cast<WhileStmt>(stmt)->cond)
          visit(stmt_cast<WhileStmt>(stmt)->cond);
        for (auto &init : stmt_cast<WhileStmt>(stmt)->inits)
          visit(init);
        for (auto &iter : stmt_cast<WhileStmt>(stmt)->iters)
          visit(iter);
        visit(stmt_cast<WhileStmt>(stmt)->stmt);
        break;

      case Stmt::Switch:
        if (stmt_cast<SwitchStmt>(stmt)->cond)
          visit(stmt_cast<SwitchStmt>(stmt)->cond);
        for (auto &init : stmt_cast<SwitchStmt>(stmt)->inits)
          visit(init);
        for (auto &decl : stmt_cast<SwitchStmt>(stmt)->decls)
          if (decl->kind() == Decl::Case)
            if (decl_cast<CaseDecl>(decl)->body)
              visit(decl_cast<CaseDecl>(decl)->body);
        break;

      case Stmt::Goto:
        break;

      case Stmt::Try:
        visit(stmt_cast<TryStmt>(stmt)->body);
        visit(stmt_cast<TryStmt>(stmt)->handler);
        break;

      case Stmt::Throw:
        if (stmt_cast<ThrowStmt>(stmt)->expr)
          visit(stmt_cast<ThrowStmt>(stmt)->expr);
        break;

      case Stmt::Break:
        break;

      case Stmt::Continue:
        break;

      case Stmt::Injection:
        break;

      case Stmt::Return:
        if (stmt_cast<ReturnStmt>(stmt)->expr)
          visit(stmt_cast<ReturnStmt>(stmt)->expr);
        break;

      case Stmt::Compound:
        for (auto &stmt : stmt_cast<CompoundStmt>(stmt)->stmts)
          visit(stmt);
        break;

      default:
        assert(false);
    }
  }

  virtual void visit(Decl *decl)
  {
    switch (decl->kind())
    {
      case Decl::Module:
        for (auto &decl : decl_cast<ModuleDecl>(decl)->decls)
          visit(decl);
        break;

      case Decl::VoidVar:
      case Decl::StmtVar:
      case Decl::ParmVar:
      case Decl::ThisVar:
      case Decl::ErrorVar:
        visit(decl_cast<VarDecl>(decl));
        break;

      case Decl::TypeArg:
        break;

      case Decl::DeclRef:
        break;

      case Decl::DeclScoped:
        for (auto &decl : decl_cast<DeclScopedDecl>(decl)->decls)
          visit(decl);
        break;

      case Decl::TypeName:
        break;

      case Decl::TypeOf:
        visit(decl_cast<TypeOfDecl>(decl)->expr);
        break;

      case Decl::TypeAlias:
        for (auto &decl : decl_cast<TypeAliasDecl>(decl)->args)
          visit(decl);
        break;

      case Decl::Struct:
      case Decl::Union:
      case Decl::VTable:
      case Decl::Concept:
      case Decl::Lambda:
      case Decl::Enum:
        for (auto &decl : decl_cast<TagDecl>(decl)->args)
          visit(decl);
        for (auto &decl : decl_cast<TagDecl>(decl)->decls)
          visit(decl);
        break;

      case Decl::Requires:
        break;

      case Decl::EnumConstant:
        visit(decl_cast<EnumConstantDecl>(decl)->value);
        break;

      case Decl::FieldVar:
        if (decl_cast<FieldVarDecl>(decl)->defult)
          visit(decl_cast<FieldVarDecl>(decl)->defult);
        break;

      case Decl::Initialiser:
        for (auto &decl : decl_cast<InitialiserDecl>(decl)->parms)
          visit(decl);
        break;

      case Decl::Case:
        if (decl_cast<CaseDecl>(decl)->label)
          visit(decl_cast<CaseDecl>(decl)->label);
        if (decl_cast<CaseDecl>(decl)->parm)
          visit(decl_cast<CaseDecl>(decl)->parm);
        if (decl_cast<CaseDecl>(decl)->body)
          visit(decl_cast<CaseDecl>(decl)->body);
        break;

      case Decl::CaseVar:
        if (decl_cast<CaseVarDecl>(decl)->value)
          visit(decl_cast<CaseVarDecl>(decl)->value);
        break;

      case Decl::Import:
        for (auto &decl : decl_cast<ImportDecl>(decl)->usings)
          visit(decl);
        break;

      case Decl::Using:
        visit(decl_cast<UsingDecl>(decl)->decl);
        break;

      case Decl::Function:
        for (auto &decl : decl_cast<FunctionDecl>(decl)->args)
          visit(decl);
        for (auto &decl : decl_cast<FunctionDecl>(decl)->parms)
          visit(decl);
        for (auto &decl : decl_cast<FunctionDecl>(decl)->inits)
          visit(decl);
        for (auto &expr : decl_cast<FunctionDecl>(decl)->constraints)
          visit(expr);
        if (decl_cast<FunctionDecl>(decl)->body)
          visit(decl_cast<FunctionDecl>(decl)->body);
        break;

      case Decl::Run:
        visit(decl_cast<RunDecl>(decl)->fn);
        break;

      case Decl::If:
        break;

      default:
        assert(false);
    }
  }
};
