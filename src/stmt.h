//
// stmt.h
//
// Copyright (c) 2020-2024 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "lexer.h"
#include <string>
#include <string_view>
#include <variant>
#include <vector>

class Decl;
class Expr;

//-------------------------- Stmt -------------------------------------------
//---------------------------------------------------------------------------

class Stmt
{
  public:

    enum Kind
    {
      Null,
      Compound,
      Declaration,
      Expression,
      If,
      For,
      Rof,
      While,
      Switch,
      Goto,
      Try,
      Throw,
      Break,
      Continue,
      Injection,
      Return,
    };

  public:
    Stmt(Kind kind, SourceLocation loc);

    Kind kind() const { return m_kind; }
    SourceLocation const &loc() const { return m_loc; }

    std::variant<Decl*, Stmt*> owner;

    virtual void dump(int indent) const = 0;

  protected:

    Kind m_kind;
    SourceLocation m_loc;
};


//---------------------- NullStmt -------------------------------------------
//---------------------------------------------------------------------------

class NullStmt : public Stmt
{
  public:
    NullStmt(SourceLocation loc);

    void dump(int indent) const override;
};


//---------------------- CompoundStmt ---------------------------------------
//---------------------------------------------------------------------------

class CompoundStmt : public Stmt
{
  public:
    CompoundStmt(SourceLocation loc);

    std::vector<Stmt*> stmts;

    SourceLocation endloc;

    void dump(int indent) const override;
};


//---------------------- DeclStmt -------------------------------------------
//---------------------------------------------------------------------------

class DeclStmt : public Stmt
{
  public:
    DeclStmt(SourceLocation loc);
    DeclStmt(Decl *decl, SourceLocation loc);

    Decl *decl = nullptr;

    void dump(int indent) const override;
};


//---------------------- ExprStmt -------------------------------------------
//---------------------------------------------------------------------------

class ExprStmt : public Stmt
{
  public:
    ExprStmt(SourceLocation loc);
    ExprStmt(Expr *expr, SourceLocation loc);

    Expr *expr = nullptr;

    void dump(int indent) const override;
};


//---------------------- IfStmt ---------------------------------------------
//---------------------------------------------------------------------------

class IfStmt : public Stmt
{
  public:

    enum Flags
    {
      Static = 0x02,
    };

    long flags = 0;

  public:
    IfStmt(SourceLocation loc);

    std::vector<Stmt*> inits;
    Expr *cond = nullptr;
    Stmt *stmts[2] = { nullptr, nullptr };

    void dump(int indent) const override;
};


//---------------------- ForStmt --------------------------------------------
//---------------------------------------------------------------------------

class ForStmt : public Stmt
{
  public:

    enum Flags
    {
      Static = 0x02,
    };

    long flags = 0;

  public:
    ForStmt(SourceLocation loc);

    std::vector<Stmt*> inits;
    Expr *cond = nullptr;
    std::vector<Stmt*> iters;
    Stmt *stmt = nullptr;

    void dump(int indent) const override;
};


//---------------------- RofStmt --------------------------------------------
//---------------------------------------------------------------------------

class RofStmt : public Stmt
{
  public:

    enum Flags
    {
      Static = 0x02,
    };

    long flags = 0;

  public:
    RofStmt(SourceLocation loc);

    std::vector<Stmt*> inits;
    Expr *cond = nullptr;
    std::vector<Stmt*> iters;
    Stmt *stmt = nullptr;

    void dump(int indent) const override;
};


//---------------------- WhileStmt ------------------------------------------
//---------------------------------------------------------------------------

class WhileStmt : public Stmt
{
  public:
    WhileStmt(SourceLocation loc);

    std::vector<Stmt*> inits;
    std::vector<Stmt*> iters;
    Expr *cond = nullptr;
    Stmt *stmt = nullptr;

    void dump(int indent) const override;
};


//---------------------- SwitchStmt -----------------------------------------
//---------------------------------------------------------------------------

class SwitchStmt : public Stmt
{
  public:
    SwitchStmt(SourceLocation loc);

    std::vector<Stmt*> inits;
    Expr *cond = nullptr;
    std::vector<Decl*> decls;

    void dump(int indent) const override;
};


//---------------------- GotoStmt -------------------------------------------
//---------------------------------------------------------------------------

class GotoStmt : public Stmt
{
  public:
    GotoStmt(SourceLocation loc);

    Expr *label = nullptr;

    void dump(int indent) const override;
};


//---------------------- TryStmt --------------------------------------------
//---------------------------------------------------------------------------

class TryStmt : public Stmt
{
  public:
    TryStmt(SourceLocation loc);

    Stmt *body = nullptr;
    Decl *errorvar = nullptr;
    Stmt *handler = nullptr;

    void dump(int indent) const override;
};


//---------------------- ThrowStmt ------------------------------------------
//---------------------------------------------------------------------------

class ThrowStmt : public Stmt
{
  public:
    ThrowStmt(SourceLocation loc);

    Expr *expr = nullptr;

    void dump(int indent) const override;
};


//---------------------- BreakStmt ------------------------------------------
//---------------------------------------------------------------------------

class BreakStmt : public Stmt
{
  public:
    BreakStmt(SourceLocation loc);

    void dump(int indent) const override;
};


//---------------------- ContinueStmt ---------------------------------------
//---------------------------------------------------------------------------

class ContinueStmt : public Stmt
{
  public:
    ContinueStmt(SourceLocation loc);

    void dump(int indent) const override;
};


//---------------------- InjectionStmt --------------------------------------
//---------------------------------------------------------------------------

class InjectionStmt : public Stmt
{
  public:
    InjectionStmt(SourceLocation loc);
    InjectionStmt(Expr *expr, SourceLocation loc);

    Expr *expr = nullptr;

    void dump(int indent) const override;
};


//---------------------- ReturnStmt -----------------------------------------
//---------------------------------------------------------------------------

class ReturnStmt : public Stmt
{
  public:
    ReturnStmt(SourceLocation loc);
    ReturnStmt(Expr *expr, SourceLocation loc);

    Expr *expr = nullptr;

    void dump(int indent) const override;
};


//
// misc functions
//

std::ostream &operator <<(std::ostream &os, Stmt const &stmt);


// checked casts

template<typename T> auto stmt_cast(Stmt*);
template<> inline auto stmt_cast<DeclStmt>(Stmt *stmt) { assert(stmt && stmt->kind() == Stmt::Declaration); return static_cast<DeclStmt*>(stmt); };
template<> inline auto stmt_cast<ExprStmt>(Stmt *stmt) { assert(stmt && stmt->kind() == Stmt::Expression); return static_cast<ExprStmt*>(stmt); };
template<> inline auto stmt_cast<IfStmt>(Stmt *stmt) { assert(stmt && stmt->kind() == Stmt::If); return static_cast<IfStmt*>(stmt); };
template<> inline auto stmt_cast<ForStmt>(Stmt *stmt) { assert(stmt && stmt->kind() == Stmt::For); return static_cast<ForStmt*>(stmt); };
template<> inline auto stmt_cast<RofStmt>(Stmt *stmt) { assert(stmt && stmt->kind() == Stmt::Rof); return static_cast<RofStmt*>(stmt); };
template<> inline auto stmt_cast<WhileStmt>(Stmt *stmt) { assert(stmt && stmt->kind() == Stmt::While); return static_cast<WhileStmt*>(stmt); };
template<> inline auto stmt_cast<SwitchStmt>(Stmt *stmt) { assert(stmt && stmt->kind() == Stmt::Switch); return static_cast<SwitchStmt*>(stmt); };
template<> inline auto stmt_cast<GotoStmt>(Stmt *stmt) { assert(stmt && stmt->kind() == Stmt::Goto); return static_cast<GotoStmt*>(stmt); };
template<> inline auto stmt_cast<TryStmt>(Stmt *stmt) { assert(stmt && stmt->kind() == Stmt::Try); return static_cast<TryStmt*>(stmt); };
template<> inline auto stmt_cast<ThrowStmt>(Stmt *stmt) { assert(stmt && stmt->kind() == Stmt::Throw); return static_cast<ThrowStmt*>(stmt); };
template<> inline auto stmt_cast<BreakStmt>(Stmt *stmt) { assert(stmt && stmt->kind() == Stmt::Break); return static_cast<BreakStmt*>(stmt); };
template<> inline auto stmt_cast<ContinueStmt>(Stmt *stmt) { assert(stmt && stmt->kind() == Stmt::Continue); return static_cast<ContinueStmt*>(stmt); };
template<> inline auto stmt_cast<InjectionStmt>(Stmt *stmt) { assert(stmt && stmt->kind() == Stmt::Injection); return static_cast<InjectionStmt*>(stmt); };
template<> inline auto stmt_cast<ReturnStmt>(Stmt *stmt) { assert(stmt && stmt->kind() == Stmt::Return); return static_cast<ReturnStmt*>(stmt); };
template<> inline auto stmt_cast<CompoundStmt>(Stmt *stmt) { assert(stmt && stmt->kind() == Stmt::Compound); return static_cast<CompoundStmt*>(stmt); };
