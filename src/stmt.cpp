//
// stmt.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "ast.h"
#include <iostream>
#include <cassert>

using namespace std;

namespace
{
  struct spaces
  {
    spaces(int n)
      : n(n)
    {
    }

    friend ostream &operator <<(ostream &os, spaces const &indent)
    {
      for(int i = 0; i < indent.n; ++i)
        os << ' ';

      return os;
    }

    int n;
  };
}

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, Stmt const &stmt)
{
  switch (stmt.kind())
  {
    case Stmt::Null:
      os << ";";
      break;

    case Stmt::Compound:
      os << "Compound";
      break;

    case Stmt::Declaration:
      os << "Declaration " << *static_cast<DeclStmt const &>(stmt).decl;
      break;

    case Stmt::Expression:
      os << "Expression " << *static_cast<ExprStmt const &>(stmt).expr;
      break;

    case Stmt::If:
      os << "If";
      break;

    case Stmt::For:
      os << "For";
      break;

    case Stmt::Rof:
      os << "Rof";
      break;

    case Stmt::While:
      os << "While";
      break;

    case Stmt::Switch:
      os << "Switch";
      break;

    case Stmt::Try:
      os << "Try";
      break;

    case Stmt::Break:
      os << "Break";
      break;

    case Stmt::Continue:
      os << "Continue";
      break;

    case Stmt::Throw:
      os << "Throw";
      break;

    case Stmt::Injection:
      os << "Injection";
      break;

    case Stmt::Return:
      os << "Return";
      break;
  }

  os << '<' << stmt.loc() << '>';

  return os;
}


//|--------------------- Stmt -----------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// Stmt::Constructor //////////////////////////////////
Stmt::Stmt(Kind kind, SourceLocation loc)
  : m_kind(kind),
    m_loc(loc)
{
}


//|--------------------- NullStmt -------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// NullStmt::Constructor //////////////////////////////
NullStmt::NullStmt(SourceLocation loc)
  : Stmt(Null, loc)
{
}

//|///////////////////// NullStmt::dump /////////////////////////////////////
void NullStmt::dump(int indent) const
{
  cout << spaces(indent) << "NullStmt " << this << " <" << m_loc << ">\n";
}


//|--------------------- CompoundStmt ---------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// CompoundStmt::Constructor //////////////////////////
CompoundStmt::CompoundStmt(SourceLocation loc)
  : Stmt(Compound, loc)
{
}

//|///////////////////// CompoundStmt::dump /////////////////////////////////
void CompoundStmt::dump(int indent) const
{
  cout << spaces(indent) << "CompoundStmt " << this << " <" << m_loc << ">\n";

  for(auto &stmt : stmts)
  {
    stmt->dump(indent + 2);
  }
}


//|--------------------- DeclStmt -------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// DeclStmt::Constructor //////////////////////////////
DeclStmt::DeclStmt(SourceLocation loc)
  : Stmt(Declaration, loc)
{
}

DeclStmt::DeclStmt(Decl *decl, SourceLocation loc)
  : Stmt(Declaration, loc),
    decl(decl)
{
}

//|///////////////////// DeclStmt::dump /////////////////////////////////////
void DeclStmt::dump(int indent) const
{
  cout << spaces(indent) << "DeclStmt " << this << " <" << m_loc << "> \n";

  if (decl)
  {
    decl->dump(indent + 2);
  }
}


//|--------------------- ExprStmt -------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ExprStmt::Constructor //////////////////////////////
ExprStmt::ExprStmt(SourceLocation loc)
  : Stmt(Expression, loc)
{
}

ExprStmt::ExprStmt(Expr *expr, SourceLocation loc)
  : Stmt(Expression, loc),
    expr(expr)
{
}

//|///////////////////// ExprStmt::dump /////////////////////////////////////
void ExprStmt::dump(int indent) const
{
  cout << spaces(indent) << "ExprStmt " << this << " <" << m_loc << ">\n";

  if (expr)
  {
    expr->dump(indent + 2);
  }
}


//|--------------------- IfStmt ---------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// IfStmt::Constructor ////////////////////////////////
IfStmt::IfStmt(SourceLocation loc)
  : Stmt(If, loc)
{
}

//|///////////////////// IfStmt::dump ///////////////////////////////////////
void IfStmt::dump(int indent) const
{
  cout << spaces(indent) << "IfStmt " << this << " <" << m_loc << ">\n";

  for(auto &init : inits)
  {
    init->dump(indent + 2);
  }

  if (cond)
  {
    cond->dump(indent + 2);
  }

  if (stmts[0])
  {
    stmts[0]->dump(indent + 2);
  }

  if (stmts[1])
  {
    stmts[1]->dump(indent + 2);
  }
}


//|--------------------- ForStmt --------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ForStmt::Constructor ///////////////////////////////
ForStmt::ForStmt(SourceLocation loc)
  : Stmt(For, loc)
{
}

//|///////////////////// ForStmt::dump //////////////////////////////////////
void ForStmt::dump(int indent) const
{
  cout << spaces(indent) << "ForStmt " << this << " <" << m_loc << ">\n";

  for(auto &init : inits)
  {
    init->dump(indent + 2);
  }

  if (cond)
  {
    cond->dump(indent + 2);
  }

  for(auto &iter : iters)
  {
    iter->dump(indent + 2);
  }

  if (stmt)
  {
    stmt->dump(indent + 2);
  }
}


//|--------------------- RofStmt --------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// RofStmt::Constructor ///////////////////////////////
RofStmt::RofStmt(SourceLocation loc)
  : Stmt(Rof, loc)
{
}

//|///////////////////// RofStmt::dump //////////////////////////////////////
void RofStmt::dump(int indent) const
{
  cout << spaces(indent) << "RofStmt " << this << " <" << m_loc << ">\n";

  for(auto &init : inits)
  {
    init->dump(indent + 2);
  }

  if (cond)
  {
    cond->dump(indent + 2);
  }

  for(auto &iter : iters)
  {
    iter->dump(indent + 2);
  }

  if (stmt)
  {
    stmt->dump(indent + 2);
  }
}


//|--------------------- WhileStmt ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// WhileStmt::Constructor /////////////////////////////
WhileStmt::WhileStmt(SourceLocation loc)
  : Stmt(While, loc)
{
}

//|///////////////////// WhileStmt::dump ///////////////////////////////////
void WhileStmt::dump(int indent) const
{
  cout << spaces(indent) << "WhileStmt " << this << " <" << m_loc << ">\n";

  for(auto &init : inits)
  {
    init->dump(indent + 2);
  }

  if (cond)
  {
    cond->dump(indent + 2);
  }

  if (stmt)
  {
    stmt->dump(indent + 2);
  }
}


//|--------------------- SwitchStmt -----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// SwitchStmt::Constructor ////////////////////////////
SwitchStmt::SwitchStmt(SourceLocation loc)
  : Stmt(Switch, loc)
{
}

//|///////////////////// SwitchStmt::dump //////////////////////////////////
void SwitchStmt::dump(int indent) const
{
  cout << spaces(indent) << "SwitchStmt " << this << " <" << m_loc << ">\n";

  for(auto &init : inits)
  {
    init->dump(indent + 2);
  }

  if (cond)
  {
    cond->dump(indent + 2);
  }

  for(auto &decl : decls)
  {
    decl->dump(indent + 2);
  }
}


//|--------------------- TryStmt --------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// TryStmt::Constructor ///////////////////////////////
TryStmt::TryStmt(SourceLocation loc)
  : Stmt(Try, loc)
{
}

//|///////////////////// TryStmt::dump //////////////////////////////////////
void TryStmt::dump(int indent) const
{
  cout << spaces(indent) << "TryStmt " << this << " <" << m_loc << ">\n";

  if (body)
  {
    body->dump(indent + 2);
  }

  if (errorvar)
  {
    errorvar->dump(indent + 2);
  }

  if (handler)
  {
    handler->dump(indent + 2);
  }
}


//|--------------------- ThrowStmt ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ThrowStmt::Constructor /////////////////////////////
ThrowStmt::ThrowStmt(SourceLocation loc)
  : Stmt(Throw, loc)
{
}

//|///////////////////// ThrowStmt::dump ////////////////////////////////////
void ThrowStmt::dump(int indent) const
{
  cout << spaces(indent) << "ThrowStmt " << this << " <" << m_loc << ">\n";

  if (expr)
  {
    expr->dump(indent + 2);
  }
}


//|--------------------- BreakStmt ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// BreakStmt::Constructor /////////////////////////////
BreakStmt::BreakStmt(SourceLocation loc)
  : Stmt(Break, loc)
{
}

//|///////////////////// BreakStmt::dump ////////////////////////////////////
void BreakStmt::dump(int indent) const
{
  cout << spaces(indent) << "BreakStmt " << this << " <" << m_loc << ">\n";
}


//|--------------------- ContinueStmt ---------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ContinueStmt::Constructor //////////////////////////
ContinueStmt::ContinueStmt(SourceLocation loc)
  : Stmt(Continue, loc)
{
}

//|///////////////////// ContinueStmt::dump /////////////////////////////////
void ContinueStmt::dump(int indent) const
{
  cout << spaces(indent) << "ContinueStmt " << this << " <" << m_loc << ">\n";
}


//|--------------------- InjectionStmt --------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// InjectionStmt::Constructor /////////////////////////
InjectionStmt::InjectionStmt(SourceLocation loc)
  : Stmt(Injection, loc)
{
}

InjectionStmt::InjectionStmt(Expr *expr, SourceLocation loc)
  : Stmt(Injection, loc),
    expr(expr)
{
}

//|///////////////////// InjectionStmt::dump ////////////////////////////////
void InjectionStmt::dump(int indent) const
{
  cout << spaces(indent) << "InjectionStmt " << this << " <" << m_loc << ">\n";

  if (expr)
  {
    expr->dump(indent + 2);
  }
}


//|--------------------- ReturnStmt -----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ReturnStmt::Constructor ////////////////////////////
ReturnStmt::ReturnStmt(SourceLocation loc)
  : Stmt(Return, loc)
{
}

ReturnStmt::ReturnStmt(Expr *expr, SourceLocation loc)
  : Stmt(Return, loc),
    expr(expr)
{
}

//|///////////////////// ReturnStmt::dump ///////////////////////////////////
void ReturnStmt::dump(int indent) const
{
  cout << spaces(indent) << "ReturnStmt " << this << " <" << m_loc << ">\n";

  if (expr)
  {
    expr->dump(indent + 2);
  }
}
