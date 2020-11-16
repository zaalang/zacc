//
// expr.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "ast.h"
#include "util.h"
#include <sstream>
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

//|///////////////////// is_literal_expr ////////////////////////////////////
bool is_literal_expr(Expr const *expr)
{
  return expr->kind() == Expr::VoidLiteral || expr->kind() == Expr::BoolLiteral || expr->kind() == Expr::CharLiteral || expr->kind() == Expr::IntLiteral || expr->kind() == Expr::FloatLiteral || expr->kind() == Expr::StringLiteral || expr->kind() == Expr::PtrLiteral || expr->kind() == Expr::ArrayLiteral || expr->kind() == Expr::CompoundLiteral;
}

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, Expr const &expr)
{
  switch (expr.kind())
  {
    case Expr::VoidLiteral:
      os << "void";
      break;

    case Expr::BoolLiteral:
      os << (static_cast<BoolLiteralExpr const &>(expr).value() ? "true" : "false");
      break;

    case Expr::CharLiteral:
      os << static_cast<CharLiteralExpr const &>(expr).value();
      break;

    case Expr::IntLiteral:
      os << static_cast<IntLiteralExpr const &>(expr).value();
      break;

    case Expr::FloatLiteral:
      os << static_cast<FloatLiteralExpr const &>(expr).value();
      break;

    case Expr::StringLiteral:
      os << '"' << escape(static_cast<StringLiteralExpr const &>(expr).value()) << '"';
      break;

    case Expr::PtrLiteral:
      os << "null";
      break;

    case Expr::ArrayLiteral:
      os << static_cast<ArrayLiteralExpr const &>(expr).value();
      break;

    case Expr::CompoundLiteral:
      os << static_cast<CompoundLiteralExpr const &>(expr).value();
      break;

    case Expr::Paren:
      os << "()";
      break;

    case Expr::UnaryOp:
      os << static_cast<UnaryOpExpr const &>(expr).name();
      break;

    case Expr::BinaryOp:
      os << static_cast<BinaryOpExpr const &>(expr).name();
      break;

    case Expr::TernaryOp:
      os << '?';
      break;

    case Expr::DeclRef:
      os << *static_cast<DeclRefExpr const &>(expr).decl;
      break;

    case Expr::Call:
      os << *static_cast<CallExpr const &>(expr).callee;
      break;

    case Expr::Sizeof:
      os << "sizeof";
      break;

    case Expr::Alignof:
      os << "alignof";
      break;

    case Expr::Cast:
      os << "cast";
      break;

    case Expr::New:
      os << "new";
      break;

    case Expr::Requires:
      os << "requires";
      break;

    case Expr::Lambda:
      os << "fn";
      break;
  }

  return os;
}


//|--------------------- Expr -----------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// Expr::Constructor //////////////////////////////////
Expr::Expr(Kind kind, SourceLocation loc)
  : m_kind(kind),
    m_loc(loc)
{
}


//|--------------------- VoidLiteralExpr ------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// VoidLiteralExpr::Constructor ///////////////////////
VoidLiteralExpr::VoidLiteralExpr(SourceLocation loc)
  : Expr(VoidLiteral, loc)
{
}

//|///////////////////// PtrLiteralExpr::dump ///////////////////////////////
void VoidLiteralExpr::dump(int indent) const
{
  cout << spaces(indent) << "VoidLiteralExpr " << this << " <" << m_loc << "> " << *this << '\n';
}


//|--------------------- BoolLiteralExpr ------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// BoolLiteralExpr::Constructor ///////////////////////
BoolLiteralExpr::BoolLiteralExpr(bool value, SourceLocation loc)
  : Expr(BoolLiteral, loc),
    m_value(value)
{
}

//|///////////////////// BoolLiteralExpr::dump //////////////////////////////
void BoolLiteralExpr::dump(int indent) const
{
  cout << spaces(indent) << "BoolLiteralExpr " << this << " <" << m_loc << "> " << *this << '\n';
}


//|--------------------- CharLiteralExpr ------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// CharLiteralExpr::Constructor ////////////////////////
CharLiteralExpr::CharLiteralExpr(Numeric::Int const &value, SourceLocation loc)
  : Expr(CharLiteral, loc),
    m_value(value)
{
}

//|///////////////////// CharLiteralExpr::dump ///////////////////////////////
void CharLiteralExpr::dump(int indent) const
{
  cout << spaces(indent) << "CharLiteralExpr " << this << " <" << m_loc << "> " << *this << '\n';
}


//|--------------------- IntLiteralExpr -------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// IntLiteralExpr::Constructor ////////////////////////
IntLiteralExpr::IntLiteralExpr(Numeric::Int const &value, SourceLocation loc)
  : Expr(IntLiteral, loc),
    m_value(value)
{
}

//|///////////////////// IntLiteralExpr::dump ///////////////////////////////
void IntLiteralExpr::dump(int indent) const
{
  cout << spaces(indent) << "IntLiteralExpr " << this << " <" << m_loc << "> " << *this << '\n';
}


//|--------------------- FloatLiteralExpr -----------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// FloatLiteralExpr::Constructor //////////////////////
FloatLiteralExpr::FloatLiteralExpr(Numeric::Float const &value, SourceLocation loc)
  : Expr(FloatLiteral, loc),
    m_value(value)
{
}

//|///////////////////// FloatLiteralExpr::dump /////////////////////////////
void FloatLiteralExpr::dump(int indent) const
{
  cout << spaces(indent) << "FloatLiteralExpr " << this << " <" << m_loc << "> " << *this << '\n';
}


//|--------------------- StringLiteralExpr ----------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// StringLiteralExpr::Constructor /////////////////////
StringLiteralExpr::StringLiteralExpr(string_view value, SourceLocation loc)
  : Expr(StringLiteral, loc),
    m_value(value)
{
}

//|///////////////////// StringLiteralExpr::dump ////////////////////////////
void StringLiteralExpr::dump(int indent) const
{
  cout << spaces(indent) << "StringLiteralExpr " << this << " <" << m_loc << "> " << *this << '\n';
}


//|--------------------- PtrLiteralExpr -------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// PtrLiteralExpr::Constructor ////////////////////////
PointerLiteralExpr::PointerLiteralExpr(SourceLocation loc)
  : Expr(PtrLiteral, loc)
{
}

//|///////////////////// PtrLiteralExpr::dump ///////////////////////////////
void PointerLiteralExpr::dump(int indent) const
{
  cout << spaces(indent) << "PtrLiteralExpr " << this << " <" << m_loc << "> " << *this << '\n';
}


//|--------------------- ArrayLiteralExpr -----------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ArrayLiteralExpr::Constructor //////////////////////
ArrayLiteralExpr::ArrayLiteralExpr(vector<Expr*> const &elements, Type *size, SourceLocation loc)
  : Expr(ArrayLiteral, loc),
    size(size),
    elements(elements)
{
}

//|///////////////////// ArrayLiteralExpr::value ////////////////////////////
string ArrayLiteralExpr::value() const
{
  stringstream ss;

  ss << '[';

  for(size_t i = 0; i < min(elements.size(), size_t(10)); ++i)
  {
    ss << ((i != 0) ? ", " : "") << *elements[i];
  }

  if (elements.size() > 10)
    ss << " ...";

  ss << ']';

  return ss.str();
}

//|///////////////////// ArrayLiteralExpr::dump /////////////////////////////
void ArrayLiteralExpr::dump(int indent) const
{
  cout << spaces(indent) << "ArrayLiteralExpr " << this << " <" << m_loc << "> " << *this << '\n';
}


//|--------------------- CompoundLiteralExpr --------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// CompoundLiteralExpr::Constructor ///////////////////
CompoundLiteralExpr::CompoundLiteralExpr(vector<Expr*> const &fields, SourceLocation loc)
  : Expr(CompoundLiteral, loc),
    fields(fields)
{
}

//|///////////////////// CompoundLiteralExpr::value /////////////////////////
string CompoundLiteralExpr::value() const
{
  stringstream ss;

  ss << '{';

  for(size_t i = 0; i < fields.size(); ++i)
  {
    ss << ((i != 0) ? ", " : "") << *fields[i];
  }

  ss << '}';

  return ss.str();
}

//|///////////////////// CompoundLiteralExpr::dump //////////////////////////
void CompoundLiteralExpr::dump(int indent) const
{
  cout << spaces(indent) << "CompoundLiteralExpr " << this << " <" << m_loc << "> " << *this << '\n';
}


//|--------------------- ParenExpr ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ParenExpr::Constructor /////////////////////////////
ParenExpr::ParenExpr(Expr *subexpr, SourceLocation loc)
  : Expr(Paren, loc),
    subexpr(subexpr)
{
}

//|///////////////////// ParenExpr::dump ////////////////////////////////////
void ParenExpr::dump(int indent) const
{
  cout << spaces(indent) << "ParenExpr " << this << " " << *this << '\n';

  if (subexpr)
  {
    subexpr->dump(indent + 2);
  }
}


//|--------------------- UnaryOpExpr ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// UnaryOpExpr::Constructor ///////////////////////////
UnaryOpExpr::UnaryOpExpr(OpCode op, Expr *subexpr, SourceLocation loc)
  : Expr(UnaryOp, loc),
    subexpr(subexpr),
    m_op(op)
{
}

//|///////////////////// UnaryOpExpr::name //////////////////////////////////
const char *UnaryOpExpr::name(UnaryOpExpr::OpCode op)
{
  switch (op)
  {
    case Plus: return "+";
    case Minus: return "-";
    case Not: return "~";
    case LNot: return "!";
    case PreInc: return "++";
    case PreDec: return "--";
    case PostInc: return "++";
    case PostDec: return "--";
    case Ref: return "&";
    case Fer: return "*";
    case Fwd: return "&&";
    case Literal: return "#";
    case Unpack: return "...";
  }

  throw logic_error("invalid unary op");
}

//|///////////////////// UnaryOpExpr::name //////////////////////////////////
const char *UnaryOpExpr::name() const
{
  return name(m_op);
}

//|///////////////////// UnaryOpExpr::dump //////////////////////////////////
void UnaryOpExpr::dump(int indent) const
{
  cout << spaces(indent) << "UnaryOpExpr " << this << " <" << m_loc << "> " << *this << '\n';

  if (subexpr)
  {
    subexpr->dump(indent + 2);
  }
}


//|--------------------- BinaryOpExpr ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// BinaryOpExpr::Constructor ///////////////////////////
BinaryOpExpr::BinaryOpExpr(OpCode op, Expr *lhs, Expr *rhs, SourceLocation loc)
  : Expr(BinaryOp, loc),
    lhs(lhs),
    rhs(rhs),
    m_op(op)
{
}

//|///////////////////// BinaryOpExpr::name /////////////////////////////////
const char *BinaryOpExpr::name(BinaryOpExpr::OpCode op)
{
  switch (op)
  {
    case Add: return "+";
    case Sub: return "-";
    case Div: return  "/";
    case Mul: return "*";
    case Rem: return "%";
    case Shl: return "<<";
    case Shr: return ">>";
    case And: return "&";
    case Or: return "|";
    case Xor: return "^";
    case LAnd: return "&&";
    case LOr: return "||";
    case LT: return "<";
    case GT: return ">";
    case LE: return "<=";
    case GE: return ">=";
    case EQ: return "==";
    case NE: return "!=";
    case Cmp: return "<=>";
    case Assign: return "=";
    case MulAssign: return "*=";
    case DivAssign: return "/=";
    case RemAssign: return "%=";
    case AddAssign: return "+=";
    case SubAssign: return "-=";
    case ShlAssign: return "<<=";
    case ShrAssign: return ">>=";
    case AndAssign: return "&=";
    case XorAssign: return "^=";
    case OrAssign: return "|=";
    case Range: return "..";
    case RangeEq: return "..=";
  }

  throw logic_error("invalid binary op");
}

//|///////////////////// BinaryOpExpr::name /////////////////////////////////
const char *BinaryOpExpr::name() const
{
  return name(m_op);
}

//|///////////////////// BinaryOpExpr::dump //////////////////////////////////
void BinaryOpExpr::dump(int indent) const
{
  cout << spaces(indent) << "BinaryOpExpr " << this << " <" << m_loc << "> " << *this << '\n';

  if (lhs)
  {
    lhs->dump(indent + 2);
  }

  if (rhs)
  {
    rhs->dump(indent + 2);
  }
}


//|--------------------- TernaryOpExpr ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// TernaryOpExpr::Constructor ///////////////////////////
TernaryOpExpr::TernaryOpExpr(Expr *cond, Expr *lhs, Expr *rhs, SourceLocation loc)
  : Expr(TernaryOp, loc),
    cond(cond),
    lhs(lhs),
    rhs(rhs)
{
}

//|///////////////////// TernaryOpExpr::dump //////////////////////////////////
void TernaryOpExpr::dump(int indent) const
{
  cout << spaces(indent) << "TernaryOpExpr " << this << " <" << m_loc << "> " << *this << '\n';

  if (cond)
  {
    cond->dump(indent + 2);
  }

  if (lhs)
  {
    lhs->dump(indent + 2);
  }

  if (rhs)
  {
    rhs->dump(indent + 2);
  }
}


//|--------------------- DeclRefExpr ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// DeclRefExpr::Constructor ///////////////////////////
DeclRefExpr::DeclRefExpr(Decl *decl, SourceLocation loc)
  : Expr(DeclRef, loc),
    decl(decl)
{
}

//|///////////////////// DeclRefExpr::Constructor ///////////////////////////
DeclRefExpr::DeclRefExpr(Expr *base, Decl *decl, SourceLocation loc)
  : Expr(DeclRef, loc),
    decl(decl),
    base(base)
{
}

//|///////////////////// DeclRefExpr::dump //////////////////////////////////
void DeclRefExpr::dump(int indent) const
{
  cout << spaces(indent) << "DeclRefExpr " << this << " <" << m_loc << ">\n";

  if (decl)
  {
    switch (decl->kind())
    {
      case Decl::DeclScoped:
        cout << spaces(indent + 2) << "DeclScopedDecl " << decl << " " << *decl << "\n";
        break;

      case Decl::DeclRef:
        cout << spaces(indent + 2) << "DeclRefDecl " << decl << " " << *decl << "\n";
        break;

      case Decl::VoidVar:
        cout << spaces(indent + 2) << "VoidVarDecl " << decl << " '" << *decl << "'\n";
        break;

      case Decl::StmtVar:
        cout << spaces(indent + 2) << "StmtVarDecl " << decl << " '" << *decl << "'\n";
        break;

      case Decl::RangeVar:
        cout << spaces(indent + 2) << "RangeVarDecl " << decl << " '" << *decl << "'\n";
        break;

      case Decl::ParmVar:
        cout << spaces(indent + 2) << "ParmVarDecl " << decl << " '" << *decl << "'\n";
        break;

      case Decl::ThisVar:
        cout << spaces(indent + 2) << "ThisVarDecl " << decl << " '" << *decl << "'\n";
        break;

      case Decl::FieldVar:
        cout << spaces(indent + 2) << "FieldVarDecl " << decl << " '" << *decl << "'\n";
        break;

      case Decl::ErrorVar:
        cout << spaces(indent + 2) << "ErrorVarDecl " << decl << " '" << *decl << "'\n";
        break;

      default:
        assert(false);
    }
  }

  if (base)
  {
    base->dump(indent + 2);
  }
}


//|--------------------- CallExpr -------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// CallExpr::Constructor //////////////////////////////
CallExpr::CallExpr(Decl *callee, SourceLocation loc)
  : Expr(Call, loc),
    callee(callee)
{
}

//|///////////////////// CallExpr::Constructor //////////////////////////////
CallExpr::CallExpr(Decl *callee, vector<Expr*> const &parms, map<string, Expr*> const &namedparms, SourceLocation loc)
  : Expr(Call, loc),
    callee(callee),
    parms(parms),
    namedparms(namedparms)
{
}

//|///////////////////// CallExpr::Constructor //////////////////////////////
CallExpr::CallExpr(Expr *base, Decl *callee, vector<Expr*> const &parms, map<string, Expr*> const &namedparms, SourceLocation loc)
  : Expr(Call, loc),
    callee(callee),
    parms(parms),
    namedparms(namedparms),
    base(base)
{
}

//|///////////////////// CallExpr::dump /////////////////////////////////////
void CallExpr::dump(int indent) const
{
  cout << spaces(indent) << "CallExpr " << this << " <" << m_loc << "> " << *this << "\n";

  for(auto &parm : parms)
  {
    parm->dump(indent + 2);
  }

  for(auto &[name, parm] : namedparms)
  {
    parm->dump(indent + 2);
  }

  if (base)
  {
    base->dump(indent + 2);
  }
}


//|--------------------- SizeofExpr -----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// SizeofExpr::Constructor ////////////////////////////
SizeofExpr::SizeofExpr(Type *type, SourceLocation loc)
  : Expr(Sizeof, loc),
    type(type)
{
}

//|///////////////////// SizeofExpr::Constructor ////////////////////////////
SizeofExpr::SizeofExpr(Expr *expr, SourceLocation loc)
  : Expr(Sizeof, loc),
    expr(expr)
{
}

//|///////////////////// SizeofExpr::dump ///////////////////////////////////
void SizeofExpr::dump(int indent) const
{
  cout << spaces(indent) << "SizeofExpr " << this << " <" << m_loc << "> " << *this << "\n";

  if (type)
  {
    type->dump(indent + 2);
  }

  if (expr)
  {
    expr->dump(indent + 2);
  }
}


//|--------------------- AlignofExpr ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// AlignofExpr::Constructor ///////////////////////////
AlignofExpr::AlignofExpr(Type *type, SourceLocation loc)
  : Expr(Alignof, loc),
    type(type)
{
}

//|///////////////////// AlignofExpr::Constructor ///////////////////////////
AlignofExpr::AlignofExpr(Expr *expr, SourceLocation loc)
  : Expr(Alignof, loc),
    expr(expr)
{
}

//|///////////////////// AlignofExpr::dump //////////////////////////////////
void AlignofExpr::dump(int indent) const
{
  cout << spaces(indent) << "AlignofExpr " << this << " <" << m_loc << "> " << *this << "\n";

  if (type)
  {
    type->dump(indent + 2);
  }

  if (expr)
  {
    expr->dump(indent + 2);
  }
}


//|--------------------- CastExpr -------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// CastExpr::Constructor //////////////////////////////
CastExpr::CastExpr(Type *type, Expr *expr, SourceLocation loc)
  : Expr(Cast, loc),
    type(type),
    expr(expr)
{
}

//|///////////////////// CastExpr::dump /////////////////////////////////////
void CastExpr::dump(int indent) const
{
  cout << spaces(indent) << "CastExpr " << this << " <" << m_loc << "> " << *this << "\n";

  if (type)
  {
    type->dump(indent + 2);
  }

  if (expr)
  {
    expr->dump(indent + 2);
  }
}


//|--------------------- NewExpr --------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// NewExpr::Constructor ///////////////////////////////
NewExpr::NewExpr(Type *type, Expr *address, SourceLocation loc)
  : Expr(New, loc),
    type(type),
    address(address)
{
}

//|///////////////////// NewExpr::Constructor ///////////////////////////////
NewExpr::NewExpr(Type *type, Expr *address, vector<Expr*> const &parms, map<std::string, Expr*> const &namedparms, SourceLocation loc)
  : Expr(New, loc),
    type(type),
    address(address),
    parms(parms),
    namedparms(namedparms)
{
}

//|///////////////////// NewExpr::dump //////////////////////////////////////
void NewExpr::dump(int indent) const
{
  cout << spaces(indent) << "NewExpr " << this << " <" << m_loc << "> " << *this << "\n";

  type->dump(indent + 2);

  address->dump(indent + 2);

  for(auto &parm : parms)
  {
    parm->dump(indent + 2);
  }

  for(auto &[name, parm] : namedparms)
  {
    parm->dump(indent + 2);
  }
}


//|--------------------- RequiresExpr ---------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// RequiresExpr::Constructor //////////////////////////
RequiresExpr::RequiresExpr(Decl *decl, SourceLocation loc)
  : Expr(Requires, loc),
    decl(decl)
{
}

//|///////////////////// RequiresExpr::dump /////////////////////////////////
void RequiresExpr::dump(int indent) const
{
  cout << spaces(indent) << "RequiresExpr " << this << " <" << m_loc << "> " << *this << "\n";

  if (decl)
  {
    decl->dump(indent + 2);
  }
}


//|--------------------- LambdaExpr -----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// LambdaExpr::Constructor ////////////////////////////
LambdaExpr::LambdaExpr(Decl *decl, SourceLocation loc)
  : Expr(Lambda, loc),
    decl(decl)
{
}

//|///////////////////// LambdaExpr::dump ///////////////////////////////////
void LambdaExpr::dump(int indent) const
{
  cout << spaces(indent) << "LambdaExpr " << this << " <" << m_loc << "> " << *this << "\n";

  if (decl)
  {
    decl->dump(indent + 2);
  }
}

