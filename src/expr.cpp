//
// expr.cpp
//
// Copyright (c) 2020-2024 Peter Niekamp. All rights reserved.
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

Ident *UnaryOpExpr::unaryop_idents[] = {
  /* Plus,      */ Ident::from("+"),
  /* Minus,     */ Ident::from("-"),
  /* Not,       */ Ident::from("~"),
  /* LNot,      */ Ident::from("!"),
  /* PreInc,    */ Ident::from("++"),
  /* PreDec,    */ Ident::from("--"),
  /* PostInc,   */ Ident::from("++"),
  /* PostDec,   */ Ident::from("--"),
  /* Unwrap,    */ Ident::from("?!"),
  /* Begin,     */ Ident::from("begin"),
  /* End,       */ Ident::from("end"),
  /* Ref,       */ Ident::from("&"),
  /* Fer,       */ Ident::from("*"),
  /* Fwd,       */ Ident::from("&&"),
  /* Literal,   */ Ident::from("#"),
  /* Extern,    */ Ident::from("extern"),
  /* Unpack     */ Ident::from("..."),
};

Ident *BinaryOpExpr::binaryop_idents[] = {
  /* Add,       */ Ident::from("+"),
  /* Sub,       */ Ident::from("-"),
  /* Div,       */ Ident::from("/"),
  /* Mul,       */ Ident::from("*"),
  /* Rem,       */ Ident::from("%"),
  /* Shl,       */ Ident::from("<<"),
  /* Shr,       */ Ident::from(">>"),
  /* And,       */ Ident::from("&"),
  /* Or,        */ Ident::from("|"),
  /* Xor,       */ Ident::from("^"),
  /* LAnd,      */ Ident::from("&&"),
  /* LOr,       */ Ident::from("||"),
  /* LT,        */ Ident::from("<"),
  /* GT,        */ Ident::from(">"),
  /* LE,        */ Ident::from("<="),
  /* GE,        */ Ident::from(">="),
  /* EQ,        */ Ident::from("=="),
  /* NE,        */ Ident::from("!="),
  /* Cmp,       */ Ident::from("<=>"),
  /* Match,     */ Ident::from("~="),
  /* Assign,    */ Ident::from("="),
  /* AddAssign, */ Ident::from("+="),
  /* SubAssign, */ Ident::from("-="),
  /* DivAssign, */ Ident::from("/="),
  /* MulAssign, */ Ident::from("*="),
  /* RemAssign, */ Ident::from("%="),
  /* ShlAssign, */ Ident::from("<<="),
  /* ShrAssign, */ Ident::from(">>="),
  /* AndAssign, */ Ident::from("&="),
  /* OrAssign,  */ Ident::from("|="),
  /* XorAssign, */ Ident::from("^="),
  /* Range,     */ Ident::from(".."),
  /* RangeEq,   */ Ident::from("..="),
  /* Coalesce,  */ Ident::from("??"),
  /* Index,     */ Ident::from("[]"),
};

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
      for (int i = 0; i < indent.n; ++i)
        os << ' ';

      return os;
    }

    int n;
  };
}

//|///////////////////// is_literal_expr ////////////////////////////////////
bool is_literal_expr(Expr *expr)
{
  switch (expr->kind())
  {
    case Expr::VoidLiteral:
    case Expr::BoolLiteral:
    case Expr::CharLiteral:
    case Expr::IntLiteral:
    case Expr::FloatLiteral:
    case Expr::StringLiteral:
    case Expr::PointerLiteral:
    case Expr::FunctionPointer:
      return true;

    case Expr::ArrayLiteral:

      for (auto &element : expr_cast<ArrayLiteralExpr>(expr)->elements)
        if (!is_literal_expr(element))
          return false;

      return true;

    case Expr::CompoundLiteral:

      for (auto &field : expr_cast<CompoundLiteralExpr>(expr)->fields)
        if (!is_literal_expr(field))
          return false;

      return true;

    default:
      return false;
  }
}

//|///////////////////// is_declref_expr ////////////////////////////////////
bool is_declref_expr(Expr *expr)
{
  return expr->kind() == Expr::DeclRef;
}

//|///////////////////// is_declrefdecl_expr ////////////////////////////////
DeclRefDecl *is_declrefdecl_expr(Expr *expr)
{
  if (expr->kind() == Expr::DeclRef && expr_cast<DeclRefExpr>(expr)->decl->kind() == Decl::DeclRef)
    return decl_cast<DeclRefDecl>(expr_cast<DeclRefExpr>(expr)->decl);

  return nullptr;
}

//|///////////////////// is_declscopeddecl_expr /////////////////////////////
DeclScopedDecl *is_declscopeddecl_expr(Expr *expr)
{
  if (expr->kind() == Expr::DeclRef && expr_cast<DeclRefExpr>(expr)->decl->kind() == Decl::DeclScoped)
    return decl_cast<DeclScopedDecl>(expr_cast<DeclRefExpr>(expr)->decl);

  return nullptr;
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

    case Expr::PointerLiteral:
      os << "null";
      break;

    case Expr::FunctionPointer:
      os << static_cast<FunctionPointerExpr const &>(expr).value();
      break;

    case Expr::ArrayLiteral:
      os << static_cast<ArrayLiteralExpr const &>(expr).value();
      break;

    case Expr::CompoundLiteral:
      os << static_cast<CompoundLiteralExpr const &>(expr).value();
      break;

    case Expr::ExprRef:
      os << "&mut";
      break;

    case Expr::Paren:
      os << '(' << *static_cast<NamedExpr const &>(expr).subexpr << ')';
      break;

    case Expr::Named:
      os << *static_cast<NamedExpr const &>(expr).name << ": " << *static_cast<NamedExpr const &>(expr).subexpr;
      break;

    case Expr::UnaryOp:
      os << *static_cast<UnaryOpExpr const &>(expr).name();
      break;

    case Expr::BinaryOp:
      os << *static_cast<BinaryOpExpr const &>(expr).name();
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

    case Expr::Offsetof:
      os << "offsetof";
      break;

    case Expr::Instanceof:
      os << "__is_instance";
      break;

    case Expr::Typeid:
      os << "typeid " << *static_cast<TypeidExpr const &>(expr).decl;
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

    case Expr::Where:
      os << "where";
      break;

    case Expr::Match:
      os << "match";
      break;

    case Expr::Lambda:
      os << "lambda";
      break;

    case Expr::Fragment:
      os << "fragment";
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


//|--------------------- PointerLiteralExpr ---------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// PointerLiteralExpr::Constructor ////////////////////
PointerLiteralExpr::PointerLiteralExpr(SourceLocation loc)
  : Expr(PointerLiteral, loc)
{
}

//|///////////////////// PointerLiteralExpr::dump ///////////////////////////
void PointerLiteralExpr::dump(int indent) const
{
  cout << spaces(indent) << "PointerLiteralExpr " << this << " <" << m_loc << "> " << *this << '\n';
}


//|--------------------- FunctionPointerExpr --------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// FunctionPointerExpr::Constructor ///////////////////
FunctionPointerExpr::FunctionPointerExpr(FnSig const &fn, SourceLocation loc)
  : Expr(FunctionPointer, loc),
    m_fn(fn)
{
}

//|///////////////////// FunctionPointerExpr::dump //////////////////////////
void FunctionPointerExpr::dump(int indent) const
{
  cout << spaces(indent) << "FunctionPointerExpr " << this << " <" << m_loc << "> " << *this << '\n';
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

ArrayLiteralExpr::ArrayLiteralExpr(Type *elementtype, vector<Expr*> const &elements, Type *size, SourceLocation loc)
  : Expr(ArrayLiteral, loc),
    size(size),
    elements(elements),
    coercedtype(elementtype)
{
}

//|///////////////////// ArrayLiteralExpr::value ////////////////////////////
string ArrayLiteralExpr::value() const
{
  stringstream ss;

  ss << '[';

  for (size_t i = 0; i < min(elements.size(), size_t(10)); ++i)
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

  ss << "{ ";

  for (size_t i = 0; i < fields.size(); ++i)
  {
    ss << ((i != 0) ? ", " : "") << *fields[i];
  }

  ss << " }";

  return ss.str();
}

//|///////////////////// CompoundLiteralExpr::dump //////////////////////////
void CompoundLiteralExpr::dump(int indent) const
{
  cout << spaces(indent) << "CompoundLiteralExpr " << this << " <" << m_loc << "> " << *this << '\n';
}


//|--------------------- ExprRefExpr ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ExprRefExpr::Constructor ///////////////////////////
ExprRefExpr::ExprRefExpr(Expr *subexpr, long qualifiers, SourceLocation loc)
  : Expr(ExprRef, loc),
    qualifiers(qualifiers),
    subexpr(subexpr)
{
}

//|///////////////////// ExprRefExpr::dump //////////////////////////////////
void ExprRefExpr::dump(int indent) const
{
  cout << spaces(indent) << "ExprRefExpr " << this << " " << *this << '\n';

  if (subexpr)
  {
    subexpr->dump(indent + 2);
  }
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


//|--------------------- NamedExpr ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// NamedExpr::Constructor /////////////////////////////
NamedExpr::NamedExpr(Ident *name, Expr *subexpr, SourceLocation loc)
  : Expr(Named, loc),
    name(name),
    subexpr(subexpr)
{
}

//|///////////////////// NamedExpr::dump ////////////////////////////////////
void NamedExpr::dump(int indent) const
{
  cout << spaces(indent) << "NamedExpr " << this << " " << *this << '\n';

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
CallExpr::CallExpr(Decl *callee, vector<Expr*> const &parms, SourceLocation loc)
  : Expr(Call, loc),
    callee(callee),
    parms(parms)
{
}

//|///////////////////// CallExpr::Constructor //////////////////////////////
CallExpr::CallExpr(Expr *base, Decl *callee, vector<Expr*> const &parms, SourceLocation loc)
  : Expr(Call, loc),
    callee(callee),
    parms(parms),
    base(base)
{
}

//|///////////////////// CallExpr::dump /////////////////////////////////////
void CallExpr::dump(int indent) const
{
  cout << spaces(indent) << "CallExpr " << this << " <" << m_loc << "> " << *this << "\n";

  if (base)
  {
    base->dump(indent + 2);
  }

  for (auto &parm : parms)
  {
    parm->dump(indent + 2);
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
AlignofExpr::AlignofExpr(Decl *decl, SourceLocation loc)
  : Expr(Alignof, loc),
    decl(decl)
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

  if (decl)
  {
    decl->dump(indent + 2);
  }
}


//|--------------------- OffsetofExpr ---------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// OffsetofExpr::Constructor //////////////////////////
OffsetofExpr::OffsetofExpr(Decl *decl, SourceLocation loc)
  : Expr(Offsetof, loc),
    decl(decl)
{
}

//|///////////////////// OffsetofExpr::dump /////////////////////////////////
void OffsetofExpr::dump(int indent) const
{
  cout << spaces(indent) << "OffsetofExpr " << this << " <" << m_loc << "> " << *this << "\n";

  if (decl)
  {
    decl->dump(indent + 2);
  }
}


//|--------------------- InstanceofExpr -------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// InstanceofExpr::Constructor ////////////////////////
InstanceofExpr::InstanceofExpr(Type *type, Type *instance, SourceLocation loc)
  : Expr(Instanceof, loc),
    type(type),
    instance(instance)
{
}

//|///////////////////// InstanceofExpr::dump ///////////////////////////////
void InstanceofExpr::dump(int indent) const
{
  cout << spaces(indent) << "InstanceofExpr " << this << " <" << m_loc << "> " << *this << "\n";

  if (type)
  {
    type->dump(indent + 2);
  }
}


//|--------------------- TypeidExpr -----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// TypeidExpr::Constructor ////////////////////////////
TypeidExpr::TypeidExpr(Decl *decl, SourceLocation loc)
  : Expr(Typeid, loc),
    decl(decl)
{
}

//|///////////////////// TypeidExpr::dump ///////////////////////////////////
void TypeidExpr::dump(int indent) const
{
  cout << spaces(indent) << "TypeidExpr " << this << " <" << m_loc << "> " << *this << "\n";

  if (decl)
  {
    decl->dump(indent + 2);
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
NewExpr::NewExpr(Type *type, Expr *address, vector<Expr*> const &parms, SourceLocation loc)
  : Expr(New, loc),
    type(type),
    address(address),
    parms(parms)
{
}

//|///////////////////// NewExpr::dump //////////////////////////////////////
void NewExpr::dump(int indent) const
{
  cout << spaces(indent) << "NewExpr " << this << " <" << m_loc << "> " << *this << "\n";

  type->dump(indent + 2);

  address->dump(indent + 2);

  for (auto &parm : parms)
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


//|--------------------- WhereExpr ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// WhereExpr::Constructor /////////////////////////////
WhereExpr::WhereExpr(Expr *expr, SourceLocation loc)
  : Expr(Where, loc),
    expr(expr)
{
}

//|///////////////////// WhereExpr::dump ////////////////////////////////////
void WhereExpr::dump(int indent) const
{
  cout << spaces(indent) << "WhereExpr " << this << " <" << m_loc << "> " << *this << "\n";

  if (expr)
  {
    expr->dump(indent + 2);
  }
}


//|--------------------- MatchExpr ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// MatchExpr::Constructor /////////////////////////////
MatchExpr::MatchExpr(Decl *decl, SourceLocation loc)
  : Expr(Match, loc),
    decl(decl)
{
}

//|///////////////////// MatchExpr::dump ////////////////////////////////////
void MatchExpr::dump(int indent) const
{
  cout << spaces(indent) << "MatchExpr " << this << " <" << m_loc << "> " << *this << "\n";

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


//|--------------------- FragmentExpr ---------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// FragmentExpr::Constructor //////////////////////////
FragmentExpr::FragmentExpr(vector<Expr*> const &args, vector<Decl*> const &decls, SourceLocation loc)
  : Expr(Fragment, loc),
    args(args),
    decls(decls)
{
}

FragmentExpr::FragmentExpr(vector<Decl*> const &decls, SourceLocation loc)
  : Expr(Fragment, loc),
    decls(decls)
{
}


//|///////////////////// FragmentExpr::dump /////////////////////////////////
void FragmentExpr::dump(int indent) const
{
  cout << spaces(indent) << "FragmentExpr " << this << " <" << m_loc << "> " << *this << "\n";

  for (auto &arg : args)
  {
    arg->dump(indent + 2);
  }

  for (auto &decl : decls)
  {
    decl->dump(indent + 2);
  }
}

