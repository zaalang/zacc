//
// expr.h
//
// Copyright (c) 2020-2023 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "lexer.h"
#include "numeric.h"
#include "mir.h"
#include <string>
#include <string_view>
#include <vector>
#include <map>

class Type;
class Decl;
class Ident;

//-------------------------- Expr -------------------------------------------
//---------------------------------------------------------------------------

class Expr
{
  public:

    enum Kind
    {
      Paren,
      VoidLiteral,
      BoolLiteral,
      CharLiteral,
      IntLiteral,
      FloatLiteral,
      StringLiteral,
      PointerLiteral,
      FunctionPointer,
      ArrayLiteral,
      CompoundLiteral,
      ExprRef,
      UnaryOp,
      BinaryOp,
      TernaryOp,
      DeclRef,
      Call,
      Sizeof,
      Alignof,
      Offsetof,
      Instanceof,
      Throws,
      Typeid,
      Cast,
      New,
      Requires,
      Match,
      Lambda,
      Fragment,
    };

  public:
    Expr(Kind kind, SourceLocation loc);

    Kind kind() const { return m_kind; }
    SourceLocation const &loc() const { return m_loc; }

    virtual void dump(int indent) const = 0;

  protected:

    Kind m_kind;
    SourceLocation m_loc;
};


//---------------------- VoidLiteralExpr ------------------------------------
//---------------------------------------------------------------------------

class VoidLiteralExpr : public Expr
{
  public:
    VoidLiteralExpr(SourceLocation loc);

    const char *value() const { return "void"; }

    void dump(int indent) const override;
};


//---------------------- BoolLiteralExpr ------------------------------------
//---------------------------------------------------------------------------

class BoolLiteralExpr : public Expr
{
  public:
    BoolLiteralExpr(bool value, SourceLocation loc);

    bool value() const { return m_value; }

    void dump(int indent) const override;

  protected:

    bool m_value;
};


//---------------------- CharLiteralExpr ------------------------------------
//---------------------------------------------------------------------------

class CharLiteralExpr : public Expr
{
  public:
    CharLiteralExpr(Numeric::Int const &value, SourceLocation loc);

    Numeric::Int const &value() const { return m_value; }

    void dump(int indent) const override;

  protected:

    Numeric::Int m_value;
};


//---------------------- IntLiteralExpr -------------------------------------
//---------------------------------------------------------------------------

class IntLiteralExpr : public Expr
{
  public:
    IntLiteralExpr(Numeric::Int const &value, SourceLocation loc);

    Numeric::Int const &value() const { return m_value; }

    void dump(int indent) const override;

  protected:

    Numeric::Int m_value;
};


//---------------------- FloatLiteralExpr -----------------------------------
//---------------------------------------------------------------------------

class FloatLiteralExpr : public Expr
{
  public:
    FloatLiteralExpr(Numeric::Float const &value, SourceLocation loc);

    Numeric::Float const &value() const { return m_value; }

    void dump(int indent) const override;

  protected:

    Numeric::Float m_value;
};


//---------------------- StringLiteralExpr ----------------------------------
//---------------------------------------------------------------------------

class StringLiteralExpr : public Expr
{
  public:
    StringLiteralExpr(std::string_view value, SourceLocation loc);

    std::string const &value() const { return m_value; }

    void dump(int indent) const override;

  protected:

    std::string m_value;
};


//---------------------- PtrLiteralExpr -------------------------------------
//---------------------------------------------------------------------------

class PointerLiteralExpr : public Expr
{
  public:
    PointerLiteralExpr(SourceLocation loc);

    const char *value() const { return "null"; }

    void dump(int indent) const override;
};


//---------------------- FunctionPointerExpr --------------------------------
//---------------------------------------------------------------------------

class FunctionPointerExpr : public Expr
{
  public:
    FunctionPointerExpr(FnSig const &fn, SourceLocation loc);

    FnSig const &value() const { return m_fn; }

    void dump(int indent) const override;

  private:

    FnSig m_fn;
};


//---------------------- ArrayLiteralExpr -----------------------------------
//---------------------------------------------------------------------------

class ArrayLiteralExpr : public Expr
{
  public:
    ArrayLiteralExpr(std::vector<Expr*> const &elements, Type *size, SourceLocation loc);
    ArrayLiteralExpr(Type *elementtype, std::vector<Expr*> const &elements, Type *size, SourceLocation loc);

    std::string value() const;

    Type *size;
    std::vector<Expr*> elements;
    Type *coercedtype = nullptr;

    void dump(int indent) const override;
};


//---------------------- CompoundLiteralExpr --------------------------------
//---------------------------------------------------------------------------

class CompoundLiteralExpr : public Expr
{
  public:
    CompoundLiteralExpr(std::vector<Expr*> const &fields, SourceLocation loc);

    std::string value() const;

    std::vector<Expr*> fields;

    void dump(int indent) const override;
};


//---------------------- ExprRefExpr ----------------------------------------
//---------------------------------------------------------------------------

class ExprRefExpr : public Expr
{
  public:

    enum Qualifiers
    {
      Mut = 0x1,
      Move = 0x2,
      Impl = 0x4,
    };

    long qualifiers = 0;

  public:
    ExprRefExpr(Expr *expr, long qualifiers, SourceLocation loc);

    Expr *expr;

    void dump(int indent) const override;
};


//---------------------- ParenExpr ------------------------------------------
//---------------------------------------------------------------------------

class ParenExpr : public Expr
{
  public:
    ParenExpr(Expr *subexpr, SourceLocation loc);

    Expr *subexpr;

    void dump(int indent) const override;
};


//---------------------- UnaryOpExpr ----------------------------------------
//---------------------------------------------------------------------------

class UnaryOpExpr : public Expr
{
  public:

    enum OpCode
    {
      Plus,
      Minus,
      Not,
      LNot,
      PreInc,
      PreDec,
      PostInc,
      PostDec,
      Unwrap,
      Begin,
      End,
      Ref,
      Fer,
      Fwd,
      Literal,
      Extern,
      Unpack
    };

    static Ident *unaryop_idents[];

    static Ident *name(UnaryOpExpr::OpCode op) { return unaryop_idents[op]; }

  public:
    UnaryOpExpr(OpCode op, Expr *subexpr, SourceLocation loc);

    OpCode op() const { return m_op; }
    Ident *name() const { return name(m_op); }

    Expr *subexpr;

    void dump(int indent) const override;

  protected:

    OpCode m_op;
};


//---------------------- BinaryOpExpr ---------------------------------------
//---------------------------------------------------------------------------

class BinaryOpExpr : public Expr
{
  public:

    enum OpCode
    {
      Add,
      Sub,
      Div,
      Mul,
      Rem,
      Shl,
      Shr,
      And,
      Or,
      Xor,
      LAnd,
      LOr,
      LT,
      GT,
      LE,
      GE,
      EQ,
      NE,
      Cmp,
      Match,
      Assign,
      AddAssign,
      SubAssign,
      DivAssign,
      MulAssign,
      RemAssign,
      ShlAssign,
      ShrAssign,
      AndAssign,
      OrAssign,
      XorAssign,
      Range,
      RangeEq,
      Coalesce,
      Index,
    };

    static Ident *binaryop_idents[];

    static Ident *name(BinaryOpExpr::OpCode op) { return binaryop_idents[op]; }

  public:
    BinaryOpExpr(OpCode op, Expr *lhs, Expr *rhs, SourceLocation loc);

    OpCode op() const { return m_op; }
    Ident *name() const { return name(m_op); }

    Expr *lhs, *rhs;

    void dump(int indent) const override;

  protected:

    OpCode m_op;
};


//---------------------- TernaryOpExpr --------------------------------------
//---------------------------------------------------------------------------

class TernaryOpExpr : public Expr
{
  public:
    TernaryOpExpr(Expr *cond, Expr *lhs, Expr *rhs, SourceLocation loc);

    Expr *cond, *lhs, *rhs;

    void dump(int indent) const override;
};


//---------------------- DeclRefExpr ----------------------------------------
//---------------------------------------------------------------------------

class DeclRefExpr : public Expr
{
  public:
    DeclRefExpr(Decl *decl, SourceLocation loc);
    DeclRefExpr(Expr *base, Decl *decl, SourceLocation loc);

    Decl *decl;

    Expr *base = nullptr;

    void dump(int indent) const override;
};


//---------------------- CallExpr -------------------------------------------
//---------------------------------------------------------------------------

class CallExpr : public Expr
{
  public:
    CallExpr(Decl *callee, SourceLocation loc);
    CallExpr(Decl *callee, std::vector<Expr*> const &parms, std::map<Ident*, Expr*> const &namedparms, SourceLocation loc);
    CallExpr(Expr *base, Decl *callee, std::vector<Expr*> const &parms, std::map<Ident*, Expr*> const &namedparms, SourceLocation loc);

    Decl *callee;
    std::vector<Expr*> parms;
    std::map<Ident*, Expr*> namedparms;

    Expr *base = nullptr;

    void dump(int indent) const override;
};


//---------------------- SizeofExpr -----------------------------------------
//---------------------------------------------------------------------------

class SizeofExpr : public Expr
{
  public:
    SizeofExpr(Type *type, SourceLocation loc);
    SizeofExpr(Expr *expr, SourceLocation loc);

    Type *type = nullptr;
    Expr *expr = nullptr;

    void dump(int indent) const override;
};


//---------------------- AlignofExpr ----------------------------------------
//---------------------------------------------------------------------------

class AlignofExpr : public Expr
{
  public:
    AlignofExpr(Type *type, SourceLocation loc);
    AlignofExpr(Decl *decl, SourceLocation loc);

    Type *type = nullptr;
    Decl *decl = nullptr;

    void dump(int indent) const override;
};


//---------------------- OffsetofExpr ---------------------------------------
//---------------------------------------------------------------------------

class OffsetofExpr : public Expr
{
  public:
    OffsetofExpr(Decl *decl, SourceLocation loc);

    Decl *decl;

    void dump(int indent) const override;
};


//---------------------- InstanceofExpr -------------------------------------
//---------------------------------------------------------------------------

class InstanceofExpr : public Expr
{
  public:
    InstanceofExpr(Type *type, Type *instance, SourceLocation loc);

    Type *type;
    Type *instance;

    void dump(int indent) const override;
};


//---------------------- ThrowsExpr -----------------------------------------
//---------------------------------------------------------------------------

class ThrowsExpr : public Expr
{
  public:
    ThrowsExpr(Expr *expr, SourceLocation loc);

    Expr *expr;

    void dump(int indent) const override;
};


//---------------------- TypeidExpr -----------------------------------------
//---------------------------------------------------------------------------

class TypeidExpr : public Expr
{
  public:
    TypeidExpr(Decl *decl, SourceLocation loc);

    Decl *decl;

    void dump(int indent) const override;
};

//---------------------- CastExpr -------------------------------------------
//---------------------------------------------------------------------------

class CastExpr : public Expr
{
  public:
    CastExpr(Type *type, Expr *expr, SourceLocation loc);

    Type *type;
    Expr *expr;

    void dump(int indent) const override;
};


//---------------------- NewExpr --------------------------------------------
//---------------------------------------------------------------------------

class NewExpr : public Expr
{
  public:
    NewExpr(Type *type, Expr *address, SourceLocation loc);
    NewExpr(Type *type, Expr *address, std::vector<Expr*> const &parms, std::map<Ident*, Expr*> const &namedparms, SourceLocation loc);

    Type *type;
    Expr *address;
    std::vector<Expr*> parms;
    std::map<Ident*, Expr*> namedparms;

    void dump(int indent) const override;
};


//---------------------- RequiresExpr ---------------------------------------
//---------------------------------------------------------------------------

class RequiresExpr : public Expr
{
  public:
    RequiresExpr(Decl *decl, SourceLocation loc);

    Decl *decl;

    void dump(int indent) const override;
};


//---------------------- MatchExpr ------------------------------------------
//---------------------------------------------------------------------------

class MatchExpr : public Expr
{
  public:
    MatchExpr(Decl *decl, SourceLocation loc);

    Decl *decl;

    void dump(int indent) const override;
};


//---------------------- LambdaExpr -----------------------------------------
//---------------------------------------------------------------------------

class LambdaExpr : public Expr
{
  public:
    LambdaExpr(Decl *decl, SourceLocation loc);

    Decl *decl;

    void dump(int indent) const override;
};


//---------------------- FragmentExpr ---------------------------------------
//---------------------------------------------------------------------------

class FragmentExpr : public Expr
{
  public:
    FragmentExpr(std::vector<Expr*> const &args, std::vector<Decl*> const &decls, SourceLocation loc);
    FragmentExpr(std::vector<Decl*> const &decls, SourceLocation loc);

    std::vector<Expr*> args;
    std::vector<Decl*> decls;

    void dump(int indent) const override;
};

//
// misc functions
//

bool is_literal_expr(Expr *expr);
bool is_declref_expr(Expr *expr);
DeclRefDecl *is_declrefdecl_expr(Expr *expr);
DeclScopedDecl *is_declscopeddecl_expr(Expr *expr);

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, Expr const &expr);


// checked casts

template<typename T> auto expr_cast(Expr*);
template<> inline auto expr_cast<ParenExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::Paren); return static_cast<ParenExpr*>(expr); };
template<> inline auto expr_cast<VoidLiteralExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::VoidLiteral); return static_cast<VoidLiteralExpr*>(expr); };
template<> inline auto expr_cast<BoolLiteralExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::BoolLiteral); return static_cast<BoolLiteralExpr*>(expr); };
template<> inline auto expr_cast<CharLiteralExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::CharLiteral); return static_cast<CharLiteralExpr*>(expr); };
template<> inline auto expr_cast<IntLiteralExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::IntLiteral); return static_cast<IntLiteralExpr*>(expr); };
template<> inline auto expr_cast<FloatLiteralExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::FloatLiteral); return static_cast<FloatLiteralExpr*>(expr); };
template<> inline auto expr_cast<PointerLiteralExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::PointerLiteral); return static_cast<PointerLiteralExpr*>(expr); };
template<> inline auto expr_cast<FunctionPointerExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::FunctionPointer); return static_cast<FunctionPointerExpr*>(expr); };
template<> inline auto expr_cast<StringLiteralExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::StringLiteral); return static_cast<StringLiteralExpr*>(expr); };
template<> inline auto expr_cast<ArrayLiteralExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::ArrayLiteral); return static_cast<ArrayLiteralExpr*>(expr); };
template<> inline auto expr_cast<CompoundLiteralExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::CompoundLiteral); return static_cast<CompoundLiteralExpr*>(expr); };
template<> inline auto expr_cast<ExprRefExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::ExprRef); return static_cast<ExprRefExpr*>(expr); };
template<> inline auto expr_cast<UnaryOpExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::UnaryOp); return static_cast<UnaryOpExpr*>(expr); };
template<> inline auto expr_cast<BinaryOpExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::BinaryOp); return static_cast<BinaryOpExpr*>(expr); };
template<> inline auto expr_cast<TernaryOpExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::TernaryOp); return static_cast<TernaryOpExpr*>(expr); };
template<> inline auto expr_cast<DeclRefExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::DeclRef); return static_cast<DeclRefExpr*>(expr); };
template<> inline auto expr_cast<CallExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::Call); return static_cast<CallExpr*>(expr); };
template<> inline auto expr_cast<SizeofExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::Sizeof); return static_cast<SizeofExpr*>(expr); };
template<> inline auto expr_cast<AlignofExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::Alignof); return static_cast<AlignofExpr*>(expr); };
template<> inline auto expr_cast<OffsetofExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::Offsetof); return static_cast<OffsetofExpr*>(expr); };
template<> inline auto expr_cast<InstanceofExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::Instanceof); return static_cast<InstanceofExpr*>(expr); };
template<> inline auto expr_cast<ThrowsExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::Throws); return static_cast<ThrowsExpr*>(expr); };
template<> inline auto expr_cast<TypeidExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::Typeid); return static_cast<TypeidExpr*>(expr); };
template<> inline auto expr_cast<CastExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::Cast); return static_cast<CastExpr*>(expr); };
template<> inline auto expr_cast<NewExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::New); return static_cast<NewExpr*>(expr); };
template<> inline auto expr_cast<RequiresExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::Requires); return static_cast<RequiresExpr*>(expr); };
template<> inline auto expr_cast<MatchExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::Match); return static_cast<MatchExpr*>(expr); };
template<> inline auto expr_cast<LambdaExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::Lambda); return static_cast<LambdaExpr*>(expr); };
template<> inline auto expr_cast<FragmentExpr>(Expr *expr) { assert(expr && expr->kind() == Expr::Fragment); return static_cast<FragmentExpr*>(expr); };
