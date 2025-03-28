//
// decl.h
//
// Copyright (c) 2020-2024 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "lexer.h"
#include "numeric.h"
#include "builtins.h"
#include "lifetime.h"
#include <string>
#include <string_view>
#include <vector>
#include <map>
#include <unordered_map>
#include <variant>

class Type;
class Stmt;
class Expr;
class Ident;

//---------------------- Decl -----------------------------------------------
//---------------------------------------------------------------------------

class Decl
{
  public:

    enum Kind
    {
      TranslationUnit,
      Module,
      Function,
      DeclScoped,
      DeclRef,
      TypeName,
      TypeOf,
      Import,
      Using,
      TypeAlias,
      TypeArg,
      IdentPattern,
      TuplePattern,
      VoidVar,
      StmtVar,
      ParmVar,
      Struct,
      Union,
      VTable,
      Lambda,
      ThisVar,
      FieldVar,
      ErrorVar,
      LambdaVar,
      Initialiser,
      Case,
      CaseVar,
      Concept,
      Requires,
      Enum,
      EnumConstant,
      Attribute,
      Run,
      If,
    };

  public:

    enum Flags
    {
      Public = 0x01,
      Conditional = 0x04,
    };

    long flags = 0;

  public:
    Decl(Kind kind);
    Decl(Kind kind, SourceLocation loc);

    Kind kind() const { return m_kind; }

    SourceLocation const &loc() const { return m_loc; }

    std::variant<Decl*, Stmt*> owner;

    virtual void dump(int indent) const = 0;

  protected:

    Kind m_kind;
    SourceLocation m_loc;
};


//---------------------- TranslationUnitDecl --------------------------------
//---------------------------------------------------------------------------

class TranslationUnitDecl : public Decl
{
  public:
    TranslationUnitDecl();

    Decl *builtins;
    Decl *mainmodule;

    std::vector<Decl*> decls;
    std::vector<std::string> cfgs;

    void dump(int indent) const override;
};


//---------------------- ModuleDecl -----------------------------------------
//---------------------------------------------------------------------------

class ModuleDecl : public Decl
{
  public:

    enum Flags
    {
      Public = 0x01,
      Indexed = 0x02,
    };

  public:
    ModuleDecl(Ident *name, std::string_view file);

    std::string const &file() const { return m_file; }

    Ident *name = nullptr;
    std::vector<Decl*> decls;

    std::unordered_map<Ident*, std::vector<Decl*>> index;

    void dump(int indent) const override;

  protected:

    std::string m_file;
};


//---------------------- FunctionDecl ---------------------------------------
//---------------------------------------------------------------------------

class FunctionDecl : public Decl
{
  public:

    enum Flags
    {
      Public = 0x01,
      Const = 0x02,
      Builtin = 0x08,
      Constructor = 0x10,
      Destructor = 0x20,
      Defaulted = 0x40,
      Deleted = 0x80,
      Static = 0x100,
      Override = 0x200,

      NoReturn = 0x1000,
      Inhibited = 0x2000,
      Safe = 0x4000,
      Unsafe = 0x8000,
      Lifetimed = 0x10000,
      NoInline = 0x20000,
      NoDiscard = 0x40000,
      Weak = 0x80000,

      ExternC = 0x100000,
      ExternWin64 = 0x200000,
      ExternSysv64 = 0x400000,
      ExternNaked = 0x800000,
      ExternInterrupt = 0x1000000,
      ExternMask = ExternC | ExternWin64 | ExternSysv64 | ExternNaked | ExternInterrupt,

      DeclType = 0x70000000,
      ConstDecl = 0x10000000,
      LambdaDecl = 0x20000000,
      RequiresDecl = 0x30000000,
      MatchDecl = 0x40000000,
      RunDecl = 0x50000000,
    };

  public:
    FunctionDecl(SourceLocation loc);

    Ident *name = nullptr;

    Type *returntype;
    std::vector<Decl*> args;
    std::vector<Decl*> parms;
    std::vector<Decl*> inits;
    Type *throws = nullptr;
    Stmt *body = nullptr;

    Builtin::Kind builtin;

    std::vector<Expr*> constraints;

    int retcnt = 0;
    Decl *retvar = nullptr;

    std::vector<Decl*> attributes;
    std::vector<Lifetime> lifetimes;

    void dump(int indent) const override;
};

//---------------------- DeclScopedDecl -------------------------------------
//---------------------------------------------------------------------------

class DeclScopedDecl : public Decl
{
  public:
    DeclScopedDecl(SourceLocation loc);
    DeclScopedDecl(std::vector<Decl*> const &decls, SourceLocation loc);

    std::vector<Decl*> decls;

    void dump(int indent) const override;
};


//---------------------- DeclRefDecl ----------------------------------------
//---------------------------------------------------------------------------

class DeclRefDecl : public Decl
{
  public:
    DeclRefDecl(SourceLocation loc);
    DeclRefDecl(Ident *name, SourceLocation loc);

    Ident *name = nullptr;
    std::vector<Type*> args;
    std::map<Ident*, Type*> namedargs;
    bool argless = true;

    void dump(int indent) const override;
};


//---------------------- TypeNameDecl ---------------------------------------
//---------------------------------------------------------------------------

class TypeNameDecl : public Decl
{
  public:
    TypeNameDecl(SourceLocation loc);
    TypeNameDecl(Type *type, SourceLocation loc);

    Type *type = nullptr;

    void dump(int indent) const override;
};


//---------------------- TypeOfDecl -----------------------------------------
//---------------------------------------------------------------------------

class TypeOfDecl : public Decl
{
  public:
    TypeOfDecl(SourceLocation loc);
    TypeOfDecl(Expr *expr, SourceLocation loc);

    Expr *expr = nullptr;

    void dump(int indent) const override;
};


//---------------------- ImportDecl -----------------------------------------
//---------------------------------------------------------------------------

class ImportDecl : public Decl
{
  public:

    enum Flags
    {
      Public = 0x01,
    };

  public:
    ImportDecl(SourceLocation loc);

    Decl *decl = nullptr;

    Ident *alias = nullptr;
    std::vector<Decl*> usings;

    void dump(int indent) const override;
};


//---------------------- UsingDecl ------------------------------------------
//---------------------------------------------------------------------------

class UsingDecl : public Decl
{
  public:

    enum Flags
    {
      Public = 0x01,
      Resolved = 0x02,
      Resolving = 0x08,
    };

  public:
    UsingDecl(SourceLocation loc);
    UsingDecl(Decl *decl, SourceLocation loc);

    Decl *decl = nullptr;

    void dump(int indent) const override;
};


//---------------------- TypeAliasDecl --------------------------------------
//---------------------------------------------------------------------------

class TypeAliasDecl : public Decl
{
  public:

    enum Flags
    {
      Public = 0x01,
      Builtin = 0x08,
      Implicit = 0x10,
    };

  public:
    TypeAliasDecl(SourceLocation loc);

    Ident *name = nullptr;

    Type *type = nullptr;
    std::vector<Decl*> args;

    void dump(int indent) const override;
};


//---------------------- TypeArgDecl ----------------------------------------
//---------------------------------------------------------------------------

class TypeArgDecl : public Decl
{
  public:

    enum Flags
    {
      Pack = 0x20,
      SplitFn = 0x40,
      SplitArray = 0x80,
    };

  public:
    TypeArgDecl(SourceLocation loc);
    TypeArgDecl(Ident *name, SourceLocation loc);

    Ident *name = nullptr;

    Type *defult = nullptr;

    void dump(int indent) const override;
};


//---------------------- Pattern --------------------------------------------
//---------------------------------------------------------------------------

class IdentPatternDecl : public Decl
{
  public:
    IdentPatternDecl(SourceLocation loc);
    IdentPatternDecl(Ident *name, SourceLocation loc);

    Ident *name;

    void dump(int indent) const override;
};

class TuplePatternDecl : public Decl
{
  public:
    TuplePatternDecl(SourceLocation loc);
    TuplePatternDecl(std::vector<Decl*> const &bindings, SourceLocation loc);

    std::vector<Decl*> bindings;

    void dump(int indent) const override;
};

//---------------------- VarDecl --------------------------------------------
//---------------------------------------------------------------------------

class VarDecl : public Decl
{
  public:

    enum Flags
    {
      Const = 0x02,
      Literal = 0x10,
      Static = 0x20,
      Mutable = 0x40,
      Range = 0x80,
      ThreadLocal = 0x100,
      CacheAligned = 0x200,
      PageAligned = 0x400,
      SelfImplicit = 0x1000,
    };

  public:
    VarDecl(Kind kind, SourceLocation loc);

    Ident *name = nullptr;
    Type *type = nullptr;

    Decl *pattern = nullptr;
};


//---------------------- VoidVarDecl ----------------------------------------
//---------------------------------------------------------------------------

class VoidVarDecl : public VarDecl
{
  public:
    VoidVarDecl(SourceLocation loc);

    void dump(int indent) const override;
};


//---------------------- StmtVarDecl ----------------------------------------
//---------------------------------------------------------------------------

class StmtVarDecl : public VarDecl
{
  public:
    StmtVarDecl(SourceLocation loc);

    Expr *value = nullptr;

    void dump(int indent) const override;
};


//---------------------- ParmVarDecl ----------------------------------------
//---------------------------------------------------------------------------

class ParmVarDecl : public VarDecl
{
  public:
    ParmVarDecl(SourceLocation loc);

    Expr *defult = nullptr;

    void dump(int indent) const override;
};


//---------------------- TagDecl --------------------------------------------
//---------------------------------------------------------------------------

class TagDecl : public Decl
{
  public:

    enum Flags
    {
      Public = 0x01,
      Packed = 0x100,
      PublicBase = 0x200,
    };

  public:
    TagDecl(Kind kind, SourceLocation loc);

    Ident *name = nullptr;
    std::vector<Decl*> args;
    std::vector<Decl*> decls;

    Type *basetype = nullptr;

    std::vector<Decl*> attributes;

    size_t alignment = 0;
};


//---------------------- StructDecl -----------------------------------------
//---------------------------------------------------------------------------

class StructDecl : public TagDecl
{
  public:
    StructDecl(SourceLocation loc);

    void dump(int indent) const override;
};


//---------------------- UnionDecl ------------------------------------------
//---------------------------------------------------------------------------

class UnionDecl : public TagDecl
{
  public:
    UnionDecl(SourceLocation loc);

    void dump(int indent) const override;
};


//---------------------- VTableDecl -----------------------------------------
//---------------------------------------------------------------------------

class VTableDecl : public TagDecl
{
  public:
    VTableDecl(SourceLocation loc);

    void dump(int indent) const override;
};


//---------------------- LambdaDecl -----------------------------------------
//---------------------------------------------------------------------------

class LambdaDecl : public TagDecl
{
  public:

    enum Flags
    {
      Quick = 0x2,
      Capture = 0x10,
      Captures = 0x20,
    };

  public:
    LambdaDecl(SourceLocation loc);

    Decl *fn = nullptr;
    std::vector<Decl*> captures;

    void dump(int indent) const override;
};


//---------------------- ThisVarDecl ----------------------------------------
//---------------------------------------------------------------------------

class ThisVarDecl : public VarDecl
{
  public:
    ThisVarDecl(SourceLocation loc);

    void dump(int indent) const override;
};


//---------------------- ErrorVarDecl ---------------------------------------
//---------------------------------------------------------------------------

class ErrorVarDecl : public VarDecl
{
  public:
    ErrorVarDecl(SourceLocation loc);

    void dump(int indent) const override;
};


//---------------------- FieldVarDecl ---------------------------------------
//---------------------------------------------------------------------------

class FieldVarDecl : public VarDecl
{
  public:
    FieldVarDecl(SourceLocation loc);

    Expr *defult = nullptr;

    std::vector<Decl*> attributes;

    void dump(int indent) const override;
};


//---------------------- LambdaVarDecl --------------------------------------
//---------------------------------------------------------------------------

class LambdaVarDecl : public VarDecl
{
  public:
    LambdaVarDecl(SourceLocation loc);

    Decl *arg = nullptr;
    Expr *value = nullptr;

    void dump(int indent) const override;
};


//---------------------- InitialiserDecl ------------------------------------
//---------------------------------------------------------------------------

class InitialiserDecl : public Decl
{
  public:

    enum Flags
    {
      VoidInit = 0x08,
    };

  public:
    InitialiserDecl(SourceLocation loc);

    Ident *name = nullptr;
    std::vector<Expr*> parms;

    void dump(int indent) const override;
};


//---------------------- CaseDecl -------------------------------------------
//---------------------------------------------------------------------------

class CaseDecl : public Decl
{
  public:
    CaseDecl(SourceLocation loc);

    Expr *label = nullptr;
    Decl *parm = nullptr;
    Stmt *body = nullptr;

    void dump(int indent) const override;
};


//---------------------- CaseVarDecl ----------------------------------------
//---------------------------------------------------------------------------

class CaseVarDecl : public VarDecl
{
  public:
    CaseVarDecl(SourceLocation loc);

    Expr *value = nullptr;

    void dump(int indent) const override;
};


//---------------------- ConceptDecl ----------------------------------------
//---------------------------------------------------------------------------

class ConceptDecl : public TagDecl
{
  public:
    ConceptDecl(SourceLocation loc);

    void dump(int indent) const override;
};


//---------------------- RequiresDecl ---------------------------------------
//---------------------------------------------------------------------------

class RequiresDecl : public Decl
{
  public:

    enum Flags
    {
      Condition = 0x1000000,
      Expression = 0x2000000,
      Match = 0x4000000,
    };

  public:
    RequiresDecl(SourceLocation loc);

    Decl *fn = nullptr;
    Type *requirestype = nullptr;

    void dump(int indent) const override;
};


//---------------------- EnumDecl -------------------------------------------
//---------------------------------------------------------------------------

class EnumDecl : public TagDecl
{
  public:
    EnumDecl(SourceLocation loc);

    void dump(int indent) const override;
};


//---------------------- EnumConstantDecl -----------------------------------
//---------------------------------------------------------------------------

class EnumConstantDecl : public Decl
{
  public:
    EnumConstantDecl(SourceLocation loc);
    EnumConstantDecl(Ident *name, SourceLocation loc);

    Ident *name = nullptr;
    Expr *value = nullptr;

    void dump(int indent) const override;
};


//---------------------- AttributeDecl --------------------------------------
//---------------------------------------------------------------------------

class AttributeDecl : public Decl
{
  public:
    AttributeDecl(SourceLocation loc);

    std::string name;
    std::string options;

    void dump(int indent) const override;
};


//---------------------- RunDecl --------------------------------------------
//---------------------------------------------------------------------------

class RunDecl : public Decl
{
  public:
    RunDecl(SourceLocation loc);

    Decl *fn = nullptr;

    void dump(int indent) const override;
};


//---------------------- IfDecl ---------------------------------------------
//---------------------------------------------------------------------------

class IfDecl : public Decl
{
  public:

    enum Flags
    {
      ResolvedTrue = 0x10,
      ResolvedFalse = 0x20,
    };

  public:
    IfDecl(SourceLocation loc);

    Expr *cond = nullptr;
    std::vector<Decl*> decls;
    Decl *elseif = nullptr;

    Decl *root = nullptr;

    void dump(int indent) const override;
};

//
// misc functions
//

Ident *decl_name(Decl *decl);

bool is_fn_decl(Decl const *decl);
bool is_var_decl(Decl const *decl);
bool is_tag_decl(Decl const *decl);
bool is_module_decl(Decl const *decl);

std::ostream &operator <<(std::ostream &os, Decl const &decl);

// checked casts

template<typename T> auto decl_cast(Decl *);
template<> inline auto decl_cast<TranslationUnitDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::TranslationUnit); return static_cast<TranslationUnitDecl*>(decl); };
template<> inline auto decl_cast<ModuleDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Module); return static_cast<ModuleDecl*>(decl); };
template<> inline auto decl_cast<FunctionDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Function); return static_cast<FunctionDecl*>(decl); };
template<> inline auto decl_cast<DeclScopedDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::DeclScoped); return static_cast<DeclScopedDecl*>(decl); };
template<> inline auto decl_cast<DeclRefDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::DeclRef); return static_cast<DeclRefDecl*>(decl); };
template<> inline auto decl_cast<TypeNameDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::TypeName); return static_cast<TypeNameDecl*>(decl); };
template<> inline auto decl_cast<TypeOfDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::TypeOf); return static_cast<TypeOfDecl*>(decl); };
template<> inline auto decl_cast<ImportDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Import); return static_cast<ImportDecl*>(decl); };
template<> inline auto decl_cast<UsingDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Using); return static_cast<UsingDecl*>(decl); };
template<> inline auto decl_cast<TypeAliasDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::TypeAlias); return static_cast<TypeAliasDecl*>(decl); };
template<> inline auto decl_cast<TypeArgDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::TypeArg); return static_cast<TypeArgDecl*>(decl); };
template<> inline auto decl_cast<IdentPatternDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::IdentPattern); return static_cast<IdentPatternDecl*>(decl); };
template<> inline auto decl_cast<TuplePatternDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::TuplePattern); return static_cast<TuplePatternDecl*>(decl); };
template<> inline auto decl_cast<VoidVarDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::VoidVar); return static_cast<VoidVarDecl*>(decl); };
template<> inline auto decl_cast<StmtVarDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::StmtVar); return static_cast<StmtVarDecl*>(decl); };
template<> inline auto decl_cast<ParmVarDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::ParmVar); return static_cast<ParmVarDecl*>(decl); };
template<> inline auto decl_cast<StructDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Struct); return static_cast<StructDecl*>(decl); };
template<> inline auto decl_cast<VTableDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::VTable); return static_cast<VTableDecl*>(decl); };
template<> inline auto decl_cast<LambdaDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Lambda); return static_cast<LambdaDecl*>(decl); };
template<> inline auto decl_cast<ThisVarDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::ThisVar); return static_cast<ThisVarDecl*>(decl); };
template<> inline auto decl_cast<FieldVarDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::FieldVar); return static_cast<FieldVarDecl*>(decl); };
template<> inline auto decl_cast<ErrorVarDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::ErrorVar); return static_cast<ErrorVarDecl*>(decl); };
template<> inline auto decl_cast<LambdaVarDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::LambdaVar); return static_cast<LambdaVarDecl*>(decl); };
template<> inline auto decl_cast<InitialiserDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Initialiser); return static_cast<InitialiserDecl*>(decl); };
template<> inline auto decl_cast<CaseDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Case); return static_cast<CaseDecl*>(decl); };
template<> inline auto decl_cast<CaseVarDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::CaseVar); return static_cast<CaseVarDecl*>(decl); };
template<> inline auto decl_cast<ConceptDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Concept); return static_cast<ConceptDecl*>(decl); };
template<> inline auto decl_cast<RequiresDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Requires); return static_cast<RequiresDecl*>(decl); };
template<> inline auto decl_cast<EnumDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Enum); return static_cast<EnumDecl*>(decl); };
template<> inline auto decl_cast<EnumConstantDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::EnumConstant); return static_cast<EnumConstantDecl*>(decl); };
template<> inline auto decl_cast<UnionDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Union); return static_cast<UnionDecl*>(decl); };
template<> inline auto decl_cast<AttributeDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Attribute); return static_cast<AttributeDecl*>(decl); };
template<> inline auto decl_cast<IfDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::If); return static_cast<IfDecl*>(decl); };
template<> inline auto decl_cast<RunDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Run); return static_cast<RunDecl*>(decl); };

template<> inline auto decl_cast<VarDecl>(Decl *decl) { assert(decl && is_var_decl(decl)); return static_cast<VarDecl*>(decl); };
template<> inline auto decl_cast<TagDecl>(Decl *decl) { assert(decl && is_tag_decl(decl)); return static_cast<TagDecl*>(decl); };
