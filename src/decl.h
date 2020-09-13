//
// decl.h
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "lexer.h"
#include "numeric.h"
#include "builtins.h"
#include <string>
#include <string_view>
#include <vector>
#include <map>
#include <variant>

class Type;
class Stmt;
class Expr;

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
      TypeOf,
      Import,
      Using,
      TypeAlias,
      TypeArg,
      VoidVar,
      StmtVar,
      ParmVar,
      Struct,
      Lambda,
      ThisVar,
      FieldVar,
      RangeVar,
      ErrorVar,
      Initialiser,
      Concept,
      Enum,
      EnumConstant,
      If,
    };

    using Owner = std::variant<Decl*, Stmt*>;

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
    };

  public:
    ModuleDecl(std::string_view name, std::string_view file);

    std::string const &file() const { return m_file; }

    std::string name;

    std::vector<Decl*> decls;

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

      ExternC = 0x1000,
      ExternMask = ExternC,

      DeclType = 0x70000000,
      ConstDecl = 0x20000000,
      LambdaDecl = 0x30000000,
      RequiresDecl = 0x40000000,
    };

  public:
    FunctionDecl(SourceLocation loc);

    std::string name;

    Type *returntype;
    std::vector<Decl*> args;
    std::vector<Decl*> parms;
    std::vector<Decl*> inits;
    Stmt *body = nullptr;

    Builtin::Kind builtin;

    Expr *throws = nullptr;
    Expr *where = nullptr;

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
    DeclRefDecl(std::string_view name, SourceLocation loc);

    std::string name;
    std::vector<Type*> args;
    std::map<std::string, Type*> namedargs;

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

    std::string alias;
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
      Implicit = 0x02,
    };

  public:
    TypeAliasDecl(SourceLocation loc);

    std::string name;

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
    };

  public:
    TypeArgDecl(SourceLocation loc);
    TypeArgDecl(std::string_view name, SourceLocation loc);

    std::string name;

    Type *defult = nullptr;

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
    };

  public:
    VarDecl(Kind kind, SourceLocation loc);

    std::string name;
    Type *type = nullptr;
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
    TagDecl(Kind kind, SourceLocation loc);

    std::string name;
    std::vector<Decl*> args;
    std::vector<Decl*> decls;
};


//---------------------- StructDecl -----------------------------------------
//---------------------------------------------------------------------------

class StructDecl : public TagDecl
{
  public:

    enum Flags
    {
      Public = 0x01,
    };

  public:
    StructDecl(SourceLocation loc);

    Type *basetype = nullptr;

    void dump(int indent) const override;
};


//---------------------- LambdaDecl -----------------------------------------
//---------------------------------------------------------------------------

class LambdaDecl : public TagDecl
{
  public:

    enum Flags
    {
      Public = 0x01,
      Captures = 0x10,
    };

  public:
    LambdaDecl(SourceLocation loc);

    FunctionDecl *fn = nullptr;
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

    void dump(int indent) const override;
};


//---------------------- RangeVarDecl ---------------------------------------
//---------------------------------------------------------------------------

class RangeVarDecl : public VarDecl
{
  public:
    RangeVarDecl(SourceLocation loc);

    Expr *range = nullptr;

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

    Decl *decl = nullptr;

    std::vector<Expr*> parms;
    std::map<std::string, Expr*> namedparms;

    void dump(int indent) const override;
};


//---------------------- ConceptDecl ----------------------------------------
//---------------------------------------------------------------------------

class ConceptDecl : public TagDecl
{
  public:

    enum Flags
    {
      Public = 0x01,
    };

  public:
    ConceptDecl(SourceLocation loc);

    void dump(int indent) const override;
};


//---------------------- RequiresDecl ---------------------------------------
//---------------------------------------------------------------------------

class RequiresDecl : public FunctionDecl
{
  public:

    enum Flags
    {
      Condition = 0x1000000,
      Expression = 0x2000000,
    };

  public:
    RequiresDecl(SourceLocation loc);

    void dump(int indent) const override;
};


//---------------------- EnumDecl -------------------------------------------
//---------------------------------------------------------------------------

class EnumDecl : public TagDecl
{
  public:

    enum Flags
    {
      Public = 0x01,
    };

  public:
    EnumDecl(SourceLocation loc);

    Type *basetype = nullptr;

    void dump(int indent) const override;
};


//---------------------- EnumConstantDecl -----------------------------------
//---------------------------------------------------------------------------

class EnumConstantDecl : public Decl
{
  public:
    EnumConstantDecl(SourceLocation loc);

    std::string name;

    Expr *value = nullptr;

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

    void dump(int indent) const override;
};

//
// misc functions
//

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
template<> inline auto decl_cast<TypeOfDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::TypeOf); return static_cast<TypeOfDecl*>(decl); };
template<> inline auto decl_cast<ImportDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Import); return static_cast<ImportDecl*>(decl); };
template<> inline auto decl_cast<UsingDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Using); return static_cast<UsingDecl*>(decl); };
template<> inline auto decl_cast<TypeAliasDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::TypeAlias); return static_cast<TypeAliasDecl*>(decl); };
template<> inline auto decl_cast<TypeArgDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::TypeArg); return static_cast<TypeArgDecl*>(decl); };
template<> inline auto decl_cast<VoidVarDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::VoidVar); return static_cast<VoidVarDecl*>(decl); };
template<> inline auto decl_cast<StmtVarDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::StmtVar); return static_cast<StmtVarDecl*>(decl); };
template<> inline auto decl_cast<ParmVarDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::ParmVar); return static_cast<ParmVarDecl*>(decl); };
template<> inline auto decl_cast<StructDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Struct); return static_cast<StructDecl*>(decl); };
template<> inline auto decl_cast<LambdaDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Lambda); return static_cast<LambdaDecl*>(decl); };
template<> inline auto decl_cast<ThisVarDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::ThisVar); return static_cast<ThisVarDecl*>(decl); };
template<> inline auto decl_cast<FieldVarDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::FieldVar); return static_cast<FieldVarDecl*>(decl); };
template<> inline auto decl_cast<RangeVarDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::RangeVar); return static_cast<RangeVarDecl*>(decl); };
template<> inline auto decl_cast<ErrorVarDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::ErrorVar); return static_cast<ErrorVarDecl*>(decl); };
template<> inline auto decl_cast<InitialiserDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Initialiser); return static_cast<InitialiserDecl*>(decl); };
template<> inline auto decl_cast<ConceptDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Concept); return static_cast<ConceptDecl*>(decl); };
template<> inline auto decl_cast<EnumDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::Enum); return static_cast<EnumDecl*>(decl); };
template<> inline auto decl_cast<EnumConstantDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::EnumConstant); return static_cast<EnumConstantDecl*>(decl); };
template<> inline auto decl_cast<IfDecl>(Decl *decl) { assert(decl && decl->kind() == Decl::If); return static_cast<IfDecl*>(decl); };

template<> inline auto decl_cast<VarDecl>(Decl *decl) { assert(decl && is_var_decl(decl)); return static_cast<VarDecl*>(decl); };
template<> inline auto decl_cast<TagDecl>(Decl *decl) { assert(decl && is_tag_decl(decl)); return static_cast<TagDecl*>(decl); };
