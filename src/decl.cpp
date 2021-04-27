//
// decl.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "ast.h"
#include <iostream>
#include <algorithm>
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

//|///////////////////// is_fn_decl /////////////////////////////////////////
bool is_fn_decl(Decl const *decl)
{
  return decl->kind() == Decl::Function;
}

//|///////////////////// is_var_decl ////////////////////////////////////////
bool is_var_decl(Decl const *decl)
{
  return decl->kind() == Decl::VoidVar || decl->kind() == Decl::StmtVar || decl->kind() == Decl::ParmVar || decl->kind() == Decl::FieldVar || decl->kind() == Decl::RangeVar || decl->kind() == Decl::ThisVar || decl->kind() == Decl::ErrorVar || decl->kind() == Decl::LambdaVar || decl->kind() == Decl::CaseVar;
}

//|///////////////////// is_tag_decl ////////////////////////////////////////
bool is_tag_decl(Decl const *decl)
{
  return decl->kind() == Decl::Struct || decl->kind() == Decl::Concept || decl->kind() == Decl::Lambda || decl->kind() == Decl::Enum || decl->kind() == Decl::Union;
}

//|///////////////////// is_module_decl /////////////////////////////////////
bool is_module_decl(Decl const *decl)
{
  return decl->kind() == Decl::Module;
}

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, Decl const &decl)
{
  switch (decl.kind())
  {
    case Decl::TranslationUnit:
      os << "::";
      break;

    case Decl::Module:
      if (auto &module = static_cast<ModuleDecl const &>(decl); true)
      {
        os << module.name;
      }
      break;

    case Decl::Import:
      if (auto &imprt = static_cast<ImportDecl const &>(decl); true)
      {
        os << imprt.alias;
      }
      break;

    case Decl::Using:
      if (auto &usein = static_cast<UsingDecl const &>(decl); usein.decl)
      {
        os << *usein.decl;
      }
      break;

    case Decl::TypeOf:
      os << "typeof";
      break;

    case Decl::DeclScoped:
      if (auto &declscoped = static_cast<DeclScopedDecl const &>(decl); true)
      {
        for(auto &scoped : declscoped.decls)
          os << *scoped << (&scoped != &declscoped.decls.back() ? "::" : "");
      }
      break;

    case Decl::DeclRef:
      if (auto &ref = static_cast<DeclRefDecl const &>(decl); true)
      {
        os << '"';

        os << ref.name;

        if (ref.args.size() != 0 || ref.namedargs.size() != 0)
        {
          os << '<';

          for(auto &arg : ref.args)
            os << *arg << (&arg != &ref.args.back() ? ", " : "");

          int i = 0;
          for(auto &[name, arg] : ref.namedargs)
            os << (!i++ ? "" : ", ") << name << ": " << *arg;

          os << '>';
        }

        os << '"';
      }
      break;

    case Decl::Function:
      if (auto &fn = static_cast<FunctionDecl const &>(decl); true)
      {
        os << fn.name;

        if (fn.args.size() != 0)
        {
          os << '<';

          for(auto &arg : fn.args)
            os << *arg << (&arg != &fn.args.back() ? ", " : "");

          os << '>';
        }

        os << '(';

        if (auto parms = fn.parms; parms.size() != 0)
        {
          for(auto &parm : parms)
            os << *parm << (&parm != &parms.back() ? ", " : "");
        }

        os << ')';

        if (auto returntype = fn.returntype)
          os << " -> " << *returntype;
      }
      break;

    case Decl::TypeAlias:
      if (auto &alias = static_cast<TypeAliasDecl const &>(decl); true)
      {
        os << alias.name;

        if (alias.args.size() != 0)
        {
          os << '<';

          for(auto &arg : alias.args)
            os << *arg << (&arg != &alias.args.back() ? ", " : "");

          os << '>';
        }
      }
      break;

    case Decl::Struct:
    case Decl::Union:
    case Decl::Lambda:
    case Decl::Concept:
    case Decl::Enum:
      if (auto &tag = static_cast<TagDecl const &>(decl); true)
      {
        os << tag.name;

        if (tag.args.size() != 0)
        {
          os << '<';

          for(auto &arg : tag.args)
            os << *arg << (&arg != &tag.args.back() ? ", " : "");

          os << '>';
        }
      }
      break;

    case Decl::TypeArg:
      if (auto &arg = static_cast<TypeArgDecl const &>(decl); true)
      {
        if (arg.flags & TypeArgDecl::Pack)
          os << "...";

        os << arg.name;
      }
      break;

    case Decl::VoidVar:
      if (auto &var = static_cast<VoidVarDecl const &>(decl); var.type)
      {
        os << *var.type << ' ' << var.name;
      }
      break;

    case Decl::StmtVar:
      if (auto &var = static_cast<StmtVarDecl const &>(decl); true)
      {
        os << var.name;
      }
      break;

    case Decl::ParmVar:
      if (auto &var = static_cast<ParmVarDecl const &>(decl); var.type)
      {
        os << *var.type;

        if (!var.name.empty())
          os << ' ' << var.name;
      }
      break;

    case Decl::ThisVar:
      if (auto &var = static_cast<ThisVarDecl const &>(decl); var.type)
      {
        os << *var.type << ' ' << var.name;
      }
      break;

    case Decl::FieldVar:
      if (auto &var = static_cast<FieldVarDecl const &>(decl); var.type)
      {
        os << *var.type << ' ' << var.name;
      }
      break;

    case Decl::RangeVar:
      if (auto &var = static_cast<RangeVarDecl const &>(decl); true)
      {
        os << var.name;
      }
      break;

    case Decl::ErrorVar:
      if (auto &var = static_cast<ErrorVarDecl const &>(decl); var.type)
      {
        os << *var.type << ' ' << var.name;
      }
      break;

    case Decl::LambdaVar:
      if (auto &var = static_cast<LambdaVarDecl const &>(decl); var.type)
      {
        os << *var.type;

        if (!var.name.empty())
          os << ' ' << var.name;
      }
      break;

    case Decl::Initialiser:
      if (auto &init = static_cast<InitialiserDecl const &>(decl); init.decl)
      {
        os << *init.decl;
      }
      break;

    case Decl::Case:
      if (auto &casse = static_cast<CaseDecl const &>(decl); casse.label)
      {
        os << *casse.label;
      }
      break;

    case Decl::CaseVar:
      if (auto &var = static_cast<CaseVarDecl const &>(decl); true)
      {
        os << var.name;
      }
      break;

    case Decl::Requires:
      if (auto &reqires = static_cast<RequiresDecl const &>(decl); true)
      {
        os << reqires.fn;
      }
      break;

    case Decl::EnumConstant:
      if (auto &var = static_cast<EnumConstantDecl const &>(decl); true)
      {
        os << var.name;
      }
      break;

    case Decl::Attribute:
      if (auto &attribute = static_cast<AttributeDecl const &>(decl); true)
      {
        os << attribute.name;
      }
      break;

    case Decl::Run:
      os << "#run";
      break;

    case Decl::If:
      os << "#if";
      break;
  }

  return os;
}

//|--------------------- Decl -----------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// Decl::Constructor //////////////////////////////////
Decl::Decl(Kind kind, SourceLocation loc)
  : m_kind(kind),
    m_loc(loc)
{
}

Decl::Decl(Kind kind)
  : m_kind(kind)
{
}


//|--------------------- TranslationUnitDecl --------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// TranslationUnitDecl::Constructor ///////////////////
TranslationUnitDecl::TranslationUnitDecl()
  : Decl(TranslationUnit)
{
}

//|///////////////////// TranslationUnitDecl::dump //////////////////////////
void TranslationUnitDecl::dump(int indent) const
{
  cout << spaces(indent) << "TranslationUnitDecl " << this << '\n';

  for(auto &decl : decls)
  {
    decl->dump(indent + 2);
  }
}


//|--------------------- ModuleDecl -----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ModuleDecl::Constructor ////////////////////////////
ModuleDecl::ModuleDecl(string_view name, string_view file)
  : Decl(Module),
    name(name),
    m_file(file)
{
}

//|///////////////////// ModuleDecl::dump ///////////////////////////////////
void ModuleDecl::dump(int indent) const
{
  cout << spaces(indent) << "ModuleDecl " << this << " <" << m_file << "> '" << *this << "'\n";

  for(auto &decl : decls)
  {
    decl->dump(indent + 2);
  }
}


//|--------------------- FunctionDecl ---------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// FunctionDecl::Constructor //////////////////////////
FunctionDecl::FunctionDecl(SourceLocation loc)
  : Decl(Function, loc),
    returntype(nullptr)
{
}

//|///////////////////// FunctionDecl::dump /////////////////////////////////
void FunctionDecl::dump(int indent) const
{
  cout << spaces(indent) << "FunctionDecl " << this << " <" << m_loc << "> '" << *this << "'\n";

  for(auto &arg : args)
  {
    arg->dump(indent + 2);
  }

  for(auto &parm : parms)
  {
    parm->dump(indent + 2);
  }

  for(auto &init: inits)
  {
    init->dump(indent + 2);
  }

  if (body)
  {
    body->dump(indent + 2);
  }
}


//|--------------------- DeclScopedDecl -------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// DeclScopedDecl::Constructor ////////////////////////
DeclScopedDecl::DeclScopedDecl(SourceLocation loc)
  : Decl(DeclScoped, loc)
{
}

DeclScopedDecl::DeclScopedDecl(vector<Decl*> const &decls, SourceLocation loc)
  : Decl(DeclScoped, loc),
    decls(decls)
{
}

//|///////////////////// DeclScopedDecl::dump ///////////////////////////////
void DeclScopedDecl::dump(int indent) const
{
  cout << spaces(indent) << "DeclScopedDecl " << this << " <" << m_loc << "> '" << *this << "'\n";
}


//|--------------------- DeclRefDecl ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// DeclRefDecl::Constructor ///////////////////////////
DeclRefDecl::DeclRefDecl(string_view name, SourceLocation loc)
  : Decl(DeclRef, loc),
    name(name)
{
}

//|///////////////////// DeclRefDecl::dump //////////////////////////////////
void DeclRefDecl::dump(int indent) const
{
  cout << spaces(indent) << "DeclRefDecl " << this << " <" << m_loc << "> '" << *this << "'\n";
}


//|--------------------- TypeOfDecl -----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// TypeOfDecl::Constructor ////////////////////////////
TypeOfDecl::TypeOfDecl(SourceLocation loc)
  : Decl(TypeOf, loc)
{
}

TypeOfDecl::TypeOfDecl(Expr *expr, SourceLocation loc)
  : Decl(TypeOf, loc),
    expr(expr)
{
}

//|///////////////////// TypeOfDecl::dump ///////////////////////////////////
void TypeOfDecl::dump(int indent) const
{
  cout << spaces(indent) << "TypeOfDecl " << this << " <" << m_loc << "> '" << *this << "'\n";

  if (expr)
  {
    expr->dump(indent + 2);
  }
}


//|--------------------- ImportDecl -----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ImportDecl::Constructor ////////////////////////////
ImportDecl::ImportDecl(SourceLocation loc)
  : Decl(Import, loc)
{
}

//|///////////////////// ImportDecl::dump ///////////////////////////////////
void ImportDecl::dump(int indent) const
{
  cout << spaces(indent) << "ImportDecl " << this << " <" << m_loc << "> '" << *this << "'\n";
}


//|--------------------- UsingDecl ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// UsingDecl::Constructor /////////////////////////////
UsingDecl::UsingDecl(SourceLocation loc)
  : Decl(Using, loc)
{
}

UsingDecl::UsingDecl(Decl *decl, SourceLocation loc)
  : Decl(Using, loc),
    decl(decl)
{
}

//|///////////////////// UsingDecl::dump ////////////////////////////////////
void UsingDecl::dump(int indent) const
{
  cout << spaces(indent) << "UsingDecl " << this << " <" << m_loc << "> '" << *this << "'\n";
}


//|--------------------- TypeAliasDecl --------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// TypeAliasDecl::Constructor /////////////////////////
TypeAliasDecl::TypeAliasDecl(SourceLocation loc)
  : Decl(TypeAlias, loc)
{
}

//|///////////////////// TypeAliasDecl::dump ////////////////////////////////
void TypeAliasDecl::dump(int indent) const
{
  cout << spaces(indent) << "TypeAlias " << this << " <" << m_loc << "> '" << *this << "'\n";
}


//|--------------------- TagDecl --------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// TagDecl::Constructor ///////////////////////////////
TagDecl::TagDecl(Kind kind, SourceLocation loc)
  : Decl(kind, loc)
{
}


//|--------------------- TypeArgDecl ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// TypeArgDecl::Constructor ///////////////////////////
TypeArgDecl::TypeArgDecl(string_view name, SourceLocation loc)
  : Decl(TypeArg, loc),
    name(name)
{
}

TypeArgDecl::TypeArgDecl(SourceLocation loc)
  : Decl(TypeArg, loc)
{
}

//|///////////////////// TypeArgDecl::dump //////////////////////////////////
void TypeArgDecl::dump(int indent) const
{
  cout << spaces(indent) << "TypeArgDecl " << this << " <" << m_loc << "> '" << *this << "'\n";

  if (defult)
  {
    defult->dump(indent + 2);
  }
}


//|--------------------- VarDecl --------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// VarDecl::Constructor ///////////////////////////////
VarDecl::VarDecl(Kind kind, SourceLocation loc)
  : Decl(kind, loc)
{
}


//|--------------------- VoidVarDecl ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// VoidVarDecl::Constructor ///////////////////////////
VoidVarDecl::VoidVarDecl(SourceLocation loc)
  : VarDecl(VoidVar, loc)
{
}

//|///////////////////// VoidVarDecl::dump //////////////////////////////////
void VoidVarDecl::dump(int indent) const
{
  cout << spaces(indent) << "VoidVarDecl " << this << " <" << m_loc << "> '" << name << "'\n";

  if (type)
  {
    type->dump(indent + 2);
  }
}


//|--------------------- StmtVarDecl ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// StmtVarDecl::Constructor ///////////////////////////
StmtVarDecl::StmtVarDecl(SourceLocation loc)
  : VarDecl(StmtVar, loc)
{
}

//|///////////////////// StmtVarDecl::dump //////////////////////////////////
void StmtVarDecl::dump(int indent) const
{
  cout << spaces(indent) << "StmtVarDecl " << this << " <" << m_loc << "> '" << name << "'\n";

  if (type)
  {
    type->dump(indent + 2);
  }

  if (value)
  {
    value->dump(indent + 2);
  }
}


//|--------------------- ParmVarDecl ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ParmVarDecl::Constructor ///////////////////////////
ParmVarDecl::ParmVarDecl(SourceLocation loc)
  : VarDecl(ParmVar, loc)
{
}

//|///////////////////// ParmVarDecl::dump //////////////////////////////////
void ParmVarDecl::dump(int indent) const
{
  cout << spaces(indent) << "ParmVarDecl " << this << " <" << m_loc << "> '" << name << "'\n";

  if (type)
  {
    type->dump(indent + 2);
  }

  if (defult)
  {
    defult->dump(indent + 2);
  }
}


//|--------------------- StructDecl -----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// StructDecl::Constructor ////////////////////////////
StructDecl::StructDecl(SourceLocation loc)
  : TagDecl(Struct, loc)
{
}

//|///////////////////// StructDecl::dump ///////////////////////////////////
void StructDecl::dump(int indent) const
{
  cout << spaces(indent) << "StructDecl " << this << " <" << m_loc << "> '" << *this << "'\n";

  if (basetype)
  {
    basetype->dump(indent + 2);
  }

  for(auto &decl : decls)
  {
    decl->dump(indent + 2);
  }
}


//|--------------------- UnionDecl ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// UnionDecl::Constructor /////////////////////////////
UnionDecl::UnionDecl(SourceLocation loc)
  : TagDecl(Union, loc)
{
}

//|///////////////////// UnionDecl::dump ////////////////////////////////////
void UnionDecl::dump(int indent) const
{
  cout << spaces(indent) << "UnionDecl " << this << " <" << m_loc << "> '" << *this << "'\n";

  for(auto &decl : decls)
  {
    decl->dump(indent + 2);
  }
}


//|--------------------- LambdaDecl -----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// LambdaDecl::Constructor ////////////////////////////
LambdaDecl::LambdaDecl(SourceLocation loc)
  : TagDecl(Lambda, loc)
{
  name = "#lambda";
}

//|///////////////////// LambdaDecl::dump ///////////////////////////////////
void LambdaDecl::dump(int indent) const
{
  cout << spaces(indent) << "LambdaDecl " << this << " <" << m_loc << "> '" << *this << "'\n";

  for(auto &capture : captures)
  {
    capture->dump(indent + 2);
  }

  for(auto &decl : decls)
  {
    decl->dump(indent + 2);
  }
}


//|--------------------- ThisVarDecl ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ThisVarDecl::Constructor ///////////////////////////
ThisVarDecl::ThisVarDecl(SourceLocation loc)
  : VarDecl(ThisVar, loc)
{
}

//|///////////////////// ThisVarDecl::dump //////////////////////////////////
void ThisVarDecl::dump(int indent) const
{
  cout << spaces(indent) << "ThisVarDecl " << this << " <" << m_loc << "> '" << name << "'\n";

  if (type)
  {
    type->dump(indent + 2);
  }
}


//|--------------------- ErrorVarDecl ---------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ErrorVarDecl::Constructor //////////////////////////
ErrorVarDecl::ErrorVarDecl(SourceLocation loc)
  : VarDecl(ErrorVar, loc)
{
}

//|///////////////////// ErrorVarDecl::dump /////////////////////////////////
void ErrorVarDecl::dump(int indent) const
{
  cout << spaces(indent) << "ErrorVarDecl " << this << " <" << m_loc << "> '" << name << "'\n";

  if (type)
  {
    type->dump(indent + 2);
  }
}


//|--------------------- FieldVarDecl ---------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// FieldVarDecl::Constructor //////////////////////////
FieldVarDecl::FieldVarDecl(SourceLocation loc)
  : VarDecl(FieldVar, loc)
{
}

//|///////////////////// FieldVarDecl::dump /////////////////////////////////
void FieldVarDecl::dump(int indent) const
{
  cout << spaces(indent) << "FieldVarDecl " << this << " <" << m_loc << "> '" << name << "'\n";

  if (type)
  {
    type->dump(indent + 2);
  }
}


//|--------------------- RangeVarDecl ---------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// RangeVarDecl::Constructor //////////////////////////
RangeVarDecl::RangeVarDecl(SourceLocation loc)
  : VarDecl(RangeVar, loc)
{
}

//|///////////////////// RangeVarDecl::dump /////////////////////////////////
void RangeVarDecl::dump(int indent) const
{
  cout << spaces(indent) << "RangeVarDecl " << this << " <" << m_loc << "> '" << name << "'\n";

  if (type)
  {
    type->dump(indent + 2);
  }

  if (range)
  {
    range->dump(indent + 2);
  }
}


//|--------------------- LambdaVarDecl --------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// LambdaVarDecl::Constructor /////////////////////////
LambdaVarDecl::LambdaVarDecl(SourceLocation loc)
  : VarDecl(LambdaVar, loc)
{
}

//|///////////////////// LambdaVarDecl::dump ////////////////////////////////
void LambdaVarDecl::dump(int indent) const
{
  cout << spaces(indent) << "LambdaVarDecl " << this << " <" << m_loc << "> '" << name << "'\n";

  if (type)
  {
    type->dump(indent + 2);
  }

  if (value)
  {
    value->dump(indent + 2);
  }
}


//|--------------------- InitialiserDecl ------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// InitialiserDecl::Constructor ///////////////////////
InitialiserDecl::InitialiserDecl(SourceLocation loc)
  : Decl(Initialiser, loc)
{
}

//|///////////////////// InitialiserDecl::dump //////////////////////////////
void InitialiserDecl::dump(int indent) const
{
  cout << spaces(indent) << "InitialiserDecl " << this << " <" << m_loc << "> '" << *this << "'\n";

  for(auto &parm : parms)
  {
    parm->dump(indent + 2);
  }

  for(auto &[name, parm] : namedparms)
  {
    parm->dump(indent + 2);
  }
}


//|--------------------- CaseDecl -------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// CaseDecl::Constructor //////////////////////////////
CaseDecl::CaseDecl(SourceLocation loc)
  : Decl(Case, loc)
{
}

//|///////////////////// CaseDecl::dump /////////////////////////////////////
void CaseDecl::dump(int indent) const
{
  cout << spaces(indent) << "CaseDecl " << this << " <" << m_loc << "> '" << *this << "'\n";

  if (label)
  {
    label->dump(indent + 2);
  }

  if (parm)
  {
    parm->dump(indent + 2);
  }

  if (body)
  {
    body->dump(indent + 2);
  }
}


//|--------------------- CaseVarDecl ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// CaseVarDecl::Constructor ///////////////////////////
CaseVarDecl::CaseVarDecl(SourceLocation loc)
  : VarDecl(CaseVar, loc)
{
}

//|///////////////////// CaseVarDecl::dump //////////////////////////////////
void CaseVarDecl::dump(int indent) const
{
  cout << spaces(indent) << "CaseVarDecl " << this << " <" << m_loc << "> '" << name << "'\n";

  if (type)
  {
    type->dump(indent + 2);
  }
}

//|--------------------- ConceptDecl ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// ConceptDecl::Constructor ///////////////////////////
ConceptDecl::ConceptDecl(SourceLocation loc)
  : TagDecl(Concept, loc)
{
}

//|///////////////////// ConceptDecl::dump /////////////////////////////////
void ConceptDecl::dump(int indent) const
{
  cout << spaces(indent) << "ConceptDecl " << this << " <" << m_loc << "> '" << *this << "'\n";

  for(auto &decl : decls)
  {
    decl->dump(indent + 2);
  }
}


//|--------------------- RequiresDecl ---------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// RequiresDecl::Constructor //////////////////////////
RequiresDecl::RequiresDecl(SourceLocation loc)
  : Decl(Requires, loc)
{

}

//|///////////////////// RequiresDecl::dump /////////////////////////////////
void RequiresDecl::dump(int indent) const
{
  cout << spaces(indent) << "RequiresDecl " << this << " <" << m_loc << "> '" << *this << "'\n";

  if (fn)
  {
    fn->dump(indent + 2);
  }

  if (requirestype)
  {
    requirestype->dump(indent + 2);
  }
}


//|--------------------- EnumDecl -------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// EnumDecl::Constructor //////////////////////////////
EnumDecl::EnumDecl(SourceLocation loc)
  : TagDecl(Enum, loc)
{
}

//|///////////////////// EnumDecl::dump ///////////////////////////////////
void EnumDecl::dump(int indent) const
{
  cout << spaces(indent) << "EnumDecl " << this << " <" << m_loc << "> '" << *this << "'\n";

  if (basetype)
  {
    basetype->dump(indent + 2);
  }

  for(auto &decl : decls)
  {
    decl->dump(indent + 2);
  }
}


//|--------------------- EnumConstantDecl -----------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// EnumConstantDecl::Constructor //////////////////////
EnumConstantDecl::EnumConstantDecl(SourceLocation loc)
  : Decl(EnumConstant, loc)
{
}

//|///////////////////// EnumConstantDecl::dump /////////////////////////////
void EnumConstantDecl::dump(int indent) const
{
  cout << spaces(indent) << "EnumDecl " << this << " <" << m_loc << "> '" << *this << "'\n";

  if (value)
  {
    value->dump(indent + 2);
  }
}


//|--------------------- AttributeDecl --------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// AttributeDecl::Constructor /////////////////////////
AttributeDecl::AttributeDecl(SourceLocation loc)
  : Decl(Attribute, loc)
{
}

//|///////////////////// AttributeDecl::dump ////////////////////////////////
void AttributeDecl::dump(int indent) const
{
  cout << spaces(indent) << "AttributeDecl " << this << " <" << m_loc << "> '" << *this << "'\n";

  if (!options.empty())
  {
    cout << spaces(indent + 2) << options << '\n';
  }
}


//|--------------------- RunDecl --------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// RunDecl::Constructor ///////////////////////////////
RunDecl::RunDecl(SourceLocation loc)
  : Decl(Run, loc)
{
}

//|///////////////////// RunDecl::dump //////////////////////////////////////
void RunDecl::dump(int indent) const
{
  cout << spaces(indent) << "RunDecl " << this << " <" << m_loc << "> '" << *this << "'\n";

  if (fn)
  {
    fn->dump(indent + 2);
  }
}


//|--------------------- IfDecl ---------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// IfDecl::Constructor ////////////////////////////////
IfDecl::IfDecl(SourceLocation loc)
  : Decl(If, loc)
{
}

//|///////////////////// IfDecl::dump ///////////////////////////////////////
void IfDecl::dump(int indent) const
{
  cout << spaces(indent) << "IfDecl " << this << " <" << m_loc << "> '" << *this << "'\n";

  if (cond)
  {
    cond->dump(indent + 2);
  }

  for(auto &decl : decls)
  {
    decl->dump(indent + 2);
  }

  if (elseif)
  {
    elseif->dump(indent + 2);
  }
}
