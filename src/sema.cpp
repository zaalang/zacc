//
// sema.cpp
//
// Copyright (c) 2020-2024 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "sema.h"
#include "util.h"
#include <iostream>
#include <cassert>

#if defined _MSC_VER
#include <io.h>
#define F_OK 0
#define access _access
#else
#include <unistd.h>
#endif

using namespace std;

//|--------------------- Sema -----------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// Sema::Constructor //////////////////////////////////
Sema::Sema()
{
}

//|///////////////////// translation_unit ///////////////////////////////////
TranslationUnitDecl *Sema::translation_unit(string_view file)
{ 
  ast = new AST(new TranslationUnitDecl);

  auto unit = decl_cast<TranslationUnitDecl>(ast->root);

  unit->builtins = make_builtin_module(ast);
  unit->builtins->owner = unit;

  unit->mainmodule = ast->make_decl<ModuleDecl>(Ident::from(basename(file)), file);
  unit->mainmodule->owner = unit;

  unit->decls.push_back(ast->make_decl<UsingDecl>(unit->builtins, SourceLocation{}));
  unit->decls.push_back(unit->mainmodule);

  unit->cfgs = m_cfgs;

  return unit;
}

//|///////////////////// module_declaration /////////////////////////////////
ModuleDecl *Sema::module_declaration(Ident *name)
{
  auto unit = decl_cast<TranslationUnitDecl>(ast->root);

  auto path = name->str();

#if defined _WIN32
  std::replace(path.begin(), path.end(), '.', '\\');
#else
  std::replace(path.begin(), path.end(), '.', '/');
#endif

  string dirbase = dirname(path);
  string filebase = basename(path);
  string filename = filebase + ".zaa";

  path = dirname(decl_cast<ModuleDecl>(unit->mainmodule)->file()) + dirbase + filename;

  if (access(path.c_str(), F_OK) != 0)
  {
    if (auto test = dirname(path) + filebase; access(test.c_str(), F_OK) == 0)
    {
      path = test + '/' + filename;
    }
  }

  if (access(path.c_str(), F_OK) != 0)
  {
    for (auto &includepath : m_include_paths)
    {
      if (auto test = includepath + '/' + dirbase + filename; access(test.c_str(), F_OK) == 0)
      {
        path = test;
        break;
      }

      if (auto test = includepath + '/' + dirbase + filebase; access(test.c_str(), F_OK) == 0)
      {
        path = test + '/' + filename;
        break;
      }
    }
  }

  auto module = ast->make_decl<ModuleDecl>(name, path);

  module->owner = unit;

  unit->decls.push_back(module);

  return module;
}

//|///////////////////// ident_pattern //////////////////////////////////////
IdentPatternDecl *Sema::ident_pattern(Ident *name, SourceLocation loc)
{
  return ast->make_decl<IdentPatternDecl>(name, loc);
}

//|///////////////////// tuple_pattern //////////////////////////////////////
TuplePatternDecl *Sema::tuple_pattern(vector<Decl*> const &decls, SourceLocation loc)
{
  return ast->make_decl<TuplePatternDecl>(decls, loc);
}

//|///////////////////// function_declaration ///////////////////////////////
FunctionDecl *Sema::function_declaration(SourceLocation loc)
{
  return ast->make_decl<FunctionDecl>(loc);
}

//|///////////////////// compound_statement /////////////////////////////////
CompoundStmt *Sema::compound_statement(SourceLocation loc)
{
  return ast->make_stmt<CompoundStmt>(loc);
}

//|///////////////////// try_statement //////////////////////////////////////
TryStmt *Sema::try_statement(SourceLocation loc)
{
  return ast->make_stmt<TryStmt>(loc);
}

//|///////////////////// declaration_statement //////////////////////////////
DeclStmt *Sema::declaration_statement(SourceLocation loc)
{
  return ast->make_stmt<DeclStmt>(loc);
}

//|///////////////////// if_statement ///////////////////////////////////////
IfStmt *Sema::if_statement(SourceLocation loc)
{
  return ast->make_stmt<IfStmt>(loc);
}

//|///////////////////// for_statement //////////////////////////////////////
ForStmt *Sema::for_statement(SourceLocation loc)
{
  return ast->make_decl<ForStmt>(loc);
}

//|///////////////////// rof_statement //////////////////////////////////////
RofStmt *Sema::rof_statement(SourceLocation loc)
{
  return ast->make_decl<RofStmt>(loc);
}

//|///////////////////// while_statement ////////////////////////////////////
WhileStmt *Sema::while_statement(SourceLocation loc)
{
  return ast->make_stmt<WhileStmt>(loc);
}

//|///////////////////// switch_statement ///////////////////////////////////
SwitchStmt *Sema::switch_statement(SourceLocation loc)
{
  return ast->make_stmt<SwitchStmt>(loc);
}

//|///////////////////// expression_statement ///////////////////////////////
ExprStmt *Sema::expression_statement(SourceLocation loc)
{
  return ast->make_stmt<ExprStmt>(loc);
}

//|///////////////////// null_statement /////////////////////////////////////
NullStmt *Sema::null_statement(SourceLocation loc)
{
  return ast->make_stmt<NullStmt>(loc);
}

//|///////////////////// goto_statement /////////////////////////////////////
GotoStmt *Sema::goto_statement(SourceLocation loc)
{
  return ast->make_stmt<GotoStmt>(loc);
}

//|///////////////////// throw_statement ////////////////////////////////////
ThrowStmt *Sema::throw_statement(SourceLocation loc)
{
  return ast->make_stmt<ThrowStmt>(loc);
}

//|///////////////////// break_statement ////////////////////////////////////
BreakStmt *Sema::break_statement(SourceLocation loc)
{
  return ast->make_stmt<BreakStmt>(loc);
}

//|///////////////////// continue_statement /////////////////////////////////
ContinueStmt *Sema::continue_statement(SourceLocation loc)
{
  return ast->make_stmt<ContinueStmt>(loc);
}

//|///////////////////// injection_statement ////////////////////////////////
InjectionStmt *Sema::injection_statement(SourceLocation loc)
{
  return ast->make_stmt<InjectionStmt>(loc);
}

//|///////////////////// return_statement ///////////////////////////////////
ReturnStmt *Sema::return_statement(SourceLocation loc)
{
  return ast->make_stmt<ReturnStmt>(loc);
}

//|///////////////////// import_declaration /////////////////////////////////
ImportDecl *Sema::import_declaration(SourceLocation loc)
{
  return ast->make_decl<ImportDecl>(loc);
}

//|///////////////////// using_declaration //////////////////////////////////
UsingDecl *Sema::using_declaration(SourceLocation loc)
{
  return ast->make_decl<UsingDecl>(loc);
}

//|///////////////////// alias_declaration //////////////////////////////////
TypeAliasDecl *Sema::alias_declaration(SourceLocation loc)
{
  return ast->make_decl<TypeAliasDecl>(loc);
}

//|///////////////////// typearg_declaration ////////////////////////////////
TypeArgDecl *Sema::typearg_declaration(SourceLocation loc)
{
  return ast->make_decl<TypeArgDecl>(loc);
}

//|///////////////////// struct_declaration /////////////////////////////////
StructDecl *Sema::struct_declaration(SourceLocation loc)
{
  return ast->make_decl<StructDecl>(loc);
}

//|///////////////////// union_declaration //////////////////////////////////
UnionDecl *Sema::union_declaration(SourceLocation loc)
{
  return ast->make_decl<UnionDecl>(loc);
}

//|///////////////////// lambda_declaration //////////////////////////////////
LambdaDecl *Sema::lambda_declaration(SourceLocation loc)
{
  return ast->make_decl<LambdaDecl>(loc);
}

//|///////////////////// vtable_declaration /////////////////////////////////
VTableDecl *Sema::vtable_declaration(SourceLocation loc)
{
  return ast->make_decl<VTableDecl>(loc);
}

//|///////////////////// var_declaration ////////////////////////////////////
StmtVarDecl *Sema::var_declaration(SourceLocation loc)
{
  return ast->make_decl<StmtVarDecl>(loc);
}

//|///////////////////// parm_declaration ///////////////////////////////////
ParmVarDecl *Sema::parm_declaration(SourceLocation loc)
{
  return ast->make_decl<ParmVarDecl>(loc);
}

//|///////////////////// field_declaration //////////////////////////////////
FieldVarDecl *Sema::field_declaration(SourceLocation loc)
{
  return ast->make_decl<FieldVarDecl>(loc);
}

//|///////////////////// initialiser_declaration ////////////////////////////
InitialiserDecl *Sema::initialiser_declaration(SourceLocation loc)
{
  return ast->make_decl<InitialiserDecl>(loc);
}

//|///////////////////// errorvar_declaration ///////////////////////////////
ErrorVarDecl *Sema::errorvar_declaration(SourceLocation loc)
{
  return ast->make_decl<ErrorVarDecl>(loc);
}

//|///////////////////// voidvar_declaration ////////////////////////////////
VoidVarDecl *Sema::voidvar_declaration(SourceLocation loc)
{
  return ast->make_decl<VoidVarDecl>(loc);
}

//|///////////////////// thisvar_declaration ////////////////////////////////
ThisVarDecl *Sema::thisvar_declaration(SourceLocation loc)
{
  return ast->make_decl<ThisVarDecl>(loc);
}

//|///////////////////// capture_declaration ////////////////////////////////
LambdaVarDecl *Sema::capture_declaration(SourceLocation loc)
{
  return ast->make_decl<LambdaVarDecl>(loc);
}

//|///////////////////// case_declaration ///////////////////////////////////
CaseDecl *Sema::case_declaration(SourceLocation loc)
{
  return ast->make_decl<CaseDecl>(loc);
}

//|///////////////////// casevar_declaration ////////////////////////////////
CaseVarDecl *Sema::casevar_declaration(SourceLocation loc)
{
  return ast->make_decl<CaseVarDecl>(loc);
}

//|///////////////////// concept_declaration ////////////////////////////////
ConceptDecl *Sema::concept_declaration(SourceLocation loc)
{
  return ast->make_decl<ConceptDecl>(loc);
}

//|///////////////////// requires_declaration ///////////////////////////////
RequiresDecl *Sema::requires_declaration(SourceLocation loc)
{
  return ast->make_decl<RequiresDecl>(loc);
}

//|///////////////////// enum_declaration ///////////////////////////////////
EnumDecl *Sema::enum_declaration(SourceLocation loc)
{
  return ast->make_decl<EnumDecl>(loc);
}

//|///////////////////// enum_constant_declaration //////////////////////////
EnumConstantDecl *Sema::enum_constant_declaration(SourceLocation loc)
{
  return ast->make_decl<EnumConstantDecl>(loc);
}

//|///////////////////// attribute_declaration //////////////////////////////
AttributeDecl *Sema::attribute_declaration(SourceLocation loc)
{
  return ast->make_decl<AttributeDecl>(loc);
}

//|///////////////////// run_declaration ////////////////////////////////////
RunDecl *Sema::run_declaration(SourceLocation loc)
{
  return ast->make_decl<RunDecl>(loc);
}

//|///////////////////// if_declaration /////////////////////////////////////
IfDecl *Sema::if_declaration(SourceLocation loc)
{
  return ast->make_decl<IfDecl>(loc);
}

//|///////////////////// make_declref ///////////////////////////////////////
DeclRefDecl *Sema::make_declref(Ident *name, SourceLocation loc)
{
  return ast->make_decl<DeclRefDecl>(name, loc);
}

//|///////////////////// make_declref ///////////////////////////////////////
DeclScopedDecl *Sema::make_declref(vector<Decl*> const &decls, SourceLocation loc)
{
  return ast->make_decl<DeclScopedDecl>(decls, loc);
}

//|///////////////////// make_typename //////////////////////////////////////
TypeNameDecl *Sema::make_typename(Type *type, SourceLocation loc)
{
  return ast->make_decl<TypeNameDecl>(type, loc);
}

//|///////////////////// make_decltype //////////////////////////////////////
TypeOfDecl *Sema::make_decltype(Expr *expr, SourceLocation loc)
{
  return ast->make_decl<TypeOfDecl>(expr, loc);
}

//|///////////////////// make_typearg ///////////////////////////////////////
TypeArgDecl *Sema::make_typearg(Ident *name, SourceLocation loc)
{
  return ast->make_decl<TypeArgDecl>(name, loc);
}

//|///////////////////// make_literal ///////////////////////////////////////
Expr *Sema::make_bool_literal(bool value, SourceLocation loc)
{
  return ast->make_expr<BoolLiteralExpr>(value, loc);
}

//|///////////////////// make_literal ///////////////////////////////////////
Expr *Sema::make_char_literal(string_view value, SourceLocation loc)
{
  return ast->make_expr<CharLiteralExpr>(Numeric::parse_char_literal(value), loc);
}

//|///////////////////// make_literal ///////////////////////////////////////
Expr *Sema::make_numeric_literal(int sign, string_view value, SourceLocation loc)
{
  if (Numeric::is_int_literal(value))
  {
    return ast->make_expr<IntLiteralExpr>(Numeric::parse_int_literal(sign, value), loc);
  }

  if (Numeric::is_float_literal(value))
  {
    return ast->make_expr<FloatLiteralExpr>(Numeric::parse_float_literal(sign, value), loc);
  }

  if (Numeric::is_char_literal(value))
  {
    return ast->make_expr<CharLiteralExpr>(Numeric::parse_char_literal(value), loc);
  }

  throw logic_error("invalid numeric literal");
}

//|///////////////////// make_literal ///////////////////////////////////////
Expr *Sema::make_numeric_literal(int sign, size_t value, SourceLocation loc)
{
  return ast->make_expr<IntLiteralExpr>(Numeric::int_literal(sign, value), loc);
}

//|///////////////////// make_literal ///////////////////////////////////////
Expr *Sema::make_string_literal(string_view value, SourceLocation loc)
{
  return ast->make_expr<StringLiteralExpr>(value, loc);
}

//|///////////////////// make_array_literal /////////////////////////////////
Expr *Sema::make_array_literal(Type *elementtype, vector<Expr*> const &elements, Type *size, SourceLocation loc)
{
  return ast->make_expr<ArrayLiteralExpr>(elementtype, elements, size, loc);
}

//|///////////////////// make_tuple_literal /////////////////////////////////
Expr *Sema::make_tuple_literal(vector<Expr*> const &fields, SourceLocation loc)
{
  return ast->make_expr<CompoundLiteralExpr>(fields, loc);
}

//|///////////////////// make_void_literal //////////////////////////////////
Expr *Sema::make_void_literal(SourceLocation loc)
{
  return ast->make_expr<VoidLiteralExpr>(loc);
}

//|///////////////////// make_pointer_literal ///////////////////////////////
Expr *Sema::make_pointer_literal(SourceLocation loc)
{
  return ast->make_expr<PointerLiteralExpr>(loc);
}

//|///////////////////// make_mutref_expression /////////////////////////////
Expr *Sema::make_ref_expression(Expr *expr, long qualifiers, SourceLocation loc)
{
  return ast->make_expr<ExprRefExpr>(expr, qualifiers, loc);
}

//|///////////////////// make_paren_expression //////////////////////////////
Expr *Sema::make_paren_expression(Expr *subexpr, SourceLocation loc)
{
  return ast->make_expr<ParenExpr>(subexpr, loc);
}

//|///////////////////// make_named_expression //////////////////////////////
Expr *Sema::make_named_expression(Ident *name, Expr *expr, SourceLocation loc)
{
  return ast->make_expr<NamedExpr>(name, expr, loc);
}

//|///////////////////// make_unary_expression //////////////////////////////
Expr *Sema::make_unary_expression(UnaryOpExpr::OpCode op, Expr *subexpr, SourceLocation loc)
{
  return ast->make_expr<UnaryOpExpr>(op, subexpr, loc);
}

//|///////////////////// make_binary_expression /////////////////////////////
Expr *Sema::make_binary_expression(BinaryOpExpr::OpCode op, Expr *lhs, Expr *rhs, SourceLocation loc)
{
  return ast->make_expr<BinaryOpExpr>(op, lhs, rhs, loc);
}

//|///////////////////// make_ternary_expression ////////////////////////////
Expr *Sema::make_ternary_expression(Expr *cond, Expr *lhs, Expr *rhs, SourceLocation loc)
{
  return ast->make_expr<TernaryOpExpr>(cond, lhs, rhs, loc);
}

//|///////////////////// make_declref_expression ////////////////////////////
Expr *Sema::make_declref_expression(Decl *decl, SourceLocation loc)
{
  return ast->make_expr<DeclRefExpr>(decl, loc);
}

//|///////////////////// make_declref_expression ////////////////////////////
Expr *Sema::make_declref_expression(Expr *base, Decl *decl, SourceLocation loc)
{
  return ast->make_expr<DeclRefExpr>(base, decl, loc);
}

//|///////////////////// make_call_expression ///////////////////////////////
Expr *Sema::make_call_expression(Decl *decl, SourceLocation loc)
{
  return ast->make_expr<CallExpr>(decl, loc);
}

//|///////////////////// make_call_expression ///////////////////////////////
Expr *Sema::make_call_expression(Decl *decl, vector<Expr*> const &parms, SourceLocation loc)
{
  return ast->make_expr<CallExpr>(decl, parms, loc);
}

//|///////////////////// make_call_expression ///////////////////////////////
Expr *Sema::make_call_expression(Expr *base, Decl *decl, vector<Expr*> const &parms, SourceLocation loc)
{
  return ast->make_expr<CallExpr>(base, decl, parms, loc);
}

//|///////////////////// make_sizeof_expression /////////////////////////////
Expr *Sema::make_sizeof_expression(Type *type, SourceLocation loc)
{
  return ast->make_expr<SizeofExpr>(type, loc);
}

//|///////////////////// make_sizeof_expression /////////////////////////////
Expr *Sema::make_sizeof_expression(Expr *expr, SourceLocation loc)
{
  return ast->make_expr<SizeofExpr>(expr, loc);
}

//|///////////////////// make_alignof_expression ////////////////////////////
Expr *Sema::make_alignof_expression(Type *type, SourceLocation loc)
{
  return ast->make_expr<AlignofExpr>(type, loc);
}

//|///////////////////// make_alignof_expression ////////////////////////////
Expr *Sema::make_alignof_expression(Decl *decl, SourceLocation loc)
{
  return ast->make_expr<AlignofExpr>(decl, loc);
}

//|///////////////////// make_offsetof_expression ///////////////////////////
Expr *Sema::make_offsetof_expression(Decl *decl, SourceLocation loc)
{
  return ast->make_expr<OffsetofExpr>(decl, loc);
}

//|///////////////////// make_instanceof_expression /////////////////////////
Expr *Sema::make_instanceof_expression(Type *type, Type *instance, SourceLocation loc)
{
  return ast->make_expr<InstanceofExpr>(type, instance, loc);
}

//|///////////////////// make_typeid_expression /////////////////////////////
Expr *Sema::make_typeid_expression(Decl *decl, SourceLocation loc)
{
  return ast->make_expr<TypeidExpr>(decl, loc);
}

//|///////////////////// make_cast_expression ///////////////////////////////
Expr *Sema::make_cast_expression(Type *type, Expr *expr, SourceLocation loc)
{
  return ast->make_expr<CastExpr>(type, expr, loc);
}

//|///////////////////// make_new_expression ////////////////////////////////
Expr *Sema::make_new_expression(Type *type, Expr *address, SourceLocation loc)
{
  return ast->make_expr<NewExpr>(type, address, loc);
}

//|///////////////////// make_new_expression ////////////////////////////////
Expr *Sema::make_new_expression(Type *type, Expr *address, vector<Expr*> const &parms, SourceLocation loc)
{
  return ast->make_expr<NewExpr>(type, address, parms, loc);
}

//|///////////////////// make_requires_expression ///////////////////////////
Expr *Sema::make_requires_expression(Decl *decl, SourceLocation loc)
{
  return ast->make_expr<RequiresExpr>(decl, loc);
}

//|///////////////////// make_where_expression //////////////////////////////
Expr *Sema::make_where_expression(Expr *expr, SourceLocation loc)
{
  return ast->make_expr<WhereExpr>(expr, loc);
}

//|///////////////////// make_match_expression //////////////////////////////
Expr *Sema::make_match_expression(Decl *decl, SourceLocation loc)
{
  return ast->make_expr<MatchExpr>(decl, loc);
}

//|///////////////////// make_lambda_expression /////////////////////////////
Expr *Sema::make_lambda_expression(Decl *decl, SourceLocation loc)
{
  return ast->make_expr<LambdaExpr>(decl, loc);
}

//|///////////////////// make_fragment_expression ///////////////////////////
Expr *Sema::make_fragment_expression(std::vector<Expr*> const &args, std::vector<Decl*> const &decls, SourceLocation loc)
{
  return ast->make_expr<FragmentExpr>(args, decls, loc);
}

//|///////////////////// make_const /////////////////////////////////////////
Type *Sema::make_const(Type *type)
{
  return ast->make_type<ConstType>(type);
}

//|///////////////////// make_pointer ///////////////////////////////////////
Type *Sema::make_pointer(Type *type)
{
  return ast->make_type<PointerType>(type);
}

//|///////////////////// make_reference /////////////////////////////////////
Type *Sema::make_reference(Type *type)
{
  return ast->make_type<ReferenceType>(type);
}

//|///////////////////// make_array /////////////////////////////////////////
Type *Sema::make_array(Type *type, Type *size)
{
  return ast->make_type<ArrayType>(type, size);
}

//|///////////////////// make_tuple /////////////////////////////////////////
Type *Sema::make_tuple(vector<Type*> const &fields)
{
  return ast->make_type<TupleType>(fields);
}

//|///////////////////// make_typeref ///////////////////////////////////////
Type *Sema::make_typeref(Decl *decl)
{
  return ast->make_type<TypeRefType>(decl);
}

//|///////////////////// make_typearg ///////////////////////////////////////
Type *Sema::make_typearg(Decl *decl)
{
  return ast->make_type<TypeArgType>(decl);
}

//|///////////////////// make_typearg ///////////////////////////////////////
Type *Sema::make_typearg(Decl *decl, Decl *koncept, vector<pair<Decl*, Type*>> const &args)
{
  return ast->make_type<TypeArgType>(decl, koncept, args);
}

//|///////////////////// make_qualarg ///////////////////////////////////////
Type *Sema::make_qualarg(Type *type)
{
  return ast->make_type<QualArgType>(type);
}

//|///////////////////// make_typelit ///////////////////////////////////////
Type *Sema::make_typelit(Expr *value)
{
  return ast->make_type<TypeLitType>(value);
}

//|///////////////////// make_constant //////////////////////////////////////
Type *Sema::make_constant(Decl *decl, Type *type)
{
  return ast->make_type<ConstantType>(decl, type);
}

//|///////////////////// make_tagtype ///////////////////////////////////////
Type *Sema::make_tagtype(Decl *decl, vector<pair<Decl*, Type*>> const &args)
{
  return ast->make_type<TagType>(decl, args);
}

//|///////////////////// make_fntype ////////////////////////////////////////
Type *Sema::make_fntype(Type *returntype, Type *paramtuple, Type *throwtype)
{
  return ast->make_type<FunctionType>(returntype, paramtuple, throwtype);
}

//|///////////////////// make_pack //////////////////////////////////////////
Type *Sema::make_pack(Type *type)
{
  return ast->make_type<PackType>(type);
}

//|///////////////////// make_unpack ////////////////////////////////////////
Type *Sema::make_unpack(Type *type)
{
  return ast->make_type<UnpackType>(type);
}

//|///////////////////// lookup_module //////////////////////////////////////
ModuleDecl *Sema::lookup_module(Ident *name)
{
  auto unit = decl_cast<TranslationUnitDecl>(ast->root);

  for (auto &decl : unit->decls)
  {
    if (is_module_decl(decl) && decl_cast<ModuleDecl>(decl)->name == name)
      return decl_cast<ModuleDecl>(decl);
  }

  return nullptr;
}

//|///////////////////// add_cfg ////////////////////////////////////////////
void Sema::add_cfg(string_view str)
{
  if (str[0] == '\'' || str[0] == '"')
  {
    str.remove_prefix(1);
    str.remove_suffix(1);
  }

  m_cfgs.emplace_back(str);
}

//|///////////////////// add_include_path ///////////////////////////////////
void Sema::add_include_path(string_view path)
{
  m_include_paths.emplace_back(path);
}

//|///////////////////// end ////////////////////////////////////////////////
void Sema::end()
{
}
