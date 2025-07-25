//
// mir.cpp
//
// Copyright (c) 2020-2024 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "ast.h"
#include "mir.h"
#include <functional>
#include <iostream>

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
      for (int i = 0; i < indent.n; ++i)
        os << ' ';

      return os;
    }

    int n;
  };

  string module_file(Decl *decl)
  {
    auto parent = decl->owner;

    while (parent != std::variant<Decl*, Stmt*>())
    {
      if (auto decl = get_if<Decl*>(&parent); decl && *decl && (*decl)->kind() == Decl::Module)
        return decl_cast<ModuleDecl>(*decl)->file();

      parent = std::visit([](auto &v) { return v->owner; }, parent);
    }

    return "";
  }

  [[maybe_unused]]
  void rebase(MIR::RValue &rvalue, MIR::local_t base, size_t offset)
  {
    switch (rvalue.kind())
    {
      case MIR::RValue::Empty:
      case MIR::RValue::Constant:
        break;

      case MIR::RValue::Variable:
        if (auto &[op, arg, fields, loc] = rvalue.get<MIR::RValue::Variable>(); arg >= base)
          arg += offset;
        break;

      case MIR::RValue::Call:
        if (auto &[callee, args, loc] = rvalue.get<MIR::RValue::Call>(); true)
          for (auto &arg : args)
            if (arg >= base)
              arg += offset;
        break;

      case MIR::RValue::Cast:
        if (auto &[arg, loc] = rvalue.get<MIR::RValue::Cast>(); arg >= base)
          arg += offset;
        break;

      default:
        assert(false);
    }
  }

  [[maybe_unused]]
  void rebase(MIR::Statement &statement, MIR::local_t base, size_t offset)
  {
    if (statement.dst >= base)
      statement.dst += offset;

    rebase(statement.src, base, offset);
  }

  [[maybe_unused]]
  void rebase(MIR::Terminator &terminator, MIR::block_t base, size_t offset)
  {
    if (terminator.blockid >= base)
      terminator.blockid += offset;

    for (auto &target : terminator.targets)
      if (get<1>(target) >= base)
        get<1>(target) += offset;
  }
}

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, FnSig const &fx)
{
  if (fx.fn)
  {
    os << '&' << *fx.fn;
  }

  return os;
}

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, MIR::Local const &local)
{
  if (local.type)
  {
    os << *local.type;

    if (local.flags & MIR::Local::Const)
      os << " const";

    if (local.flags & MIR::Local::LValue)
      os << " lvalue";

    if (local.flags & MIR::Local::RValue)
      os << " rvalue";

    if (local.flags & MIR::Local::XValue)
      os << " xvalue";

    if (local.flags & MIR::Local::MoveRef)
      os << " moveref";

    if (local.flags & MIR::Local::Unaligned)
      os << " unaligned";

    if (local.flags & MIR::Local::Reference)
      os << " &";
  }

  return os;
}

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, MIR::RValue::ConstantData const &constant)
{
  os << "const ";

  if (holds_alternative<BoolLiteralExpr*>(constant))
    os << (get<BoolLiteralExpr*>(constant)->value() ? "true" : "false");

  else if (holds_alternative<CharLiteralExpr*>(constant))
    os << '\'' << get<CharLiteralExpr*>(constant)->value() << '\'';

  else if (holds_alternative<StringLiteralExpr*>(constant))
    os << '"' << escape(get<StringLiteralExpr*>(constant)->value()) << '"';

  else
    std::visit([&](auto &v) { os << v->value(); }, constant);

  return os;
}

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, MIR::RValue::VariableData const &variable)
{
  auto &[op, arg, fields, loc] = variable;

  switch (op)
  {
    case MIR::RValue::Ref:
      os << '&' << '_' << arg;
      break;

    case MIR::RValue::Val:
      os << '_' << arg;
      break;

    case MIR::RValue::Fer:
      os << '*' << '_' << arg;
      break;

    case MIR::RValue::Idx:
      os << '+' << '_' << arg;
      break;
  }

  for (auto &field : fields)
  {
    switch (field.op)
    {
      case MIR::RValue::Ref:
        os << '.' << field.index;
        break;

      case MIR::RValue::Val:
        os << "->" << field.index;
        break;

      case MIR::RValue::Fer:
        assert(false);
        break;

      case MIR::RValue::Idx:
        os << '[' << field.index << ']';
        break;
    }
  }

  return os;
}

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, MIR::RValue::CallData const &call)
{
  auto &[callee, args, loc] = call;

  if (callee.fn->name)
    os << *callee.fn->name;

#if 1
  if (callee.typeargs.size() != 0)
  {
    os << '<';

    int i = 0;
    for (auto &[decl, type] : callee.typeargs)
    {
      if (decl->kind() == Decl::ParmVar && !(decl_cast<ParmVarDecl>(decl)->flags & VarDecl::Literal))
        continue;

      os << (!i++ ? "" : ", ") << *decl << ": " << *type;
    }

    os << '>';
  }
#endif

  os << '(';

  for (auto &arg : args)
  {
    os << '_' << arg;

    if (&arg != &args.back())
      os << ", ";
  }

  os << ')';

  return os;
}

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, MIR::RValue::CastData const &cast)
{
  auto &[arg, loc] = cast;

  os << "cast" << '(' << '_' << arg << ')';

  return os;
}

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, MIR::RValue::InjectionData const &injection)
{
  auto &[decl, args, loc] = injection;

  os << "-> " << *decl;

  os << '(';

  for (auto &arg : args)
  {
    os << '_' << arg;

    if (&arg != &args.back())
      os << ", ";
  }

  os << ')';

  return os;
}

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, MIR::RValue const &rvalue)
{
  switch (rvalue.kind())
  {
    case MIR::RValue::Empty:
      os << "void";
      break;

    case MIR::RValue::Constant:
      os << rvalue.get<MIR::RValue::Constant>();
      break;

    case MIR::RValue::Variable:
      os << rvalue.get<MIR::RValue::Variable>();
      break;

    case MIR::RValue::Call:
      os << rvalue.get<MIR::RValue::Call>();
      break;

    case MIR::RValue::Cast:
      os << rvalue.get<MIR::RValue::Cast>();
      break;

    case MIR::RValue::Injection:
      os << rvalue.get<MIR::RValue::Injection>();
      break;
  }

  return os;
}

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, MIR::Statement const &statement)
{
  switch (statement.kind)
  {
    case MIR::Statement::NoOp:
      os << "NoOp";
      break;

    case MIR::Statement::Assign:
      os << '_' << statement.dst << " = " << statement.src;
      break;

    case MIR::Statement::Construct:
      os << '_' << statement.dst << " = " << "new(_" << statement.dst - 1 << ") " << statement.src;
      break;

    case MIR::Statement::StorageLive:
      os << "StorageLive(_" << statement.dst << ")";
      break;

    case MIR::Statement::StorageDead:
      os << "StorageDead(_" << statement.dst << ")";
      break;

    case MIR::Statement::StorageLoop:
      os << "StorageLoop(_" << statement.dst << ")";
      break;
  }

  return os;
}

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, MIR::Terminator const &terminator)
{
  switch (terminator.kind)
  {
    case MIR::Terminator::Return:
      os << "return";
      break;

    case MIR::Terminator::Goto:
      os << "goto bb" << terminator.blockid;
      break;

    case MIR::Terminator::Switch:
      os << "switch(_" << terminator.value << ") -> [";
      for (auto &[k, b] : terminator.targets)
        os << k << ": bb" << b << ", ";
      os << "otherwise: bb" << terminator.blockid << "]";
      break;

    case MIR::Terminator::Catch:
      os << "catch(_" << terminator.value << ") -> bb" << terminator.blockid << ", otherwise: bb" << terminator.blockid + 1;
      break;

    case MIR::Terminator::Throw:
      os << "throw(_" << terminator.value << ") -> bb" << terminator.blockid;
      break;

    case MIR::Terminator::Unreachable:
      os << "unreachable";
      break;
  }

  return os;
}


//|--------------------- FnSig ----------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// Constructor ////////////////////////////////////////
FnSig::FnSig(FunctionDecl *fn, Type *throwtype)
  : fn(fn),
    throwtype(throwtype)
{
  hash = std::hash<Decl*>()(fn);
}

//|///////////////////// Constructor ////////////////////////////////////////
FnSig::FnSig(FunctionDecl *fn, vector<pair<Decl*, Type*>> typeargs, Type *throwtype)
  : fn(fn),
    throwtype(throwtype),
    typeargs(std::move(typeargs))
{
  hash = std::hash<Decl*>()(fn);

  for (auto &arg : this->typeargs)
  {
    hash ^= std::hash<Decl*>()(arg.first);
  }
}

//|///////////////////// set_type ///////////////////////////////////////////
void FnSig::set_type(Decl *in, Type *out)
{
  auto j = lower_bound(typeargs.begin(), typeargs.end(), in, [](auto &lhs, auto &rhs) { return less<>{}(lhs.first, rhs); });

  if (j == typeargs.end() || j->first != in)
  {
    typeargs.emplace(j, in, out);

    hash ^= std::hash<Decl*>()(in);
  }
  else
  {
    j->second = out;
  }
}

//|///////////////////// is_concrete_call ///////////////////////////////////
bool is_concrete_call(FnSig const &fx)
{
  for (auto &[decl, type] : fx.typeargs)
  {
    if (decl->kind() == Decl::ParmVar && (decl_cast<ParmVarDecl>(decl)->flags & VarDecl::Literal))
      continue;

    if (is_qualarg_type(type))
    {
      if (type_cast<QualArgType>(type)->type && !is_concrete_type(type_cast<QualArgType>(type)->type))
        return false;

      continue;
    }

    if (!is_concrete_type(type))
      return false;
  }

  return true;
}


//|--------------------- MIR ------------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// RValue loc /////////////////////////////////////////
SourceLocation MIR::RValue::loc() const
{
  switch (kind())
  {
    case MIR::RValue::Constant:
      return std::visit([&](auto &v) { return static_cast<Expr*>(v); }, get<MIR::RValue::Constant>())->loc();

    case MIR::RValue::Variable:
      return std::get<3>(get<MIR::RValue::Variable>());

    case MIR::RValue::Call:
      return std::get<2>(get<MIR::RValue::Call>());

    case MIR::RValue::Cast:
      return std::get<1>(get<MIR::RValue::Cast>());

    case MIR::RValue::Injection:
      return std::get<2>(get<MIR::RValue::Injection>());

    default:
      return {};
  }
}

//|///////////////////// RValue literal /////////////////////////////////////
MIR::RValue::ConstantData MIR::RValue::literal(Expr *expr)
{
  switch (expr->kind())
  {
    case Expr::VoidLiteral:
      return expr_cast<VoidLiteralExpr>(expr);

    case Expr::BoolLiteral:
      return expr_cast<BoolLiteralExpr>(expr);

    case Expr::CharLiteral:
      return expr_cast<CharLiteralExpr>(expr);

    case Expr::IntLiteral:
      return expr_cast<IntLiteralExpr>(expr);

    case Expr::FloatLiteral:
      return expr_cast<FloatLiteralExpr>(expr);

    case Expr::PointerLiteral:
      return expr_cast<PointerLiteralExpr>(expr);

    case Expr::FunctionPointer:
      return expr_cast<FunctionPointerExpr>(expr);

    case Expr::StringLiteral:
      return expr_cast<StringLiteralExpr>(expr);

    case Expr::ArrayLiteral:
      return expr_cast<ArrayLiteralExpr>(expr);

    case Expr::CompoundLiteral:
      return expr_cast<CompoundLiteralExpr>(expr);

    default:
      assert(false);
  }

  throw std::logic_error("invalid literal type");
}

//|///////////////////// MIR::dump //////////////////////////////////////////
void MIR::Local::dump(int indent, size_t idx) const
{
  cout << spaces(indent) << "var " << "_" << idx << " : " << *this << ";\n";
}

//|///////////////////// MIR::dump //////////////////////////////////////////
void MIR::Statement::dump(int indent, size_t idx) const
{
#if 1
  if (kind == MIR::Statement::StorageLive || kind == MIR::Statement::StorageDead || kind == MIR::Statement::StorageLoop)
    return;
#endif

  cout << spaces(indent) << *this << ";\n";
}

//|///////////////////// MIR::dump //////////////////////////////////////////
void MIR::Terminator::dump(int indent) const
{
  cout << spaces(indent) << *this << ";\n";
}

//|///////////////////// MIR::dump //////////////////////////////////////////
void MIR::Block::dump(int indent, size_t idx) const
{
  cout << spaces(indent) << "bb" << idx << ": {\n";

  for (auto &statement : statements)
  {
    statement.dump(indent + 2, &statement - &statements.front());
  }

  terminator.dump(indent + 2);

  cout << spaces(indent) << "}\n";
}

//|///////////////////// MIR::dump //////////////////////////////////////////
void MIR::Fragment::dump(int indent) const
{
  cout << spaces(indent) << "-> " << type << " {\n";
  cout << spaces(indent) << "  return " << value << ";\n";
  cout << spaces(indent) << "}\n";
}

//|///////////////////// MIR::dump //////////////////////////////////////////
void MIR::dump() const
{
  if (fx.fn)
  {
    auto fn = fx.fn;

    cout << "# " << module_file(fx.fn) << ":" << fx.fn->loc() << '\n';

    switch (fn->flags & FunctionDecl::DeclType)
    {
      case FunctionDecl::ConstDecl:
        cout << "const " << *fn->name;
        break;

      case FunctionDecl::RequiresDecl:
        cout << "requires";
        break;

      case FunctionDecl::MatchDecl:
        cout << "match";
        break;

      case FunctionDecl::RunDecl:
        cout << "run";
        break;

      default:
        cout << "fn " << *fn->name;
    }
  }

#if 1
  if (fx.typeargs.size() != 0)
  {
    cout << '<';

    int i = 0;
    for (auto &[decl, type] : fx.typeargs)
    {
      if (decl->kind() == Decl::ParmVar)
        continue;

      cout << (!i++ ? "" : ", ") << *decl << ": " << *type;
    }

    cout << '>';
  }
#endif

  if (locals.size() != 0)
  {
    cout << '(';

    for (size_t i = args_beg, end = args_end; i != end; ++i)
    {
      cout << locals[i] << " _" << i << (i + 1 != end ? ", " : "");
    }

    cout << ')';

    if (throws)
      cout << " throws(" << *locals[1].type << ")";

    cout << " -> " << *locals[0].type << " {\n";

    locals[0].dump(2, 0);

    if (throws)
    {
      locals[1].dump(2, 1);
    }

    for (size_t i = args_end, end = locals.size(); i != end; ++i)
    {
      locals[i].dump(2, i);
    }
  }

  cout << '\n';

  for (auto &block : blocks)
  {
    block.dump(2, &block - &blocks.front());
  }

  cout << "}\n";

  cout << endl;
}

//|///////////////////// insert_blocks //////////////////////////////////////
MIR::Block &insert_blocks(MIR &mir, MIR::block_t position, size_t count)
{
  auto j = mir.blocks.insert(mir.blocks.begin() + position, count, MIR::Block());

  for (auto &block : mir.blocks)
  {
    rebase(block.terminator, position, count);
  }

  for (auto i = position; i < position + count; ++i)
  {
    mir.blocks[i].terminator = MIR::Terminator::gotoer(i + 1);
  }

  return *j;
}

//|///////////////////// dump_mir ///////////////////////////////////////////
void dump_mir(MIR const &mir)
{
  mir.dump();
}
