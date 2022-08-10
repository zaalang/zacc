//
// mir.h
//
// Copyright (C) 2020-2022 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "type.h"
#include "util.h"
#include <string>
#include <tuple>
#include <vector>
#include <variant>
#include <algorithm>
#include <cassert>

class FunctionDecl;
class VoidLiteralExpr;
class BoolLiteralExpr;
class CharLiteralExpr;
class IntLiteralExpr;
class FloatLiteralExpr;
class PointerLiteralExpr;
class FunctionPointerExpr;
class StringLiteralExpr;
class ArrayLiteralExpr;
class CompoundLiteralExpr;
class FragmentExpr;
class VarDecl;

//-------------------------- FnSig ------------------------------------------
//---------------------------------------------------------------------------

class FnSig
{
  public:
    FnSig(FunctionDecl *fn = nullptr, Type *throwtype = nullptr);
    FnSig(FunctionDecl *fn, std::vector<std::pair<Decl*, Type*>> typeargs, Type *throwtype = nullptr);

    FunctionDecl *fn;

    void set_type(Decl *in, Type *out);

    auto find_type(Decl *decl)
    {
      return std::find_if(typeargs.begin(), typeargs.end(), [&](auto &k) { return k.first == decl; });
    }

    auto find_type(Decl *decl) const
    {
      return std::find_if(typeargs.begin(), typeargs.end(), [&](auto &k) { return k.first == decl; });
    }

    explicit operator bool() const { return fn; }

    friend bool operator ==(FnSig const &lhs, FnSig const &rhs)
    {
      return lhs.fn == rhs.fn && lhs.typeargs == rhs.typeargs && lhs.throwtype == rhs.throwtype;
    }

    friend bool operator !=(FnSig const &lhs, FnSig const &rhs)
    {
      return !(lhs == rhs);
    }

    auto arguments() const
    {
      return iterator_pair(typeargs.begin(), typeargs.end());
    }

    auto parameters() const
    {
      auto skip = [](auto &decl) { return decl_cast<ParmVarDecl>(decl)->flags & VarDecl::Literal; };

      return iterator_pair(skip_iterator(fn->parms.begin(), fn->parms.end(), skip), fn->parms.end());
    }

    Type *throwtype;

    std::vector<std::pair<Decl*, Type*>> typeargs;

    size_t hash;
};

namespace std
{
  template <>
  struct hash<FnSig>
  {
    std::size_t operator()(FnSig const &fx) const
    {
      return fx.hash;
    }
  };
}

bool is_concrete_call(FnSig const &fx);

//-------------------------- MIR --------------------------------------------
//---------------------------------------------------------------------------

class MIR
{
  public:

    using local_t = std::size_t;
    using field_t = std::size_t;
    using block_t = std::size_t;
    using statement_t = std::size_t;

    //-------------------------- Local --------------------------------------
    //-----------------------------------------------------------------------

    class Local
    {
      public:

        enum Flags
        {
          Const = 0x02,
          Literal = 0x04,
          Reference = 0x08,

          LValue = 0x10,
          RValue = 0x20,
          XValue = 0x40, // or XLValue if forwarded

          ConstRef = 0x80,

          Unaligned = 0x100,
          ThreadLocal = 0x200,
          CacheAligned = 0x400,
          PageAligned = 0x800,
        };

        long flags;

        Type *type;
        Type *defn;

        bool concrete() const { return is_concrete_type(type); }
        bool zerosized() const { return !(flags & MIR::Local::Reference) && (type->flags & Type::ZeroSized); }

        Local(std::nullptr_t = nullptr)
          : flags(0), type(nullptr), defn(nullptr)
        {
        }

        Local(Type *type, long flags = 0)
          : flags(flags), type(type), defn(type)
        {
        }

        Local(Type *type, Type *defn, long flags = 0)
          : flags(flags), type(type), defn(defn)
        {
        }

        bool operator!() const { return !type; }
        explicit operator bool() const { return type; }

      protected:

        void dump(int indent, size_t idx) const;

        friend class MIR;
    };

    //-------------------------- RValue -------------------------------------
    //-----------------------------------------------------------------------

    struct RValue
    {
      enum Kind
      {
        Empty,
        Constant,
        Variable,
        Call,
        Cast,
        Injection,
      };

      enum Op
      {
        Val,
        Ref,
        Fer,
        Idx,
      };

      struct Field
      {
        Op op;
        field_t index;
      };

      using ConstantData = std::variant<VoidLiteralExpr*, BoolLiteralExpr*, CharLiteralExpr*, IntLiteralExpr*, FloatLiteralExpr*, PointerLiteralExpr*, FunctionPointerExpr*, StringLiteralExpr*, ArrayLiteralExpr*, CompoundLiteralExpr*>;
      using VariableData = std::tuple<Op, local_t, std::vector<Field>, SourceLocation>;
      using CallData = std::tuple<FnSig, std::vector<local_t>, SourceLocation>;
      using CastData = std::tuple<local_t, SourceLocation>;
      using InjectionData = std::tuple<FragmentExpr*, std::vector<local_t>, SourceLocation>;

      auto kind() const { return value.index(); }

      template<size_t i> auto &get() { return std::get<i>(value); }
      template<size_t i> auto const &get() const { return std::get<i>(value); }

      RValue() = default;

      template<typename T>
      RValue(T &&value)
        : value(std::forward<T>(value))
      {
      }

      SourceLocation loc() const;

      explicit operator bool() const { return value.index() != 0; }

      static ConstantData literal(Expr *expr);
      static VariableData local(Op op, local_t arg, SourceLocation loc) { return { op, arg, {}, loc }; }
      static VariableData field(Op op, local_t arg, Field field, SourceLocation loc) { return { op, arg, { field }, loc }; }
      static VariableData field(Op op, local_t arg, std::vector<Field> fields, SourceLocation loc) { return { op, arg, std::move(fields), loc }; }
      static CallData call(FnSig sig, std::vector<local_t> args, SourceLocation loc) { return { std::move(sig), std::move(args), loc }; }
      static CastData cast(local_t arg, SourceLocation loc) { return { arg, loc }; }
      static InjectionData injection(FragmentExpr *expr, std::vector<local_t> args, SourceLocation loc) { return { expr, std::move(args), loc }; }

      private:

      std::variant<std::monostate, ConstantData, VariableData, CallData, CastData, InjectionData> value;
    };

    //-------------------------- Statement ----------------------------------
    //-----------------------------------------------------------------------

    class Statement
    {
      public:

        enum Kind
        {
          NoOp,
          Assign,
          Construct,
          StorageLive,
          StorageDead,
          StorageLoop,
        };

        Kind kind;

        local_t dst;
        RValue src;

        static Statement assign(local_t dst, RValue const &src) { return { Assign, dst, src }; }
        static Statement construct(local_t dst, RValue const &src) { return { Construct, dst, src }; }
        static Statement storagelive(local_t dst) { return { StorageLive, dst }; }
        static Statement storagedead(local_t dst) { return { StorageDead, dst }; }
        static Statement storageloop(local_t dst) { return { StorageLoop, dst }; }

      protected:

        void dump(int indent, size_t idx) const;

        friend class MIR;
    };

    //-------------------------- Terminator ---------------------------------
    //-----------------------------------------------------------------------

    class Terminator
    {
      public:

        enum Kind
        {
          Return,
          Goto,
          Switch,
          Catch,
          Throw,
          Unreachable,
        };

        Kind kind;

        local_t value;
        block_t blockid;

        std::vector<std::tuple<size_t, block_t>> targets;

        static Terminator returner() { return { Return }; }
        static Terminator gotoer(block_t dst) { return { Goto, 0, dst }; }
        static Terminator switcher(local_t value, block_t otherwise) { return { Switch, value, otherwise }; }
        static Terminator switcher(local_t value, block_t block_false, block_t block_true) { return { Switch, value, block_true, { { 0, block_false } } }; }
        static Terminator catcher(local_t value, block_t dst) { return { Catch, value, dst }; }
        static Terminator thrower(local_t value, block_t dst) { return { Throw, value, dst }; }
        static Terminator unreachable() { return { Unreachable }; }

      protected:

        void dump(int indent) const;

        friend class MIR;
    };

    //-------------------------- Block --------------------------------------
    //-----------------------------------------------------------------------

    class Block
    {
      public:

        std::vector<Statement> statements;

        Terminator terminator;

      protected:

        void dump(int indent, size_t idx) const;

        friend class MIR;
    };

    //-------------------------- VarInfo ------------------------------------
    //-----------------------------------------------------------------------

    struct VarInfo
    {
      local_t local;
      VarDecl *vardecl;
    };

    //-------------------------- LineInfo -----------------------------------
    //-----------------------------------------------------------------------

    struct LineInfo
    {
      block_t block;
      statement_t statement;
      int lineno;
    };

    //-------------------------- Fragment -----------------------------------
    //-----------------------------------------------------------------------

    struct Fragment
    {
      MIR::Local type;
      MIR::RValue value;

      void dump(int indent) const;

      explicit operator bool() const { return type.type; }
    };

  public:

    FnSig fx;

    std::vector<Local> locals;
    std::vector<Block> blocks;

    std::vector<std::tuple<local_t, RValue>> statics;

  public:

    bool throws;
    size_t args_beg;
    size_t args_end;

    std::vector<VarInfo> varinfos;
    std::vector<LineInfo> lineinfos;

    local_t add_local(Local local) { locals.push_back(std::move(local)); return locals.size() - 1; }
    block_t add_block(Block block) { blocks.push_back(std::move(block)); return blocks.size() - 1; }

    statement_t add_statement(Statement statement) { blocks.back().statements.push_back(std::move(statement)); return blocks.back().statements.size() - 1; }

    void add_varinfo(local_t local, VarDecl *vardecl) { varinfos.push_back(VarInfo{ local, vardecl }); }
    void add_lineinfo(block_t block, statement_t statement, int lineno) { lineinfos.push_back(LineInfo{ block, statement, lineno }); }

    void dump() const;

  public:

    template<typename T, typename ...Args>
    T *make_decl(Args&&... args);

    template<typename T, typename ...Args>
    T *make_expr(Args&&... args);
};

//|///////////////////// make_decl //////////////////////////////////////////
template<typename T, typename ...Args>
T *MIR::make_decl(Args&&... args)
{
  return new T(std::forward<Args>(args)...);
}

//|///////////////////// make_expr //////////////////////////////////////////
template<typename T, typename ...Args>
T *MIR::make_expr(Args&&... args)
{
  return new T(std::forward<Args>(args)...);
}

//|///////////////////// functions //////////////////////////////////////////

MIR::Block &insert_blocks(MIR &mir, MIR::block_t position, size_t count = 1);

MIR::Statement *find_assignment(MIR &mir, MIR::local_t dst, MIR::Block &block, MIR::Statement &statement);

// misc

std::ostream &operator <<(std::ostream &os, FnSig const &fn);
std::ostream &operator <<(std::ostream &os, MIR::Local const &local);
std::ostream &operator <<(std::ostream &os, MIR::RValue::ConstantData const &constant);
std::ostream &operator <<(std::ostream &os, MIR::RValue::VariableData const &variable);
std::ostream &operator <<(std::ostream &os, MIR::RValue::CallData const &call);
std::ostream &operator <<(std::ostream &os, MIR::RValue const &rvalue);
std::ostream &operator <<(std::ostream &os, MIR::Statement const &statement);
std::ostream &operator <<(std::ostream &os, MIR::Terminator const &terminator);

void dump_mir(MIR const &mir);
