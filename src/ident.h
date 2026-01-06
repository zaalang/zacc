//
// ident.h
//
// Copyright (c) 2021-2026 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include <string>
#include <string_view>
#include <unordered_map>
#include <cstdint>

//---------------------- Ident ----------------------------------------------
//---------------------------------------------------------------------------

class Ident
{
  public:

    enum Kind
    {
      String,
      Index,
      Hash,
      Dollar,
    };

  public:

    static Ident *from(std::string_view value);
    static Ident *make_index_ident(size_t value);
    static Ident *make_index_ident(std::string_view value);
    static Ident *make_hash_ident(std::string_view value);
    static Ident *make_dollar_ident(uintptr_t value);

    static inline Ident *kw_var = from("var");
    static inline Ident *kw_this = from("this");
    static inline Ident *kw_void = from("void");
    static inline Ident *kw_null = from("null");
    static inline Ident *kw_super = from("super");
    static inline Ident *kw_kind = from("kind");
    static inline Ident *kw_allocator = from("allocator");
    static inline Ident *kw_opt_allocator = from("allocator?");
    static inline Ident *kw_import = from("import");
    static inline Ident *kw_using = from("using");
    static inline Ident *kw_else = from("else");
    static inline Ident *kw_main = from("main");

    static inline Ident *op_call = from("()");
    static inline Ident *op_index = from("[]");
    static inline Ident *op_scope = from("::");
    static inline Ident *op_assign = from("=");
    static inline Ident *op_equality = from("==");
    static inline Ident *op_compare = from("<=>");
    static inline Ident *op_match = from("~=");
    static inline Ident *op_deref = from("*");
    static inline Ident *op_run = from("#run");
    static inline Ident *op_requires = from("#requires");

    static inline Ident *type_ptr = from("#ptr");
    static inline Ident *type_ref = from("#ref");
    static inline Ident *type_lit = from("#lit");
    static inline Ident *type_enum = from("#enum");
    static inline Ident *type_array = from("#array");
    static inline Ident *type_union = from("#union");
    static inline Ident *type_tuple = from("#tuple");
    static inline Ident *type_lambda = from("#lambda");
    static inline Ident *type_vtable = from("#vtable");

  public:

    Kind kind() const { return m_kind; }

    virtual std::string str() const = 0;
    virtual std::string_view sv() const = 0;

  protected:
    Ident(Kind kind);

    Kind m_kind;
};

class StringIdent : public Ident
{
  public:
    StringIdent(std::string_view value);

    virtual std::string str() const override { return m_value; }
    virtual std::string_view sv() const override { return m_value; }

  private:

    std::string m_value;
};

class IndexIdent : public Ident
{
  public:
    IndexIdent(size_t value);

    virtual std::string str() const override { return std::to_string(m_value); }
    virtual std::string_view sv() const override { return "#"; }

    size_t value() const { return m_value; }

  private:

    size_t m_value;
};

class HashIdent : public Ident
{
  public:
    HashIdent(Ident *value);

    virtual std::string str() const override { return "#"; }
    virtual std::string_view sv() const override { return "#"; }

    Ident *value() const { return m_value; }

  private:

    Ident *m_value;
};

class DollarIdent : public Ident
{
  public:
    DollarIdent(uintptr_t value);

    virtual std::string str() const override { return "$"; }
    virtual std::string_view sv() const override { return "$"; }

    uintptr_t value() const { return m_value; }

  private:

    uintptr_t m_value;
};

inline bool operator==(Ident const *lhs, std::string_view rhs)
{
  return lhs && lhs->sv() == rhs;
}

//
// misc functions
//

std::ostream &operator <<(std::ostream &os, Ident const &ident);
