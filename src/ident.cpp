//
// ident.cpp
//
// Copyright (c) 2021-2023 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "ident.h"
#include <iostream>
#include <charconv>
#include <cassert>

using namespace std;

//|///////////////////// print //////////////////////////////////////////////
std::ostream &operator <<(std::ostream &os, Ident const &ident)
{
  switch (ident.kind())
  {
    case Ident::String:
      os << ident.sv();
      break;

    case Ident::Index:
      os << '#' << static_cast<IndexIdent const &>(ident).value();
      break;

    case Ident::Hash:
      os << ident.sv();
      break;

    case Ident::Dollar:
      os << ident.sv();
      break;

    default:
      assert(false);
  }

  return os;
}

//|--------------------- StringIdent ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// StringIdent::Constructor ///////////////////////////
StringIdent::StringIdent(string_view value)
  : Ident(String),
    m_value(value)
{
}

//|--------------------- IndexIdent -----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// IndexIdent::Constructor ////////////////////////////
IndexIdent::IndexIdent(size_t value)
  : Ident(Index),
    m_value(value)
{
}

//|--------------------- HashIdent ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// HashIdent::Constructor /////////////////////////////
HashIdent::HashIdent(Ident *value)
  : Ident(Hash),
    m_value(value)
{
}

//|--------------------- DollarIdent ----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// DollarIdent::Constructor ///////////////////////////
DollarIdent::DollarIdent(uintptr_t value)
  : Ident(Dollar),
    m_value(value)
{
}

//|--------------------- Ident ----------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// Ident::Constructor /////////////////////////////////
Ident::Ident(Kind kind)
  : m_kind(kind)
{
}

//|///////////////////// from ///////////////////////////////////////////////
Ident *Ident::from(string_view value)
{
  static unordered_map<string_view, Ident*> stringtable;

  if (auto j = stringtable.find(value); j != stringtable.end())
    return j->second;

  auto ident = new StringIdent(value);

  stringtable.emplace(ident->sv(), ident);

  return ident;
}

//|///////////////////// make_index_ident ///////////////////////////////////
Ident *Ident::make_index_ident(string_view value)
{
  auto index = size_t(-1);

  if (auto [p, ec] = from_chars(value.data(), value.data() + value.length(), index); ec != std::errc())
    assert(false);

  return new IndexIdent(index);
}

Ident *Ident::make_index_ident(size_t value)
{
  return new IndexIdent(value);
}

//|///////////////////// make_hash_ident ////////////////////////////////////
Ident *Ident::make_hash_ident(string_view value)
{
  return new HashIdent(from(value));
}

//|///////////////////// make_dollar_ident //////////////////////////////////
Ident *Ident::make_dollar_ident(uintptr_t value)
{
  return new DollarIdent(value);
}
