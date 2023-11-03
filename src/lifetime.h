//
// lifetime.h
//
// Copyright (c) 2021-2023 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "lexer.h"
#include <string>
#include <vector>

struct Lifetime
{
  enum Type
  {
    unknown,

    consume,
    borrow,
    clone,
    depend,
    poison,
    assign,
    append,
    follow,
    launder,
    repose,
    swap,
    none,
  };

  Type type = unknown;
  SourceLocation loc;
  std::string_view text;
};

std::vector<Lifetime> parse_lifetime(std::string_view str, SourceLocation loc);

//-------------------------- Lifetime ---------------------------------------
//---------------------------------------------------------------------------

void lifetime(class MIR const &mir, struct TypeTable &typetable, class Diag &diag);
