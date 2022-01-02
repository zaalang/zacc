//
// ast.h
//
// Copyright (C) 2020-2022 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "ident.h"
#include "decl.h"
#include "expr.h"
#include "stmt.h"
#include "type.h"

//-------------------------- AST --------------------------------------------
//---------------------------------------------------------------------------

class AST
{
  public:
    AST(Decl *root = nullptr);
    AST(AST const &) = delete;
    AST &operator=(AST const &) = delete;

    Decl *root;

    void dump() const;

  public:

    template<typename T, typename ...Args>
    T *make_decl(Args&&... args);

    template<typename T, typename ...Args>
    T *make_stmt(Args&&... args);

    template<typename T, typename ...Args>
    T *make_expr(Args&&... args);

    template<typename T, typename ...Args>
    T *make_type(Args&&... args);
};

//|///////////////////// make_decl //////////////////////////////////////////
template<typename T, typename ...Args>
T *AST::make_decl(Args&&... args)
{
  return new T(std::forward<Args>(args)...);
}

//|///////////////////// make_stmt //////////////////////////////////////////
template<typename T, typename ...Args>
T *AST::make_stmt(Args&&... args)
{
  return new T(std::forward<Args>(args)...);
}

//|///////////////////// make_expr //////////////////////////////////////////
template<typename T, typename ...Args>
T *AST::make_expr(Args&&... args)
{
  return new T(std::forward<Args>(args)...);
}

//|///////////////////// make_type //////////////////////////////////////////
template<typename T, typename ...Args>
T *AST::make_type(Args&&... args)
{
  return new T(std::forward<Args>(args)...);
}

// misc

void dump_ast(AST const *ast);
