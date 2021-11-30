//
// lifetime.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "lifetime.h"
#include "lower.h"
#include "diag.h"
#include <unordered_set>
#include <iostream>

using namespace std;

namespace
{
  struct Context
  {
    Diag &diag;

    struct Storage
    {
      bool live = false;
      bool consumed = false;
      unordered_set<MIR::local_t> depends_upon;
    };

    struct Thread
    {
      MIR::block_t block;
      vector<Storage> locals;

      Thread(MIR::block_t block, vector<Storage> locals)
        : block(block),
          locals(std::move(locals))
      {
      }
    };

    vector<Thread> threads;

    void add_thread(MIR::block_t block, vector<Storage> locals)
    {
      threads.push_back(Thread(block, std::move(locals)));
    }

    Type *ptrliteraltype;

    TypeTable &typetable;

    Context(TypeTable &typetable, Diag &diag)
      : diag(diag),
        typetable(typetable)
    {
      ptrliteraltype = type(Builtin::Type_PtrLiteral);
    }
  };

  //|///////////////////// analyse_assign_variable //////////////////////////
  void analyse_assign_variable(Context &ctx, MIR const &mir, MIR::local_t dst, MIR::RValue::VariableData const &variable)
  {
    auto &[op, arg, fields, loc] = variable;

    switch(op)
    {
      case MIR::RValue::Val:
        if (all_of(fields.begin(), fields.end(), [](auto k){ return k.op != MIR::RValue::Val; }))
          ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[arg].depends_upon;
        break;

      case MIR::RValue::Ref:
        if (all_of(fields.begin(), fields.end(), [](auto k){ return k.op != MIR::RValue::Val; }))
          ctx.threads[0].locals[dst].depends_upon.insert(arg);
        break;

      case MIR::RValue::Fer:
        if (all_of(fields.begin(), fields.end(), [](auto k){ return k.op != MIR::RValue::Val; }))
          for(auto dep : ctx.threads[0].locals[arg].depends_upon)
            ctx.threads[0].locals[dst].depends_upon.merge(ctx.threads[0].locals[dep].depends_upon);
        break;

      case MIR::RValue::Idx:
        assert(false);
        break;
    }
  }

  //|///////////////////// analyse_call /////////////////////////////////////
  void analyse_call(Context &ctx, MIR const &mir, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (callee.fn->flags & FunctionDecl::Destructor)
      return;

    if (callee.fn->name == Ident::op_assign)
    {
      for(auto i : ctx.threads[0].locals[args[0]].depends_upon)
        ctx.threads[0].locals[i].consumed = false;
    }

    for(auto arg : args)
    {
      for(auto i : ctx.threads[0].locals[arg].depends_upon)
      {
        if (!ctx.threads[0].locals[i].live)
          ctx.diag.error("potentially dangling variable access", mir.fx.fn, loc);

        if (ctx.threads[0].locals[i].consumed)
          ctx.diag.error("potentially consumed variable access", mir.fx.fn, loc);
      }
    }

    if (callee.fn->flags & FunctionDecl::Builtin)
    {
      switch(callee.fn->builtin)
      {
        case Builtin::Assign:
          for(auto dep : ctx.threads[0].locals[args[0]].depends_upon)
            ctx.threads[0].locals[dep].depends_upon = ctx.threads[0].locals[args[1]].depends_upon;
          ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[args[0]].depends_upon;
          break;

        case Builtin::PreInc:
        case Builtin::PreDec:
          ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[args[0]].depends_upon;
          break;

        case Builtin::OffsetAdd:
        case Builtin::OffsetSub:
          ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[args[0]].depends_upon;
          break;

        case Builtin::ArrayData:
        case Builtin::ArrayIndex:
        case Builtin::ArrayBegin:
        case Builtin::ArrayEnd:
          ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[args[0]].depends_upon;
          break;

        case Builtin::DeRef:
          ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[args[0]].depends_upon;
          break;

        default:
          break;
      }
    }

    if (callee.fn->flags & FunctionDecl::Lifetimed)
    {
      for(auto attr : callee.fn->attributes)
      {
        auto attribute = decl_cast<AttributeDecl>(attr);

        if (attribute->name == "lifetime")
        {
          if (attribute->options.substr(1, 7) == "consume")
          {
            for(auto dep : ctx.threads[0].locals[args[0]].depends_upon)
              ctx.threads[0].locals[dep].consumed = true;
          }
        }
      }
    }
  }

  //|///////////////////// analyse_cast /////////////////////////////////////
  void analyse_cast(Context &ctx, MIR const &mir, MIR::local_t dst, MIR::RValue::CastData const &cast)
  {
    auto &[arg, loc] = cast;

    ctx.threads[0].locals[dst].depends_upon = ctx.threads[0].locals[arg].depends_upon;
  }

  //|///////////////////// analyse_assign_statement /////////////////////////
  void analyse_assign_statement(Context &ctx, MIR const &mir, MIR::Statement const &statement)
  {
    auto &src = statement.src;
    auto &dst = statement.dst;

    switch (src.kind())
    {
      case MIR::RValue::Empty:
        break;

      case MIR::RValue::Constant:
        break;

      case MIR::RValue::Variable:
        analyse_assign_variable(ctx, mir, dst, src.get<MIR::RValue::Variable>());
        break;

      case MIR::RValue::Call:
        analyse_call(ctx, mir, dst, src.get<MIR::RValue::Call>());
        break;

      case MIR::RValue::Cast:
        analyse_cast(ctx, mir, dst, src.get<MIR::RValue::Cast>());
        break;
    }
  }

  //|///////////////////// analyse_construct_statement //////////////////////
  void analyse_construct_statement(Context &ctx, MIR const &mir, MIR::Statement const &statement)
  {
  }

  //|///////////////////// analyse_storage_live /////////////////////////////
  void analyse_storage_live(Context &ctx, MIR const &mir, MIR::Statement const &statement)
  {
    ctx.threads[0].locals[statement.dst].live = true;
  }

  //|///////////////////// analyse_storage_dead /////////////////////////////
  void analyse_storage_dead(Context &ctx, MIR const &mir, MIR::Statement const &statement)
  {
    ctx.threads[0].locals[statement.dst].live = false;
  }

  //|///////////////////// analyse //////////////////////////////////////////
  void analyse(Context &ctx, MIR const &mir)
  {
    if (mir.fx.fn->flags & FunctionDecl::Defaulted)
      return;

    ctx.add_thread(0, vector<Context::Storage>(mir.locals.size() + mir.args_end));

    for(auto arg = mir.args_beg; arg != mir.args_end; ++arg)
    {
      ctx.threads[0].locals[arg].live = true;

      if (is_reference_type(mir.locals[arg].type))
      {
        ctx.threads[0].locals[arg + mir.locals.size()].live = true;
        ctx.threads[0].locals[arg].depends_upon.insert(arg + mir.locals.size());
      }
    }

    for(size_t block_id = 0; block_id < mir.blocks.size(); ++block_id)
    {
      auto &block = mir.blocks[block_id];

      auto j = find_if(ctx.threads.begin(), ctx.threads.end(), [&](auto &k) { return k.block == block_id; });

      if (j == ctx.threads.end())
        continue;

      if (j != ctx.threads.begin())
        std::swap(ctx.threads.front(), *j);

      for(size_t i = 1; i != ctx.threads.size(); )
      {
        if (ctx.threads[i].block <= block_id)
        {
          if (ctx.threads[i].block == block_id)
          {
            for(size_t k = 0; k < ctx.threads[0].locals.size(); ++k)
              ctx.threads[0].locals[k].depends_upon.merge(ctx.threads[i].locals[k].depends_upon);
          }

          ctx.threads.erase(ctx.threads.begin() + i);

          continue;
        }

        ++i;
      }

      for(auto &statement : block.statements)
      {
//        cout << statement << endl;

        switch (statement.kind)
        {
          case MIR::Statement::NoOp:
            break;

          case MIR::Statement::Assign:
            analyse_assign_statement(ctx, mir, statement);
            break;

          case MIR::Statement::Construct:
            analyse_construct_statement(ctx, mir, statement);
            break;

          case MIR::Statement::StorageLive:
            analyse_storage_live(ctx, mir, statement);
            break;

          case MIR::Statement::StorageDead:
            analyse_storage_dead(ctx, mir, statement);
            break;
        }
      }

      switch (block.terminator.kind)
      {
        case MIR::Terminator::Return:
          break;

        case MIR::Terminator::Goto:
          ctx.threads[0].block = block.terminator.blockid;
          break;

        case MIR::Terminator::Switch:
          ctx.threads[0].block = block.terminator.blockid;
          for(auto &[value, block]: block.terminator.targets)
            if (block > block_id)
              ctx.add_thread(block, ctx.threads[0].locals);
          break;

        case MIR::Terminator::Catch:
          ctx.threads[0].block = block.terminator.blockid + 1;
          break;

        case MIR::Terminator::Throw:
          ctx.threads[0].block = block.terminator.blockid;
          break;

        case MIR::Terminator::Unreachable:
          break;
      }
    }

    for(auto arg = mir.args_beg; arg != mir.args_end; ++arg)
      ctx.threads[0].locals[arg].live = false;

    for(auto i : ctx.threads[0].locals[0].depends_upon)
    {
      if (!ctx.threads[0].locals[i].live)
        ctx.diag.error("potentially dangling return value", mir.fx.fn, mir.fx.fn->loc());
    }
  }
}


//|--------------------- Lifetime -------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// lifetime ///////////////////////////////////////////
void lifetime(MIR const &mir, TypeTable &typetable, Diag &diag)
{
  Context ctx(typetable, diag);

#if 0
  dump_mir(mir);
#endif

  if (ctx.diag.has_errored())
    return;

  analyse(ctx, mir);
}
