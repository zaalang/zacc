//
// codegen.h
//
// Copyright (c) 2020-2024 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "ast.h"

std::string get_default_triple();

//-------------------------- CodeGen ----------------------------------------
//---------------------------------------------------------------------------

struct GenOpts
{
  std::string modulename = "zaan";

  std::string cpu = "generic";
  std::string features = "";

  std::string triple = get_default_triple();

  enum class OutputType { EmitLL, EmitAsm, EmitObj } outputtype = OutputType::EmitObj;
  enum class OptLevel { None, Less, Default, Aggressive } optlevel = OptLevel::None;

  enum class Reloc { None, PIC } reloc = Reloc::None;
  enum class RedZone { None, Yes } redzone = RedZone::Yes;
  enum class CodeModel { None, Tiny, Small, Kernel, Medium, Large } model = CodeModel::None;
  enum class StackProtect { None, Yes } stackprotect = StackProtect::Yes;

  enum class DebugInfo { None, Dwarf, CodeView } debuginfo = DebugInfo::None;
  enum class CheckedMode { Checked, Unchecked } checkmode = CheckedMode::Checked;

  bool linker = true;
  bool dump_mir = false;

  std::vector<char const *> llvmargs;
};

void codegen(AST *ast, std::string const &target, GenOpts const &genopts, class Diag &diag);
