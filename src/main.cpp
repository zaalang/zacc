//
// zacc
//
// Copyright (C) 2020-2022 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "sema.h"
#include "diag.h"
#include "lexer.h"
#include "parser.h"
#include "typer.h"
#include "lower.h"
#include "codegen.h"
#include "toolchain.h"
#include <iostream>
#include <string>
#include <cstring>
#include <algorithm>

#if defined _WIN32
#include <windows.h>
#endif

using namespace std;

//|//////////////////// main ////////////////////////////////////////////////
int main(int argc, char *argv[])
{
  Diag diag("zacc");

#if defined _WIN32
  HANDLE handle = GetStdHandle(STD_OUTPUT_HANDLE);
  DWORD mode = 0;
  GetConsoleMode(handle, &mode);
  SetConsoleMode(handle, mode | 0x0004);
#endif

  string input = "";

  for(int i = 0, j = 0; i < argc; ++i)
  {    
    if (argv[i][0] == '-')
    {
      if ((argv[i][1] == 'I' || argv[i][1] == 'L' || argv[i][1] == 'l' || argv[i][1] == 'o') && argv[i][2] == 0)
        ++i;

      continue;
    }

    if (j == 1)
      input = argv[i];

    ++j;
  }

  if (input == "")
  {
    cerr << "no input files\n";
    exit(1);
  }

  try
  {
    Sema sema;
    GenOpts opts;

    for(int i = 0; i < argc; ++i)
    {
      if (strncmp(argv[i], "-I", 2) == 0)
        sema.add_include_path(argv[i][2] != 0 ? argv[i] + 2 : argv[++i]);

      if (strncmp(argv[i], "-D", 2) == 0)
        sema.add_cfg(argv[i][2] != 0 ? argv[i] + 2 : argv[++i]);

      if (strncmp(argv[i], "--cfg", 5) == 0)
        sema.add_cfg(argv[i][5] != 0 ? argv[i] + 6 : argv[++i]);

      if (strcmp(argv[i], "--emit-asm") == 0)
        opts.outputtype = GenOpts::OutputType::EmitAsm;

      if (strcmp(argv[i], "--emit-ll") == 0)
        opts.outputtype = GenOpts::OutputType::EmitLL;

      if (strcmp(argv[i], "-g") == 0)
        opts.debuginfo = (opts.triple.find("msvc") != std::string::npos) ? GenOpts::DebugInfo::CodeView : GenOpts::DebugInfo::Dwarf;

      if (strcmp(argv[i], "-O1") == 0)
        opts.optlevel = GenOpts::OptLevel::Less;

      if (strcmp(argv[i], "-O2") == 0)
        opts.optlevel = GenOpts::OptLevel::Default;

      if (strcmp(argv[i], "-O3") == 0)
        opts.optlevel = GenOpts::OptLevel::Aggressive;

      if (strcmp(argv[i], "-fpic") == 0)
        opts.reloc = GenOpts::Reloc::PIC;

      if (strcmp(argv[i], "-funchecked") == 0)
        opts.checkmode = GenOpts::CheckedMode::Unchecked;

      if (strcmp(argv[i], "-fstack-protect") == 0)
        opts.stackprotect = GenOpts::StackProtect::Yes;

      if (strcmp(argv[i], "-fno-stack-protect") == 0)
        opts.stackprotect = GenOpts::StackProtect::None;

      if (strcmp(argv[i], "-mred-zone") == 0)
        opts.redzone = GenOpts::RedZone::Yes;

      if (strcmp(argv[i], "-mno-red-zone") == 0)
        opts.redzone = GenOpts::RedZone::None;

      if (strcmp(argv[i], "-mcmodel=kernel") == 0)
        opts.model = GenOpts::CodeModel::Kernel;

      if (strcmp(argv[i], "-mcmodel=large") == 0)
        opts.model = GenOpts::CodeModel::Large;

      if (strcmp(argv[i], "-c") == 0)
        opts.linker = false;

      if (strcmp(argv[i], "--dump-mir") == 0)
        opts.dump_mir = true;

      if (strncmp(argv[i], "--target", 8) == 0)
        opts.triple = argv[i][8] != 0 ? argv[i] + 9 : argv[++i];

      if (strncmp(argv[i], "--features", 10) == 0)
        opts.features = argv[i][10] != 0 ? argv[i] + 11 : argv[++i];

      if (strcmp(argv[i], "-mllvm") == 0)
        opts.llvmargs.push_back(argv[++i]);
    }

    if (opts.triple.find("linux") != std::string::npos)
      sema.add_cfg("os.linux");

    if (opts.triple.find("windows") != std::string::npos)
      sema.add_cfg("os.windows");

    if (opts.checkmode == GenOpts::CheckedMode::Checked)
      sema.add_cfg("zaa.build.checked");

    if (opts.outputtype != GenOpts::OutputType::EmitObj)
      opts.linker = false;

    opts.modulename = input;

    ToolChain toolchain(opts.triple);

    if (!toolchain)
    {
      cerr << "unable to initialise toolchain\n";
      exit(1);
    }

    string outfile = filename(toolchain, basename(input), opts.outputtype);

    for(int i = 0; i < argc; ++i)
    {
      if (strncmp(argv[i], "-o", 2) == 0)
        outfile = filename(toolchain, string_view(argv[i][2] != 0 ? argv[i] + 2 : argv[++i]), opts.outputtype);
    }

    sema.add_cfg("zaa.build.outdir=" + dirname(outfile));

    parse(input, sema, diag);

#if 0
    dump_ast(sema.ast);
    cout << "--" << endl;
#endif

    if (diag.has_errored())
    {
      cerr << diag;

      exit(1);
    }

    typer(sema.ast, sema, diag);

#if 0
    dump_ast(sema.ast);
    cout << "--" << endl;
#endif

    if (diag.has_errored())
    {
      cerr << diag;

      exit(1);
    }

    codegen(sema.ast, outfile, opts, diag);

    cerr << diag;

    if (diag.has_errored())
      exit(1);

    if (opts.linker)
    {
      string exefile = filename(toolchain, outfile, ToolChain::Executable);

      vector<string> libraries;

      for(int i = 0; i < argc; ++i)
      {
        if (strncmp(argv[i], "-L", 2) == 0)
          toolchain.add_library_path(argv[i][2] != 0 ? argv[i] + 2 : argv[++i]);

        if (strncmp(argv[i], "-l", 2) == 0)
          libraries.push_back(argv[i][2] != 0 ? argv[i] + 2 : argv[++i]);
      }

      toolchain.ld(outfile, exefile, libraries);
    }
  }
  catch(exception &e)
  {
    cerr << diag << endl;
    cerr << "Compiler Error: " << e.what() << endl;
    exit(1);
  }
}
