# `reopt-vcg` setup and usage

`reopt-vcg` is developed using the [Lean 4](https://github.com/leanprover/lean4) programming language (which is currently in-development as well).

## Dependencies

The following dependencies should be installed before installing `reopt-vcg`:

```
curl
git
gcc
g++
make
libgmp-dev
zlib1g-dev
lib32z1-dev
clang-8
llvm-8
```

On MacOS dependencies such as `llvm-8` can be installed via a package manager
such as [homebrew](https://brew.sh/), e.g. `brew install llvm@8`.

## Cloning and Building

First, `git clone` the repository and run `git submodule update --init` within it
to acquire the necessary submodules.

Once the dependencies are installed and repository/submodules are cloned, running the
`build.sh` script from the root directory will do the following:

1. ensure an appropriate version of `lean` is installed (using
[elan](https://github.com/leanprover/elan)),

2. ensure an `llvm-config` for LLVM version 8.0.* is available (set
the `LLVM_CONFIG` environment variable if necessary), and

3. build `reopt-vcg` and place the executable at `build/bin/reopt-vcg`.

## Development

In addition to building the project, the `Makefile` will generate a script
`set_lean_env_vars.sh` which can be used to set the `LEAN_PATH` and
`LEAN_SRC_PATH` environment variables. This will allow Lean 4's language server
to provide live feedback and information while perusing/editing `*.lean` files in
the project.

The editor modes listed below rely on the aforementioned Lean environment
variables being populated. (In the future, this project may be restructured to
use `leanpkg.toml`s at which point `set_lean_env_vars.sh` would be unnecessary.)

### VSCode

The [lean4](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) extension for
VSCode is a convenient way to edit and browse the lean code in this project.

E.g.,
```
$ ./build.sh
...
$ source ./set_lean_env_vars.sh
$ code .
```

and then open any `*.lean` file.

### Emacs

An Emacs
[lean4-mode](https://github.com/leanprover/lean4/tree/master/lean4-mode) is also
available, and should work after building and setting the environment variables
(as described in the VSCode extension section).




## Usage

Once built, `reopt-vcg` can be run on the example `reopt`-produced annotation files in `test-programs`, e.g.:

```
$ cd test-programs
$ ../build/bin/reopt-vcg --kbackend nweb23_static_freebsd.ann 
Generating verification conditions for LLVM module...
..............................
FAIL
    setpgrp.block_0_400f00.0 @ 0x400f00: return address is next instruction
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/setpgrp_block_0_400f00_3.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/setpgrp_block_0_400f00_3.smt2`
.....................
FAIL
    leapcorr.block_0_40c120.1 @ 0x40c120: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/leapcorr_block_0_40c120_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/leapcorr_block_0_40c120_1.smt2`
..................................................
FAIL
    leapcorr.block_0_40c158.3 @ 0x40c15c: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/leapcorr_block_0_40c158_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/leapcorr_block_0_40c158_1.smt2`
......................................................................................................................................................................................................
FAIL
    _rtld_thread_init.block_0_40e3e0.0 @ 0x40e3e7: return address is next instruction
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/_rtld_thread_init_block_0_40e3e0_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/_rtld_thread_init_block_0_40e3e0_1.smt2`
........................................................................................................................................................................
FAIL
    _none_mbrtowc.block_0_413af8.1 @ 0x413af8: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/_none_mbrtowc_block_0_413af8_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/_none_mbrtowc_block_0_413af8_1.smt2`
..............
FAIL
    _none_mbrtowc.block_0_413afd.1 @ 0x413aff: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/_none_mbrtowc_block_0_413afd_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/_none_mbrtowc_block_0_413afd_1.smt2`
.........................................................
FAIL
    _none_mbsnrtowcs.block_0_413c4e.2 @ 0x413c51: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/_none_mbsnrtowcs_block_0_413c4e_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/_none_mbsnrtowcs_block_0_413c4e_1.smt2`
..................................................................
FAIL
    _none_mbsnrtowcs.block_0_413c5b.1 @ 0x413c5b: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/_none_mbsnrtowcs_block_0_413c5b_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/_none_mbsnrtowcs_block_0_413c5b_1.smt2`
................................................................................
FAIL
    _none_mbsnrtowcs.block_0_413c76.1 @ 0x413c76: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/_none_mbsnrtowcs_block_0_413c76_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/_none_mbsnrtowcs_block_0_413c76_1.smt2`
............................................................................................................................
FAIL
    _none_mbsnrtowcs.block_0_413cb9.1 @ 0x413cb9: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/_none_mbsnrtowcs_block_0_413cb9_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/_none_mbsnrtowcs_block_0_413cb9_1.smt2`
.................................................................................
FAIL
    strnlen.block_0_413ce5.1 @ 0x413ce7: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/strnlen_block_0_413ce5_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/strnlen_block_0_413ce5_1.smt2`
.....................................
FAIL
    strnlen.block_0_413cf0.2 @ 0x413cf0: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/strnlen_block_0_413cf0_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/strnlen_block_0_413cf0_1.smt2`
................................................................................................................
FAIL
    __rshift_D2A.block_0_41812c.4 @ 0x41812c: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__rshift_D2A_block_0_41812c_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__rshift_D2A_block_0_41812c_1.smt2`
................................
FAIL
    __rshift_D2A.block_0_418146.1 @ 0x418146: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__rshift_D2A_block_0_418146_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__rshift_D2A_block_0_418146_1.smt2`
...........................................................................................................................
FAIL
    __rshift_D2A.block_0_418190.1 @ 0x418190: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__rshift_D2A_block_0_418190_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__rshift_D2A_block_0_418190_1.smt2`
.......................................................................
FAIL
    __strcp_D2A.block_0_418530.1 @ 0x418530: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__strcp_D2A_block_0_418530_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__strcp_D2A_block_0_418530_1.smt2`
.....................................
FAIL
    __strcp_D2A.block_0_418540.2 @ 0x418540: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__strcp_D2A_block_0_418540_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__strcp_D2A_block_0_418540_1.smt2`
.....................................................................
FAIL
    memchr.block_0_419447.1 @ 0x419447: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/memchr_block_0_419447_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/memchr_block_0_419447_1.smt2`
.................................................................................................
FAIL
    __sread.block_0_419f80.2 @ 0x419f84: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__sread_block_0_419f80_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__sread_block_0_419f80_1.smt2`
...........................
FAIL
    cfgetospeed.block_0_419fa0.2 @ 0x419fa0: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/cfgetospeed_block_0_419fa0_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/cfgetospeed_block_0_419fa0_1.smt2`
............
FAIL
    cfgetispeed.block_0_419fb0.2 @ 0x419fb0: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/cfgetispeed_block_0_419fb0_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/cfgetispeed_block_0_419fb0_1.smt2`
..................................................
FAIL
    cfmakeraw.block_0_419ff0.1 @ 0x419ff0: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/cfmakeraw_block_0_419ff0_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/cfmakeraw_block_0_419ff0_1.smt2`
..
FAIL
    cfmakeraw.block_0_419ff0.4 @ 0x419ff2: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/cfmakeraw_block_0_419ff0_3.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/cfmakeraw_block_0_419ff0_3.smt2`
....
FAIL
    cfmakeraw.block_0_419ff0.10 @ 0x419ff6: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/cfmakeraw_block_0_419ff0_7.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/cfmakeraw_block_0_419ff0_7.smt2`
....................................
FAIL
    cfmakesane.block_0_41a340.19 @ 0x41a36d: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/cfmakesane_block_0_41a340_13.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/cfmakesane_block_0_41a340_13.smt2`
..................................................................................
FAIL
    __get_current_messages_locale.block_0_41c8a0.1 @ 0x41c8a0: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__get_current_messages_locale_block_0_41c8a0_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__get_current_messages_locale_block_0_41c8a0_1.smt2`
........................................................
FAIL
    _MSKanji_mbsinit.block_0_41d4da.1 @ 0x41d4dc: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/_MSKanji_mbsinit_block_0_41d4da_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/_MSKanji_mbsinit_block_0_41d4da_1.smt2`
..................................................................
FAIL
    _GBK_mbsinit.block_0_41d7ba.1 @ 0x41d7bc: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/_GBK_mbsinit_block_0_41d7ba_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/_GBK_mbsinit_block_0_41d7ba_1.smt2`
..................................................................
FAIL
    _GB2312_mbsinit.block_0_41d95a.1 @ 0x41d95c: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/_GB2312_mbsinit_block_0_41d95a_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/_GB2312_mbsinit_block_0_41d95a_1.smt2`
..................................................................
FAIL
    _GB18030_mbsinit.block_0_41db5a.1 @ 0x41db5c: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/_GB18030_mbsinit_block_0_41db5a_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/_GB18030_mbsinit_block_0_41db5a_1.smt2`
............................................
FAIL
    _EUC_mbsinit.block_0_41de3a.2 @ 0x41de3c: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/_EUC_mbsinit_block_0_41de3a_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/_EUC_mbsinit_block_0_41de3a_1.smt2`
..................................................................
FAIL
    _BIG5_mbsinit.block_0_41e36a.1 @ 0x41e36c: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/_BIG5_mbsinit_block_0_41e36a_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/_BIG5_mbsinit_block_0_41e36a_1.smt2`
..........................................................................................................
FAIL
    _UTF8_mbsinit.block_0_41eb5a.2 @ 0x41eb5c: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/_UTF8_mbsinit_block_0_41eb5a_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/_UTF8_mbsinit_block_0_41eb5a_1.smt2`
................................
FAIL
    __printf_render_n.block_0_420020.2 @ 0x420020: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420020_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420020_1.smt2`
............................
FAIL
    __printf_render_n.block_0_420027.1 @ 0x420027: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420027_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420027_1.smt2`
..
FAIL
    __printf_render_n.block_0_420027.3 @ 0x42002a: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420027_3.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420027_3.smt2`
..
FAIL
    __printf_render_n.block_0_420027.6 @ 0x42002d: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420027_5.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420027_5.smt2`
.......................
FAIL
    __printf_render_n.block_0_420035.2 @ 0x420035: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420035_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420035_1.smt2`
............................
FAIL
    __printf_render_n.block_0_42003e.1 @ 0x42003e: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_42003e_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_42003e_1.smt2`
..
FAIL
    __printf_render_n.block_0_42003e.3 @ 0x420041: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_42003e_3.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_42003e_3.smt2`
..
FAIL
    __printf_render_n.block_0_42003e.6 @ 0x420044: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_42003e_5.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_42003e_5.smt2`
..............
FAIL
    __printf_render_n.block_0_420050.2 @ 0x420050: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420050_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420050_1.smt2`
..........................
FAIL
    __printf_render_n.block_0_420059.2 @ 0x420059: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420059_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420059_1.smt2`
..........................
FAIL
    __printf_render_n.block_0_420062.2 @ 0x420062: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420062_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420062_1.smt2`
..........................
FAIL
    __printf_render_n.block_0_42006b.2 @ 0x42006b: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_42006b_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_42006b_1.smt2`
..........................
FAIL
    __printf_render_n.block_0_420072.2 @ 0x420072: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420072_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420072_1.smt2`
..........................
FAIL
    __printf_render_n.block_0_420079.2 @ 0x420079: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420079_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420079_1.smt2`
..........................
FAIL
    __printf_render_n.block_0_420080.1 @ 0x420080: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420080_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420080_1.smt2`
..
FAIL
    __printf_render_n.block_0_420080.3 @ 0x420083: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420080_3.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420080_3.smt2`
..
FAIL
    __printf_render_n.block_0_420080.6 @ 0x420086: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420080_5.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420080_5.smt2`
.............
FAIL
    __printf_render_n.block_0_420090.1 @ 0x420090: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420090_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420090_1.smt2`
..
FAIL
    __printf_render_n.block_0_420090.3 @ 0x420093: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420090_3.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420090_3.smt2`
..
FAIL
    __printf_render_n.block_0_420090.6 @ 0x420096: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_render_n_block_0_420090_5.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_render_n_block_0_420090_5.smt2`
....................................
FAIL
    register_printf_function.block_0_4200ad.9 @ 0x4200be: LLVM and machine code store to same heap address
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/register_printf_function_block_0_4200ad_2.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/register_printf_function_block_0_4200ad_2.smt2`
..............................................
FAIL
    register_printf_render.block_0_4200ed.9 @ 0x4200fe: LLVM and machine code store to same heap address
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/register_printf_render_block_0_4200ed_2.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/register_printf_render_block_0_4200ed_2.smt2`
....................................
FAIL
    fileno_unlocked.block_0_421fd0.2 @ 0x421fd0: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/fileno_unlocked_block_0_421fd0_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/fileno_unlocked_block_0_421fd0_1.smt2`
.........................................
FAIL
    __printf_arginfo_int.block_0_424c0d.4 @ 0x424c13: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_arginfo_int_block_0_424c0d_3.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_arginfo_int_block_0_424c0d_3.smt2`
...........................
FAIL
    __printf_arginfo_int.block_0_424c1a.2 @ 0x424c1a: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_arginfo_int_block_0_424c1a_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_arginfo_int_block_0_424c1a_1.smt2`
............................................................
FAIL
    __printf_arginfo_int.block_0_424c43.2 @ 0x424c43: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_arginfo_int_block_0_424c43_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_arginfo_int_block_0_424c43_1.smt2`
...........................
FAIL
    __printf_arginfo_int.block_0_424c4c.2 @ 0x424c4c: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_arginfo_int_block_0_424c4c_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_arginfo_int_block_0_424c4c_1.smt2`
..................................................
FAIL
    __printf_arginfo_int.block_0_424c70.2 @ 0x424c70: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_arginfo_int_block_0_424c70_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_arginfo_int_block_0_424c70_1.smt2`
...........................
FAIL
    __printf_arginfo_int.block_0_424c79.2 @ 0x424c79: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_arginfo_int_block_0_424c79_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_arginfo_int_block_0_424c79_1.smt2`
.................................................
FAIL
    __printf_arginfo_int.block_0_424c92.2 @ 0x424c92: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_arginfo_int_block_0_424c92_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_arginfo_int_block_0_424c92_1.smt2`
....................................
FAIL
    __printf_arginfo_int.block_0_424cbb.2 @ 0x424cbb: read heap address not in stack space
    Verification failed: the SMT query returned `sat`

    To see the output, run `reopt-vcg nweb23_static_freebsd.ann --export <dir>`
    The SMT query will be stored in <dir>/__printf_arginfo_int_block_0_424cbb_1.smt2
    The default invocation of CVC4 for these queries is as follows:
      `cvc4 --lang=smt2 --arrays-exp --no-fmf-bound --incremental <dir>/__printf_arginfo_int_block_0_424cbb_1.smt2`
................................
======================= 55 VC GENERATION WARNINGS =======================
leapcorr.block_0_40c120.1 @ 0x40c120: LLVM alignment of 4  is unchecked.
leapcorr.block_0_40c158.3 @ 0x40c158: LLVM alignment of 8  is unchecked.
_none_mbsnrtowcs.block_0_413c4e.2 @ 0x413c4e: LLVM alignment of 8  is unchecked.
_none_mbsnrtowcs.block_0_413cb9.1 @ 0x413cb9: LLVM alignment of 8  is unchecked.
__rshift_D2A.block_0_41812c.4 @ 0x41812c: LLVM alignment of 4  is unchecked.
__rshift_D2A.block_0_418146.1 @ 0x418146: LLVM alignment of 4  is unchecked.
__rshift_D2A.block_0_418146.13 @ 0x418151: LLVM alignment of 4  is unchecked.
__rshift_D2A.block_0_418190.1 @ 0x418190: LLVM alignment of 4  is unchecked.
__sread.block_0_419f80.2 @ 0x419f80: LLVM alignment of 2  is unchecked.
cfgetospeed.block_0_419fa0.2 @ 0x419fa0: LLVM alignment of 4  is unchecked.
cfgetispeed.block_0_419fb0.2 @ 0x419fb0: LLVM alignment of 4  is unchecked.
cfmakeraw.block_0_419ff0.1 @ 0x419ff0: LLVM alignment of 4  is unchecked.
cfmakeraw.block_0_419ff0.4 @ 0x419ff0: LLVM alignment of 4  is unchecked.
cfmakeraw.block_0_419ff0.10 @ 0x419ff2: LLVM alignment of 4  is unchecked.
cfmakeraw.block_0_419ff0.26 @ 0x41a00d: LLVM alignment of 4  is unchecked.
cfmakesane.block_0_41a340.19 @ 0x41a366: LLVM alignment of 8  is unchecked.
cfmakesane.block_0_41a340.23 @ 0x41a374: LLVM alignment of 8  is unchecked.
cfmakesane.block_0_41a340.28 @ 0x41a37f: LLVM alignment of 4  is unchecked.
__get_current_messages_locale.block_0_41c8a0.1 @ 0x41c8a0: LLVM alignment of 4  is unchecked.
_MSKanji_mbsinit.block_0_41d4da.1 @ 0x41d4da: LLVM alignment of 4  is unchecked.
_GBK_mbsinit.block_0_41d7ba.1 @ 0x41d7ba: LLVM alignment of 4  is unchecked.
_GB2312_mbsinit.block_0_41d95a.1 @ 0x41d95a: LLVM alignment of 4  is unchecked.
_GB18030_mbsinit.block_0_41db5a.1 @ 0x41db5a: LLVM alignment of 4  is unchecked.
_EUC_mbsinit.block_0_41de3a.2 @ 0x41de3a: LLVM alignment of 4  is unchecked.
_BIG5_mbsinit.block_0_41e36a.1 @ 0x41e36a: LLVM alignment of 4  is unchecked.
_UTF8_mbsinit.block_0_41eb5a.2 @ 0x41eb5a: LLVM alignment of 4  is unchecked.
__printf_render_n.block_0_420020.2 @ 0x420020: LLVM alignment of 4  is unchecked.
__printf_render_n.block_0_420027.1 @ 0x420027: LLVM alignment of 8  is unchecked.
__printf_render_n.block_0_420027.3 @ 0x420027: LLVM alignment of 8  is unchecked.
__printf_render_n.block_0_420027.6 @ 0x42002a: LLVM alignment of 4  is unchecked.
__printf_render_n.block_0_420035.2 @ 0x420035: LLVM alignment of 4  is unchecked.
__printf_render_n.block_0_42003e.1 @ 0x42003e: LLVM alignment of 8  is unchecked.
__printf_render_n.block_0_42003e.3 @ 0x42003e: LLVM alignment of 8  is unchecked.
__printf_render_n.block_0_42003e.6 @ 0x420041: LLVM alignment of 4  is unchecked.
__printf_render_n.block_0_420050.2 @ 0x420050: LLVM alignment of 4  is unchecked.
__printf_render_n.block_0_420059.2 @ 0x420059: LLVM alignment of 4  is unchecked.
__printf_render_n.block_0_420062.2 @ 0x420062: LLVM alignment of 4  is unchecked.
__printf_render_n.block_0_42006b.2 @ 0x42006b: LLVM alignment of 4  is unchecked.
__printf_render_n.block_0_420072.2 @ 0x420072: LLVM alignment of 4  is unchecked.
__printf_render_n.block_0_420079.2 @ 0x420079: LLVM alignment of 4  is unchecked.
__printf_render_n.block_0_420080.1 @ 0x420080: LLVM alignment of 8  is unchecked.
__printf_render_n.block_0_420080.3 @ 0x420080: LLVM alignment of 8  is unchecked.
__printf_render_n.block_0_420080.6 @ 0x420083: LLVM alignment of 4  is unchecked.
__printf_render_n.block_0_420090.1 @ 0x420090: LLVM alignment of 8  is unchecked.
__printf_render_n.block_0_420090.3 @ 0x420090: LLVM alignment of 8  is unchecked.
__printf_render_n.block_0_420090.6 @ 0x420093: LLVM alignment of 4  is unchecked.
fileno_unlocked.block_0_421fd0.2 @ 0x421fd0: LLVM alignment of 2  is unchecked.
__printf_arginfo_int.block_0_424c0d.4 @ 0x424c0d: LLVM alignment of 4  is unchecked.
__printf_arginfo_int.block_0_424c1a.2 @ 0x424c1a: LLVM alignment of 4  is unchecked.
__printf_arginfo_int.block_0_424c43.2 @ 0x424c43: LLVM alignment of 4  is unchecked.
__printf_arginfo_int.block_0_424c4c.2 @ 0x424c4c: LLVM alignment of 4  is unchecked.
__printf_arginfo_int.block_0_424c70.2 @ 0x424c70: LLVM alignment of 4  is unchecked.
__printf_arginfo_int.block_0_424c79.2 @ 0x424c79: LLVM alignment of 4  is unchecked.
__printf_arginfo_int.block_0_424c92.2 @ 0x424c92: LLVM alignment of 4  is unchecked.
__printf_arginfo_int.block_0_424cbb.2 @ 0x424cbb: LLVM alignment of 4  is unchecked.

======================= 51 VC GENERATION ERRORS  =======================
function malloc_mutex_init: argument has unsupported type (%arg3 : <8 x double>)
function _pthread_mutex_init_calloc_cb_stub: argument has unsupported type (%arg3 : <8 x double>)
function pow2_ceil: argument has unsupported type (%arg1 : <8 x double>)
function extent_tree_ad_new: argument has unsupported type (%arg3 : <8 x double>)
function arena_run_tree_new: argument has unsupported type (%arg1 : <8 x double>)
function arena_run_trim_tail: argument has unsupported type (%arg6 : <8 x double>)
function __chk_fail: argument has unsupported type (%arg3 : <8 x double>)
function __stack_chk_fail_local: argument has unsupported type (%arg3 : <8 x double>)
function atoi: argument has unsupported type (%arg1 : <8 x double>)
function differ_by_repeat: argument has unsupported type (%arg3 : <8 x double>)
function increment_overflow: argument has unsupported type (%arg2 : <8 x double>)
function long_increment_overflow: argument has unsupported type (%arg2 : <8 x double>)
function offtime: argument has unsupported type (%arg6 : <8 x double>)
function gmtime_r: argument has unsupported type (%arg6 : <8 x double>)
function gmt_init: argument has unsupported type (%arg6 : <8 x double>)
function tzsetwall: argument has unsupported type (%arg6 : <8 x double>)
function tzset: argument has unsupported type (%arg3 : <8 x double>)
function gmtime_key_init: argument has unsupported type (%arg6 : <8 x double>)
function localtime_key_init: argument has unsupported type (%arg6 : <8 x double>)
function asctime: argument has unsupported type (%arg3 : <8 x double>)
function _rtld_addr_phdr: argument has unsupported type (%arg3 : <8 x double>)
function __clean_env_destructor: argument has unsupported type (%arg6 : <8 x double>)
function getprogname: argument has unsupported type (%arg0 : <8 x double>)
function __fpclassifyf: argument has unsupported type (%arg0 : <8 x double>)
function __freedtoa: argument has unsupported type (%arg6 : <8 x double>)
function __b2d_D2A: argument has unsupported type (%arg2 : <8 x double>)
function sigemptyset: argument has unsupported type (%arg1 : <8 x double>)
function sigfillset: argument has unsupported type (%arg3 : <8 x double>)
function _cleanup: argument has unsupported type (%arg6 : <8 x double>)
function _flockfile_debug_stub: argument has unsupported type (%arg6 : <8 x double>)
function __sseek: argument has unsupported type (%arg6 : <8 x double>)
function lseek: argument has unsupported type (%arg6 : <8 x double>)
function __error_unthreaded: argument has unsupported type (%arg3 : <8 x double>)
function __get_current_time_locale: argument has unsupported type (%arg0 : <8 x double>)
function __printf_init: argument has unsupported type (%arg3 : <8 x double>)
function __printf_render_pct: argument has unsupported type (%arg6 : <8 x double>)
function ftell: argument has unsupported type (%arg6 : <8 x double>)
function __get_current_numeric_locale: argument has unsupported type (%arg0 : <8 x double>)
function __get_current_monetary_locale: argument has unsupported type (%arg0 : <8 x double>)
function _fini: argument has unsupported type (%arg6 : <8 x double>)
_set_tp.block_0_400f50.0 @ 0x400f50: unexpected sort (Unexpected sort in wordAsType: {i64,i64,<8 x double>})
leapcorr.block_0_40c148.5 @ 0x40c156: unexpected sort (Unexpected sort in wordAsType: {i64,i1})
send.block_0_40e150.0 @ 0x40e156: unexpected sort (Unexpected sort in wordAsType: {i64,i64,<8 x double>})
__rshift_D2A.block_0_418100.8 @ 0x418112: unexpected sort (Unexpected sort in wordAsType: {i32,i1})
raise.block_0_4193a0.2 @ 0x4193a3: unexpected sort (Unexpected sort in wordAsType: {i64,i64,<8 x double>})
raise.block_0_4193a8.4 @ 0x4193ad: unexpected sort (Unexpected sort in wordAsType: {i64,i64,<8 x double>})
__sclose.block_0_419f40.5 @ 0x419f44: unexpected sort (Unexpected sort in wordAsType: {i64,i64,<8 x double>})
__swrite.block_0_419f60.7 @ 0x419f6b: unexpected sort (Unexpected sort in wordAsType: {i64,i64,<8 x double>})
tcdrain.block_0_41a020.0 @ 0x41a029: unexpected sort (Unexpected sort in wordAsType: {i64,<8 x double>})
tcgetattr.block_0_41a0b0.0 @ 0x41a0ba: unexpected sort (Unexpected sort in wordAsType: {i64,<8 x double>})
__printf_arginfo_int.block_0_424ca2.0 @ 0x424cb6: unexpected sort (Unexpected sort in wordAsType: {i64,i64,<8 x double>})

======================= VC GENERATION ERROR SUMMARY =======================
* (40) [module] argument has unsupported type
    - (5) %arg0 : <8 x double>
    - (4) %arg1 : <8 x double>
    - (3) %arg2 : <8 x double>
    - (12) %arg3 : <8 x double>
    - (16) %arg6 : <8 x double>
* (11) [block] unexpected sort
    - (1) Unexpected sort in wordAsType: {i32,i1}
    - (2) Unexpected sort in wordAsType: {i64,<8 x double>}
    - (1) Unexpected sort in wordAsType: {i64,i1}
    - (7) Unexpected sort in wordAsType: {i64,i64,<8 x double>}

23 out of 73 functions were assigned verification conditions without error.

====================== GOAL VERIFICATION SUMMARY =======================
2863 out of 2927 generated verification goals successfully proven.

64 goals failed to be verified:
* (60) read heap address not in stack space
    - (60) no additional information
* (2) LLVM and machine code store to same heap address
    - (2) no additional information
* (2) return address is next instruction
    - (2) no additional information
```
