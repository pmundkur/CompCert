## CompCert port to RV32G
This is a preliminary and very alpha port of CompCert 2.6 to 32-bit
RISC-V, specifically RV32G.  The port consumes C programs and
generates RV32G assembly files.  It currently uses the gcc newlib
toolchain as the backend to assemble and link RV32G binaries.

Please read the main CompCert readme for CompCert dependencies.  Note
that this is a port of CompCert version 2.6, requiring the older Coq
version 8.4 pl5.

## Setting up RV32G Dependencies

You will need the RISC-V [Newlib toolchain](https://github.com/riscv/riscv-tools/blob/master/README.md#newlibman).

**Important:** The RISC-V toolchain is often in a state of flux.  The
following has been tested with the _master_ branch of riscv-tools, as
of July 15th, 2016.  The submodules of riscv-tools will pull in most
of the appropriate versions of the toolchain submodules.  However, you
will need to update the riscv-isa-sim and riscv-pk submodules to their
latest _master_ versions as of July 15th.

When building the toolchain, you will need to enable 32-bit support:

1. Change the following line in build.sh
```
- build_project riscv-gnu-toolchain --prefix=$RISCV
+ build_project riscv-gnu-toolchain --prefix=$RISCV --enable-multilib
```

2. You will need to manually build a 32-bit pk.  After the build script
   builds a 64-bit pk, go into `riscv-tools/riscv-pk/build`, and edit the
   Makefile as follows:

  * Add -m32 to CFLAGS and LDFLAGS
  * Change the base-directory of prefix from `riscv64-unknown-elf` to
    `riscv32-unknown-elf`. This will allow you to install the 32-bit
    pk along-side the 64-bit pk.

  Then run `make clean && make && make install`.

## Compiling CompCert for RV32G

* Ensure you have the RV32G toolchain in your path.

* $ ./configure rv32-elf && make

## Compiling using CompCert RV32G

* Ensure you have the RV32G toolchain in your path.

* From the top-level CompCert directory,

  $ ./ccomp -Lruntime -o program.exe program.c

## Running CompCert RV32G binaries

  $ spike --isa=RV32 $RISCV/riscv32-unknown-elf/bin/pk program.exe

## Example

```
$ cat hello.c
#include <stdio.h>
int main(int argc, const char **argv) {
  printf("hello %s %d!\n", "world", 1);
  return 0;
}

$ ./ccomp -o hello -Lruntime hello.c
$ spike --isa=RV32 $RISCV/riscv32-unknown-elf/bin/pk hello
hello world 1!
```

## Known issues

* The main missing piece is full support for the RV32G stdarg/vararg
  calling convention: it currently does not support floating point
  arguments.  The soft-float calling convention is also not yet
  supported.

* Two minor lemmas are still to be proved in rv32/Asmgenproof1.v

* Extensive testing is still to be done.
