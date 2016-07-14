This is a preliminary and very alpha port of CompCert 2.6 to 32-bit
RISC-V, specifically RV32G.  The port consumes C programs and
generates RV32G assembly files.  It currently uses the gcc newlib
toolchain as the backend to assemble and link RV32G binaries.

Please read the main CompCert readme for CompCert dependencies.

Setting up RV32G Dependencies
-----------------------------

You will need the RISC-V Newlib toolchain.
https://github.com/riscv/riscv-tools/blob/master/README.md#newlibman

When building the toolchain, you will need to enable 32-bit support:

- Change the following line in build.sh
     build_project riscv-gnu-toolchain --prefix=$RISCV
  to
     build_project riscv-gnu-toolchain --prefix=$RISCV --enable-multilib

- You will need to manually build a 32-bit pk.  After the build script
  builds a 64-bit pk, go into riscv-tools/riscv-pk/build, and edit the
  Makefile as follows:

  . Add -m32 to CFLAGS and LDFLAGS
  . Change the base-directory of prefix from
      riscv64-unknown-elf
    to
      riscv32-unknown-elf
    This will allow you to install the 32-bit pk along-side the 64-bit
    pk.

  Then run make clean && make && make install.

Compiling CompCert for RV32G
----------------------------

- Ensure you have the RV32G toolchain in your path.

- $ ./configure rv32-elf
  $ make

Compiling using CompCert RV32G
------------------------------

- Ensure you have the RV32G toolchain in your path.

- From the top-level CompCert directory,

  $ ./ccomp -Lruntime -o program.exe program.c

Running CompCert RV32G binaries
-------------------------------

$ spike --isa=RV32 /path/to/toolchain-install-dir/riscv32-unknown-elf/bin/pk program.exe

Known issues
------------

- Floating point is incomplete, so don't use this with any
  floating-point code.  Specifically,
  . the handling of NaN does not match the RISC-V spec
  . the stdarg calling convention does not work with floating-point arguments

- Two minor lemmas are still to be proved in rv32/Asmgenproof1.v

- Extensive testing is still to be done.
