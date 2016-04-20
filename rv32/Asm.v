(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Adapted for RV32G by Prashanth Mundkur, SRI International. *)

(** Abstract syntax and semantics for RISC-V assembly language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Stacklayout.
Require Import Conventions.

(** * Abstract syntax *)

(** Integer registers, floating-point registers. X0 is hardwired to 0
    which does not fit in the model (I think) and so is omitted.
*)

Inductive ireg: Type :=
  | X1:  ireg | X2:  ireg | X3:  ireg | X4:  ireg | X5:  ireg
  | X6:  ireg | X7:  ireg | X8:  ireg | X9:  ireg | X10: ireg
  | X11: ireg | X12: ireg | X13: ireg | X14: ireg | X15: ireg
  | X16: ireg | X17: ireg | X18: ireg | X19: ireg | X20: ireg
  | X21: ireg | X22: ireg | X23: ireg | X24: ireg | X25: ireg
  | X26: ireg | X27: ireg | X28: ireg | X29: ireg | X30: ireg
  | X31: ireg.

Inductive freg: Type :=
  | F0: freg  | F1: freg  | F2: freg  | F3: freg
  | F4: freg  | F5: freg  | F6: freg  | F7: freg
  | F8: freg  | F9: freg  | F10: freg | F11: freg
  | F12: freg | F13: freg | F14: freg | F15: freg
  | F16: freg | F17: freg | F18: freg | F19: freg
  | F20: freg | F21: freg | F22: freg | F23: freg
  | F24: freg | F25: freg | F26: freg | F27: freg
  | F28: freg | F29: freg | F30: freg | F31: freg.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** We model the following registers of the RISC-V architecture. *)

Inductive preg: Type :=
  | IR: ireg -> preg                    (**r integer registers *)
  | FR: freg -> preg                    (**r double-precision float registers *)
  | PC: preg.                           (**r program counter *)

Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq. Defined.

Module PregEq.
  Definition t  := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

(** Conventional names for stack pointer ([SP]) and return address ([RA]). *)

Notation "'SP'" := X2 (only parsing).
Notation "'RA'" := X1 (only parsing).

(** The instruction set.  Most instructions correspond exactly to
  actual instructions of the RISC-V processor. See the RISC-V
  user-mode specification for more details.  Some instructions,
  described below, are pseudo-instructions: they expand to canned
  instruction sequences during the printing of the assembly code. *)

Definition label := positive.

(** A note on immediates: there are various constraints on immediate
  operands to RISC-V instructions.  We do not attempt to capture these
  restrictions in the abstract syntax nor in the semantics.  The
  assembler will emit an error if immediate operands exceed the
  representable range.  Of course, our RISC-V generator (file
  [Asmgen]) is careful to respect this range. *)

Inductive instruction : Type :=
  (* Integer register-immediate instructions *)
  | Paddi   (rd: ireg) (rs: ireg) (imm: int)        (**r add immediate *)
  | Pslti   (rd: ireg) (rs: ireg) (imm: int)        (**r set-less-than immediate *)
  | Psltiu  (rd: ireg) (rs: ireg) (imm: int)        (**r set-less-than unsigned immediate *)
  | Pandi   (rd: ireg) (rs: ireg) (imm: int)        (**r and immediate *)
  | Pori    (rd: ireg) (rs: ireg) (imm: int)        (**r or immediate *)
  | Pxori   (rd: ireg) (rs: ireg) (imm: int)        (**r xor immediate *)
  | Pslli   (rd: ireg) (rs: ireg) (imm: int)        (**r shift-left-logical immediate *)
  | Psrli   (rd: ireg) (rs: ireg) (imm: int)        (**r shift-right-logical immediate *)
  | Psrai   (rd: ireg) (rs: ireg) (imm: int)        (**r shift-right-arith immediate *)
  | Plui    (rd: ireg)            (imm: int)        (**r load upper-immediate *)

(* Omit for now:
  | Pauipc (rd: ireg)            (imm: int)         (**r add-upper immediate to PC *)
*)

  (* Integer register-register instructions *)
  | Pmv     (rd: ireg) (rs: ireg)                   (**r integer move *)
  | Padd    (rd: ireg) (rs1 rs2: ireg)              (**r integer addition *)
  | Psub    (rd: ireg) (rs1 rs2: ireg)              (**r integer subtraction *)

  | Pmul    (rd: ireg) (rs1 rs2: ireg)              (**r integer multiply: low32 *)
  | Pmulh   (rd: ireg) (rs1 rs2: ireg)              (**r integer multiply: high32 (signed   x signed) *)
  | Pmulhu  (rd: ireg) (rs1 rs2: ireg)              (**r integer multiply: high32 (unsigned x unsigned) *)
(* Omit for now.
  | Pmulhsu (rd: ireg) (rs1 rs2: ireg)              (**r integer multiply: high32 (signed   x unsigned) *)
*)
  | Pdiv    (rd: ireg) (rs1 rs2: ireg)              (**r integer division *)
  | Pdivu   (rd: ireg) (rs1 rs2: ireg)              (**r unsigned integer division *)
  | Prem    (rd: ireg) (rs1 rs2: ireg)              (**r integer remainder *)
  | Premu   (rd: ireg) (rs1 rs2: ireg)              (**r unsigned integer remainder *)

  | Pslt    (rd: ireg) (rs1 rs2: ireg)              (**r set-less-than *)
  | Psltu   (rd: ireg) (rs1 rs2: ireg)              (**r set-less-than unsigned *)
  | Pand    (rd: ireg) (rs1 rs2: ireg)              (**r bitwise and *)

  | Por     (rd: ireg) (rs1 rs2: ireg)              (**r bitwise or *)
  | Pxor    (rd: ireg) (rs1 rs2: ireg)              (**r bitwise xor *)
  | Psll    (rd: ireg) (rs1 rs2: ireg)              (**r shift-left-logical *)
  | Psrl    (rd: ireg) (rs1 rs2: ireg)              (**r shift-right-logical *)
  | Psra    (rd: ireg) (rs1 rs2: ireg)              (**r shift-right-arith *)

  | Pnot    (rd: ireg) (rs: ireg)                   (**r bitwise not: assembler pseudo *)

  (* Unconditional jumps.  Links are always to X1/RA. *)
  | Pj_l    (l: label)                              (**r jump to label *)
  | Pj_s    (symb: ident) (sg: signature)           (**r jump to symbol *)
  | Pj_r    (r: ireg)     (sg: signature)           (**r jump register *)
  | Pj_sl   (symb: ident) (sg: signature)           (**r jump-and-link symbol *)
  | Pj_rl   (r: ireg)     (sg: signature)           (**r jump-and-link register *)

  (* Conditional branches *)
  | Pbeq    (rs1 rs2: ireg) (l: label)              (**r branch-if-equal signed *)
  | Pbequ   (rs1 rs2: ireg) (l: label)              (**r branch-if-equal unsigned (== Pbeq) *)
  | Pbne    (rs1 rs2: ireg) (l: label)              (**r branch-if-not-equal signed *)
  | Pbneu   (rs1 rs2: ireg) (l: label)              (**r branch-if-not-equal unsigned (== Pne) *)
  | Pblt    (rs1 rs2: ireg) (l: label)              (**r branch-if-less signed *)
  | Pbltu   (rs1 rs2: ireg) (l: label)              (**r branch-if-less unsigned *)
  | Pbge    (rs1 rs2: ireg) (l: label)              (**r branch-if-greater-or-equal signed *)
  | Pbgeu   (rs1 rs2: ireg) (l: label)              (**r branch-if-greater-or-equal unsigned *)

  (* Loads and stores *)
  | Plb     (rd: ireg) (ra: ireg) (imm: int)        (**r load signed int8 *)
  | Plbu    (rd: ireg) (ra: ireg) (imm: int)        (**r load unsigned int8 *)
  | Plh     (rd: ireg) (ra: ireg) (imm: int)        (**r load signed int16 *)
  | Plhu    (rd: ireg) (ra: ireg) (imm: int)        (**r load unsigned int16 *)
  | Plw     (rd: ireg) (ra: ireg) (imm: int)        (**r load int32 *)
  | Plw_a   (rd: ireg) (ra: ireg) (imm: int)        (**r load any32 *)

  | Psb     (rs: ireg) (ra: ireg) (imm: int)        (**r store int8 *)
  | Psh     (rs: ireg) (ra: ireg) (imm: int)        (**r store int16 *)
  | Psw     (rs: ireg) (ra: ireg) (imm: int)        (**r store int32 *)
  | Psw_a   (rs: ireg) (ra: ireg) (imm: int)        (**r store any32 *)

  (* Synchronization *)
  | Pfence                                          (**r fence *)

  (* floating point register move *)
  | Pfmv     (rd: freg) (rs: freg)                  (**r move *)

  (* 32-bit (single-precision) floating point *)
  | Pfls     (rd: freg) (ra: ireg) (imm: int)       (**r load float *)
  | Pfss     (rs: freg) (ra: ireg) (imm: int)       (**r store float *)

  | Pfnegs   (rd: freg) (rs: freg)                  (**r negation *)
  | Pfabss   (rd: freg) (rs: freg)                  (**r absolute value *)

  | Pfadds   (rd: freg) (rs1 rs2: freg)             (**r addition *)
  | Pfsubs   (rd: freg) (rs1 rs2: freg)             (**r subtraction *)
  | Pfmuls   (rd: freg) (rs1 rs2: freg)             (**r multiplication *)
  | Pfdivs   (rd: freg) (rs1 rs2: freg)             (**r division *)
  | Pfmins   (rd: freg) (rs1 rs2: freg)             (**r minimum *)
  | Pfmaxs   (rd: freg) (rs1 rs2: freg)             (**r maximum *)

  | Pfeqs    (rd: ireg) (rs1 rs2: freg)             (**r compare equal *)
  | Pflts    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than *)
  | Pfles    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than/equal *)

  | Pfsqrts  (rd: freg) (rs: freg)                  (**r square-root *)

  | Pfmadds  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-add *)
  | Pfmsubs  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-sub *)
  | Pfnmadds (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-add *)
  | Pfnmsubs (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-sub *)

  | Pfcvtws  (rd: ireg) (rs: freg)                  (**r float32 -> int32 conversion *)
  | Pfcvtwus (rd: ireg) (rs: freg)                  (**r float32 -> unsigned int32 conversion *)
  | Pfcvtsw  (rd: freg) (rs: ireg)                  (**r int32 -> float32 conversion *)
  | Pfcvtswu (rd: freg) (rs: ireg)                  (**r unsigned int32 -> float32 conversion *)

  (* 64-bit (double-precision) floating point *)
  | Pfld     (rd: freg) (ra: ireg) (imm: int)       (**r load 64-bit float *)
  | Pfld_a   (rd: freg) (ra: ireg) (imm: int)       (**r load any64 *)
  | Pfsd     (rd: freg) (ra: ireg) (imm: int)       (**r store 64-bit float *)
  | Pfsd_a   (rd: freg) (ra: ireg) (imm: int)       (**r store any64 *)

  | Pfnegd   (rd: freg) (rs: freg)                  (**r negation *)
  | Pfabsd   (rd: freg) (rs: freg)                  (**r absolute value *)

  | Pfaddd   (rd: freg) (rs1 rs2: freg)             (**r addition *)
  | Pfsubd   (rd: freg) (rs1 rs2: freg)             (**r subtraction *)
  | Pfmuld   (rd: freg) (rs1 rs2: freg)             (**r multiplication *)
  | Pfdivd   (rd: freg) (rs1 rs2: freg)             (**r division *)
  | Pfmind   (rd: freg) (rs1 rs2: freg)             (**r minimum *)
  | Pfmaxd   (rd: freg) (rs1 rs2: freg)             (**r maximum *)

  | Pfeqd    (rd: ireg) (rs1 rs2: freg)             (**r compare equal *)
  | Pfltd    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than *)
  | Pfled    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than/equal *)

  | Pfsqrtd  (rd: freg) (rs: freg)                  (**r square-root *)

  | Pfmaddd  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-add *)
  | Pfmsubd  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-sub *)
  | Pfnmaddd (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-add *)
  | Pfnmsubd (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-sub *)

  | Pfcvtwd  (rd: ireg) (rs: freg)                  (**r float -> int32 conversion *)
  | Pfcvtwud (rd: ireg) (rs: freg)                  (**r float -> unsigned int32 conversion *)
  | Pfcvtdw  (rd: freg) (rs: ireg)                  (**r int32 -> float conversion *)
  | Pfcvtdwu (rd: freg) (rs: ireg)                  (**r unsigned int32 -> float conversion *)

  | Pfcvtds  (rd: freg) (rs: freg)                  (**r float32 -> float   *)
  | Pfcvtsd  (rd: freg) (rs: freg)                  (**r float   -> float32 *)

  (* Pseudo-instructions *)
  | Pallocframe (sz: Z) (pos: int)                  (**r allocate new stack frame *)
  | Pfreeframe  (sz: Z) (pos: int)                  (**r deallocate stack frame and restore previous frame *)
  | Plabel  (lbl: label)                            (**r define a code label *)
  | Ploadsymbol (rd: ireg) (lbl: ident) (ofs: int)  (**r load the address of a symbol *)
  | Ploadfi (rd: freg) (f: float)                   (**r load an immediate float *)
  | Ploadsi (rd: freg) (f: float32)                 (**r load an immediate single *)
  | Pbtbl   (r: ireg)  (tbl: list label)            (**r N-way branch through a jump table *)
  | Pbuiltin: external_function -> list (builtin_arg preg)
              -> builtin_res preg -> instruction    (**r built-in function (pseudo) *)

  (* pseudos since we don't model x0 === 0 *)
  | Pseti   (rd: ireg) (imm: int)                   (**r set immediate, via addi X0 imm *)
  | Pseqz   (rd: ireg) (rs: ireg)                   (**r rd <- rs == 0 *)
  | Psnez   (rd: ireg) (rs: ireg)                   (**r rd <- rs != 0 *)
  | Pbeqz   (r: ireg) (lbl: label)                  (**r branch if zero, using X0 *)
  | Pbnez   (r: ireg) (lbl: label)                  (**r branch if non-zero, using X0 *)

  (* pseudos for unsigned in/equality *)
  | Pequ    (rd: ireg) (rs1 rs2: ireg)              (**r rd <- rs1 == rs2 *)
  | Pneu    (rd: ireg) (rs1 rs2: ireg).             (**r rd <- rs1 != rs2 *)

(** The pseudo-instructions are the following:

- [Plabel]: define a code label at the current program point.

- [Ploadsymbol]: load the address of a symbol in an integer register.
  Expands to a load from an address in the constant data section
  initialized with the symbol value:
<<
        lw      rd, lbl
        .const_data
lbl:    .word   symbol
        .text
>>
  Initialized data in the constant data section are not modeled here,
  which is why we use a pseudo-instruction for this purpose.

- [Ploadfi rd fval]: load an immediate float into a float register rd.
  Expands to a load from an address in the constant data section,
  using the integer register x5:
<<
        lui x5, %hi(lbl)
        fld rd, %lo(lbl)(x5)
lbl:
        .double fval
>>

- [Ploadsi rd fval]: load an immediate single into a float register rd.
  Expands to a load from an address in the constant data section,
  using the integer register x5:
<<
        lui x5, %hi(lbl)
        flw rd, %lo(lbl)(x5)
lbl:
        .float fval
>>

- [Pallocframe sz pos]: in the formal semantics, this
  pseudo-instruction allocates a memory block with bounds [0] and
  [sz], stores the value of the stack pointer at offset [pos] in this
  block, and sets the stack pointer to the address of the bottom of
  this block.
  In the printed ASM assembly code, this allocation is:
<<
        mv      x30, sp
        sub     sp,  sp, #sz
        sw      x30, #pos(sp)
>>
  This cannot be expressed in our memory model, which does not reflect
  the fact that stack frames are adjacent and allocated/freed
  following a stack discipline.

- [Pfreeframe sz pos]: in the formal semantics, this pseudo-instruction
  reads the word at [pos] of the block pointed by the stack pointer,
  frees this block, and sets the stack pointer to the value read.
  In the printed ASM assembly code, this freeing
  is just a load of register [sp] relative to [sp] itself:
<<
        lw      sp, #pos(sp)
>>
  Again, our memory model cannot comprehend that this operation
  frees (logically) the current stack frame.

- [Pbtbl reg table]: this is a N-way branch, implemented via a jump table
  as follows:
<<
        li      x6, table
        add     x6, x6, reg
        jr      x6
table:  .long   table[0], table[1], ...
>>
  Note that [reg] contains 4 times the index of the desired table entry.

- [Pequ rd rs1 rs2]: since unsigned comparisons have particular
  semantics for pointers, we cannot encode equality directly using
  xor/sub etc, which have only integer semantics.
<<
        xor     rd, rs1, rs2
        seqz    rd, rd
>>

- [Pneu rd rs1 rs2]: similarly for unsigned inequality.
<<
        xor     rd, rs1, rs2
        snez    rd, rd
>>
*)

Definition code := list instruction.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain (but do not enforce)
  the convention that integer registers are mapped to values of
  type [Tint] and float registers to values of type [Tfloat]. *)

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

(** Assigning multiple registers *)

Fixpoint set_regs (rl: list preg) (vl: list val) (rs: regset) : regset :=
  match rl, vl with
  | r1 :: rl', v1 :: vl' => set_regs rl' vl' (rs#r1 <- v1)
  | _, _ => rs
  end.

(** Assigning the result of a builtin *)

Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl lbl0); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

Variable ge: genv.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next:  regset -> mem -> outcome
  | Stuck: outcome.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)

Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.add rs#PC Vone).

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Int.repr pos))) m
      | _          => Stuck
      end
  end.

(** Auxiliaries for memory accesses *)

Definition exec_load (chunk: memory_chunk) (addr: val) (r: preg)
                     (rs: regset) (m: mem) :=
  match Mem.loadv chunk m addr with
  | None => Stuck
  | Some v => Next (nextinstr (rs#r <- v)) m
  end.

Definition exec_store (chunk: memory_chunk) (addr: val) (r: preg)
                      (rs: regset) (m: mem) :=
  match Mem.storev chunk m addr (rs r) with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

(** Evaluating a branch *)

Definition eval_branch (c: comparison) (v1 v2: val) (l: label) (f: function)  (rs: regset) (m: mem) : outcome :=
  match Val.cmp_bool c v1 v2 with
    | Some true  => goto_label f l rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
  end.

Definition eval_u_branch (c: comparison) (v1 v2: val) (l: label) (f: function)  (rs: regset) (m: mem) : outcome :=
  match Val.cmpu_bool (Mem.valid_pointer m) c v1 v2 with
    | Some true  => goto_label f l rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
  end.

(** Execution of a single instruction [i] in initial state [rs] and
    [m].  Return updated state.  For instructions that correspond to
    actual RISC-V instructions, the cases are straightforward
    transliterations of the informal descriptions given in the RISC-V
    user-mode specification.  For pseudo-instructions, refer to the
    informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the RISC-V code
    we generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction. *)

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  | Paddi d s i =>
      Next (nextinstr (rs#d <- (Val.add rs#s (Vint i)))) m
  | Pslti d s i =>
      Next (nextinstr (rs#d <- (Val.cmp Clt rs#s (Vint i)))) m
  | Psltiu d s i =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs#s (Vint i)))) m
  | Pandi d s i =>
      Next (nextinstr (rs#d <- (Val.and rs#s (Vint i)))) m
  | Pori d s i =>
      Next (nextinstr (rs#d <- (Val.or rs#s (Vint i)))) m
  | Pxori d s i =>
      Next (nextinstr (rs#d <- (Val.xor rs#s (Vint i)))) m
  | Pslli d s i =>
      Next (nextinstr (rs#d <- (Val.shl rs#s (Vint i)))) m
  | Psrli d s i =>
      Next (nextinstr (rs#d <- (Val.shru rs#s (Vint i)))) m
  | Psrai d s i =>
      Next (nextinstr (rs#d <- (Val.shr rs#s (Vint i)))) m
  | Plui d i =>
      Next (nextinstr (rs#d <- (Vint (Int.shl i (Int.repr 12))))) m

  | Pmv d s =>
      Next (nextinstr (rs#d <- (rs#s))) m
  | Padd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.add rs#s1 rs#s2))) m
  | Psub d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.sub rs#s1 rs#s2))) m

  | Pmul d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mul rs#s1 rs#s2))) m
  | Pmulh d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulhs rs#s1 rs#s2))) m
  | Pmulhu d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulhu rs#s1 rs#s2))) m

  | Pdiv d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divs rs#s1 rs#s2)))) m
  | Pdivu d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divu rs#s1 rs#s2)))) m
  | Prem d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.mods rs#s1 rs#s2)))) m
  | Premu d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.modu rs#s1 rs#s2)))) m

  | Pslt d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmp Clt rs#s1 rs#s2))) m
  | Psltu d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs#s1 rs#s2))) m

  | Pand d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.and rs#s1 rs#s2))) m
  | Por d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.or rs#s1 rs#s2))) m
  | Pxor d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.xor rs#s1 rs#s2))) m
  | Psll d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shl rs#s1 rs#s2))) m
  | Psrl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shru rs#s1 rs#s2))) m
  | Psra d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shr rs#s1 rs#s2))) m

  | Pnot d s =>
      Next (nextinstr (rs#d <- (Val.notint rs#s))) m

  | Pj_l l =>
      goto_label f l rs m
  | Pj_s s sg =>
      Next (rs#PC <- (Genv.symbol_address ge s Int.zero)) m
  | Pj_r r sg =>
      Next (rs#PC <- (rs#r)) m
  | Pj_sl s sg =>
      Next (rs#PC <- (Genv.symbol_address ge s Int.zero)
              #RA <- (Val.add rs#PC Vone)
           ) m
  | Pj_rl r sg =>
      Next (rs#PC <- (rs#r)
              #RA <- (Val.add rs#PC Vone)
           ) m
  | Pbeq  s1 s2 l =>
      eval_branch   Ceq (rs#s1) (rs#s2) l f rs m
  | Pbne  s1 s2 l =>
      eval_branch   Cne (rs#s1) (rs#s2) l f rs m
  | Pblt  s1 s2 l =>
      eval_branch   Clt (rs#s1) (rs#s2) l f rs m
  | Pbge  s1 s2 l =>
      eval_branch   Cge (rs#s1) (rs#s2) l f rs m
  | Pbequ s1 s2 l =>
      eval_u_branch Ceq (rs#s1) (rs#s2) l f rs m
  | Pbneu s1 s2 l =>
      eval_u_branch Cne (rs#s1) (rs#s2) l f rs m
  | Pbltu s1 s2 l =>
      eval_u_branch Clt (rs#s1) (rs#s2) l f rs m
  | Pbgeu s1 s2 l =>
      eval_u_branch Cge (rs#s1) (rs#s2) l f rs m

  | Plb d a i =>
      exec_load Mint8signed (Val.add rs#a (Vint i)) d rs m
  | Plbu d a i =>
      exec_load Mint8unsigned (Val.add rs#a (Vint i)) d rs m
  | Plh d a i =>
      exec_load Mint16signed (Val.add rs#a (Vint i)) d rs m
  | Plhu d a i =>
      exec_load Mint16unsigned (Val.add rs#a (Vint i)) d rs m
  | Plw d a i =>
      exec_load Mint32 (Val.add rs#a (Vint i)) d rs m
  | Plw_a d a i =>
      exec_load Many32 (Val.add rs#a (Vint i)) d rs m

  | Psb s a i =>
      exec_store Mint8unsigned (Val.add rs#a (Vint i)) s rs m
  | Psh s a i =>
      exec_store Mint16unsigned (Val.add rs#a (Vint i)) s rs m
  | Psw s a i =>
      exec_store Mint32 (Val.add rs#a (Vint i)) s rs m
  | Psw_a s a i =>
      exec_store Many32 (Val.add rs#a (Vint i)) s rs m

  | Pfmv d s =>
      Next (nextinstr (rs#d <- (rs#s))) m

  | Pfls d a i =>
      exec_load Mfloat32 (Val.add rs#a (Vint i)) d rs m
  | Pfss s a i =>
      exec_store Mfloat32 (Val.add rs#a (Vint i)) s rs m

  | Pfnegs d s =>
      Next (nextinstr (rs#d <- (Val.negfs rs#s))) m
  | Pfabss d s =>
      Next (nextinstr (rs#d <- (Val.absfs rs#s))) m

  | Pfadds d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addfs rs#s1 rs#s2))) m
  | Pfsubs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subfs rs#s1 rs#s2))) m
  | Pfmuls d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulfs rs#s1 rs#s2))) m
  | Pfdivs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.divfs rs#s1 rs#s2))) m
  | Pfeqs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Ceq rs#s1 rs#s2))) m
  | Pflts d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Clt rs#s1 rs#s2))) m
  | Pfles d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Cle rs#s1 rs#s2))) m

  | Pfcvtws d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intofsingle rs#s)))) m
  | Pfcvtwus d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intuofsingle rs#s)))) m
  | Pfcvtsw d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleofint rs#s)))) m
  | Pfcvtswu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleofintu rs#s)))) m

  | Pfld d a i =>
      exec_load Mfloat64 (Val.add rs#a (Vint i)) d rs m
  | Pfld_a d a i =>
      exec_load Many64 (Val.add rs#a (Vint i)) d rs m
  | Pfsd s a i =>
      exec_store Mfloat64 (Val.add rs#a (Vint i)) s rs m
  | Pfsd_a s a i =>
      exec_store Many64 (Val.add rs#a (Vint i)) s rs m

  | Pfnegd d s =>
      Next (nextinstr (rs#d <- (Val.negf rs#s))) m
  | Pfabsd d s =>
      Next (nextinstr (rs#d <- (Val.absf rs#s))) m

  | Pfaddd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addf rs#s1 rs#s2))) m
  | Pfsubd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subf rs#s1 rs#s2))) m
  | Pfmuld d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulf rs#s1 rs#s2))) m
  | Pfdivd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.divf rs#s1 rs#s2))) m
  | Pfeqd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Ceq rs#s1 rs#s2))) m
  | Pfltd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Clt rs#s1 rs#s2))) m
  | Pfled d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Cle rs#s1 rs#s2))) m

  | Pfcvtwd d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intoffloat rs#s)))) m
  | Pfcvtwud d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intuoffloat rs#s)))) m
  | Pfcvtdw d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatofint rs#s)))) m
  | Pfcvtdwu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatofintu rs#s)))) m

  | Pfcvtds d s =>
      Next (nextinstr (rs#d <- (Val.floatofsingle rs#s))) m
  | Pfcvtsd d s =>
      Next (nextinstr (rs#d <- (Val.singleoffloat rs#s))) m

  (* Pseudo-instructions *)

  | Pallocframe sz pos =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := (Vptr stk Int.zero) in
      match Mem.storev Mint32 m1 (Val.add sp (Vint pos)) rs#SP with
      | None => Stuck
      | Some m2 => Next (nextinstr (rs #X30 <- (rs#SP) #SP <- sp)) m2
      end
  | Pfreeframe sz pos =>
      match Mem.loadv Mint32 m (Val.add rs#SP (Vint pos)) with
      | None => Stuck
      | Some v =>
          match rs#SP with
          | Vptr stk ofs =>
              match Mem.free m stk 0 sz with
              | None => Stuck
              | Some m' => Next (nextinstr (rs#SP <- v)) m'
              end
          | _ => Stuck
          end
      end
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Ploadsymbol rd lbl ofs =>
      Next (nextinstr (rs#rd <- (Genv.symbol_address ge lbl ofs))) m
  | Ploadfi rd f =>
      Next (nextinstr (rs#rd <- (Vfloat f))) m
  | Ploadsi rd f =>
      Next (nextinstr (rs#rd <- (Vsingle f))) m
  | Pbtbl r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl =>
              (* undefine regs in destroyed_by_jumptable *)
              goto_label f lbl (rs#X5 <- Vundef #X6 <- Vundef) m
          end
      | _ => Stuck
      end
  | Pbuiltin ef args res =>
      Stuck (**r treated specially below *)

  (* pseudos, since we don't model x0 === 0 *)
  | Pseti d i =>
      Next (nextinstr (rs#d <- (Vint i))) m
  | Pseqz d s =>
      Next (nextinstr (rs#d <- (Val.notbool rs#s))) m
  | Psnez d s =>
      Next (nextinstr (rs#d <- (Val.boolval rs#s))) m
  | Pbeqz s l =>
      eval_branch Ceq (rs#s) Vzero l f rs m
  | Pbnez s l =>
      eval_branch Cne (rs#s) Vzero l f rs m

  (* pseudos for unsigned in/equality *)
  | Pequ d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Ceq rs#s1 rs#s2))) m
  | Pneu d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Cne rs#s1 rs#s2))) m

  (** The following instructions and directives are not generated directly by Asmgen,
      so we do not model them. *)
  | Pfence

  | Pfmins _ _ _
  | Pfmaxs _ _ _
  | Pfsqrts _ _
  | Pfmadds _ _ _ _
  | Pfmsubs _ _ _ _
  | Pfnmadds _ _ _ _
  | Pfnmsubs _ _ _ _

  | Pfmind _ _ _
  | Pfmaxd _ _ _
  | Pfsqrtd _ _
  | Pfmaddd _ _ _ _
  | Pfmsubd _ _ _ _
  | Pfnmaddd _ _ _ _
  | Pfnmsubd _ _ _ _
    => Stuck
  end.

(** Translation of the LTL/Linear/Mach view of machine registers to
  the RISC-V view.  Note that no LTL register maps to [RA].  This
  register is reserved as temporary, to be used by the generated RV32G
  code.  *)

Definition preg_of (r: mreg) : preg :=
  match r with
               | R5  => X5  | R6  => X6  | R7  => X7
  | R8  => X8  | R9  => X9  | R10 => X10 | R11 => X11
  | R12 => X12 | R13 => X13 | R14 => X14 | R15 => X15
  | R16 => X16 | R17 => X17 | R18 => X18 | R19 => X19
  | R20 => X20 | R21 => X21 | R22 => X22 | R23 => X23
  | R24 => X24 | R25 => X25 | R26 => X26 | R27 => X27
  | R28 => X28 | R29 => X29 | R30 => X30 | R31 => X31

  | FR0  => F0  | FR1  => F1  | FR2  => F2  | FR3  => F3
  | FR4  => F4  | FR5  => F5  | FR6  => F6  | FR7  => F7
  | FR8  => F8  | FR9  => F9  | FR10 => F10 | FR11 => F11
  | FR12 => F12 | FR13 => F13 | FR14 => F14 | FR15 => F15
  | FR16 => F16 | FR17 => F17 | FR18 => F18 | FR19 => F19
  | FR20 => F20 | FR21 => F21 | FR22 => F22 | FR23 => F23
  | FR24 => F24 | FR25 => F25 | FR26 => F26 | FR27 => F27
  | FR28 => F28 | FR29 => F29 | FR30 => F30 | FR31 => F31
  end.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use RISC-V registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.add (rs SP) (Vint (Int.repr bofs))) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg rs m) (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : list preg :=
  map preg_of (loc_result sg).

(** Execution of the instruction at [rs#PC]. *)

Inductive state: Type :=
  | State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs SP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr
              (set_res res vres
                (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call' ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (set_regs (loc_external_result (ef_sig ef) ) res rs)#PC <- (rs RA) ->
      step (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Int.zero)
        # SP <- Vzero
        # RA <- Vzero in
      Genv.init_mem p = Some m0 ->
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vzero ->
      rs#X10 = Vint r ->
      final_state (State rs m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (forall ll vl1, list_forall2 (extcall_arg rs m) ll vl1 ->
          forall vl2, list_forall2 (extcall_arg rs m) ll vl2 -> vl1 = vl2).
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; auto.
    inv H; inv H3; congruence.
  intros. red in H0; red in H1. eauto.
Qed.

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
(* determ *)
  inv H; inv H0; Equalities.
  split. constructor. auto.
  discriminate.
  discriminate.
  assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ'. eexact H3. eexact H8. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
(* trace length *)
  red; intros. inv H; simpl.
  omega.
  eapply external_call_trace_length; eauto.
  inv H2; eapply external_call_trace_length; eauto.
(* initial states *)
  inv H; inv H0. f_equal. congruence.
(* final no step *)
  inv H. unfold Vzero in H0. red; intros; red; intros. inv H; congruence.
(* final states *)
  inv H; inv H0. congruence.
Qed.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | IR RA  => false
  | IR _   => true
  | FR _   => true
  | PC     => false
  end.
