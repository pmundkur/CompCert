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

(* Printing RV32G assembly code in asm syntax *)

open Printf
open Datatypes
open Camlcoq
open Sections
open AST
open Memdata
open Asm
open PrintAsmaux
open Fileinfo

(* Module containing the printing functions *)

module Target : TARGET =
  struct
(* Code generation options. *)

    let literals_in_code = ref false     (* to be turned into a proper option *)

(* Basic printing functions *)

    let comment = "#"

    let symbol        = elf_symbol
    let symbol_offset = elf_symbol_offset
    let label         = elf_label

    let print_label oc lbl = label oc (transl_label lbl)

    let use_abi_name = true

    let int_reg_num_name = function
                     | X1  -> "x1"  | X2  -> "x2"  | X3  -> "x3"
      | X4  -> "x4"  | X5  -> "x5"  | X6  -> "x6"  | X7  -> "x7"
      | X8  -> "x8"  | X9  -> "x9"  | X10 -> "x10" | X11 -> "x11"
      | X12 -> "x12" | X13 -> "x13" | X14 -> "x14" | X15 -> "x15"
      | X16 -> "x16" | X17 -> "x17" | X18 -> "x18" | X19 -> "x19"
      | X20 -> "x20" | X21 -> "x21" | X22 -> "x22" | X23 -> "x23"
      | X24 -> "x24" | X25 -> "x25" | X26 -> "x26" | X27 -> "x27"
      | X28 -> "x28" | X29 -> "x29" | X30 -> "x30" | X31 -> "x31"

    let int_reg_abi_name = function
                     | X1  -> "ra"  | X2  -> "sp"  | X3  -> "gp"
      | X4  -> "tp"  | X5  -> "t0"  | X6  -> "t1"  | X7  -> "t2"
      | X8  -> "s0"  | X9  -> "s1"  | X10 -> "a0"  | X11 -> "a1"
      | X12 -> "a2"  | X13 -> "a3"  | X14 -> "a4"  | X15 -> "a5"
      | X16 -> "a6"  | X17 -> "a7"  | X18 -> "s2"  | X19 -> "s3"
      | X20 -> "s4"  | X21 -> "s5"  | X22 -> "s6"  | X23 -> "s7"
      | X24 -> "s8"  | X25 -> "s9"  | X26 -> "s10" | X27 -> "s11"
      | X28 -> "t3"  | X29 -> "t4"  | X30 -> "t5"  | X31 -> "t6"

    let float_reg_num_name = function
      | F0  -> "f0"  | F1  -> "f1"  | F2  -> "f2"  | F3  -> "f3"
      | F4  -> "f4"  | F5  -> "f5"  | F6  -> "f6"  | F7  -> "f7"
      | F8  -> "f8"  | F9  -> "f9"  | F10 -> "f10" | F11 -> "f11"
      | F12 -> "f12" | F13 -> "f13" | F14 -> "f14" | F15 -> "f15"
      | F16 -> "f16" | F17 -> "f17" | F18 -> "f18" | F19 -> "f19"
      | F20 -> "f20" | F21 -> "f21" | F22 -> "f22" | F23 -> "f23"
      | F24 -> "f24" | F25 -> "f25" | F26 -> "f26" | F27 -> "f27"
      | F28 -> "f28" | F29 -> "f29" | F30 -> "f30" | F31 -> "f31"

    let float_reg_abi_name = function
      | F0  -> "ft0" | F1  -> "ft1" | F2  -> "ft2" | F3  -> "ft3"
      | F4  -> "ft4" | F5  -> "ft5" | F6  -> "ft6" | F7  -> "ft7"
      | F8  -> "fs0" | F9  -> "fs1" | F10 -> "fa0" | F11 -> "fa1"
      | F12 -> "fa2" | F13 -> "fa3" | F14 -> "fa4" | F15 -> "fa5"
      | F16 -> "fa6" | F17 -> "fa7" | F18 -> "fs2" | F19 -> "fs3"
      | F20 -> "fs4" | F21 -> "fs5" | F22 -> "fs6" | F23 -> "fs7"
      | F24 -> "fs8" | F25 -> "fs9" | F26 ->"fs10" | F27 -> "fs11"
      | F28 -> "ft3" | F29 -> "ft4" | F30 -> "ft5" | F31 -> "ft6"

    let int_reg_name   = if use_abi_name then int_reg_abi_name   else int_reg_num_name
    let float_reg_name = if use_abi_name then float_reg_abi_name else float_reg_num_name

    let ireg oc r = output_string oc (int_reg_name r)
    let freg oc r = output_string oc (float_reg_name r)

    let preg oc = function
      | IR r -> ireg oc r
      | FR r -> freg oc r
      | _    -> assert false

(* Names of sections *)

    let name_of_section = function
      | Section_text         -> ".text"
      | Section_data i | Section_small_data i ->
          if i then ".data" else "COMM"
      | Section_const i | Section_small_const i ->
          if i then ".section	.rodata" else "COMM"
      | Section_string       -> ".section	.rodata"
      | Section_literal      -> ".section	.rodata"
      | Section_jumptable    -> ".section	.rodata"
      | Section_debug_info _ -> ".section	.debug_info,\"\",%progbits"
      | Section_debug_loc    -> ".section	.debug_loc,\"\",%progbits"
      | Section_debug_abbrev -> ".section	.debug_abbrev,\"\",%progbits"
      | Section_debug_line _ -> ".section	.debug_line,\"\",%progbits"
      | Section_debug_ranges -> ".section	.debug_ranges,\"\",%progbits"
      | Section_debug_str    -> ".section	.debug_str,\"MS\",%progbits,1"
      | Section_user(s, wr, ex) ->
          sprintf ".section	\"%s\",\"a%s%s\",%%progbits"
            s (if wr then "w" else "") (if ex then "x" else "")

    let section oc sec =
      fprintf oc "	%s\n" (name_of_section sec)

(* Record current code position and latest position at which to
   emit float and symbol constants. *)

    let currpos = ref 0
    let size_constants = ref 0
    let max_pos_constants = ref max_int

    let distance_to_emit_constants () =
      if !literals_in_code
      then !max_pos_constants - (!currpos + !size_constants)
      else max_int

(* Associate labels to floating-point constants and to symbols. *)

    let float_labels   = (Hashtbl.create 39 : (int64, int) Hashtbl.t)
    let float32_labels = (Hashtbl.create 39 : (int32, int) Hashtbl.t)

    let label_float bf =
      try
        Hashtbl.find float_labels bf
      with Not_found ->
        let lbl' = new_label() in
        Hashtbl.add float_labels bf lbl';
        size_constants := !size_constants + 8;
        max_pos_constants := min !max_pos_constants (!currpos + 1024);
        lbl'

    let label_float32 bf =
      try
        Hashtbl.find float32_labels bf
      with Not_found ->
        let lbl' = new_label() in
        Hashtbl.add float32_labels bf lbl';
        size_constants := !size_constants + 4;
        max_pos_constants := min !max_pos_constants (!currpos + 1024);
        lbl'

    let symbol_labels =
      (Hashtbl.create 39 : (ident * Integers.Int.int, int) Hashtbl.t)

    let label_symbol id ofs =
      try
        Hashtbl.find symbol_labels (id, ofs)
      with Not_found ->
        let lbl' = new_label() in
        Hashtbl.add symbol_labels (id, ofs) lbl';
        size_constants := !size_constants + 4;
        max_pos_constants := min !max_pos_constants (!currpos + 4096);
        lbl'

    let reset_constants () =
      Hashtbl.clear float_labels;
      Hashtbl.clear float32_labels;
      Hashtbl.clear symbol_labels;
      size_constants := 0;
      max_pos_constants := max_int

    let emit_constants oc =
      if Hashtbl.length float_labels > 0 then
        begin
          fprintf oc "	.align 3\n";
          Hashtbl.iter
            (fun bf lbl ->
              (* Little-endian floats *)
             let bfhi = Int64.shift_right_logical bf 32
             and bflo = Int64.logand bf 0xFFFF_FFFFL in
             fprintf oc "%a:	.word	0x%Lx, 0x%Lx\n" label lbl bflo bfhi)
            float_labels;
        end;
      if Hashtbl.length float32_labels > 0
         || Hashtbl.length symbol_labels > 0
      then
        begin
          fprintf oc "	.align	2\n";
          Hashtbl.iter
            (fun bf lbl ->
               fprintf oc "%a:	.word	0x%lx\n" label lbl bf)
            float32_labels;
          Hashtbl.iter
            (fun (id, ofs) lbl ->
               fprintf oc "%a:	.word	%a\n" label lbl symbol_offset (id, ofs))
            symbol_labels;
        end;
      reset_constants ()

(* Generate code to load the address of id + ofs in register r *)

    let loadsymbol oc r id ofs =
      let lbl  = label_symbol id ofs in
      let zero = camlint_of_coqint ofs = Int32.zero in
      fprintf oc "	lui	%a, %%hi(%a)\n" ireg r label lbl;
      fprintf oc "	add	%a, %a, %%lo(%a)\n" ireg r ireg r label lbl;
      if not zero then
        fprintf oc "	add	%a, %a\n" ireg r coqint ofs;
      fprintf oc "	lw	%a, 0(%a)\n" ireg r ireg r;
      if not zero then 4 else 3

(* Emit .file / .loc debugging directives *)

    let print_file_line oc file line =
      print_file_line oc comment file line

    let print_location oc loc =
      if loc <> Cutil.no_loc then print_file_line oc (fst loc) (snd loc)

(* Printing of instructions *)
    let print_instruction oc = function
      (* Integer register-immediate instructions *)
      | Paddi (rd, rs, imm) ->
         fprintf oc "	addi	%a, %a, %a\n" ireg rd ireg rs coqint imm; 1
      | Pslti (rd, rs, imm) ->
         fprintf oc "	slti	%a, %a, %a\n" ireg rd ireg rs coqint imm; 1
      | Psltiu (rd, rs, imm) ->
         fprintf oc "	sltiu	%a, %a, %a\n" ireg rd ireg rs coqint imm; 1
      | Pandi (rd, rs, imm) ->
         fprintf oc "	andi	%a, %a, %a\n" ireg rd ireg rs coqint imm; 1
      | Pori (rd, rs, imm) ->
         fprintf oc "	ori	%a, %a, %a\n" ireg rd ireg rs coqint imm; 1
      | Pxori (rd, rs, imm) ->
         fprintf oc "	xori	%a, %a, %a\n" ireg rd ireg rs coqint imm; 1
      | Pslli (rd, rs, imm) ->
         fprintf oc "	slli	%a, %a, %a\n" ireg rd ireg rs coqint imm; 1
      | Psrli (rd, rs, imm) ->
         fprintf oc "	srli	%a, %a, %a\n" ireg rd ireg rs coqint imm; 1
      | Psrai (rd, rs, imm) ->
         fprintf oc "	srai	%a, %a, %a\n" ireg rd ireg rs coqint imm; 1
      | Plui (rd, imm) ->
         fprintf oc "	lui	%a, %a\n"     ireg rd coqint imm; 1

      (* Integer register-register instructions *)
      | Pmv(rd, rs) ->
         fprintf oc "	mv	%a, %a\n"     ireg rd ireg rs; 1
      | Padd(rd, rs1, rs2) ->
         fprintf oc "	add	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1
      | Psub(rd, rs1, rs2) ->
         fprintf oc "	sub	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1

      | Pmul(rd, rs1, rs2) ->
         fprintf oc "	mul	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1
      | Pmulh(rd, rs1, rs2) ->
         fprintf oc "	mulh	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1
      | Pmulhu(rd, rs1, rs2) ->
         fprintf oc "	mulhu	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1

      | Pdiv(rd, rs1, rs2) ->
         fprintf oc "	div	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1
      | Pdivu(rd, rs1, rs2) ->
         fprintf oc "	divu	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1
      | Prem(rd, rs1, rs2) ->
         fprintf oc "	rem	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1
      | Premu(rd, rs1, rs2) ->
         fprintf oc "	remu	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1

      | Pslt(rd, rs1, rs2) ->
         fprintf oc "	slt	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1
      | Psltu(rd, rs1, rs2) ->
         fprintf oc "	sltu	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1
      | Pand(rd, rs1, rs2) ->
         fprintf oc "	and	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1

      | Por(rd, rs1, rs2) ->
         fprintf oc "	or	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1
      | Pxor(rd, rs1, rs2) ->
         fprintf oc "	xor	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1
      | Psll(rd, rs1, rs2) ->
         fprintf oc "	sll	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1
      | Psrl(rd, rs1, rs2) ->
         fprintf oc "	srl	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1
      | Psra(rd, rs1, rs2) ->
         fprintf oc "	sra	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2; 1

      | Pnot(rd, rs) ->
         fprintf oc "	not	%a, %a\n"     ireg rd ireg rs; 1

      (* Unconditional jumps.  Links are always to X1/RA. *)
      (* TODO: fix up arguments for calls to variadics, to move *)
      (* floating point arguments to integer registers.  How? *)
      | Pj_l(l) ->
         fprintf oc "	j	%a\n" print_label l; 1
      | Pj_s(s, sg) ->
         fprintf oc "	j	%a\n" symbol s; 1
      | Pj_r(r, sg) ->
         fprintf oc "	jr	%a\n" ireg r; 1
      | Pj_sl(s, sg) ->
         fprintf oc "	call	%a\n" symbol s; 1
      | Pj_rl(r, sg) ->
         fprintf oc "	jalr	%a\n" ireg r; 1

      (* Conditional branches *)
      | Pbeq(rs1, rs2, l) | Pbequ(rs1, rs2, l) ->
         fprintf oc "	beq	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l; 1
      | Pbne(rs1, rs2, l) | Pbneu(rs1, rs2, l) ->
         fprintf oc "	bne	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l; 1
      | Pblt(rs1, rs2, l) ->
         fprintf oc "	blt	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l; 1
      | Pbltu(rs1, rs2, l) ->
         fprintf oc "	bltu	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l; 1
      | Pbge(rs1, rs2, l) ->
         fprintf oc "	bge	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l; 1
      | Pbgeu(rs1, rs2, l) ->
         fprintf oc "	bgeu	%a, %a, %a\n" ireg rs1 ireg rs2 print_label l; 1

      (* Loads and stores *)
      | Plb(rd, ra, imm) ->
         fprintf oc "	lb	%a, %a(%a)\n" ireg rd coqint imm ireg ra; 1
      | Plbu(rd, ra, imm) ->
         fprintf oc "	lbu	%a, %a(%a)\n" ireg rd coqint imm ireg ra; 1
      | Plh(rd, ra, imm) ->
         fprintf oc "	lh	%a, %a(%a)\n" ireg rd coqint imm ireg ra; 1
      | Plhu(rd, ra, imm) ->
         fprintf oc "	lhu	%a, %a(%a)\n" ireg rd coqint imm ireg ra; 1
      | Plw(rd, ra, imm) ->
         fprintf oc "	lw	%a, %a(%a)\n" ireg rd coqint imm ireg ra; 1
      | Plw_a(rd, ra, imm) ->
         fprintf oc "	lw	%a, %a(%a)\n" ireg rd coqint imm ireg ra; 1

      | Psb(rd, ra, imm) ->
         fprintf oc "	sb	%a, %a(%a)\n" ireg rd coqint imm ireg ra; 1
      | Psh(rd, ra, imm) ->
         fprintf oc "	sh	%a, %a(%a)\n" ireg rd coqint imm ireg ra; 1
      | Psw(rd, ra, imm) ->
         fprintf oc "	sw	%a, %a(%a)\n" ireg rd coqint imm ireg ra; 1
      | Psw_a(rd, ra, imm) ->
         fprintf oc "	sw	%a, %a(%a)\n" ireg rd coqint imm ireg ra; 1

      (* Synchronization *)
      | Pfence ->
         fprintf oc "	fence\n"; 1

      (* floating point register move *)
      | Pfmv (fd,fs) ->
         fprintf oc "	fmv.d	%a, %a\n"     freg fd freg fs; 1

      (* 32-bit (single-precision) floating point *)
      | Pfls (fd, ra, imm) ->
         fprintf oc "	flw	%a, %a(%a)\n" freg fd coqint imm ireg ra; 1
      | Pfss (fs, ra, imm) ->
         fprintf oc "	fsw	%a, %a(%a)\n" freg fs coqint imm ireg ra; 1

      | Pfnegs (fd, fs) ->
         fprintf oc "	fneg.s	%a, %a\n"     freg fd freg fs; 1
      | Pfabss (fd, fs) ->
         fprintf oc "	fabs.s	%a, %a\n"     freg fd freg fs; 1

      | Pfadds (fd, fs1, fs2) ->
         fprintf oc "	fadd.s	%a, %a, %a\n" freg fd freg fs1 freg fs2; 1
      | Pfsubs (fd, fs1, fs2) ->
         fprintf oc "	fsub.s	%a, %a, %a\n" freg fd freg fs1 freg fs2; 1
      | Pfmuls (fd, fs1, fs2) ->
         fprintf oc "	fmul.s	%a, %a, %a\n" freg fd freg fs1 freg fs2; 1
      | Pfdivs (fd, fs1, fs2) ->
         fprintf oc "	fdiv.s	%a, %a, %a\n" freg fd freg fs1 freg fs2; 1
      | Pfmins (fd, fs1, fs2) ->
         fprintf oc "	fmin.s	%a, %a, %a\n" freg fd freg fs1 freg fs2; 1
      | Pfmaxs (fd, fs1, fs2) ->
         fprintf oc "	fmax.s	%a, %a, %a\n" freg fd freg fs1 freg fs2; 1

      | Pfeqs (rd, fs1, fs2) ->
         fprintf oc "	feq.s   %a, %a, %a\n" ireg rd freg fs1 freg fs2; 1
      | Pflts (rd, fs1, fs2) ->
         fprintf oc "	flt.s   %a, %a, %a\n" ireg rd freg fs1 freg fs2; 1
      | Pfles (rd, fs1, fs2) ->
         fprintf oc "	fle.s   %a, %a, %a\n" ireg rd freg fs1 freg fs2; 1

      | Pfsqrts (fd, fs) ->
         fprintf oc "	fsqrt.s %a, %a\n"     freg fd freg fs; 1

      | Pfmadds (fd, fs1, fs2, fs3) ->
         fprintf oc "	fmadd.s	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3; 1
      | Pfmsubs (fd, fs1, fs2, fs3) ->
         fprintf oc "	fmsub.s	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3; 1
      | Pfnmadds (fd, fs1, fs2, fs3) ->
         fprintf oc "	fnmadd.s	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3; 1
      | Pfnmsubs (fd, fs1, fs2, fs3) ->
         fprintf oc "	fnmsub.s	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3; 1

      | Pfcvtws (rd, fs) ->
         fprintf oc "	fcvt.w.s	%a, %a\n" ireg rd freg fs; 1
      | Pfcvtwus (rd, fs) ->
         fprintf oc "	fcvt.wu.	%a, %a\n" ireg rd freg fs; 1
      | Pfcvtsw (fd, rs) ->
         fprintf oc "	fcvt.s.w	%a, %a\n" freg fd ireg rs; 1
      | Pfcvtswu (fd, rs) ->
         fprintf oc "	fcvt.s.wu	%a, %a\n" freg fd ireg rs; 1

      (* 32-bit (single-precision) floating point *)
      | Pfld (fd, ra, imm) ->
         fprintf oc "	fld	%a, %a(%a)\n" freg fd coqint imm ireg ra; 1
      | Pfld_a (fd, ra, imm) ->
         fprintf oc "	fld	%a, %a(%a)\n" freg fd coqint imm ireg ra; 1
      | Pfsd (fs, ra, imm) ->
         fprintf oc "	fsd	%a, %a(%a)\n" freg fs coqint imm ireg ra; 1
      | Pfsd_a (fs, ra, imm) ->
         fprintf oc "	fsd	%a, %a(%a)\n" freg fs coqint imm ireg ra; 1

      | Pfnegd (fd, fs) ->
         fprintf oc "	fneg.d	%a, %a\n"     freg fd freg fs; 1
      | Pfabsd (fd, fs) ->
         fprintf oc "	fabs.d	%a, %a\n"     freg fd freg fs; 1

      | Pfaddd (fd, fs1, fs2) ->
         fprintf oc "	fadd.d	%a, %a, %a\n" freg fd freg fs1 freg fs2; 1
      | Pfsubd (fd, fs1, fs2) ->
         fprintf oc "	fsub.d	%a, %a, %a\n" freg fd freg fs1 freg fs2; 1
      | Pfmuld (fd, fs1, fs2) ->
         fprintf oc "	fmul.d	%a, %a, %a\n" freg fd freg fs1 freg fs2; 1
      | Pfdivd (fd, fs1, fs2) ->
         fprintf oc "	fdiv.d	%a, %a, %a\n" freg fd freg fs1 freg fs2; 1
      | Pfmind (fd, fs1, fs2) ->
         fprintf oc "	fmin.d	%a, %a, %a\n" freg fd freg fs1 freg fs2; 1
      | Pfmaxd (fd, fs1, fs2) ->
         fprintf oc "	fmax.d	%a, %a, %a\n" freg fd freg fs1 freg fs2; 1

      | Pfeqd (rd, fs1, fs2) ->
         fprintf oc "	feq.d	%a, %a, %a\n" ireg rd freg fs1 freg fs2; 1
      | Pfltd (rd, fs1, fs2) ->
         fprintf oc "	flt.d	%a, %a, %a\n" ireg rd freg fs1 freg fs2; 1
      | Pfled (rd, fs1, fs2) ->
         fprintf oc "	fle.d	%a, %a, %a\n" ireg rd freg fs1 freg fs2; 1

      | Pfsqrtd (fd, fs) ->
         fprintf oc "	fsqrt.d	%a, %a\n" freg fd freg fs; 1

      | Pfmaddd (fd, fs1, fs2, fs3) ->
         fprintf oc "	fmadd.d	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3; 1
      | Pfmsubd (fd, fs1, fs2, fs3) ->
         fprintf oc "	fmsub.d	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3; 1
      | Pfnmaddd (fd, fs1, fs2, fs3) ->
         fprintf oc "	fnmadd.d	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3; 1
      | Pfnmsubd (fd, fs1, fs2, fs3) ->
         fprintf oc "	fnmsub.d	%a, %a, %a, %a\n" freg fd freg fs1 freg fs2 freg fs3; 1

      | Pfcvtwd (rd, fs) ->
         fprintf oc "	fcvt.l.d	%a, %a\n" ireg rd freg fs; 1
      | Pfcvtwud (rd, fs) ->
         fprintf oc "	fcvt.lu.d	%a, %a\n" ireg rd freg fs; 1
      | Pfcvtdw (fd, rs) ->
         fprintf oc "	fcvt.d.l	%a, %a\n" freg fd ireg rs; 1
      | Pfcvtdwu (fd, rs) ->
         fprintf oc "	fcvt.d.lu	%a, %a\n" freg fd ireg rs; 1

      | Pfcvtds (fd, fs) ->
         fprintf oc "	fmv.x.s	%a, %a\n" freg fd freg fs; 1
      | Pfcvtsd (fd, fs) ->
         fprintf oc "	fmv.s.x	%a, %a\n" freg fd freg fs; 1

      (* Pseudo-instructions *)
      | Pallocframe(sz, ofs) ->
         assert false
      | Pfreeframe(sz, ofs) ->
         assert false
      | Plabel lbl ->
         fprintf oc "%a:\n" print_label lbl; 0
      | Ploadsymbol(rd, id, ofs) ->
         loadsymbol oc rd id ofs
      | Ploadfi(fd, f) ->
         let d   = camlint64_of_coqint(Floats.Float.to_bits f) in
         let lbl = label_float d in
         fprintf oc "	lui	%a, %%hi(%a) %s %.18g\n"
                 ireg X5 elf_label lbl
                 comment (camlfloat_of_coqfloat f);
         fprintf oc "	fld	%a, %%lo(%a)(%a)\n"
                 freg fd label lbl ireg X5; 2
      | Ploadsi(fd, f) ->
         let s   = camlint_of_coqint(Floats.Float32.to_bits f) in
         let lbl = label_float32 s in
         fprintf oc "	lui	%a, %%hi(%a) %s %.18g\n"
                 ireg X5 label lbl
                 comment (camlfloat_of_coqfloat32 f);
         fprintf oc "	flw	%a, %%lo(%a)(%a)\n"
                 freg fd label lbl ireg X5; 2
      | Pbtbl(r, tbl) ->
         let lbl = new_label() in
         fprintf oc "%s jumptable [ " comment;
         List.iter (fun l -> fprintf oc "%a " print_label l) tbl;
         fprintf oc "]\n";
         (* Note: it doesn't matter if the incoming reg r is either
            R5 or R6. *)
         fprintf oc "	sll	x5, %a, 2\n" ireg r;
         fprintf oc "	lui	x6, %%hi(%a)\n" label lbl;
         fprintf oc "	add	x6, x6, %%lo(%a)\n" label lbl;
         fprintf oc "	add	x6, x6, x5\n";
         fprintf oc "	lw	x6, 0(x6)\n";
         fprintf oc "	jr	x6\n";
         jumptables := (lbl, tbl) :: !jumptables;
         fprintf oc "%s end pseudoinstr btbl\n" comment; 6
      | Pbuiltin(ef, args, res) ->
         begin match ef with
          | EF_annot(txt, targs) ->
              fprintf oc "%s annotation: " comment;
              print_annot_text preg "sp" oc (camlstring_of_coqstring txt) args;
              0
          | EF_debug(kind, txt, targs) ->
              print_debug_info comment print_file_line preg "sp" oc
                               (P.to_int kind) (extern_atom txt) args;
              0
          | EF_inline_asm(txt, sg, clob) ->
              fprintf oc "%s begin inline assembly\n\t" comment;
              print_inline_asm preg oc (camlstring_of_coqstring txt) sg args res;
              fprintf oc "%s end inline assembly\n" comment;
              5 (* hoping this is an upper bound...  *)
          | _ ->
              assert false
         end

      (* pseudos since we don't model x0 === 0 *)
      | Pseti(rd, imm) ->
         fprintf oc "	li	%a, %a\n"     ireg rd coqint imm; 1
      | Pseqz(rd, rs) ->
         fprintf oc "	seqz	%a, %a\n"     ireg rd ireg rs; 1
      | Psnez(rd, rs) ->
         fprintf oc "	snez	%a, %a\n"     ireg rd ireg rs; 1
      | Pbeqz(r, l) ->
         fprintf oc "	beqz	%a, %a\n"     ireg r print_label l; 1
      | Pbnez(r, l) ->
         fprintf oc "	bnez	%a, %a\n"     ireg r print_label l; 1

      (* pseudos for unsigned in/equality *)
      | Pequ(rd, rs1, rs2) ->
         fprintf oc "	xor	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2;
         fprintf oc "	seqz	%a, %a\n"     ireg rd ireg rd; 2
      | Pneu(rd, rs1, rs2) ->
         fprintf oc "	xor	%a, %a, %a\n" ireg rd ireg rs1 ireg rs2;
         fprintf oc "	snez	%a, %a\n"     ireg rd ireg rd; 2

    let no_fallthrough = function
       | Pj_l _  -> true
       | Pj_s _  -> true
       | Pj_r _  -> true
       | Pj_sl _ -> true
       | Pj_rl _ -> true
       | _ -> false

    let rec print_instructions oc instrs =
      match instrs with
      | [] -> ()
      | i :: il ->
          let n = print_instruction oc i in
          currpos := !currpos + n * 4;
          let d = distance_to_emit_constants() in
          if d < 256 && no_fallthrough i then
            emit_constants oc
          else if d < 16 then begin
            let lbl = new_label() in
            fprintf oc "	b	%a\n" label lbl;
            emit_constants oc;
            fprintf oc "%a:\n" label lbl
          end;
          print_instructions oc il

    let get_section_names name =
      let (text, lit) =
        match C2C.atom_sections name with
        | t :: l :: _ -> (t, l)
        | _    -> (Section_text, Section_literal) in
      text,lit,Section_jumptable

    let print_align oc alignment =
      fprintf oc "	.align %d\n" alignment

    let print_jumptable oc jmptbl =
      let print_tbl oc (lbl, tbl) =
        fprintf oc "%a:\n" label lbl;
        List.iter
          (fun l -> fprintf oc "	.word	%a\n" print_label l)
          tbl in
      if !jumptables <> [] then
        begin
          section oc jmptbl;
          fprintf oc "	.balign 4\n";
          List.iter (print_tbl oc) !jumptables;
          jumptables := []
        end

    let print_fun_info = elf_print_fun_info

    let print_optional_fun_info _ = ()

    let print_var_info = elf_print_var_info

    let print_comm_symb oc sz name align =
      if C2C.atom_is_static name then
        fprintf oc "	.local	%a\n" symbol name;
        fprintf oc "	.comm	%a, %s, %d\n"
        symbol name
        (Z.to_string sz)
        align

    let print_instructions oc fn =
      current_function_sig := fn.fn_sig;
      print_instructions oc fn.fn_code;
      if !literals_in_code then emit_constants oc

    let emit_constants oc lit =
      if not !literals_in_code && !size_constants > 0 then begin
        section oc lit;
        emit_constants oc
      end

(* Data *)

    let print_init oc = function
      | Init_int8 n ->
          fprintf oc "	.byte	%ld\n" (camlint_of_coqint n)
      | Init_int16 n ->
          fprintf oc "	.short	%ld\n" (camlint_of_coqint n)
      | Init_int32 n ->
          fprintf oc "	.word	%ld\n" (camlint_of_coqint n)
      | Init_int64 n ->
          fprintf oc "	.quad	%Ld\n" (camlint64_of_coqint n)
      | Init_float32 n ->
          fprintf oc "	.word   0x%lx %s %.15g \n" (camlint_of_coqint (Floats.Float32.to_bits n))
            comment (camlfloat_of_coqfloat n)
      | Init_float64 n ->
          fprintf oc "	.quad   %Ld %s %.18g\n" (camlint64_of_coqint (Floats.Float.to_bits n))
            comment (camlfloat_of_coqfloat n)
      | Init_space n ->
          if Z.gt n Z.zero then
            fprintf oc "	.space  %s\n" (Z.to_string n)
      | Init_addrof(symb, ofs) ->
          fprintf oc "	.word	%a\n" symbol_offset (symb, ofs)

    let print_prologue oc =
      if !Clflags.option_g then begin
        section oc Section_text;
      end

    let print_epilogue oc =
      if !Clflags.option_g then begin
        Debug.compute_gnu_file_enum (fun f -> ignore (print_file oc f));
        section oc Section_text;
      end

    let default_falignment = 2

    let label = elf_label

    let new_label = new_label

    let cfi_startproc oc = ()
    let cfi_endproc oc = ()
  end

let sel_target () =
  (module Target:TARGET)
