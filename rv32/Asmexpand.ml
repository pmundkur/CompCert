(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Adapted for RV32G by Prashanth Mundkur, SRI International. *)

(* Expanding built-ins and some pseudo-instructions by rewriting
   of the RV32G assembly code. *)

open Asm
open Asmexpandaux
open Asmgen
open AST
open Camlcoq
open Integers

exception Error of string

(* Useful constants and helper functions *)

let _0  = Integers.Int.zero
let _1  = Integers.Int.one
let _2  = coqint_of_camlint 2l
let _4  = coqint_of_camlint 4l
let _8  = coqint_of_camlint 8l
let _m1 = coqint_of_camlint (-1l)

(* Emit instruction sequences that set or offset a register by a constant. *)

let expand_movimm dst n =
  match Asmgen.make_immed n with
  | Imm_single imm ->
      emit (Pseti (dst, imm))
  | Imm_pair (hi, lo) ->
      emit (Plui (dst, hi));
      emit (Paddi (dst, dst, lo))

let expand_addimm dst src n =
  match Asmgen.make_immed n with
  | Imm_single imm ->
      emit (Paddi (dst, src, imm))
  | Imm_pair (hi, lo) ->
      emit (Plui  (X5, hi));
      emit (Paddi (X5, X5, lo));
      emit (Padd  (dst, src, X5))

(* Built-ins.  They come in two flavors:
   - annotation statements: take their arguments in registers or stack
     locations; generate no code;
   - inlined by the compiler: take their arguments in arbitrary
     registers.
*)

(* Handling of annotations *)

let expand_annot_val txt targ args res =
  emit (Pbuiltin (EF_annot(txt,[targ]), args, BR_none));
  match args, res with
  | [BA(IR src)], BR(IR dst) ->
     if dst <> src then emit (Pmv (dst, src))
  | [BA(FR src)], BR(FR dst) ->
     if dst <> src then emit (Pfmv (dst, src))
  | _, _ ->
     raise (Error "ill-formed __builtin_annot_val")

(* Detection of immediates *)

let is_immed n =
  match Asmgen.make_immed n with
  | Imm_single _ -> true
  | Imm_pair _ -> false

let offset_in_range ofs =
  is_immed ofs

(* Handling of memcpy *)

let memcpy_arg arg tmp =
  match arg with
  | BA (IR r) ->
     if r <> tmp then emit (Pmv (tmp, r))
  | BA_addrstack ofs ->
     expand_addimm tmp X2 ofs
  | _ ->
     assert false

let src_dst_regs src dst =
  if src = BA (IR X5) then
    if dst = BA (IR X6)
    then (emit (Pmv (X7, X5)); (X7, X6))
    else (emit (Pmv (X6, X5)); (X6, X7))
  else if dst = BA (IR X5) then
    if src = BA (IR X6)
    then (emit (Pmv (X7, X5)); (X6, X7))
    else (emit (Pmv (X6, X5)); (X7, X6))
  else
    if dst <> BA (IR X6) then (X6, X7) else (X7, X6)

let expand_builtin_memcpy_small sz al src dst =
  let (s, d) = src_dst_regs src dst in
  memcpy_arg src s;
  memcpy_arg dst d;
  let rec copy osrc odst sz =
    if sz >= 8 && al >= 4 then
      begin
        emit (Pfld (F0, s, osrc));
        emit (Pfsd (F0, d, odst));
        copy (Int.add osrc _8) (Int.add odst _8) (sz - 8);
      end
    else if sz >= 4 && al >= 4 then
      begin
        emit (Plw (X1, s, osrc));
        emit (Psw (X1, d, odst));
        copy (Int.add osrc _4) (Int.add odst _4) (sz - 4);
      end
    else if sz >= 2 && al >= 2 then
      begin
        emit (Plh (X1, s, osrc));
        emit (Psw (X1, d, odst));
        copy (Int.add osrc _2) (Int.add odst _2) (sz - 2);
      end
    else if sz >= 1 then
      begin
        emit (Plb (X1, s, osrc));
        emit (Psb (X1, d, odst));
        copy (Int.add osrc _1) (Int.add odst _1) (sz - 1);
      end
  in copy _0 _0 sz

let expand_builtin_memcpy_big sz al src dst =
  assert (sz >= al);
  assert (sz mod al = 0);
  (* Use X6 and X7 as src/dst pointers, and X1 as ld/st temporary. We
     might have to use X5 for addrstack arguments, so move inputs out
     from there.  *)
  let (s, d) = src_dst_regs src dst in
  memcpy_arg src s;
  memcpy_arg dst d;
  let (load, store, chunksize) =
    if al >= 4 then
      (Plw (X1, s, _0), Psw (X1, d, _0), 4)
    else if al = 2 then
      (Plh (X1, s, _0), Psh (X1, d, _0), 2)
    else
      (Plb (X1, s, _0), Psb (X1, d, _0), 1) in
  expand_movimm X5 (coqint_of_camlint (Int32.of_int (sz / chunksize)));
  let lbl = new_label () in
  emit (Plabel lbl);
  emit load;
  expand_addimm X5 X5 _m1;
  emit store;
  emit (Pbnez (X5, lbl))

let expand_builtin_memcpy  sz al args =
  let (dst, src) =
    match args with [d; s] -> (d, s) | _ -> assert false in
  if sz <= 32
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst

(* Handling of volatile reads and writes *)

let expand_builtin_vload_common chunk base ofs res =
  match chunk, res with
  | Mint8unsigned, BR(IR res) ->
     emit (Plbu (res, base, ofs))
  | Mint8signed, BR(IR res) ->
     emit (Plb  (res, base, ofs))
  | Mint16unsigned, BR(IR res) ->
     emit (Plhu (res, base, ofs))
  | Mint16signed, BR(IR res) ->
     emit (Plh  (res, base, ofs))
  | Mint32, BR(IR res) ->
     emit (Plw  (res, base, ofs))
  | Mint64, BR_splitlong(BR(IR res1), BR(IR res2)) ->
     let ofs' = Int.add ofs _4 in
     if base <> res2 then begin
         emit (Plw (res2, base, ofs));
         emit (Plw (res1, base, ofs'))
       end else begin
         emit (Plw (res1, base, ofs'));
         emit (Plw (res2, base, ofs))
       end
  | Mfloat32, BR(FR res) ->
     emit (Pfls (res, base, ofs))
  | Mfloat64, BR(FR res) ->
     emit (Pfld (res, base, ofs))
  | _ ->
     assert false

let expand_builtin_vload chunk args res =
  match args with
  | [BA(IR addr)] ->
      expand_builtin_vload_common chunk addr _0 res
  | [BA_addrstack ofs] ->
      if offset_in_range (Int.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vload_common chunk X2 ofs res
      else begin
        expand_addimm X1 X2 ofs; (* ra <- sp + ofs *)
        expand_builtin_vload_common chunk X1 _0 res
      end
  | [BA_addrglobal(id, ofs)] ->
      emit (Ploadsymbol (X1,id,ofs));
      expand_builtin_vload_common chunk X1 _0 res
  | _ ->
      assert false

let expand_builtin_vstore_common chunk base ofs src =
  match chunk, src with
  | (Mint8signed | Mint8unsigned), BA(IR src) ->
     emit (Psb (src, base, ofs))
  | (Mint16signed | Mint16unsigned), BA(IR src) ->
     emit (Psh (src, base, ofs))
  | Mint32, BA(IR src) ->
     emit (Psw (src, base, ofs))
  | Mint64, BA_splitlong(BA(IR src1), BA(IR src2)) ->
     let ofs' = Int.add ofs _4 in
     emit (Psw (src2, base, ofs));
     emit (Psw (src1, base, ofs'))
  | Mfloat32, BA(FR src) ->
     emit (Pfss (src, base, ofs))
  | Mfloat64, BA(FR src) ->
     emit (Pfsd (src, base, ofs))
  | _ ->
     assert false

let expand_builtin_vstore chunk args =
  match args with
  | [BA(IR addr); src] ->
      expand_builtin_vstore_common chunk addr _0 src
  | [BA_addrstack ofs; src] ->
      if offset_in_range (Int.add ofs (Memdata.size_chunk chunk)) then
        expand_builtin_vstore_common chunk X2 ofs src
      else begin
        expand_addimm X1 X2 ofs;
        expand_builtin_vstore_common chunk X1 _0 src
      end
  | [BA_addrglobal(id, ofs); src] ->
      emit (Ploadsymbol (X1,id,ofs));
      expand_builtin_vstore_common chunk X1 _0 src
  | _ ->
      assert false

(* Handling of varargs *)

let align n a = (n + a - 1) land (-a)

let rec named_args_size sz = function
  | [] -> sz
  | (Tint | Tsingle | Tany32) :: l -> named_args_size (Int32.add sz 4l) l
  | (Tlong | Tfloat | Tany64) :: l -> named_args_size (Int32.add sz 8l) l

(* Space needed to save unnamed arguments. *)
let saveregs_size fn_sig =
  assert fn_sig.sig_cc.cc_vararg;
  let args_sz = named_args_size 0l fn_sig.sig_args in
  let save_space = Int32.sub 32l args_sz in
  if save_space > 0l then save_space else 0l

(* Arguments to variadics are only in integer registers. *)
let int_arg_regs = [ X17; X16; X15; X14; X13; X12; X11; X10 ]

(* Save all unnamed args in the saveregs area at the top of the stack. *)
let rec save_regs sa ofs = function
  | []      -> assert false
  | h :: tl -> if ofs >= 4l then begin
                   let ofs = Int32.sub ofs 4l in
                   emit (Psw (h, sa, Z.of_sint32 ofs));
                   save_regs sa ofs tl;
                end

let expand_builtin_va_start r =
  if not !current_function.fn_sig.sig_cc.cc_vararg then
    invalid_arg "Fatal error: va_start used in non-vararg function";
  let sa_size = saveregs_size (!current_function).fn_sig in
  let sa_ofs  = Int32.sub !PrintAsmaux.current_function_stacksize sa_size in
  expand_addimm X30 X2 (Z.of_sint32 sa_ofs);
  emit (Psw (X30, r, _0))

(* Handling of compiler-inlined builtins *)

let expand_builtin_inline name args res =
  match name, args, res with
  (* Synchronization *)
  | "__builtin_fence", [], _ ->
     emit Pfence
  (* Vararg stuff *)
  | "__builtin_va_start", [BA(IR a)], _ ->
     expand_builtin_va_start a
  (* Catch-all *)
  | _ ->
     raise (Error ("unrecognized builtin " ^ name))

let expand_instruction instr =
  match instr with
  | Pallocframe (sz, ofs) ->
     emit (Pmv (X30, X2));
     (* When the callee is a variadic, we will need additional stack
        to save unnamed arguments.  The caller will put all arguments
        in integer registers, including floats; this argument fix-up
        for the caller is done in TargetPrinter.  NOTE: This is not
        compliant with the standard RV32G ABI, which passes only the
        variadic arguments in the integer registers.  *)
     let save_regs_size = if (!current_function).fn_sig.sig_cc.cc_vararg
                          then saveregs_size (!current_function).fn_sig
                          else 0l in
     let stk_sz = Int32.add save_regs_size (Z.to_int32 sz) in
     expand_addimm X2 X2 (Integers.Int.neg (Z.of_sint32 stk_sz));
     emit (Psw (X30, X2, ofs));
     (* X30 is now usable for save_regs *)
     if save_regs_size > 0l then
       begin
         expand_addimm X30 X2 sz;
         save_regs X30 save_regs_size int_arg_regs;
       end;
     PrintAsmaux.current_function_stacksize := stk_sz
  | Pfreeframe (sz, ofs) ->
     let sz = if (!current_function).fn_sig.sig_cc.cc_vararg
              then Z.of_sint32 (Int32.add (Z.to_int32 sz)
                                (saveregs_size (!current_function).fn_sig))
              else sz in
     if is_immed sz
     then emit (Paddi (X2, X2, sz))
     else emit (Plw (X2, X2, ofs))
  | Pbuiltin (ef,args,res) ->
     begin match ef with
           | EF_builtin (name,sg) ->
              expand_builtin_inline (camlstring_of_coqstring name) args res
           | EF_vload chunk ->
              expand_builtin_vload chunk args res
           | EF_vstore chunk ->
              expand_builtin_vstore chunk args
           | EF_annot_val (txt,targ) ->
              expand_annot_val txt targ args res
           | EF_memcpy(sz, al) ->
              expand_builtin_memcpy (Int32.to_int (camlint_of_coqint sz))
                (Int32.to_int (camlint_of_coqint al)) args
           | EF_annot _ | EF_debug _ | EF_inline_asm _ ->
              emit instr
           | _ ->
              assert false
     end
  | _ ->
     emit instr

(* NOTE: Dwarf register maps for RV32G are not yet specified
   officially.  This is just a placeholder.  *)
let int_reg_to_dwarf = function
               | X1  -> 1  | X2  -> 2  | X3  -> 3
   | X4  -> 4  | X5  -> 5  | X6  -> 6  | X7  -> 7
   | X8  -> 8  | X9  -> 9  | X10 -> 10 | X11 -> 11
   | X12 -> 12 | X13 -> 13 | X14 -> 14 | X15 -> 15
   | X16 -> 16 | X17 -> 17 | X18 -> 18 | X19 -> 19
   | X20 -> 20 | X21 -> 21 | X22 -> 22 | X23 -> 23
   | X24 -> 24 | X25 -> 25 | X26 -> 26 | X27 -> 27
   | X28 -> 28 | X29 -> 29 | X30 -> 30 | X31 -> 31

let float_reg_to_dwarf = function
   | F0  -> 32 | F1  -> 33 | F2  -> 34 | F3  -> 35
   | F4  -> 36 | F5  -> 37 | F6  -> 38 | F7  -> 39
   | F8  -> 40 | F9  -> 41 | F10 -> 42 | F11 -> 43
   | F12 -> 44 | F13 -> 45 | F14 -> 46 | F15 -> 47
   | F16 -> 48 | F17 -> 49 | F18 -> 50 | F19 -> 51
   | F20 -> 52 | F21 -> 53 | F22 -> 54 | F23 -> 55
   | F24 -> 56 | F25 -> 57 | F26 -> 58 | F27 -> 59
   | F28 -> 60 | F29 -> 61 | F30 -> 62 | F31 -> 63

let preg_to_dwarf = function
   | IR r -> int_reg_to_dwarf r
   | FR r -> float_reg_to_dwarf r
   | _ -> assert false

let expand_function id fn =
  try
    set_current_function fn;
    if !Clflags.option_g then
      expand_debug id (* sp= *) 2 preg_to_dwarf expand_instruction fn.fn_code
    else
      List.iter expand_instruction fn.fn_code;
    Errors.OK (get_current_function ())
  with Error s ->
    Errors.Error (Errors.msg (coqstring_of_camlstring s))

let expand_fundef id = function
  | Internal f ->
      begin match expand_function id f with
      | Errors.OK tf -> Errors.OK (Internal tf)
      | Errors.Error msg -> Errors.Error msg
      end
  | External ef ->
      Errors.OK (External ef)

let expand_program (p: Asm.program) : Asm.program Errors.res =
  AST.transform_partial_ident_program expand_fundef p
