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

(** Machine- and ABI-dependent layout information for activation records. *)

Require Import Coqlib.
Require Import Bounds.

(** The general shape of activation records is as follows,
  from bottom (lowest offsets) to top:
- Space for outgoing arguments to function calls.
- Local stack slots.
- Saved values of float callee-save registers used by the function.
- Saved values of integer callee-save registers used by the function.
- Pointer to activation record of the caller.
- Saved return address into caller.
- Space for the stack-allocated data declared in Cminor.

Stack alignment on RV32G is at 16-byte boundaries.

The [frame_env] compilation environment records the positions of
the boundaries between areas in the frame part.
*)

Definition fe_ofs_arg := 0.

Record frame_env : Type := mk_frame_env {
  fe_size: Z;
  fe_ofs_retaddr: Z;
  fe_ofs_link: Z;
  fe_ofs_local: Z;
  fe_ofs_float_callee_save: Z;
  fe_num_float_callee_save: Z;
  fe_ofs_int_callee_save: Z;
  fe_num_int_callee_save: Z;
  fe_stack_data: Z
}.

(** Computation of the frame environment from the bounds of the current
  function. *)

Definition make_env (b: bounds) :=
  let ol    := align (4 * b.(bound_outgoing)) 8 in      (* locals *)
  let oendl := ol + 4 * b.(bound_local) in
  let ofcs  := align oendl 16 in                        (* float callee-saves *)
  let oendf := ofcs + 8 * b.(bound_float_callee_save) in
  let oics  := align oendf 16 in                        (* integer callee-saves *)
  let oendi := oics + 4 * b.(bound_int_callee_save) in
  let olink := align oendi 16 in                        (* back link *)
  let ora   := olink + 4 in                             (* retaddr *)
  let ostkdata := ora + 4 in                            (* stack data *)
  let sz    := align (ostkdata + b.(bound_stack_data)) 8 in
  mk_frame_env sz ora olink ol
               ofcs b.(bound_float_callee_save)
               oics b.(bound_int_callee_save)
               ostkdata.

(** Separation property *)

Remark frame_env_separated:
  forall b,
  let fe := make_env b in
  0 <= fe_ofs_arg
  /\ fe_ofs_arg + 4 * b.(bound_outgoing) <= fe.(fe_ofs_local)
  /\ fe.(fe_ofs_local) + 4 * b.(bound_local) <= fe.(fe_ofs_float_callee_save)
  /\ fe.(fe_ofs_float_callee_save) + 8 * b.(bound_float_callee_save) <= fe.(fe_ofs_int_callee_save)
  /\ fe.(fe_ofs_int_callee_save) + 4 * b.(bound_int_callee_save) <= fe.(fe_ofs_link)
  /\ fe.(fe_ofs_link) + 4 <= fe.(fe_ofs_retaddr)
  /\ fe.(fe_ofs_retaddr) + 4 <= fe.(fe_stack_data)
  /\ fe.(fe_stack_data) + b.(bound_stack_data) <= fe.(fe_size).
Proof.
  intros.
  generalize (align_le (4 * bound_outgoing b) 8 (refl_equal)).
  generalize (align_le (fe_ofs_local fe + 4 * bound_local b) 16 (refl_equal)).
  generalize (align_le (fe_ofs_float_callee_save fe + 8 * bound_float_callee_save b) 16 (refl_equal)).
  generalize (align_le (fe_ofs_int_callee_save fe + 4 * bound_int_callee_save b) 16 (refl_equal)).
  generalize (align_le (fe_stack_data fe + b.(bound_stack_data)) 8 (refl_equal)).
  unfold fe, make_env, fe_size, fe_ofs_retaddr, fe_ofs_link,
    fe_ofs_local, fe_ofs_int_callee_save, fe_num_int_callee_save,
    fe_ofs_float_callee_save, fe_num_float_callee_save,
    fe_stack_data, fe_ofs_arg.
  intros.
  generalize (bound_local_pos b); intro;
  generalize (bound_int_callee_save_pos b); intro;
  generalize (bound_float_callee_save_pos b); intro;
  generalize (bound_outgoing_pos b); intro;
  generalize (bound_stack_data_pos b); intro.
  omega.
Qed.

(** Alignment property *)

(* TODO: Check if we can strengthen these claims for 16-byte alignment. *)
Remark frame_env_aligned:
  forall b,
  let fe := make_env b in
  (4 | fe.(fe_ofs_link))
  /\ (8 | fe.(fe_ofs_local))
  /\ (4 | fe.(fe_ofs_int_callee_save))
  /\ (8 | fe.(fe_ofs_float_callee_save))
  /\ (4 | fe.(fe_ofs_retaddr))
  /\ (8 | fe.(fe_stack_data))
  /\ (8 | fe.(fe_size)).
Proof.
  intros.
  unfold fe, make_env, fe_size, fe_ofs_retaddr, fe_ofs_link,
    fe_ofs_local, fe_ofs_int_callee_save, fe_num_int_callee_save,
    fe_ofs_float_callee_save, fe_num_float_callee_save,
    fe_stack_data.
  set (x1 := 4 * bound_outgoing b).
  assert (4 | x1).
    unfold x1; exists (bound_outgoing b); ring.
  set (ol := align x1 8).
  assert (8 | ol).
    apply align_divides. omega.
  set (oendl := ol + 4 * bound_local b).
  assert (4 | oendl).
    apply Zdivide_plus_r. apply Zdivides_trans with 8; auto. exists 2; auto.
    exists (bound_local b); ring.
  set (ofcs := align oendl 16).
  assert (8 | ofcs).
    apply Zdivides_trans with 16; auto. exists 2; auto.
    apply align_divides. omega.
  set (oics := align (ofcs + 8 * b.(bound_float_callee_save)) 16).
  assert (4 | oics).
    apply Zdivides_trans with 16; auto. exists 4; auto.
    apply align_divides. omega.
  set (olink := align (oics + 4 * b.(bound_int_callee_save)) 16).
  assert (4 | olink).
    apply Zdivides_trans with 16; auto. exists 4; auto.
    apply align_divides. omega.
  set (ora := olink + 4).
  assert (4 | ora).
    apply Zdivide_plus_r; auto. exists 1; auto.
  set (ostkdata := ora + 4).
  assert (8 | ostkdata).
    unfold ostkdata. unfold ora.
    replace (olink + 4 + 4) with (olink + 8) by omega.
    apply Zdivide_plus_r. apply Zdivides_trans with 16. exists 2; auto.
    apply align_divides. omega. exists 1; auto.
  set (sz := align (ostkdata + b.(bound_stack_data)) 8).
  assert (8 | sz).
    apply align_divides. omega.
  tauto.
Qed.
