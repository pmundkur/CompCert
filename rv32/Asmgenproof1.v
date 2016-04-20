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

(** Correctness proof for RV32G code generation: auxiliary results. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Compopts.
Require Import Asm.
Require Import Asmgen.
Require Import Conventions.
Require Import Asmgenproof0.

(** Decomposition of an integer constant. *)

Lemma lo_imm:
  forall n imm, make_immed n = Imm_single imm -> n = imm.
Proof.
  intros; unfold make_immed in H.
  destruct ((Int.eq (Int.shr n (Int.repr 11)) Int.zero)
              || (Int.eq (Int.shr n (Int.repr 11)) Int.mone)) eqn:?; try discriminate.
  inv H; auto.
Qed.

Lemma hi_lo_add:
  forall n hi lo, make_immed n = Imm_pair hi lo ->
  Int.add (Int.shl hi (Int.repr 12)) lo = n.
Proof.
  intros; unfold make_immed in H.
  destruct (Int.eq (Int.shru n (Int.repr 11)) Int.zero) eqn:?; try discriminate.
  inv H.
Admitted.

Lemma hi_lo_zero:
  forall n hi lo, make_immed n = Imm_pair hi lo -> Int.eq lo Int.zero = true ->
  Int.shl hi (Int.repr 12) = n.
Proof.
  intros.
  generalize (Int.eq_spec lo Int.zero); rewrite H0; intros.
  exploit hi_lo_add; eauto.
  rewrite H1. rewrite Int.add_zero. auto.
Qed.

(** Useful properties of registers. *)

Definition if_preg (r: preg) : bool :=
  match r with
  | IR _ => true
  | FR _ => true
  | PC   => false
  end.

Lemma data_if_preg: forall r, data_preg r = true -> if_preg r = true.
Proof.
  intros. destruct r; reflexivity || discriminate.
Qed.

Lemma if_preg_not_PC: forall r, if_preg r = true -> r <> PC.
Proof.
  intros; red; intros; subst; discriminate.
Qed.

Lemma ireg_not_PC: forall r, IR r <> PC.
Proof.
  congruence.
Qed.

Hint Resolve data_if_preg if_preg_not_PC ireg_not_PC: asmgen.

Lemma ireg_of_not_RA:
  forall m r, ireg_of m = OK r -> IR r <> IR RA.
Proof.
  intros. erewrite <- ireg_of_eq; eauto with asmgen.
Qed.
Hint Resolve ireg_of_not_RA: asmgen.

Lemma ireg_of_not_RA':
  forall m r, ireg_of m = OK r -> r <> RA.
Proof.
  intros. generalize (ireg_of_not_RA _ _ H). congruence.
Qed.
Hint Resolve ireg_of_not_RA': asmgen.

Lemma int_temp_R5_R6:
  forall r, int_temp_for r = R5 \/ int_temp_for r = R6.
Proof.
  intros. unfold int_temp_for.
  destruct (mreg_eq r).
  right; auto. left; auto.
Qed.

Lemma int_temp_X5_X6:
  forall m tmp, ireg_of (int_temp_for m) = OK tmp -> tmp = X5 \/ tmp = X6.
Proof.
  intros until tmp.
  unfold int_temp_for, ireg_of, preg_of; destruct (mreg_eq m R5); intro H; inv H.
  right; auto. left; auto.
Qed.

Lemma int_temp_ne:
  forall r tmp, ireg_of (int_temp_for r) = OK tmp -> preg_of r <> tmp.
Proof.
  intros until tmp. unfold int_temp_for.
  destruct (mreg_eq r R5); unfold ireg_of, preg_of; intro H; inv H.
  discriminate.
  destruct r; try discriminate.
  intro H; auto.
Qed.

Lemma int_temp_ne2:
  forall m r tmp, ireg_of (int_temp_for m) = OK tmp -> ireg_of m = OK r -> tmp <> r.
Proof.
  intros until tmp. unfold int_temp_for.
  destruct (mreg_eq m R5); unfold ireg_of; unfold preg_of; intro H; inv H.
  - intro EQ; inv EQ. discriminate.
  - destruct m; intro EQ; inv EQ; try discriminate.
    intro H; auto.
Qed.
(** Useful simplification tactic *)

Ltac Simplif :=
  ((rewrite nextinstr_inv by eauto with asmgen)
     || (rewrite nextinstr_inv1 by eauto with asmgen)
     || (rewrite Pregmap.gss)
     || (rewrite nextinstr_pc)
     || (rewrite Pregmap.gso by eauto with asmgen)); auto with asmgen.

Ltac Simpl := repeat Simplif.

(** * Correctness of RV32G constructor functions *)

Section CONSTRUCTORS.

Variable ge: genv.
Variable fn: function.

(** Loading a base + hi offset. *)

Lemma load_hibase_correct:
  forall rd base hi k rs m,
  base <> rd ->
  exists rs',
     exec_straight ge fn (load_hibase rd base hi k) rs m k rs' m
  /\ rs'#rd = Val.add rs#base (Vint (Int.shl hi (Int.repr 12)))
  /\ forall r, if_preg r = true -> r <> rd -> rs' r = rs r.
Proof.
  intros. unfold load_hibase.
  econstructor. split.
  eapply exec_straight_two. simpl; reflexivity.
  simpl; reflexivity. auto with asmgen.
  auto with asmgen.
  split. Simpl. rewrite Val.add_commut. auto.
  intros; Simpl.
Qed.

(** Loading a constant. *)

Lemma loadimm_correct:
  forall r n k rs m,
  exists rs',
     exec_straight ge fn (loadimm r n k) rs m k rs' m
  /\ rs'#r = Vint n
  /\ forall r': preg, r' <> r -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold loadimm.
  destruct (make_immed n) eqn:IMM.
  - (* imm_single *)
    econstructor. apply lo_imm in IMM; subst. split.
    apply exec_straight_one. simpl; reflexivity.
    auto with asmgen.
    split. rewrite nextinstr_inv. rewrite Pregmap.gss. auto.
    auto with asmgen. intros. Simpl.
  - (* imm_pair *)
    destruct (Int.eq lo Int.zero) eqn:LO.
    + econstructor. split. exploit hi_lo_zero; eauto; intros.
      unfold load_hilo; rewrite LO.
      apply exec_straight_one. simpl; reflexivity.
      auto with asmgen.
      split. rewrite nextinstr_inv. rewrite Pregmap.gss.
      exploit hi_lo_zero; eauto; intros.
      rewrite H; auto. auto with asmgen.
      intros; Simpl.
    + econstructor. split. unfold load_hilo; rewrite LO.
      eapply exec_straight_two.
      instantiate (1 := m). simpl; eauto. simpl; eauto. auto. auto.
      split. rewrite nextinstr_inv; auto with asmgen.
      rewrite Pregmap.gss; auto with asmgen.
      rewrite nextinstr_inv; auto with asmgen.
      rewrite Pregmap.gss; auto with asmgen.
      simpl. exploit hi_lo_add; eauto; intros.
      rewrite H; auto.
      intros; Simpl.
Qed.

(** Add integer immediate. *)

Lemma addimm_small_correct:
  forall rd r n tmp k rs m imm,
  tmp <> r ->
  make_immed n = Imm_single imm ->
  exists rs',
     exec_straight ge fn (addimm rd r n tmp k) rs m k rs' m
  /\ rs'#rd = Val.add rs#r (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
               rs' r = rs r.
Proof.
  intros. unfold addimm. destruct (make_immed n) eqn:IMM.
  econstructor; split. apply exec_straight_one; simpl; auto.
  split; intros; Simpl.
  discriminate.
Qed.

Lemma addimm_hi_correct:
  forall rd r n tmp k rs m hi lo,
  tmp <> r ->
  make_immed n = Imm_pair hi lo -> Int.eq lo Int.zero = true ->
  exists rs',
     exec_straight ge fn (addimm rd r n tmp k) rs m k rs' m
  /\ rs'#rd = Val.add rs#r (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
               rs' r = rs r.
Proof.
  intros until lo. intros TMP IMM LO. unfold addimm.
  destruct (make_immed n) eqn:MKIMM. discriminate. inv IMM.
  econstructor; split.
  unfold load_hilo. rewrite LO.
  eapply exec_straight_two; simpl. reflexivity. reflexivity.
  rewrite nextinstr_pc; rewrite Pregmap.gso; auto with asmgen. Simpl.
  split; Simpl. rewrite (hi_lo_zero n hi lo); auto with asmgen.
  intros; Simpl.
Qed.

Lemma addimm_large_correct:
  forall rd r n tmp k rs m hi lo,
  tmp <> r ->
  make_immed n = Imm_pair hi lo -> Int.eq lo Int.zero = false ->
  exists rs',
     exec_straight ge fn (addimm rd r n tmp k) rs m k rs' m
  /\ rs'#rd = Val.add rs#r (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
               rs' r = rs r.
Proof.
  intros until lo. intros TMP IMM LO. unfold addimm.
  destruct (make_immed n) eqn:MKIMM. discriminate. inv IMM.
  econstructor; split.
  unfold load_hilo. rewrite LO.
  eapply exec_straight_three; simpl; auto with asmgen.
  split; Simpl. simpl; rewrite (hi_lo_add n hi lo); auto.
  intros. Simpl.
Qed.

Lemma addimm_correct:
  forall rd r n tmp k rs m,
  tmp <> r ->
  exists rs',
     exec_straight ge fn (addimm rd r n tmp k) rs m k rs' m
  /\ rs'#rd = Val.add rs#r (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
               rs' r = rs r.
Proof.
  intros until m. intros TMP.
  destruct (make_immed n) eqn:IMM.
  - apply addimm_small_correct with imm; auto.
  - destruct (Int.eq lo Int.zero) eqn:LO.
    + apply addimm_hi_correct with hi lo; auto.
    + apply addimm_large_correct with hi lo; auto.
Qed.

(** And integer immediate. *)

Lemma andimm_small_correct:
  forall rd r n tmp k rs m imm,
  tmp <> r ->
  make_immed n = Imm_single imm ->
  exists rs',
    exec_straight ge fn (andimm rd r n tmp k) rs m k rs' m
    /\ rs'#rd = Val.and rs#r (Vint n)
    /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
                 rs' r = rs r.
Proof.
  intros. unfold andimm. destruct (make_immed n) eqn:IMM.
  econstructor; split. apply exec_straight_one; simpl; auto.
  split; intros; Simpl.
  discriminate.
Qed.

Lemma andimm_hi_correct:
  forall rd r n tmp k rs m hi lo,
  tmp <> r ->
  make_immed n = Imm_pair hi lo -> Int.eq lo Int.zero = true ->
  exists rs',
     exec_straight ge fn (andimm rd r n tmp k) rs m k rs' m
  /\ rs'#rd = Val.and rs#r (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
               rs' r = rs r.
Proof.
  intros until lo. intros TMP IMM LO. unfold andimm.
  destruct (make_immed n) eqn:MKIMM. discriminate. inv IMM.
  econstructor; split.
  unfold load_hilo. rewrite LO.
  eapply exec_straight_two; simpl. reflexivity. reflexivity.
  rewrite nextinstr_pc; rewrite Pregmap.gso; auto with asmgen. Simpl.
  split; Simpl. rewrite (hi_lo_zero n hi lo); auto with asmgen.
  intros; Simpl.
Qed.

Lemma andimm_large_correct:
  forall rd r n tmp k rs m hi lo,
  tmp <> r ->
  make_immed n = Imm_pair hi lo -> Int.eq lo Int.zero = false ->
  exists rs',
     exec_straight ge fn (andimm rd r n tmp k) rs m k rs' m
  /\ rs'#rd = Val.and rs#r (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
               rs' r = rs r.
Proof.
  intros until lo. intros TMP IMM LO. unfold andimm.
  destruct (make_immed n) eqn:MKIMM. discriminate. inv IMM.
  econstructor; split.
  unfold load_hilo. rewrite LO.
  eapply exec_straight_three; simpl; auto with asmgen.
  split; Simpl. simpl; rewrite (hi_lo_add n hi lo); auto.
  intros. Simpl.
Qed.

Lemma andimm_correct:
  forall rd r n tmp k rs m,
  tmp <> r ->
  exists rs',
     exec_straight ge fn (andimm rd r n tmp k) rs m k rs' m
  /\ rs'#rd = Val.and rs#r (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
               rs' r = rs r.
Proof.
  intros until m. intros TMP.
  destruct (make_immed n) eqn:IMM.
  - apply andimm_small_correct with imm; auto.
  - destruct (Int.eq lo Int.zero) eqn:LO.
    + apply andimm_hi_correct with hi lo; auto.
    + apply andimm_large_correct with hi lo; auto.
Qed.

(** Or integer immediate. *)

Lemma orimm_small_correct:
  forall rd r n tmp k rs m imm,
  tmp <> r ->
  make_immed n = Imm_single imm ->
  exists rs',
     exec_straight ge fn (orimm rd r n tmp k) rs m k rs' m
  /\ rs'#rd = Val.or rs#r (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
               rs' r = rs r.
Proof.
  intros. unfold orimm. destruct (make_immed n) eqn:IMM.
  econstructor; split. apply exec_straight_one; simpl; auto.
  split; intros; Simpl.
  discriminate.
Qed.

Lemma orimm_hi_correct:
  forall rd r n tmp k rs m hi lo,
  tmp <> r ->
  make_immed n = Imm_pair hi lo -> Int.eq lo Int.zero = true ->
  exists rs',
     exec_straight ge fn (orimm rd r n tmp k) rs m k rs' m
  /\ rs'#rd = Val.or rs#r (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
               rs' r = rs r.
Proof.
  intros until lo. intros TMP IMM LO. unfold orimm.
  destruct (make_immed n) eqn:MKIMM. discriminate. inv IMM.
  econstructor; split.
  unfold load_hilo. rewrite LO.
  eapply exec_straight_two; simpl. reflexivity. reflexivity.
  rewrite nextinstr_pc; rewrite Pregmap.gso; auto with asmgen. Simpl.
  split; Simpl. rewrite (hi_lo_zero n hi lo); auto with asmgen.
  intros; Simpl.
Qed.

Lemma orimm_large_correct:
  forall rd r n tmp k rs m hi lo,
  tmp <> r ->
  make_immed n = Imm_pair hi lo -> Int.eq lo Int.zero = false ->
  exists rs',
     exec_straight ge fn (orimm rd r n tmp k) rs m k rs' m
  /\ rs'#rd = Val.or rs#r (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
               rs' r = rs r.
Proof.
  intros until lo. intros TMP IMM LO. unfold orimm.
  destruct (make_immed n) eqn:MKIMM. discriminate. inv IMM.
  econstructor; split.
  unfold load_hilo. rewrite LO.
  eapply exec_straight_three; simpl; auto with asmgen.
  split; Simpl. simpl; rewrite (hi_lo_add n hi lo); auto.
  intros. Simpl.
Qed.

Lemma orimm_correct:
  forall rd r n tmp k rs m,
  tmp <> r ->
  exists rs',
     exec_straight ge fn (orimm rd r n tmp k) rs m k rs' m
  /\ rs'#rd = Val.or rs#r (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
               rs' r = rs r.
Proof.
  intros until m. intros TMP.
  destruct (make_immed n) eqn:IMM.
  - apply orimm_small_correct with imm; auto.
  - destruct (Int.eq lo Int.zero) eqn:LO.
    + apply orimm_hi_correct with hi lo; auto.
    + apply orimm_large_correct with hi lo; auto.
Qed.

(** Xor integer immediate. *)

Lemma xorimm_small_correct:
  forall rd r n tmp k rs m imm,
  tmp <> r ->
  make_immed n = Imm_single imm ->
  exists rs',
     exec_straight ge fn (xorimm rd r n tmp k) rs m k rs' m
  /\ rs'#rd = Val.xor rs#r (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
               rs' r = rs r.
Proof.
  intros. unfold xorimm. destruct (make_immed n) eqn:IMM.
  econstructor; split. apply exec_straight_one; simpl; auto.
  split; intros; Simpl.
  discriminate.
Qed.

Lemma xorimm_hi_correct:
  forall rd r n tmp k rs m hi lo,
  tmp <> r ->
  make_immed n = Imm_pair hi lo -> Int.eq lo Int.zero = true ->
  exists rs',
     exec_straight ge fn (xorimm rd r n tmp k) rs m k rs' m
  /\ rs'#rd = Val.xor rs#r (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
               rs' r = rs r.
Proof.
  intros until lo. intros TMP IMM LO. unfold xorimm.
  destruct (make_immed n) eqn:MKIMM. discriminate. inv IMM.
  econstructor; split.
  unfold load_hilo. rewrite LO.
  eapply exec_straight_two; simpl. reflexivity. reflexivity.
  rewrite nextinstr_pc; rewrite Pregmap.gso; auto with asmgen. Simpl.
  split; Simpl. rewrite (hi_lo_zero n hi lo); auto with asmgen.
  intros; Simpl.
Qed.

Lemma xorimm_large_correct:
  forall rd r n tmp k rs m hi lo,
  tmp <> r ->
  make_immed n = Imm_pair hi lo -> Int.eq lo Int.zero = false ->
  exists rs',
     exec_straight ge fn (xorimm rd r n tmp k) rs m k rs' m
  /\ rs'#rd = Val.xor rs#r (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
               rs' r = rs r.
Proof.
  intros until lo. intros TMP IMM LO. unfold xorimm.
  destruct (make_immed n) eqn:MKIMM. discriminate. inv IMM.
  econstructor; split.
  unfold load_hilo. rewrite LO.
  eapply exec_straight_three; simpl; auto with asmgen.
  split; Simpl. simpl; rewrite (hi_lo_add n hi lo); auto.
  intros. Simpl.
Qed.

Lemma xorimm_correct:
  forall rd r n tmp k rs m,
  tmp <> r ->
  exists rs',
     exec_straight ge fn (xorimm rd r n tmp k) rs m k rs' m
  /\ rs'#rd = Val.xor rs#r (Vint n)
  /\ forall r, data_preg r = true -> r <> rd -> r <> tmp ->
               rs' r = rs r.
Proof.
  intros until m. intros TMP.
  destruct (make_immed n) eqn:IMM.
  - apply xorimm_small_correct with imm; auto.
  - destruct (Int.eq lo Int.zero) eqn:LO.
    + apply xorimm_hi_correct with hi lo; auto.
    + apply xorimm_large_correct with hi lo; auto.
Qed.

(** Translation of conditionals *)

Ltac ArgsInv :=
  repeat (match goal with
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: match ?args with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct args
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H
  | [ H: match _ with left _ => _ | right _ => assertion_failed end = OK _ |- _ ] => monadInv H
  | [ H: match _ with true => _ | false => assertion_failed end = OK _ |- _ ] => monadInv H
  end);
  subst;
  repeat (match goal with
  | [ H: ireg_of ?x = OK ?y |- _ ] => simpl in *; rewrite (ireg_of_eq _ _ H) in *
  | [ H: freg_of ?x = OK ?y |- _ ] => simpl in *; rewrite (freg_of_eq _ _ H) in *
  end).

Lemma transl_cond_float_correct:
  forall cmp rd farg1 farg2 k rs m c b,
  transl_cond_float cmp rd farg1 farg2 k = OK c ->
  Val.cmpf cmp rs#(preg_of farg1) rs#(preg_of farg2) = b ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of rd) = Val.cmpf cmp rs#(preg_of farg1) rs#(preg_of farg2)
  /\ forall r, data_preg r = true -> r <> preg_of rd -> rs' r = rs r.
Proof.
  intros until b. intros TR CND.
  unfold transl_cond_float in TR; destruct cmp; ArgsInv.
  - (* Ceq *)
    econstructor. split.
    apply exec_straight_one; simpl. reflexivity. Simpl.
    split. Simpl. intros; Simpl.
  - (* Cne *)
    econstructor. split.
    eapply exec_straight_two; simpl. reflexivity; Simpl.
    reflexivity. Simpl. Simpl.
    split. rewrite nextinstr_inv.
    rewrite (nextinstr_inv x (rs # x <- (Val.cmpf Ceq (rs x0) (rs x1))) (ireg_not_PC x)).
    rewrite Pregmap.gss. rewrite Pregmap.gss.
    unfold Val.cmpf, Val.cmpf_bool; destruct (rs x0); destruct (rs x1); auto.
    rewrite Float.cmp_ne_eq. destruct (Float.cmp Ceq f f0); simpl; auto.
    apply (ireg_not_PC x).
    intros; Simpl.
  - (* Clt *)
    econstructor. split.
    apply exec_straight_one; simpl. reflexivity. Simpl.
    split. Simpl. intros; Simpl.
  - (* Cle *)
    econstructor. split.
    apply exec_straight_one; simpl. reflexivity. Simpl.
    split. Simpl. intros; Simpl.
  - (* Cgt *)
    econstructor. split.
    eapply exec_straight_one; simpl. reflexivity. Simpl.
    split. Simpl.
    unfold Val.cmpf, Val.cmpf_bool; destruct (rs x0); destruct (rs x1); auto.
    rewrite <- (Float.cmp_swap Clt f f0). simpl. auto.
    intros; Simpl.
  - (* Cge *)
    econstructor. split.
    apply exec_straight_one; simpl. reflexivity. Simpl.
    split. Simpl.
    unfold Val.cmpf, Val.cmpf_bool; destruct (rs x0); destruct (rs x1); auto.
    rewrite <- (Float.cmp_swap Cge f0 f). simpl. auto.
    intros; Simpl.
Qed.

Lemma transl_cond_float_correct2:
  forall cmp rd farg1 farg2 k rs m c,
  transl_cond_float cmp rd farg1 farg2 k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef
       (Val.cmpf cmp rs#(preg_of farg1) rs#(preg_of farg2))
       (rs' (preg_of rd))
  /\ forall r : preg, data_preg r = true -> r <> preg_of rd -> rs' r = rs r.
Proof.
  intros until c. intro TR.
  destruct (Val.cmpf cmp rs#(preg_of farg1) rs#(preg_of farg2)) eqn:CMP.
  - (* vundef *)
    generalize (transl_cond_float_correct cmp rd farg1 farg2 k rs m c Vundef).
    intros [rs' [EX [RES INV]]]; auto. exists rs'; split; auto.
  - (* vint *)
    generalize (transl_cond_float_correct cmp rd farg1 farg2 k rs m c (Vint i)).
    intros [rs' [EX [RES INV]]]; auto. exists rs'; split; auto.
    split. rewrite CMP in RES. rewrite <- RES; auto with asmgen.
    auto with asmgen.
  - (* vlong *)
    generalize (transl_cond_float_correct cmp rd farg1 farg2 k rs m c (Vlong i)).
    intros [rs' [EX [RES INV]]]; auto. exists rs'; split; auto.
    split. rewrite CMP in RES. rewrite <- RES; auto with asmgen.
    auto with asmgen.
  - (* vfloat *)
    generalize (transl_cond_float_correct cmp rd farg1 farg2 k rs m c (Vfloat f)).
    intros [rs' [EX [RES INV]]]; auto. exists rs'; split; auto.
    split. rewrite CMP in RES. rewrite <- RES; auto with asmgen.
    auto with asmgen.
  - (* vsingle *)
    generalize (transl_cond_float_correct cmp rd farg1 farg2 k rs m c (Vsingle f)).
    intros [rs' [EX [RES INV]]]; auto. exists rs'; split; auto.
    split. rewrite CMP in RES. rewrite <- RES; auto with asmgen.
    auto with asmgen.
  - (* vptr *)
    generalize (transl_cond_float_correct cmp rd farg1 farg2 k rs m c (Vptr b i)).
    intros [rs' [EX [RES INV]]]; auto. exists rs'; split; auto.
    split. rewrite CMP in RES. rewrite <- RES; auto with asmgen.
    auto with asmgen.
Qed.

Lemma transl_cond_single_correct:
  forall cmp rd farg1 farg2 k rs m c b,
  transl_cond_single cmp rd farg1 farg2 k = OK c ->
  Val.cmpfs cmp rs#(preg_of farg1) rs#(preg_of farg2) = b ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of rd) = Val.cmpfs cmp rs#(preg_of farg1) rs#(preg_of farg2)
  /\ forall r, data_preg r = true -> r <> preg_of rd -> rs' r = rs r.
Proof.
  intros until b. intros TR CND.
  unfold transl_cond_single in TR; destruct cmp; ArgsInv.
  - (* Ceq *)
    econstructor. split.
    apply exec_straight_one; simpl. reflexivity. Simpl.
    split. Simpl. intros; Simpl.
  - (* Cne *)
    econstructor. split.
    eapply exec_straight_two; simpl. reflexivity; Simpl.
    reflexivity. Simpl. Simpl.
    split. rewrite nextinstr_inv.
    rewrite (nextinstr_inv x (rs # x <- (Val.cmpfs Ceq (rs x0) (rs x1))) (ireg_not_PC x)).
    rewrite Pregmap.gss. rewrite Pregmap.gss.
    unfold Val.cmpfs, Val.cmpfs_bool; destruct (rs x0); destruct (rs x1); auto.
    rewrite Float32.cmp_ne_eq. destruct (Float32.cmp Ceq f f0); simpl; auto.
    apply (ireg_not_PC x).
    intros; Simpl.
  - (* Clt *)
    econstructor. split.
    apply exec_straight_one; simpl. reflexivity. Simpl.
    split. Simpl. intros; Simpl.
  - (* Cle *)
    econstructor. split.
    apply exec_straight_one; simpl. reflexivity. Simpl.
    split. Simpl. intros; Simpl.
  - (* Cgt *)
    econstructor. split.
    eapply exec_straight_one; simpl. reflexivity. Simpl.
    split. Simpl.
    unfold Val.cmpfs, Val.cmpfs_bool; destruct (rs x0); destruct (rs x1); auto.
    rewrite <- (Float32.cmp_swap Clt f f0). simpl. auto.
    intros; Simpl.
  - (* Cge *)
    econstructor. split.
    apply exec_straight_one; simpl. reflexivity. Simpl.
    split. Simpl.
    unfold Val.cmpfs, Val.cmpfs_bool; destruct (rs x0); destruct (rs x1); auto.
    rewrite <- (Float32.cmp_swap Cge f0 f). simpl. auto.
    intros; Simpl.
Qed.

Lemma transl_cond_single_correct2:
  forall cmp rd farg1 farg2 k rs m c,
  transl_cond_single cmp rd farg1 farg2 k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef
       (Val.cmpfs cmp rs#(preg_of farg1) rs#(preg_of farg2))
       (rs' (preg_of rd))
  /\ forall r : preg, data_preg r = true -> r <> preg_of rd -> rs' r = rs r.
Proof.
  intros until c. intro TR.
  destruct (Val.cmpfs cmp rs#(preg_of farg1) rs#(preg_of farg2)) eqn:CMP.
  - (* vundef *)
    generalize (transl_cond_single_correct cmp rd farg1 farg2 k rs m c Vundef).
    intros [rs' [EX [RES INV]]]; auto. exists rs'; split; auto.
  - (* vint *)
    generalize (transl_cond_single_correct cmp rd farg1 farg2 k rs m c (Vint i)).
    intros [rs' [EX [RES INV]]]; auto. exists rs'; split; auto.
    split. rewrite CMP in RES. rewrite <- RES; auto with asmgen.
    auto with asmgen.
  - (* vlong *)
    generalize (transl_cond_single_correct cmp rd farg1 farg2 k rs m c (Vlong i)).
    intros [rs' [EX [RES INV]]]; auto. exists rs'; split; auto.
    split. rewrite CMP in RES. rewrite <- RES; auto with asmgen.
    auto with asmgen.
  - (* vfloat *)
    generalize (transl_cond_single_correct cmp rd farg1 farg2 k rs m c (Vfloat f)).
    intros [rs' [EX [RES INV]]]; auto. exists rs'; split; auto.
    split. rewrite CMP in RES. rewrite <- RES; auto with asmgen.
    auto with asmgen.
  - (* vsingle *)
    generalize (transl_cond_single_correct cmp rd farg1 farg2 k rs m c (Vsingle f)).
    intros [rs' [EX [RES INV]]]; auto. exists rs'; split; auto.
    split. rewrite CMP in RES. rewrite <- RES; auto with asmgen.
    auto with asmgen.
  - (* vptr *)
    generalize (transl_cond_single_correct cmp rd farg1 farg2 k rs m c (Vptr b i)).
    intros [rs' [EX [RES INV]]]; auto. exists rs'; split; auto.
    split. rewrite CMP in RES. rewrite <- RES; auto with asmgen.
    auto with asmgen.
Qed.

Lemma transl_cond_int_false_correct:
  forall cond arg1 arg2 lbl k rs m c,
  transl_cond_int cond arg1 arg2 lbl k = OK c ->
  eval_condition cond (map rs (map preg_of (arg1 :: arg2 :: nil))) m = Some false ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ forall r, data_preg r = true -> preg_notin r (destroyed_by_cond cond) -> rs'#r = rs r.
Proof.
  intros until c. intros TR COND.
  unfold transl_cond_int in TR; destruct cond; ArgsInv.
  - (* Ccomp *)
    econstructor. split. destruct c0; simpl in COND.
    + (* Ceq *)
      monadInv EQ2. apply exec_straight_one; simpl.
      unfold eval_branch. rewrite COND. auto. apply nextinstr_pc.
    + (* Cne *)
      monadInv EQ2. apply exec_straight_one; simpl.
      unfold eval_branch. rewrite COND. auto. apply nextinstr_pc.
    + (* Clt *)
      monadInv EQ2. apply exec_straight_one; simpl.
      unfold eval_branch. rewrite COND. auto. apply nextinstr_pc.
    + (* Cle *)
      monadInv EQ2. apply exec_straight_one; simpl.
      unfold eval_branch. rewrite <- Val.swap_cmp_bool; simpl.
      rewrite COND. auto.  apply nextinstr_pc.
    + (* Cgt *)
      monadInv EQ2. apply exec_straight_one; simpl.
      unfold eval_branch. rewrite <- Val.swap_cmp_bool; simpl.
      rewrite COND. auto.  apply nextinstr_pc.
    + (* Cge *)
      monadInv EQ2. apply exec_straight_one; simpl.
      unfold eval_branch. rewrite COND. auto. apply nextinstr_pc.
    + (* reg inv *)
      intros; Simpl.
  - (* Ccompu *)
    econstructor. split. destruct c0; simpl in COND.
    + (* Ceq *)
      monadInv EQ2. apply exec_straight_one; simpl.
      unfold eval_u_branch. rewrite COND. auto. apply nextinstr_pc.
    + (* Cne *)
      monadInv EQ2. apply exec_straight_one; simpl.
      unfold eval_u_branch. rewrite COND. auto. apply nextinstr_pc.
    + (* Clt *)
      monadInv EQ2. apply exec_straight_one; simpl.
      unfold eval_u_branch. rewrite COND. auto. apply nextinstr_pc.
    + (* Cle *)
      monadInv EQ2. apply exec_straight_one; simpl.
      unfold eval_u_branch. rewrite <- Val.swap_cmpu_bool; simpl.
      rewrite COND. auto.  apply nextinstr_pc.
    + (* Cgt *)
      monadInv EQ2. apply exec_straight_one; simpl.
      unfold eval_u_branch. rewrite <- Val.swap_cmpu_bool; simpl.
      rewrite COND. auto.  apply nextinstr_pc.
    + (* Cge *)
      monadInv EQ2. apply exec_straight_one; simpl.
      unfold eval_u_branch. rewrite COND. auto. apply nextinstr_pc.
    + (* reg inv *)
      intros; Simpl.
Qed.

Lemma transl_cond_false_correct:
  forall cond args lbl k rs m c,
  transl_cond cond args lbl k = OK c ->
  eval_condition cond (map rs (map preg_of args)) m = Some false ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ forall r, data_preg r = true -> preg_notin r (destroyed_by_cond cond) -> rs'#r = rs r.
Proof.
Local Transparent destroyed_by_cond.
  intros until c. intros TR COND.
  unfold transl_cond in TR; destruct cond; ArgsInv.
  - (* Ccomp *)
    apply (transl_cond_int_false_correct (Ccomp c0) m0 m1 lbl k rs m c TR COND).
  - (* Ccompu *)
    apply (transl_cond_int_false_correct (Ccompu c0) m0 m1 lbl k rs m c TR COND).
  - (* Ccompimm *)
    generalize (loadimm_correct x i x0 rs m). intros [lirs [P [Q R]]].
    generalize (transl_cond_int_false_correct (Ccomp c0) m0 (int_temp_for m0) lbl k lirs m x0 EQ1).
    simpl in COND; simpl. rewrite (ireg_of_eq (int_temp_for m0) x EQ). rewrite Q.
    rewrite R; auto with asmgen.
    intros [rs' [EX INV]]; auto.
    exists rs'. split.
    eapply exec_straight_trans. eauto. auto.
    intros; Simpl. inv H0.
    rewrite INV; auto with asmgen. rewrite R; auto with asmgen.
    generalize (int_temp_R5_R6 m0); intros [R5 | R6].
    rewrite R5 in EQ; inv EQ; auto.
    rewrite R6 in EQ; inv EQ; auto.
    apply (int_temp_ne m0 x EQ).
  - (* Compuimm *)
    generalize (loadimm_correct x i x0 rs m). intros [lirs [P [Q R]]].
    generalize (transl_cond_int_false_correct (Ccompu c0) m0 (int_temp_for m0) lbl k lirs m x0 EQ1).
    simpl in COND; simpl. rewrite (ireg_of_eq (int_temp_for m0) x EQ). rewrite Q.
    rewrite R; auto with asmgen.
    intros [rs' [EX INV]]; auto.
    exists rs'. split.
    eapply exec_straight_trans. eauto. auto.
    intros; Simpl. inv H0.
    rewrite INV; auto with asmgen. rewrite R; auto with asmgen.
    generalize (int_temp_R5_R6 m0); intros [R5 | R6].
    rewrite R5 in EQ; inv EQ; auto.
    rewrite R6 in EQ; inv EQ; auto.
    apply (int_temp_ne m0 x EQ).
  - (* Ccompf *)
    simpl in COND.
    exploit (transl_cond_float_correct c0 R5 m0 m1 (Pbnez X5 lbl :: k) rs m c Vfalse); auto.
    unfold Val.cmpf; rewrite COND; auto.
    intros [rs1 [EX [RES INV]]].
    unfold Val.cmpf in RES; rewrite COND in RES; simpl in RES.
    econstructor; split.
    eapply exec_straight_trans. apply EX.
    apply exec_straight_one. simpl. rewrite RES.
    unfold eval_branch, Vzero, Vfalse; simpl.
    rewrite Int.eq_true; simpl. reflexivity. apply nextinstr_pc.
    intros; Simpl.
  - (* Cnotcompf *)
    simpl in COND; unfold option_map in COND.
    destruct (Val.cmpf_bool c0 (rs (preg_of m0)) (rs (preg_of m1))) eqn:CMPF; inv COND.
    rewrite negb_false_iff in H0; subst b.
    exploit (transl_cond_float_correct  c0 R5 m0 m1 (Pbeqz X5 lbl :: k) rs m c Vtrue); auto.
    unfold Val.cmpf; rewrite CMPF; auto.
    intros [rs1 [EX [RES INV]]].
    unfold Val.cmpf in RES. rewrite CMPF in RES; simpl in RES.
    econstructor; split.
    eapply exec_straight_trans. apply EX.
    apply exec_straight_one. simpl. rewrite RES.
    unfold eval_branch, Vtrue, Vzero; simpl.
    rewrite Int.eq_false. reflexivity. apply Int.one_not_zero.
    apply nextinstr_pc.
    intros; Simpl.
  - (* Ccompfs *)
    simpl in COND.
    exploit (transl_cond_single_correct c0 R5 m0 m1 (Pbnez X5 lbl :: k) rs m c Vfalse); auto.
    unfold Val.cmpfs; rewrite COND; auto.
    intros [rs1 [EX [RES INV]]].
    unfold Val.cmpfs in RES; rewrite COND in RES; simpl in RES.
    econstructor; split.
    eapply exec_straight_trans. apply EX.
    apply exec_straight_one. simpl. rewrite RES.
    unfold eval_branch, Vzero, Vfalse; simpl.
    rewrite Int.eq_true; simpl. reflexivity. apply nextinstr_pc.
    intros; Simpl.
  - (* Cnotcompfs *)
    simpl in COND; unfold option_map in COND.
    destruct (Val.cmpfs_bool c0 (rs (preg_of m0)) (rs (preg_of m1))) eqn:CMPF; inv COND.
    rewrite negb_false_iff in H0; subst b.
    exploit (transl_cond_single_correct c0 R5 m0 m1 (Pbeqz X5 lbl :: k) rs m c Vtrue); auto.
    unfold Val.cmpfs; rewrite CMPF; auto.
    intros [rs1 [EX [RES INV]]].
    unfold Val.cmpfs in RES. rewrite CMPF in RES; simpl in RES.
    econstructor; split.
    eapply exec_straight_trans. apply EX.
    apply exec_straight_one. simpl. rewrite RES.
    unfold eval_branch, Vtrue, Vzero; simpl.
    rewrite Int.eq_false. reflexivity. apply Int.one_not_zero.
    apply nextinstr_pc.
    intros; Simpl.
Qed.

Lemma transl_cond_int_true_correct:
  forall cond arg1 arg2 lbl k rs m c,
  transl_cond_int cond arg1 arg2 lbl k = OK c ->
  eval_condition cond (map rs (map preg_of (arg1 :: arg2 :: nil))) m = Some true ->
  exists jmp,
     c = jmp :: k
  /\ exec_instr ge fn jmp rs m = goto_label fn lbl rs m.
Proof.
  intros until c. intros TR COND.
  unfold transl_cond_int in TR; destruct cond; ArgsInv.
  - (* Ccomp *)
    destruct c0; auto. monadInv EQ2.
    + (* Ceq *)
      exists (Pbeq x x0 lbl). split. auto.
      simpl. unfold eval_branch. rewrite COND; auto.
    + (* Cne *)
      monadInv EQ2. exists (Pbne x x0 lbl). split. auto.
      simpl. unfold eval_branch. rewrite COND; auto.
    + (* Clt *)
      monadInv EQ2. exists (Pblt x x0 lbl). split. auto.
      simpl. unfold eval_branch. rewrite COND; auto.
    + (* Cle *)
      monadInv EQ2. exists (Pbge x0 x lbl). split. auto.
      simpl. unfold eval_branch.
      rewrite <- Val.swap_cmp_bool in COND; simpl in COND.
      rewrite COND; auto.
    + (* Cgt *)
      monadInv EQ2. exists (Pblt x0 x lbl). split. auto.
      simpl. unfold eval_branch.
      rewrite <- Val.swap_cmp_bool in COND; simpl in COND.
      rewrite COND; auto.
    + (* Cge *)
      monadInv EQ2. exists (Pbge x x0 lbl). split. auto.
      simpl. unfold eval_branch. rewrite COND; auto.
  - (* Ccompu *)
    destruct c0; auto. monadInv EQ2.
    + (* Ceq *)
      exists (Pbequ x x0 lbl). split. auto.
      simpl. unfold eval_u_branch. rewrite COND; auto.
    + (* Cne *)
      monadInv EQ2. exists (Pbneu x x0 lbl). split. auto.
      simpl. unfold eval_u_branch. rewrite COND; auto.
    + (* Clt *)
      monadInv EQ2. exists (Pbltu x x0 lbl). split. auto.
      simpl. unfold eval_u_branch. rewrite COND; auto.
    + (* Cle *)
      monadInv EQ2. exists (Pbgeu x0 x lbl). split. auto.
      simpl. unfold eval_u_branch.
      rewrite <- Val.swap_cmpu_bool in COND; simpl in COND.
      rewrite COND; auto.
    + (* Cgt *)
      monadInv EQ2. exists (Pbltu x0 x lbl). split. auto.
      simpl. unfold eval_u_branch.
      rewrite <- Val.swap_cmpu_bool in COND; simpl in COND.
      rewrite COND; auto.
    + (* Cge *)
      monadInv EQ2. exists (Pbgeu x x0 lbl). split. auto.
      simpl. unfold eval_u_branch. rewrite COND; auto.
Qed.

Lemma transl_cond_true_correct:
  forall cond args lbl k rs m c,
  transl_cond cond args lbl k = OK c ->
  eval_condition cond (map rs (map preg_of args)) m = Some true ->
     (exists rs' jmp,
         exec_straight ge fn c rs m (jmp :: k) rs' m
      /\ exec_instr ge fn jmp rs' m = goto_label fn lbl rs' m
      /\ forall r, data_preg r = true -> preg_notin r (destroyed_by_cond cond) -> rs'#r = rs r)
  \/ (exists jmp,
         c = jmp :: k
      /\ exec_instr ge fn jmp rs m = goto_label fn lbl rs m).
Proof.
Local Transparent destroyed_by_cond.
  intros until c. intros TR COND.
  unfold transl_cond in TR; destruct cond; ArgsInv.
  - (* Ccomp *)
    generalize (transl_cond_int_true_correct (Ccomp c0) m0 m1 lbl k rs m c TR COND).
    intros [jmp [C EX]].
    right. exists jmp.
    split; auto.
  - (* Ccompu *)
    generalize (transl_cond_int_true_correct (Ccompu c0) m0 m1 lbl k rs m c TR COND).
    intros [jmp [C EX]].
    right. exists jmp.
    split; auto.
  - (* Ccompimm *)
    generalize (loadimm_correct x i x0 rs m). intros [lirs [P [Q R]]].
    generalize (transl_cond_int_true_correct (Ccomp c0) m0 (int_temp_for m0) lbl k lirs m x0 EQ1).
    simpl in COND; simpl. rewrite (ireg_of_eq (int_temp_for m0) x EQ). rewrite Q.
    rewrite R; auto with asmgen.
    intros [jmp [CONT EX]]; auto. left.
    exists lirs, jmp. subst x0.
    split; auto. split. auto.
    intros; Simpl. inv H0. rewrite R; auto with asmgen.
    generalize (int_temp_R5_R6 m0); intros [R5 | R6].
    rewrite R5 in EQ; inv EQ; auto.
    rewrite R6 in EQ; inv EQ; auto.
    apply (int_temp_ne m0 x EQ).
  - (* Ccompuimm *)
    generalize (loadimm_correct x i x0 rs m). intros [lirs [P [Q R]]].
    generalize (transl_cond_int_true_correct (Ccompu c0) m0 (int_temp_for m0) lbl k lirs m x0 EQ1).
    simpl in COND; simpl. rewrite (ireg_of_eq (int_temp_for m0) x EQ). rewrite Q.
    rewrite R; auto with asmgen.
    intros [jmp [CONT EX]]; auto. left.
    exists lirs, jmp. subst x0.
    split; auto. split. auto.
    intros; Simpl. inv H0. rewrite R; auto with asmgen.
    generalize (int_temp_R5_R6 m0); intros [R5 | R6].
    rewrite R5 in EQ; inv EQ; auto.
    rewrite R6 in EQ; inv EQ; auto.
    apply (int_temp_ne m0 x EQ).
  - (* Ccompf *)
    simpl in COND.
    exploit (transl_cond_float_correct c0 R5 m0 m1 (Pbnez X5 lbl :: k) rs m c Vtrue); auto.
    unfold Val.cmpf; rewrite COND; auto.
    intros [rs1 [EX [RES INV]]].
    unfold Val.cmpf in RES; rewrite COND in RES; simpl in RES.
    left. econstructor. exists (Pbnez X5 lbl).
    split; eauto.
    split. simpl. rewrite RES. unfold eval_branch; simpl.
    rewrite Int.eq_false. simpl; auto.
    apply Int.one_not_zero.
    simpl; simpl in INV; auto.
  - (* Cnotcompf *)
    simpl in COND; unfold option_map in COND.
    destruct (Val.cmpf_bool c0 (rs (preg_of m0)) (rs (preg_of m1))) eqn:CMPF; inv COND.
    rewrite negb_true_iff in H0; subst b.
    exploit (transl_cond_float_correct  c0 R5 m0 m1 (Pbeqz X5 lbl :: k) rs m c Vfalse); auto.
    unfold Val.cmpf; rewrite CMPF; auto.
    intros [rs1 [EX [RES INV]]].
    unfold Val.cmpf in RES. rewrite CMPF in RES; simpl in RES.
    left. econstructor. exists (Pbeqz X5 lbl).
    split; eauto.
    split. simpl. rewrite RES. unfold eval_branch; simpl.
    rewrite Int.eq_true. auto.
    simpl; simpl in INV; auto.
  - (* Ccompfs *)
    simpl in COND.
    exploit (transl_cond_single_correct c0 R5 m0 m1 (Pbnez X5 lbl :: k) rs m c Vtrue); auto.
    unfold Val.cmpfs; rewrite COND; auto.
    intros [rs1 [EX [RES INV]]].
    unfold Val.cmpfs in RES; rewrite COND in RES; simpl in RES.
    left. econstructor. exists (Pbnez X5 lbl).
    split; eauto.
    split. simpl. rewrite RES. unfold eval_branch; simpl.
    rewrite Int.eq_false. simpl; auto.
    apply Int.one_not_zero.
    simpl; simpl in INV; auto.
  - (* Cnotcompfs *)
    simpl in COND; unfold option_map in COND.
    destruct (Val.cmpfs_bool c0 (rs (preg_of m0)) (rs (preg_of m1))) eqn:CMPF; inv COND.
    rewrite negb_true_iff in H0; subst b.
    exploit (transl_cond_single_correct  c0 R5 m0 m1 (Pbeqz X5 lbl :: k) rs m c Vfalse); auto.
    unfold Val.cmpfs; rewrite CMPF; auto.
    intros [rs1 [EX [RES INV]]].
    unfold Val.cmpfs in RES. rewrite CMPF in RES; simpl in RES.
    left. econstructor. exists (Pbeqz X5 lbl).
    split; eauto.
    split. simpl. rewrite RES. unfold eval_branch; simpl.
    rewrite Int.eq_true. auto.
    simpl; simpl in INV; auto.
Qed.

(** Indexed memory accesses. *)

Lemma indexed_memory_access_correct:
  forall (P: regset -> Prop) (mk_instr: ireg -> int -> instruction)
         (base: ireg) n k (rs: regset) m m',
  base <> RA ->
  (forall (r1: ireg) (rs1: regset) n1 k,
     Val.add rs1#r1 (Vint n1) = Val.add rs#base (Vint n) ->
     (forall (r: preg), if_preg r = true -> r <> RA -> rs1 r = rs r) ->
     exists rs',
       exec_straight ge fn (mk_instr r1 n1 :: k) rs1 m k rs' m' /\ P rs') ->
  exists rs',
     exec_straight ge fn (indexed_memory_access mk_instr base n k) rs m k rs' m'
  /\ P rs'.
Proof.
  intros until m'. intros BASE SEM.
  unfold indexed_memory_access.
  destruct (make_immed n) eqn:IMM.
  - apply SEM; auto.
  - destruct (load_hibase_correct RA base hi (mk_instr RA lo :: k) rs m BASE)
      as (rs1 & A & B & C).
    destruct (SEM X1 rs1 lo k) as (rs2 & D & E).
    rewrite B. rewrite Val.add_assoc. f_equal. simpl.
    rewrite (hi_lo_add n hi lo IMM); auto. auto.
    exists rs2. split. eapply exec_straight_trans; eauto.
    auto.
Qed.

Lemma loadind_int_correct:
  forall (base: ireg) ofs dst (rs: regset) m v k,
  base <> RA ->
  Mem.loadv Mint32 m (Val.add rs#base (Vint ofs)) = Some v ->
  exists rs',
     exec_straight ge fn (loadind_int base ofs dst k) rs m k rs' m
  /\ rs'#dst = v
  /\ forall r, if_preg r = true -> r <> RA -> r <> dst -> rs'#r = rs#r.
Proof.
  intros until k. intros BASE LOAD.
  unfold loadind_int. apply indexed_memory_access_correct; intros; auto.
  econstructor; split.
  apply exec_straight_one. simpl. unfold exec_load.
  rewrite H. rewrite LOAD. eauto. auto.
  split; intros; Simpl.
Qed.

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k c (rs: regset) m v,
  base <> RA ->
  loadind base ofs ty dst k = OK c ->
  Mem.loadv (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, if_preg r = true -> r <> RA -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  unfold loadind. intros until v. intros BASE TR LOAD.
  destruct ty; destruct (preg_of dst); inv TR; simpl in LOAD.
  - (* int *)
    apply loadind_int_correct; auto.
  - (* float *)
    apply indexed_memory_access_correct; intros; auto.
    econstructor; split.
    apply exec_straight_one. simpl. unfold exec_load.
    rewrite H. rewrite LOAD. eauto. auto.
    split; intros; Simpl.
  - (* single *)
    apply indexed_memory_access_correct; intros; auto.
    econstructor; split.
    apply exec_straight_one. simpl. unfold exec_load.
    rewrite H. rewrite LOAD. eauto. auto.
    split; intros; Simpl.
  - (* any32 *)
    apply indexed_memory_access_correct; intros; auto.
    econstructor; split.
    apply exec_straight_one. simpl. unfold exec_load.
    rewrite H. rewrite LOAD. eauto. auto.
    split; intros; Simpl.
  - (* any64 *)
    apply indexed_memory_access_correct; intros; auto.
    econstructor; split.
    apply exec_straight_one. simpl. unfold exec_load.
    rewrite H. rewrite LOAD. eauto. auto.
    split; intros; Simpl.
Qed.

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k c (rs: regset) m m',
  base <> RA ->
  storeind src base ofs ty k = OK c ->
  Mem.storev (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) (rs#(preg_of src)) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, if_preg r = true -> r <> RA -> rs'#r = rs#r.
Proof.
  unfold storeind; intros until m'. intros BASE TR STORE.
  assert (DATA: data_preg (preg_of src) = true) by eauto with asmgen.
  destruct ty; destruct (preg_of src); inv TR; simpl in STORE.
  - (* int *)
    apply indexed_memory_access_correct; intros; auto.
    econstructor; split.
    apply exec_straight_one. simpl. unfold exec_store.
    rewrite H. rewrite H0; auto with asmgen. rewrite STORE; eauto. auto.
    intros; Simpl.
  - (* float *)
    apply indexed_memory_access_correct; intros; auto.
    econstructor; split.
    apply exec_straight_one. simpl. unfold exec_store.
    rewrite H. rewrite H0; auto with asmgen. rewrite STORE; eauto. auto.
    intros; Simpl.
  - (* single *)
    apply indexed_memory_access_correct; intros; auto.
    econstructor; split.
    apply exec_straight_one. simpl. unfold exec_store.
    rewrite H. rewrite H0; auto with asmgen. rewrite STORE; eauto. auto.
    intros; Simpl.
  - (* any32 *)
    apply indexed_memory_access_correct; intros; auto.
    econstructor; split.
    apply exec_straight_one. simpl. unfold exec_store.
    rewrite H. rewrite H0; auto with asmgen. rewrite STORE; eauto. auto.
    intros; Simpl.
  - (* any64 *)
    apply indexed_memory_access_correct; intros; auto.
    econstructor; split.
    apply exec_straight_one. simpl. unfold exec_store.
    rewrite H. rewrite H0; auto with asmgen. rewrite STORE; eauto. auto.
    intros; Simpl.
Qed.

(** Translation of arithmetic operations. *)

Ltac TranslOpSimpl :=
  econstructor; split;
  [ apply exec_straight_one; [simpl; eauto | reflexivity ]
  | split ].

(* Non-comparison (~ Ocmp) operations *)

Lemma transl_op_correct_same:
  forall op args res k c (rs: regset) m v,
  transl_op op args res k = OK c ->
  eval_operation ge rs#SP op (map rs (map preg_of args)) m = Some v ->
  match op with Ocmp _ => False | _ => True end ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of res) = v
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs'#r = rs#r.
Proof.
Local Transparent destroyed_by_op.
  intros until v. intros TR EV NOCMP.
  unfold transl_op in TR; destruct op; ArgsInv; simpl in EV; inv EV; try (TranslOpSimpl; fail).
  - (* Omove *)
    destruct (preg_of res) eqn:RES; try discriminate;
    destruct (preg_of m0) eqn:ARG; inv TR.
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Ointconst *)
    generalize (loadimm_correct x i k rs m). intros [rs' [A [B C]]].
    exists rs'; auto with asmgen.
  - (* Ofloatconst *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Osingleconst *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Oaddrsymbol *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Oaddrstack *)
    assert (TMP: X5 <> SP). discriminate.
    generalize (addimm_correct x SP i X5 k rs m TMP).
    intros [rs' [EX [RES OTH]]].
    exists rs'. split. auto. split. auto.
    intros. rewrite OTH; auto. inv H1; auto.

  - (* Oadd *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Oaddimm *)
    assert (TMP: x1 <> x0). apply (int_temp_ne2 m0 x0 x1 EQ0 EQ1).
    generalize (addimm_correct x x0 i x1 k rs m TMP).
    intros [rs' [EX [RES OTH]]].
    exists rs'. split. auto. split. auto.
    intros; apply OTH; auto.
    generalize (int_temp_X5_X6 m0 x1 EQ0).
    intros [X5 | X6]; subst; inv H1; auto.
  - (* Osub *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Omul *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Omulhs *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Omulhu *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Odiv *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
    rewrite H0; auto.
  - (* Odivu *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
    rewrite H0; auto.
  - (* Omod *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
    rewrite H0; auto.
  - (* Omodu *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
    rewrite H0; auto.

  - (* Oand *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Oandimm *)
    assert (TMP: x1 <> x0). apply (int_temp_ne2 m0 x0 x1 EQ0 EQ1).
    generalize (andimm_correct x x0 i x1 k rs m TMP).
    intros [rs' [EX [RES OTH]]].
    exists rs'. split. auto. split. auto.
    intros; apply OTH; auto.
    generalize (int_temp_X5_X6 m0 x1 EQ0).
    intros [X5 | X6]; subst; inv H1; auto.
  - (* Oor *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Oorimm *)
    assert (TMP: x1 <> x0). apply (int_temp_ne2 m0 x0 x1 EQ0 EQ1).
    generalize (orimm_correct x x0 i x1 k rs m TMP).
    intros [rs' [EX [RES OTH]]].
    exists rs'. split. auto. split. auto.
    intros; apply OTH; auto.
    generalize (int_temp_X5_X6 m0 x1 EQ0).
    intros [X5 | X6]; subst; inv H1; auto.
  - (* Oxor *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Oxorimm *)
    assert (TMP: x1 <> x0). apply (int_temp_ne2 m0 x0 x1 EQ0 EQ1).
    generalize (xorimm_correct x x0 i x1 k rs m TMP).
    intros [rs' [EX [RES OTH]]].
    exists rs'. split. auto. split. auto.
    intros; apply OTH; auto.
    generalize (int_temp_X5_X6 m0 x1 EQ0).
    intros [X5 | X6]; subst; inv H1; auto.
  - (* Onot *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.

  - (* Oshl *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Oshlimm *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Oshr *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Oshrimm *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Oshru *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Oshruimm *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.

  - (* Onegf *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Oabsf *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Oaddf *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Osubf *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Omulf *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Odivf *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Onegfs *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Oabsfs *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Oaddfs *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Osubfs *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Omulfs *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Odivfs *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.

  - (* Osingleoffloat *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
  - (* Ofloatofsingle *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.

  - (* Ointoffloat *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
    rewrite H0; auto.
  - (* Ointuoffloat *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
    rewrite H0; auto.
  - (* Ofloatofint *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
    rewrite H0; auto.
  - (* Ofloatofintu *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
    rewrite H0; auto.
  - (* Ointofsingle *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
    rewrite H0; auto.
  - (* Ointuofsingle *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
    rewrite H0; auto.
  - (* Osingleofint *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
    rewrite H0; auto.
  - (* Osingleofintu *)
    econstructor; split. apply exec_straight_one; simpl; eauto. intuition Simpl.
    rewrite H0; auto.
  - (* Ocmp *)
    contradiction.
Qed.

(* Integer comparisons *)

Lemma xor_neq:
  forall i1 i2, i1 <> i2 -> Int.eq (Int.xor i1 i2) Int.zero = false.
Proof.
Admitted.

Lemma xor_notbool_eq: forall v1 v2,
  Val.of_optbool (Val.cmp_bool Ceq v1 v2) = Val.notbool (Val.xor v1 v2).
Proof.
  intros; destruct v1; destruct v2; simpl; auto.
  case (Int.eq_dec i i0); intro.
  - rewrite e. rewrite Int.xor_idem. rewrite ! Int.eq_true. auto.
  - rewrite (Int.eq_false _ _ n). rewrite (xor_neq _ _ n). auto.
Qed.

Lemma xor_bool_neq: forall v1 v2,
  Val.of_optbool (Val.cmp_bool Cne v1 v2) = Val.boolval (Val.xor v1 v2).
Proof.
  intros; destruct v1; destruct v2; simpl; auto.
  case (Int.eq_dec i i0); intro.
  - rewrite e. rewrite Int.xor_idem. rewrite ! Int.eq_true. auto.
  - rewrite (Int.eq_false _ _ n). rewrite (xor_neq _ _ n). auto.
Qed.

Lemma transl_cond_op_int_correct:
  forall cond rs1 rs2 rd k c (rs: regset) m,
  transl_cond_op_int cond rs1 rs2 rd k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef (Val.of_optbool (eval_condition cond (map rs (map preg_of (rs1 :: rs2 :: nil))) m))
                 rs'#(preg_of rd)
  /\ forall r, data_preg r = true -> r <> preg_of rd -> rs' r = rs r.
Proof.
  intros until m. intros TR.
  unfold transl_cond_op_int in TR; unfold eval_condition;
  destruct cond; destruct c0; ArgsInv.
  - (* Ccomp Ceq *)
    econstructor. split.
    eapply exec_straight_two; simpl; auto with asmgen.
    split; intros; Simpl.
    apply Val.lessdef_same. apply xor_notbool_eq.
  - (* Ccomp Cne *)
    econstructor. split.
    eapply exec_straight_two; simpl; auto with asmgen.
    split; intros; Simpl.
    apply Val.lessdef_same. apply xor_bool_neq.
  - (* Ccomp lt *)
    econstructor. split.
    eapply exec_straight_one; simpl; auto with asmgen.
    split; intros; Simpl.
  - (* Ccomp Cle *)
    econstructor. split.
    eapply exec_straight_two; simpl; auto with asmgen.
    split; intros; Simpl.
    apply Val.lessdef_same.
    unfold Val.cmp, Val.xor, Val.of_optbool, Val.cmp_bool;
      destruct (rs x); destruct (rs x0); simpl; auto.
    destruct (Int.lt i0 i); simpl.
    rewrite Int.xor_idem; auto.
    rewrite Int.xor_zero_one; auto.
  - (* Ccomp Cgt *)
    econstructor. split.
    eapply exec_straight_one; simpl; auto with asmgen.
    split; intros; Simpl.
    apply Val.lessdef_same.
    unfold Val.cmp, Val.of_bool.
    rewrite <- Val.swap_cmp_bool; auto.
  - (* Ccomp Cge *)
    econstructor. split.
    eapply exec_straight_two; simpl; auto with asmgen.
    split; intros; Simpl.
    apply Val.lessdef_same.
    unfold Val.cmp, Val.xor, Val.of_optbool, Val.cmp_bool;
      destruct (rs x); destruct (rs x0); simpl; auto.
    destruct (Int.lt i i0); simpl.
    rewrite Int.xor_idem; auto.
    rewrite Int.xor_zero_one; auto.
  - (* Ccompu Ceq *)
    econstructor. split.
    eapply exec_straight_one; simpl; auto with asmgen.
    split; intros; Simpl.
  - (* Ccompu Cne *)
    econstructor. split.
    eapply exec_straight_one; simpl; auto with asmgen.
    split; intros; Simpl.
  - (* Ccompu Clt *)
    econstructor. split.
    eapply exec_straight_one; simpl; auto with asmgen.
    split; intros; Simpl.
  - (* Ccompu Cle *)
    econstructor. split.
    eapply exec_straight_two; simpl; auto with asmgen.
    split; intros; Simpl.
    apply Val.lessdef_same.
    rewrite <- (Val.swap_cmpu_bool (Mem.valid_pointer m) Cle (rs x0) (rs x)); simpl.
    change (Clt) with (negate_comparison Cge).
    rewrite (Val.negate_cmpu (Mem.valid_pointer m) Cge (rs x0) (rs x)).
    unfold Val.cmpu.
    destruct (Val.cmpu_bool (Mem.valid_pointer m) Cge (rs x0) (rs x)); auto.
    destruct b; auto with ints.
  - (* Ccompu Cgt *)
    econstructor. split.
    eapply exec_straight_one; simpl; auto with asmgen.
    split; intros; Simpl.
    apply Val.lessdef_same. unfold Val.cmpu.
    rewrite <- (Val.swap_cmpu_bool (Mem.valid_pointer m) Clt (rs x) (rs x0)); auto.
  - (* Ccompu Cge *)
    econstructor. split.
    eapply exec_straight_two; simpl; auto with asmgen.
    split; intros; Simpl.
    apply Val.lessdef_same.
    change (Clt) with (negate_comparison Cge).
    rewrite (Val.negate_cmpu (Mem.valid_pointer m) Cge (rs x) (rs x0)).
    unfold Val.cmpu.
    destruct (Val.cmpu_bool (Mem.valid_pointer m) Cge (rs x) (rs x0)); auto.
    destruct b; auto with ints.
Qed.

(* lessdef maintained over negb implemented as xor 1. *)
Lemma lessdef_xor_one:
  forall ob v,
  Val.lessdef (Val.of_optbool ob) v ->
  Val.lessdef (Val.of_optbool (option_map negb ob)) (Val.xor v (Vint Int.one)).
Proof.
  intros; destruct ob.
  - (* some b *)
    destruct b; destruct v; simpl; simpl in H; inv H.
    rewrite Int.xor_idem; fold Vfalse; apply Val.lessdef_refl.
    rewrite Int.xor_zero_one; fold Vtrue; apply Val.lessdef_refl.
  - (* none *)
    simpl; apply Val.lessdef_undef.
Qed.

Lemma transl_cond_op_correct:
  forall cond args rd k c (rs: regset) m,
  transl_cond_op cond args rd k = OK c ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef (Val.of_optbool (eval_condition cond rs ## (preg_of ## args) m)) rs'#(preg_of rd)
  /\ forall r, data_preg r = true -> r <> preg_of rd -> preg_notin r (destroyed_by_op (Ocmp cond)) -> rs' r = rs r.
Proof.
  intros until m. intros TR. unfold transl_cond_op in TR; destruct cond; ArgsInv; simpl.
  - (* Ccomp *)
    exploit (transl_cond_op_int_correct (Ccomp c0) m0 m1 rd k c rs m); auto.
    intros [rs' [EX [LD INV]]]. exists rs'; auto.
  - (* Ccompu *)
    exploit (transl_cond_op_int_correct (Ccompu c0) m0 m1 rd k c rs m); auto.
    intros [rs' [EX [LD INV]]]. exists rs'; auto.
  - (* Ccompimm *)
    generalize (loadimm_correct x i x0 rs m).
    intros [rsl [EXL [RESL INVL]]].
    generalize (transl_cond_op_int_correct (Ccomp c0) m0 (int_temp_for m0) rd k x0 rsl m).
    intros [rs' [EXC [LD INVC]]]; auto.
    econstructor. split.
    eapply exec_straight_trans; eauto. split.
    simpl in LD. simpl.
    rewrite <- (ireg_of_eq (int_temp_for m0) x EQ) in RESL. rewrite <- RESL.
    rewrite <- INVL; auto with asmgen.
    apply (int_temp_ne m0 x EQ).
    intros. rewrite INVC; auto with asmgen. rewrite INVL; auto with asmgen.
    generalize (int_temp_X5_X6 m0 x EQ); intro TMP; inv TMP; intuition.
  - (* Ccompuimm *)
    generalize (loadimm_correct x i x0 rs m).
    intros [rsl [EXL [RESL INVL]]].
    generalize (transl_cond_op_int_correct (Ccompu c0) m0 (int_temp_for m0) rd k x0 rsl m).
    intros [rs' [EXC [LD INVC]]]; auto.
    econstructor. split.
    eapply exec_straight_trans; eauto. split.
    simpl in LD. simpl.
    rewrite <- (ireg_of_eq (int_temp_for m0) x EQ) in RESL. rewrite <- RESL.
    rewrite <- INVL; auto with asmgen.
    apply (int_temp_ne m0 x EQ).
    intros. rewrite INVC; auto with asmgen. rewrite INVL; auto with asmgen.
    generalize (int_temp_X5_X6 m0 x EQ); intro TMP; inv TMP; intuition.
  - (* Ccompf *)
    generalize (transl_cond_float_correct2 c0 rd m0 m1 k rs m c).
    intros [rs' [EX [LD INV]]]; auto. exists rs'.
    split; auto.
  - (* Cnotcompf *)
    generalize (transl_cond_float_correct2 c0 rd m0 m1 (Pxori x x Int.one :: k) rs m c).
    intros [rs1 [EX [LD INV]]]; auto.
    econstructor. split.
    eapply exec_straight_trans; eauto.
    apply exec_straight_one. simpl; reflexivity. auto with asmgen.
    rewrite <- (ireg_of_eq rd x EQ).
    split. rewrite nextinstr_inv; auto with asmgen. rewrite Pregmap.gss.
    exploit lessdef_xor_one; eauto.
    intros; rewrite <- INV; Simpl; assumption.
  - (* Ccompfs *)
    generalize (transl_cond_single_correct2 c0 rd m0 m1 k rs m c).
    intros [rs' [EX [LD INV]]]; auto. exists rs'.
    split; auto.
  - (* Cnotcompfs *)
    generalize (transl_cond_single_correct2 c0 rd m0 m1 (Pxori x x Int.one :: k) rs m c).
    intros [rs1 [EX [LD INV]]]; auto.
    econstructor. split.
    eapply exec_straight_trans; eauto.
    apply exec_straight_one. simpl; reflexivity. auto with asmgen.
    rewrite <- (ireg_of_eq rd x EQ).
    split. rewrite nextinstr_inv; auto with asmgen. rewrite Pregmap.gss.
    exploit lessdef_xor_one; eauto.
    intros; rewrite <- INV; Simpl; assumption.
Qed.

Lemma transl_op_correct:
  forall op args res k c (rs: regset) m v,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#SP) op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r.
Proof.
  intros.
  assert (EITHER: match op with Ocmp _ => False | _ => True end \/ exists cmp, op = Ocmp cmp).
    destruct op; auto. right; exists c0; auto.
  destruct EITHER as [A | [cmp A]].
  - exploit transl_op_correct_same; eauto. intros [rs' [P [Q R]]].
    subst v. exists rs'; eauto.
  - (* Ocmp *)
    subst op.  simpl in H. simpl in H0. inv H0.
    exploit (transl_cond_op_correct cmp args res k c rs m); eauto.
Qed.

(** Translation of loads and stores. *)

Lemma transl_memory_access_correct:
  forall (mk_instr: ireg -> int -> instruction) addr args k c (rs: regset) a m,
  transl_memory_access mk_instr addr args k = OK c ->
  eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some a ->
  exists base ofs rs',
    (exec_straight ge fn c rs m (mk_instr base ofs :: k) rs' m
     \/ (c = mk_instr base ofs :: k /\ rs' = rs))
  /\ Val.add rs'# base (Vint ofs) = a
  /\ forall r, data_preg r = true -> rs' r = rs r.
Proof.
  intros until m. intros TR EV.
  unfold transl_memory_access in TR; destruct addr; destruct (make_immed i) eqn:IMM; ArgsInv.
  - (* Aindexed, small imm *)
    exists x, imm, rs; split. right. auto.
    split. rewrite <- (lo_imm i imm IMM). inv EV; auto.
    intros; auto.
  - (* Aindexed, large imm *)
    generalize (ireg_of_not_RA' m0 x EQ); intros TMP.
    generalize (load_hibase_correct X1 x hi (mk_instr X1 lo :: k) rs m TMP).
    intros [rs' [EX [RES OTH]]]. exists RA, lo, rs'.
    split. left; auto. split. inv EV; auto.
    rewrite RES. rewrite Val.add_assoc; simpl; rewrite (hi_lo_add i); auto.
    intros; apply OTH; auto with asmgen.
  - (* Ainstack, small imm *)
    exists SP, imm, rs; split. right. auto.
    split. inv TR; auto. auto.
    split. rewrite <- (lo_imm i imm IMM).
    simpl in EV; inv EV; auto.
    intros; auto.
  - (* Ainstack, large imm *)
    assert (TMP: X2 <> X1). discriminate.
    generalize (load_hibase_correct RA SP hi (mk_instr RA lo :: k) rs m TMP).
    intros [rs' [EX [RES OTH]]]. inv TR.
    exists RA, lo, rs'. split. left; auto.
    split. rewrite RES. simpl in EV; inv EV.
    rewrite Val.add_assoc; simpl; rewrite (hi_lo_add i); auto.
    intros; apply OTH; auto with asmgen.
Qed.

Lemma transl_load_correct:
  forall chunk addr args dst k c (rs: regset) a m v,
  transl_load chunk addr args dst k = OK c ->
  eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, data_preg r = true -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros until v. intros TR EA LOAD.
  destruct chunk; simpl in TR; monadInv TR.
  - destruct (transl_memory_access_correct (Plb x) addr args k c rs a m EQ0 EA)
      as (base & ofs & rs' & [EX | [C RS]] & ADDR & INV).
    + (* large immediate *)
      econstructor. split. eapply exec_straight_trans. apply EX.
      apply exec_straight_one; simpl. rewrite ADDR.
      unfold exec_load; rewrite LOAD. auto. auto with asmgen.
      generalize (ireg_of_eq dst x EQ); intros DST.
      split. rewrite (ireg_of_eq dst x EQ).
      rewrite nextinstr_inv; auto with asmgen.
      rewrite Pregmap.gss; auto.
      intros; Simpl.
    + (* small immediate *)
      generalize (ireg_of_eq dst x EQ); intros DST.
      econstructor. split. rewrite C. apply exec_straight_one; simpl.
      unfold exec_load. rewrite RS in ADDR. rewrite ADDR. rewrite LOAD.
      auto. auto with asmgen.
      split. rewrite DST; auto with asmgen.
      rewrite nextinstr_inv; auto with asmgen. rewrite Pregmap.gss; auto.
      intros; Simpl.
  - destruct (transl_memory_access_correct (Plbu x) addr args k c rs a m EQ0 EA)
      as (base & ofs & rs' & [EX | [C RS]] & ADDR & INV).
    + (* large immediate *)
      econstructor. split. eapply exec_straight_trans. apply EX.
      apply exec_straight_one; simpl. rewrite ADDR.
      unfold exec_load; rewrite LOAD. auto. auto with asmgen.
      generalize (ireg_of_eq dst x EQ); intros DST.
      split. rewrite (ireg_of_eq dst x EQ).
      rewrite nextinstr_inv; auto with asmgen.
      rewrite Pregmap.gss; auto.
      intros; Simpl.
    + (* small immediate *)
      generalize (ireg_of_eq dst x EQ); intros DST.
      econstructor. split. rewrite C. apply exec_straight_one; simpl.
      unfold exec_load. rewrite RS in ADDR. rewrite ADDR. rewrite LOAD.
      auto. auto with asmgen.
      split. rewrite DST; auto with asmgen.
      rewrite nextinstr_inv; auto with asmgen. rewrite Pregmap.gss; auto.
      intros; Simpl.
  - destruct (transl_memory_access_correct (Plh x) addr args k c rs a m EQ0 EA)
      as (base & ofs & rs' & [EX | [C RS]] & ADDR & INV).
    + (* large immediate *)
      econstructor. split. eapply exec_straight_trans. apply EX.
      apply exec_straight_one; simpl. rewrite ADDR.
      unfold exec_load; rewrite LOAD. auto. auto with asmgen.
      generalize (ireg_of_eq dst x EQ); intros DST.
      split. rewrite (ireg_of_eq dst x EQ).
      rewrite nextinstr_inv; auto with asmgen.
      rewrite Pregmap.gss; auto.
      intros; Simpl.
    + (* small immediate *)
      generalize (ireg_of_eq dst x EQ); intros DST.
      econstructor. split. rewrite C. apply exec_straight_one; simpl.
      unfold exec_load. rewrite RS in ADDR. rewrite ADDR. rewrite LOAD.
      auto. auto with asmgen.
      split. rewrite DST; auto with asmgen.
      rewrite nextinstr_inv; auto with asmgen. rewrite Pregmap.gss; auto.
      intros; Simpl.
  - destruct (transl_memory_access_correct (Plhu x) addr args k c rs a m EQ0 EA)
      as (base & ofs & rs' & [EX | [C RS]] & ADDR & INV).
    + (* large immediate *)
      econstructor. split. eapply exec_straight_trans. apply EX.
      apply exec_straight_one; simpl. rewrite ADDR.
      unfold exec_load; rewrite LOAD. auto. auto with asmgen.
      generalize (ireg_of_eq dst x EQ); intros DST.
      split. rewrite (ireg_of_eq dst x EQ).
      rewrite nextinstr_inv; auto with asmgen.
      rewrite Pregmap.gss; auto.
      intros; Simpl.
    + (* small immediate *)
      generalize (ireg_of_eq dst x EQ); intros DST.
      econstructor. split. rewrite C. apply exec_straight_one; simpl.
      unfold exec_load. rewrite RS in ADDR. rewrite ADDR. rewrite LOAD.
      auto. auto with asmgen.
      split. rewrite DST; auto with asmgen.
      rewrite nextinstr_inv; auto with asmgen. rewrite Pregmap.gss; auto.
      intros; Simpl.
  - destruct (transl_memory_access_correct (Plw x) addr args k c rs a m EQ0 EA)
      as (base & ofs & rs' & [EX | [C RS]] & ADDR & INV).
    + (* large immediate *)
      econstructor. split. eapply exec_straight_trans. apply EX.
      apply exec_straight_one; simpl. rewrite ADDR.
      unfold exec_load; rewrite LOAD. auto. auto with asmgen.
      generalize (ireg_of_eq dst x EQ); intros DST.
      split. rewrite (ireg_of_eq dst x EQ).
      rewrite nextinstr_inv; auto with asmgen.
      rewrite Pregmap.gss; auto.
      intros; Simpl.
    + (* small immediate *)
      generalize (ireg_of_eq dst x EQ); intros DST.
      econstructor. split. rewrite C. apply exec_straight_one; simpl.
      unfold exec_load. rewrite RS in ADDR. rewrite ADDR. rewrite LOAD.
      auto. auto with asmgen.
      split. rewrite DST; auto with asmgen.
      rewrite nextinstr_inv; auto with asmgen. rewrite Pregmap.gss; auto.
      intros; Simpl.
  - destruct (transl_memory_access_correct (Pfls x) addr args k c rs a m EQ0 EA)
      as (base & ofs & rs' & [EX | [C RS]] & ADDR & INV).
    + (* large immediate *)
      econstructor. split. eapply exec_straight_trans. apply EX.
      apply exec_straight_one; simpl. rewrite ADDR.
      unfold exec_load; rewrite LOAD. auto. auto with asmgen.
      generalize (freg_of_eq dst x EQ); intros DST.
      split. rewrite (freg_of_eq dst x EQ).
      rewrite nextinstr_inv; auto with asmgen.
      rewrite Pregmap.gss; auto.
      intros; Simpl.
    + (* small immediate *)
      generalize (freg_of_eq dst x EQ); intros DST.
      econstructor. split. rewrite C. apply exec_straight_one; simpl.
      unfold exec_load. rewrite RS in ADDR. rewrite ADDR. rewrite LOAD.
      auto. auto with asmgen.
      split. rewrite DST; auto with asmgen.
      rewrite nextinstr_inv; auto with asmgen. rewrite Pregmap.gss; auto.
      intros; Simpl.
  - destruct (transl_memory_access_correct (Pfld x) addr args k c rs a m EQ0 EA)
      as (base & ofs & rs' & [EX | [C RS]] & ADDR & INV).
    + (* large immediate *)
      econstructor. split. eapply exec_straight_trans. apply EX.
      apply exec_straight_one; simpl. rewrite ADDR.
      unfold exec_load; rewrite LOAD. auto. auto with asmgen.
      generalize (freg_of_eq dst x EQ); intros DST.
      split. rewrite (freg_of_eq dst x EQ).
      rewrite nextinstr_inv; auto with asmgen.
      rewrite Pregmap.gss; auto.
      intros; Simpl.
    + (* small immediate *)
      generalize (freg_of_eq dst x EQ); intros DST.
      econstructor. split. rewrite C. apply exec_straight_one; simpl.
      unfold exec_load. rewrite RS in ADDR. rewrite ADDR. rewrite LOAD.
      auto. auto with asmgen.
      split. rewrite DST; auto with asmgen.
      rewrite nextinstr_inv; auto with asmgen. rewrite Pregmap.gss; auto.
      intros; Simpl.
Qed.

Lemma transl_store_correct:
  forall chunk addr args src k c (rs: regset) a m m',
  transl_store chunk addr args src k = OK c ->
  eval_addressing ge (rs#SP) addr (map rs (map preg_of args)) = Some a ->
  Mem.storev chunk m a rs#(preg_of src) = Some m' ->
  exists rs',
     exec_straight ge fn c rs m k rs' m'
  /\ forall r, data_preg r = true -> preg_notin r (destroyed_by_store chunk addr) -> rs'#r = rs#r.
Proof.
  intros until m'. intros TR EA STORE.
  destruct chunk; simpl in TR; monadInv TR.
  - destruct (transl_memory_access_correct (Psb x) addr args k c rs a m EQ0 EA)
      as (base & ofs & rs' & [EX | [C RS]] & ADDR & INV).
    + (* large immediate *)
      generalize (ireg_of_eq src x EQ); intros SRC.
      econstructor. split. eapply exec_straight_trans. apply EX.
      apply exec_straight_one; simpl. rewrite ADDR.
      unfold exec_store. rewrite INV. rewrite SRC in STORE.
      assert (Mem.storev Mint8unsigned m a (rs x) = Some m').
        rewrite <- STORE. destruct a; simpl; auto. symmetry.
        apply Mem.store_signed_unsigned_8.
      rewrite H; auto. rewrite <- SRC; auto with asmgen. auto with asmgen.
      intros; Simpl.
    + (* small immediate *)
      generalize (ireg_of_eq src x EQ); intros SRC.
      econstructor. split. rewrite C. apply exec_straight_one; simpl.
      unfold exec_store. rewrite RS in ADDR. rewrite ADDR. rewrite SRC in STORE.
      assert (Mem.storev Mint8unsigned m a (rs x) = Some m').
        rewrite <- STORE. destruct a; simpl; auto. symmetry.
        apply Mem.store_signed_unsigned_8.
      rewrite H; auto. auto with asmgen.
      intros; Simpl.
  - destruct (transl_memory_access_correct (Psb x) addr args k c rs a m EQ0 EA)
      as (base & ofs & rs' & [EX | [C RS]] & ADDR & INV).
    + (* large immediate *)
      generalize (ireg_of_eq src x EQ); intros SRC.
      econstructor. split. eapply exec_straight_trans. apply EX.
      apply exec_straight_one; simpl. rewrite ADDR.
      unfold exec_store. rewrite INV. rewrite SRC in STORE.
      rewrite STORE; auto. rewrite <- SRC; auto with asmgen.
      auto with asmgen.
      intros; Simpl.
    + (* small immediate *)
      generalize (ireg_of_eq src x EQ); intros SRC.
      econstructor. split. rewrite C. apply exec_straight_one; simpl.
      unfold exec_store. rewrite RS in ADDR. rewrite ADDR. rewrite SRC in STORE.
      rewrite STORE; auto. auto with asmgen.
      intros; Simpl.
  - destruct (transl_memory_access_correct (Psh x) addr args k c rs a m EQ0 EA)
      as (base & ofs & rs' & [EX | [C RS]] & ADDR & INV).
    + (* large immediate *)
      generalize (ireg_of_eq src x EQ); intros SRC.
      econstructor. split. eapply exec_straight_trans. apply EX.
      apply exec_straight_one; simpl. rewrite ADDR.
      unfold exec_store. rewrite INV. rewrite SRC in STORE.
      assert (Mem.storev Mint16unsigned m a (rs x) = Some m').
        rewrite <- STORE. destruct a; simpl; auto. symmetry.
        apply Mem.store_signed_unsigned_16.
      rewrite H; auto. rewrite <- SRC; auto with asmgen. auto with asmgen.
      intros; Simpl.
    + (* small immediate *)
      generalize (ireg_of_eq src x EQ); intros SRC.
      econstructor. split. rewrite C. apply exec_straight_one; simpl.
      unfold exec_store. rewrite RS in ADDR. rewrite ADDR. rewrite SRC in STORE.
      assert (Mem.storev Mint16unsigned m a (rs x) = Some m').
        rewrite <- STORE. destruct a; simpl; auto. symmetry.
        apply Mem.store_signed_unsigned_16.
      rewrite H; auto. auto with asmgen.
      intros; Simpl.
  - destruct (transl_memory_access_correct (Psh x) addr args k c rs a m EQ0 EA)
      as (base & ofs & rs' & [EX | [C RS]] & ADDR & INV).
    + (* large immediate *)
      generalize (ireg_of_eq src x EQ); intros SRC.
      econstructor. split. eapply exec_straight_trans. apply EX.
      apply exec_straight_one; simpl. rewrite ADDR.
      unfold exec_store. rewrite INV. rewrite SRC in STORE.
      rewrite STORE; auto. rewrite <- SRC; auto with asmgen.
      auto with asmgen.
      intros; Simpl.
    + (* small immediate *)
      generalize (ireg_of_eq src x EQ); intros SRC.
      econstructor. split. rewrite C. apply exec_straight_one; simpl.
      unfold exec_store. rewrite RS in ADDR. rewrite ADDR. rewrite SRC in STORE.
      rewrite STORE; auto. auto with asmgen.
      intros; Simpl.
  - destruct (transl_memory_access_correct (Psw x) addr args k c rs a m EQ0 EA)
      as (base & ofs & rs' & [EX | [C RS]] & ADDR & INV).
    + (* large immediate *)
      generalize (ireg_of_eq src x EQ); intros SRC.
      econstructor. split. eapply exec_straight_trans. apply EX.
      apply exec_straight_one; simpl. rewrite ADDR.
      unfold exec_store. rewrite INV. rewrite SRC in STORE.
      rewrite STORE; auto. rewrite <- SRC; auto with asmgen.
      auto with asmgen.
      intros; Simpl.
    + (* small immediate *)
      generalize (ireg_of_eq src x EQ); intros SRC.
      econstructor. split. rewrite C. apply exec_straight_one; simpl.
      unfold exec_store. rewrite RS in ADDR. rewrite ADDR. rewrite SRC in STORE.
      rewrite STORE; auto. auto with asmgen.
      intros; Simpl.
  - destruct (transl_memory_access_correct (Pfss x) addr args k c rs a m EQ0 EA)
      as (base & ofs & rs' & [EX | [C RS]] & ADDR & INV).
    + (* large immediate *)
      generalize (freg_of_eq src x EQ); intros SRC.
      econstructor. split. eapply exec_straight_trans. apply EX.
      apply exec_straight_one; simpl. rewrite ADDR.
      unfold exec_store. rewrite INV. rewrite SRC in STORE.
      rewrite STORE; auto. rewrite <- SRC; auto with asmgen.
      auto with asmgen.
      intros; Simpl.
    + (* small immediate *)
      generalize (freg_of_eq src x EQ); intros SRC.
      econstructor. split. rewrite C. apply exec_straight_one; simpl.
      unfold exec_store. rewrite RS in ADDR. rewrite ADDR. rewrite SRC in STORE.
      rewrite STORE; auto. auto with asmgen.
      intros; Simpl.
  - destruct (transl_memory_access_correct (Pfsd x) addr args k c rs a m EQ0 EA)
      as (base & ofs & rs' & [EX | [C RS]] & ADDR & INV).
    + (* large immediate *)
      generalize (freg_of_eq src x EQ); intros SRC.
      econstructor. split. eapply exec_straight_trans. apply EX.
      apply exec_straight_one; simpl. rewrite ADDR.
      unfold exec_store. rewrite INV. rewrite SRC in STORE.
      rewrite STORE; auto. rewrite <- SRC; auto with asmgen.
      auto with asmgen.
      intros; Simpl.
    + (* small immediate *)
      generalize (freg_of_eq src x EQ); intros SRC.
      econstructor. split. rewrite C. apply exec_straight_one; simpl.
      unfold exec_store. rewrite RS in ADDR. rewrite ADDR. rewrite SRC in STORE.
      rewrite STORE; auto. auto with asmgen.
      intros; Simpl.
Qed.

End CONSTRUCTORS.
