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

(** Function calling conventions and other conventions regarding the use of
    machine registers and stack slots. *)

Require Import Coqlib.
Require Import AST.
Require Import Events.
Require Import Locations.

(** * Classification of machine registers *)

(** Machine registers (type [mreg] in module [Locations]) are divided in
  the following groups:
- Callee-save registers, whose value is preserved across a function call.
- Caller-save registers that can be modified during a function call.

  We follow the RISC-V RV32G application binary interface (ABI) in our choice
  of callee- and caller-save registers.
*)

Definition int_caller_save_regs :=
  R5  :: R6  :: R7 ::
  R10 :: R11 ::
  R12 :: R13 :: R14 :: R15 :: R16 :: R17 ::
  R28 :: R29 :: R30 :: R31 ::
  nil.

Definition float_caller_save_regs :=
  FR0  :: FR1  :: FR2  :: FR3  :: FR4  :: FR5  :: FR6  :: FR7  ::
  FR10 :: FR11 ::
  FR12 :: FR13 :: FR14 :: FR15 :: FR16 :: FR17 ::
  FR28 :: FR29 :: FR30 :: FR31 ::
  nil.

Definition int_callee_save_regs :=
  R8  :: R9  ::
  R18 :: R19 :: R20 :: R21 :: R22 :: R23 :: R24 :: R25 :: R26 :: R27 ::
  nil.

Definition float_callee_save_regs :=
  FR8  :: FR9  ::
  FR18 :: FR19 :: FR20 :: FR21 :: FR22 :: FR23 :: FR24 :: FR25 :: FR26 :: FR27 ::
  nil.

Definition destroyed_at_call :=
  int_caller_save_regs ++ float_caller_save_regs.

Definition dummy_int_reg   := R6.    (**r Used in [Coloring]. *)
Definition dummy_float_reg := FR0.   (**r Used in [Coloring]. *)

(** The [index_int_callee_save] and [index_float_callee_save] associate
  a unique positive integer to callee-save registers.  This integer is
  used in [Stacking] to determine where to save these registers in
  the activation record if they are used by the current function. *)

Definition index_int_callee_save (r: mreg) :=
  match r with
  | R8  =>  0 | R9  =>  1
  | R18 =>  2 | R19 =>  3 | R20 =>  4 | R21 =>  5
  | R22 =>  6 | R23 =>  7 | R24 =>  8 | R25 =>  9
  | R26 => 10 | R27 => 11
  | _   => -1
  end.

Definition index_float_callee_save (r: mreg) :=
  match r with
  | FR8  =>  0 | FR9  =>  1
  | FR18 =>  2 | FR19 =>  3 | FR20 =>  4 | FR21 =>  5
  | FR22 =>  6 | FR23 =>  7 | FR24 =>  8 | FR25 =>  9
  | FR26 => 10 | FR27 => 11
  | _   => -1
  end.

Ltac ElimOrEq :=
  match goal with
  |  |- (?x = ?y) \/ _ -> _ =>
       let H := fresh in
       (intro H; elim H; clear H;
        [intro H; rewrite <- H; clear H | ElimOrEq])
  |  |- False -> _ =>
       let H := fresh in (intro H; contradiction)
  end.

Ltac OrEq :=
  match goal with
  | |- (?x = ?x) \/ _ => left; reflexivity
  | |- (?x = ?y) \/ _ => right; OrEq
  | |- False => fail
  end.

Ltac NotOrEq :=
  match goal with
  | |- (?x = ?y) \/ _ -> False =>
       let H := fresh in (
       intro H; elim H; clear H; [intro; discriminate | NotOrEq])
  | |- False -> False =>
       contradiction
  end.

Lemma index_int_callee_save_pos:
  forall r, In r int_callee_save_regs -> index_int_callee_save r >= 0.
Proof.
  intro r. simpl; ElimOrEq; unfold index_int_callee_save; omega.
Qed.

Lemma index_float_callee_save_pos:
  forall r, In r float_callee_save_regs -> index_float_callee_save r >= 0.
Proof.
  intro r. simpl; ElimOrEq; unfold index_float_callee_save; omega.
Qed.

Lemma index_int_callee_save_pos2:
  forall r, index_int_callee_save r >= 0 -> In r int_callee_save_regs.
Proof.
  destruct r; simpl; intro; omegaContradiction || OrEq.
Qed.

Lemma index_float_callee_save_pos2:
  forall r, index_float_callee_save r >= 0 -> In r float_callee_save_regs.
Proof.
  destruct r; simpl; intro; omegaContradiction || OrEq.
Qed.

Lemma index_int_callee_save_inj:
  forall r1 r2,
  In r1 int_callee_save_regs ->
  In r2 int_callee_save_regs ->
  r1 <> r2 ->
  index_int_callee_save r1 <> index_int_callee_save r2.
Proof.
  intros r1 r2.
  simpl; ElimOrEq; ElimOrEq; unfold index_int_callee_save;
  intros; congruence.
Qed.

Lemma index_float_callee_save_inj:
  forall r1 r2,
  In r1 float_callee_save_regs ->
  In r2 float_callee_save_regs ->
  r1 <> r2 ->
  index_float_callee_save r1 <> index_float_callee_save r2.
Proof.
  intros r1 r2.
  simpl; ElimOrEq; ElimOrEq; unfold index_float_callee_save;
  intros; congruence.
Qed.

(** The following lemmas show that
    (temporaries, destroyed at call, integer callee-save, float callee-save)
    is a partition of the set of machine registers. *)

Lemma int_float_callee_save_disjoint:
  list_disjoint int_callee_save_regs float_callee_save_regs.
Proof.
  red; intros r1 r2. simpl; ElimOrEq; ElimOrEq; discriminate.
Qed.

Lemma register_classification:
  forall r,
  In r destroyed_at_call \/ In r int_callee_save_regs \/ In r float_callee_save_regs.
Proof.
  destruct r;
  try (left; simpl; OrEq);
  try (right; left; simpl; OrEq);
  try (right; right; simpl; OrEq).
Qed.

Lemma int_callee_save_not_destroyed:
  forall r,
    In r destroyed_at_call -> In r int_callee_save_regs -> False.
Proof.
  intros. revert H0 H. simpl. ElimOrEq; NotOrEq.
Qed.

Lemma float_callee_save_not_destroyed:
  forall r,
    In r destroyed_at_call -> In r float_callee_save_regs -> False.
Proof.
  intros. revert H0 H. simpl. ElimOrEq; NotOrEq.
Qed.

Lemma int_callee_save_type:
  forall r, In r int_callee_save_regs -> mreg_type r = Tany32.
Proof.
  intro. simpl; ElimOrEq; reflexivity.
Qed.

Lemma float_callee_save_type:
  forall r, In r float_callee_save_regs -> mreg_type r = Tany64.
Proof.
  intro. simpl; ElimOrEq; reflexivity.
Qed.

Ltac NoRepet :=
  match goal with
  | |- list_norepet nil =>
      apply list_norepet_nil
  | |- list_norepet (?a :: ?b) =>
      apply list_norepet_cons; [simpl; intuition discriminate | NoRepet]
  end.

Lemma int_callee_save_norepet:
  list_norepet int_callee_save_regs.
Proof.
  unfold int_callee_save_regs; NoRepet.
Qed.

Lemma float_callee_save_norepet:
  list_norepet float_callee_save_regs.
Proof.
  unfold float_callee_save_regs; NoRepet.
Qed.

(** * Function calling conventions *)

(** The functions in this section determine the locations (machine registers
  and stack slots) used to communicate arguments and results between the
  caller and the callee during function calls.  These locations are functions
  of the signature of the function and of the call instruction.
  Agreement between the caller and the callee on the locations to use
  is guaranteed by our dynamic semantics for Cminor and RTL, which demand
  that the signature of the call instruction is identical to that of the
  called function.

  Calling conventions are largely arbitrary: they must respect the properties
  proved in this section (such as no overlapping between the locations
  of function arguments), but this leaves much liberty in choosing actual
  locations.  To ensure binary interoperability of code generated by our
  compiler with libraries compiled by another RISC-V compiler, we
  implement the standard conventions defined in the RISC-V specification. *)

(** ** Location of function result *)

(** We currently do not support the "soft-float" configuration.

  The result value of a function is passed back to the caller in
  registers [R10] or [F10] or [R10, R11], depending on the type of the
  returned value.  We treat a function without result as a function
  with one integer result. *)

Definition loc_result (s: signature) : list mreg :=
  match s.(sig_res) with
  | None => R10 :: nil
  | Some (Tint | Tany32) => R10 :: nil
  | Some (Tfloat | Tsingle | Tany64) => FR10 :: nil
  | Some Tlong => R10 :: R11 :: nil
  end.

(** The result registers have types compatible with that given in the signature. *)

Lemma loc_result_type:
  forall sig,
  subtype_list (proj_sig_res' sig) (map mreg_type (loc_result sig)) = true.
Proof.
  intros. unfold proj_sig_res', loc_result. destruct (sig_res sig) as [[]|]; auto.
Qed.

(** The result locations are caller-save registers *)

Lemma loc_result_caller_save:
  forall (s: signature) (r: mreg),
  In r (loc_result s) -> In r destroyed_at_call.
Proof.
  intros.
  assert (r = R10 \/ r = R11 \/ r = FR10).
    unfold loc_result in H. destruct (sig_res s); [destruct t|idtac]; simpl in H; intuition.
  destruct H0 as [A | [A | A]]; subst r; simpl; OrEq.
Qed.

(** ** Location of function arguments *)

(** The RISC-V RV32G ABI states the following convention for passing arguments
  to a function:

- Arguments are passed in registers when possible.

- Up to eight integer registers (ai: int_param_regs) and up to eight
  floating-point registers (fai: float_param_regs) are used for this
  purpose.

- If the arguments to a function are conceptualized as fields of a C
  struct, each with pointer alignment, the argument registers are a
  shadow of the first eight pointer-words of that struct. If argument
  i < 8 is a floating-point type, it is passed in floating-point
  register fa_i; otherwise, it is passed in integer register a_i.

- Floating-point arguments to variadic functions (except those that
  are explicitly named in the parameter list) are passed in integer
  registers.

- The portion of the conceptual struct that is not passed in argument
  registers is passed on the stack. The stack pointer sp points to the
  first argument not passed in a register.
*)

Definition int_param_regs :=
  R10 :: R11 :: R12 :: R13 :: R14 :: R15 :: R16 :: R17 :: nil.
Definition float_param_regs :=
  FR10 :: FR11 :: FR12 :: FR13 :: FR14 :: FR15 :: FR16 :: FR17 :: nil.

Fixpoint loc_arguments_rec
    (tyl: list typ) (r ofs: Z) {struct tyl} : list loc :=
  match tyl with
  | nil => nil
  | (Tint | Tany32) as ty :: tys =>
      match list_nth_z int_param_regs r with
      | Some ireg =>
          R ireg :: loc_arguments_rec tys (r + 1) ofs
      | None =>
          S Outgoing ofs ty :: loc_arguments_rec tys r (ofs + 1)
      end
  | Tsingle as ty :: tys =>
      match list_nth_z float_param_regs r with
      | Some freg =>
          R freg :: loc_arguments_rec tys (r + 1) ofs
      | None =>
          S Outgoing ofs ty :: loc_arguments_rec tys r (ofs + 1)
      end
  | Tlong :: tys =>
      let r := align r 2 in
      match list_nth_z int_param_regs r, list_nth_z int_param_regs (r + 1) with
      | Some r1, Some r2 =>
          R r1 :: R r2 :: loc_arguments_rec tys (r + 2) ofs
      | _, _ =>
          let ofs := align ofs 2 in
          S Outgoing ofs Tint :: S Outgoing (ofs + 1) Tint :: loc_arguments_rec tys r (ofs + 2)
      end
  | (Tfloat | Tany64) as ty :: tys =>
      let r := align r 2 in
      match list_nth_z float_param_regs r with
      | Some freg =>
          R freg :: loc_arguments_rec tys (r + 2) ofs
      | None =>
          let ofs := align ofs 2 in
          S Outgoing ofs ty :: loc_arguments_rec tys r (ofs + 2)
      end
  end.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list loc :=
  loc_arguments_rec s.(sig_args) 0 0.

(** [size_arguments s] returns the number of [Outgoing] slots used
  to call a function with signature [s]. *)

Fixpoint size_arguments_rec (tyl: list typ) (r ofs: Z) {struct tyl} : Z :=
  match tyl with
  | nil => ofs
  | (Tint | Tany32) :: tys =>
      match list_nth_z int_param_regs r with
      | Some ireg => size_arguments_rec tys (r + 1) ofs
      | None => size_arguments_rec tys r (ofs + 1)
      end
  | Tsingle :: tys =>
      match list_nth_z float_param_regs r with
      | Some freg => size_arguments_rec tys (r + 1) ofs
      | None => size_arguments_rec tys r (ofs + 1)
      end
  | Tlong :: tys =>
      let r := align r 2 in
      match list_nth_z int_param_regs r, list_nth_z int_param_regs (r + 1) with
      | Some r1, Some r2 => size_arguments_rec tys (r + 2) ofs
      | _, _ => size_arguments_rec tys r (align ofs 2 + 2)
      end
  | (Tfloat | Tany64) :: tys =>
      let r := align r 2 in
      match list_nth_z float_param_regs r with
      | Some freg => size_arguments_rec tys (r + 2) ofs
      | None => size_arguments_rec tys r (align ofs 2 + 2)
      end
  end.

Definition size_arguments (s: signature) : Z :=
  size_arguments_rec s.(sig_args) 0 0.

(** A tail-call is possible for a signature if the corresponding
    arguments are all passed in registers. *)

Definition tailcall_possible (s: signature) : Prop :=
  forall l, In l (loc_arguments s) ->
  match l with R _ => True | S _ _ _ => False end.

(** Argument locations are either caller-save registers or [Outgoing]
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => In r destroyed_at_call
  | S Outgoing ofs ty => ofs >= 0 /\ ty <> Tlong
  | _ => False
  end.

Remark loc_arguments_rec_charact:
  forall tyl ir ofs l,
  In l (loc_arguments_rec tyl ir ofs) ->
  match l with
  | R r => In r int_param_regs \/ In r float_param_regs
  | S Outgoing ofs' ty => ofs' >= ofs /\ ty <> Tlong
  | S _ _ _ => False
  end.
Proof.
Opaque list_nth_z.
  induction tyl; simpl loc_arguments_rec; intros.
  elim H.
  destruct a.
- (* int *)
  destruct (list_nth_z int_param_regs ir) as [r|] eqn:E; destruct H.
  subst. left. eapply list_nth_z_in; eauto.
  eapply IHtyl; eauto.
  subst. split. omega. congruence.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto. intuition omega.
- (* float *)
  set (ir' := align ir 2) in *.
  destruct (list_nth_z float_param_regs ir') as [r|] eqn:E; destruct H.
  subst. right. eapply list_nth_z_in; eauto.
  eapply IHtyl; eauto.
  subst. split. apply Zle_ge. apply align_le. omega. congruence.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto.
  assert (ofs <= align ofs 2) by (apply align_le; omega).
  intuition omega.
- (* long *)
  set (ir' := align ir 2) in *.
  destruct (list_nth_z int_param_regs ir') as [r1|] eqn:E1.
  destruct (list_nth_z int_param_regs (ir' + 1)) as [r2|] eqn:E2.
  destruct H. subst; left; eapply list_nth_z_in; eauto.
  destruct H. subst; left; eapply list_nth_z_in; eauto.
  eapply IHtyl; eauto.
  assert (ofs <= align ofs 2) by (apply align_le; omega).
  destruct H. subst. split. omega. congruence.
  destruct H. subst. split. omega. congruence.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto. intuition omega.
  assert (ofs <= align ofs 2) by (apply align_le; omega).
  destruct H. subst. split. omega. congruence.
  destruct H. subst. split. omega. congruence.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto. intuition omega.
- (* single *)
  destruct (list_nth_z float_param_regs ir) as [r|] eqn:E; destruct H.
  subst. right. eapply list_nth_z_in; eauto.
  eapply IHtyl; eauto.
  subst. split. omega. congruence.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto.
  assert (ofs <= align ofs 2) by (apply align_le; omega).
  intuition omega.
- (* any32 *)
  destruct (list_nth_z int_param_regs ir) as [r|] eqn:E; destruct H.
  subst. left. eapply list_nth_z_in; eauto.
  eapply IHtyl; eauto.
  subst. split. omega. congruence.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto. intuition omega.
- (* any64 *)
  set (ir' := align ir 2) in *.
  destruct (list_nth_z float_param_regs ir') as [r|] eqn:E; destruct H.
  subst. right. eapply list_nth_z_in; eauto.
  eapply IHtyl; eauto.
  subst. split. apply Zle_ge. apply align_le. omega. congruence.
  exploit IHtyl; eauto. destruct l; auto. destruct sl; auto.
  assert (ofs <= align ofs 2) by (apply align_le; omega).
  intuition omega.
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (l: loc),
  In l (loc_arguments s) -> loc_argument_acceptable l.
Proof.
  unfold loc_arguments; intros.
  generalize (loc_arguments_rec_charact _ _ _ _ H).
  destruct l.
  intro H0; elim H0; simpl; ElimOrEq; OrEq.
  destruct sl; try contradiction. simpl. intuition omega.
Qed.
Hint Resolve loc_arguments_acceptable: locs.

(** The offsets of [Outgoing] arguments are below [size_arguments s]. *)

Remark size_arguments_rec_above:
  forall tyl ir ofs0,
  ofs0 <= size_arguments_rec tyl ir ofs0.
Proof.
  induction tyl; simpl; intros.
  omega.
  destruct a.
  destruct (list_nth_z int_param_regs ir); eauto. apply Zle_trans with (ofs0 + 1); auto; omega.
  set (ir' := align ir 2).
  destruct (list_nth_z float_param_regs ir'); eauto.
  apply Zle_trans with (align ofs0 2). apply align_le; omega.
  apply Zle_trans with (align ofs0 2 + 2); auto; omega.
  set (ir' := align ir 2).
  destruct (list_nth_z int_param_regs ir'); eauto.
  destruct (list_nth_z int_param_regs (ir' + 1)); eauto.
  apply Zle_trans with (align ofs0 2). apply align_le; omega.
  apply Zle_trans with (align ofs0 2 + 2); auto; omega.
  apply Zle_trans with (align ofs0 2). apply align_le; omega.
  apply Zle_trans with (align ofs0 2 + 2); auto; omega.
  destruct (list_nth_z float_param_regs ir); eauto.
  apply Zle_trans with (ofs0 + 1). omega. eauto.
  destruct (list_nth_z int_param_regs ir); eauto. apply Zle_trans with (ofs0 + 1); auto; omega.
  set (ir' := align ir 2).
  destruct (list_nth_z float_param_regs ir'); eauto.
  apply Zle_trans with (align ofs0 2). apply align_le; omega.
  apply Zle_trans with (align ofs0 2 + 2); auto; omega.
Qed.

Lemma size_arguments_above:
  forall s, size_arguments s >= 0.
Proof.
  intros; unfold size_arguments. apply Zle_ge.
  apply size_arguments_rec_above.
Qed.

Lemma loc_arguments_bounded:
  forall (s: signature) (ofs: Z) (ty: typ),
  In (S Outgoing ofs ty) (loc_arguments s) ->
  ofs + typesize ty <= size_arguments s.
Proof.
  intros.
  assert (forall tyl ir ofs0,
    In (S Outgoing ofs ty) (loc_arguments_rec tyl ir ofs0) ->
    ofs + typesize ty <= size_arguments_rec tyl ir ofs0).
{
  induction tyl; simpl; intros.
  elim H0.
  destruct a.
- (* int *)
  destruct (list_nth_z int_param_regs ir); destruct H0.
  congruence.
  eauto.
  inv H0. apply size_arguments_rec_above.
  eauto.
- (* float *)
  set (ir' := align ir 2) in *.
  destruct (list_nth_z float_param_regs ir'); destruct H0.
  congruence.
  eauto.
  inv H0. apply size_arguments_rec_above. eauto.
- (* long *)
  set (ir' := align ir 2) in *.
  destruct (list_nth_z int_param_regs ir').
  destruct (list_nth_z int_param_regs (ir' + 1)).
  destruct H0. congruence. destruct H0. congruence. eauto.
  destruct H0. inv H0.
  transitivity (align ofs0 2 + 2). simpl; omega. apply size_arguments_rec_above.
  destruct H0. inv H0.
  transitivity (align ofs0 2 + 2). simpl; omega. apply size_arguments_rec_above.
  eauto.
  destruct H0. inv H0.
  transitivity (align ofs0 2 + 2). simpl; omega. apply size_arguments_rec_above.
  destruct H0. inv H0.
  transitivity (align ofs0 2 + 2). simpl; omega. apply size_arguments_rec_above.
  eauto.
- (* single *)
  destruct (list_nth_z float_param_regs ir); destruct H0.
  congruence.
  eauto.
  inv H0. apply size_arguments_rec_above.
  eauto.
- (* any32 *)
  destruct (list_nth_z int_param_regs ir); destruct H0.
  congruence.
  eauto.
  inv H0. apply size_arguments_rec_above.
  eauto.
- (* any64 *)
  set (ir' := align ir 2) in *.
  destruct (list_nth_z float_param_regs ir'); destruct H0.
  congruence.
  eauto.
  inv H0. apply size_arguments_rec_above.
  eauto.
}
  eauto.
Qed.

Lemma loc_arguments_main:
  loc_arguments signature_main = nil.
Proof.
  reflexivity.
Qed.
