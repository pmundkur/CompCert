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

Require Import String.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Op.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations.  These include:
- Integer registers that can be allocated to RTL pseudo-registers ([Rxx]).
- Floating-point registers that can be allocated to RTL pseudo-registers
  ([Fxx]).

  The type [mreg] does not include reserved machine registers such as
  the zero register (x0), the link register (x1), the stack pointer
  (x2), the global pointer (x3), and the thread pointer (x4).
*)

Inductive mreg: Type :=
 (** Allocatable integer regs. *)
              | R5:  mreg | R6:  mreg | R7:  mreg
  | R8:  mreg | R9:  mreg | R10: mreg | R11: mreg
  | R12: mreg | R13: mreg | R14: mreg | R15: mreg
  | R16: mreg | R17: mreg | R18: mreg | R19: mreg
  | R20: mreg | R21: mreg | R22: mreg | R23: mreg
  | R24: mreg | R25: mreg | R26: mreg | R27: mreg
  | R28: mreg | R29: mreg | R30: mreg | R31: mreg
  (** Allocatable double-precision float regs *)
  | FR0:  mreg | FR1:  mreg | FR2:  mreg | FR3:  mreg
  | FR4:  mreg | FR5:  mreg | FR6:  mreg | FR7:  mreg
  | FR8:  mreg | FR9:  mreg | FR10: mreg | FR11: mreg
  | FR12: mreg | FR13: mreg | FR14: mreg | FR15: mreg
  | FR16: mreg | FR17: mreg | FR18: mreg | FR19: mreg
  | FR20: mreg | FR21: mreg | FR22: mreg | FR23: mreg
  | FR24: mreg | FR25: mreg | FR26: mreg | FR27: mreg
  | FR28: mreg | FR29: mreg | FR30: mreg | FR31: mreg.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition mreg_type (r: mreg): typ :=
  match r with
        | R5  | R6  | R7  | R8  | R9  | R10 | R11
  | R12 | R13 | R14 | R15 | R16 | R17 | R18 | R19
  | R20 | R21 | R22 | R23 | R24 | R25 | R26 | R27
  | R28 | R29 | R30 | R31 => Tany32

  | FR0  | FR1  | FR2  | FR3  | FR4  | FR5  | FR6  | FR7
  | FR8  | FR9  | FR10 | FR11 | FR12 | FR13 | FR14 | FR15
  | FR16 | FR17 | FR18 | FR19 | FR20 | FR21 | FR22 | FR23
  | FR24 | FR25 | FR26 | FR27 | FR28 | FR29 | FR30 | FR31 => Tany64
  end.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
                | R5  =>  1 | R6  =>  2 | R7  =>  3
    | R8  =>  4 | R9  =>  5 | R10 =>  6 | R11 =>  7
    | R12 =>  8 | R13 =>  9 | R14 => 10 | R15 => 11
    | R16 => 12 | R17 => 13 | R18 => 14 | R19 => 15
    | R20 => 16 | R21 => 17 | R22 => 18 | R23 => 19
    | R24 => 20 | R25 => 21 | R26 => 22 | R27 => 23
    | R28 => 24 | R29 => 25 | R30 => 26 | R31 => 27

    | FR0  => 28 | FR1  => 29 | FR2  => 30 | FR3  => 31
    | FR4  => 32 | FR5  => 33 | FR6  => 34 | FR7  => 35
    | FR8  => 36 | FR9  => 37 | FR10 => 38 | FR11 => 39
    | FR12 => 40 | FR13 => 41 | FR14 => 42 | FR15 => 43
    | FR16 => 44 | FR17 => 45 | FR18 => 46 | FR19 => 47
    | FR20 => 48 | FR21 => 49 | FR22 => 50 | FR23 => 51
    | FR24 => 52 | FR25 => 53 | FR26 => 54 | FR27 => 55
    | FR28 => 56 | FR29 => 57 | FR30 => 58 | FR31 => 59
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    destruct r1; destruct r2; simpl; intro; discriminate || reflexivity.
  Qed.
End IndexedMreg.

Definition is_stack_reg (r: mreg) : bool := false.

(** ** Names of registers *)

Local Open Scope string_scope.

Definition register_names :=
                  ("R5",  R5)  :: ("R6",  R6)  :: ("R7",  R7)  ::
  ("R8",  R8)  :: ("R9",  R9)  :: ("R10", R10) :: ("R11", R11) ::
  ("R12", R12) :: ("R13", R13) :: ("R14", R14) :: ("R15", R15) ::
  ("R16", R16) :: ("R17", R17) :: ("R18", R18) :: ("R19", R19) ::
  ("R20", R20) :: ("R21", R21) :: ("R22", R22) :: ("R23", R23) ::
  ("R24", R24) :: ("R25", R25) :: ("R26", R26) :: ("R27", R27) ::
  ("R28", R28) :: ("R29", R29) :: ("R30", R30) :: ("R31", R31) ::

  ("F0",  FR0)  :: ("F1",  FR1)  :: ("F2",  FR2)  :: ("F3",  FR3)  ::
  ("F4",  FR4)  :: ("F5",  FR5)  :: ("F6",  FR6)  :: ("F7",  FR7)  ::
  ("F8",  FR8)  :: ("F9",  FR9)  :: ("F10", FR10) :: ("F11", FR11) ::
  ("F12", FR12) :: ("F13", FR13) :: ("F14", FR14) :: ("F15", FR15) ::
  ("F16", FR16) :: ("F17", FR17) :: ("F18", FR18) :: ("F19", FR19) ::
  ("F20", FR20) :: ("F21", FR21) :: ("F22", FR22) :: ("F23", FR23) ::
  ("F24", FR24) :: ("F25", FR25) :: ("F26", FR26) :: ("F27", FR27) ::
  ("F27", FR27) :: ("F28", FR28) :: ("F29", FR29) :: ("F30", FR30) ::
  nil.

Definition register_by_name (s: string) : option mreg :=
  let fix assoc (l: list (string * mreg)) : option mreg :=
    match l with
    | nil => None
    | (s1, r1) :: l' => if string_dec s s1 then Some r1 else assoc l'
    end
  in assoc register_names.

(** ** Destroyed registers, preferred registers *)

(* R5 and R6 are used for immediate ops. We need only one temporary
   reg, but we select between the two to not collide with the incoming
   arg reg.  We also need them for the Ccomp[u]imm conditionals.
 *)
Definition destroyed_by_op (op: operation): list mreg :=
  match op with
  | Ointoffloat | Ointuoffloat | Ointofsingle | Ointuofsingle
      => FR6 :: nil

  (* via loadimm *)
  | Ointconst _ | Oaddrstack _
  | Oaddimm _ | Oandimm _ | Oorimm _ | Oxorimm _
  | Ocmp _  (* via immediates *)
      => R5 :: R6 :: nil
  | _ => nil
  end.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_cond (cond: condition): list mreg :=
  match cond with
  | Ccompimm _ _ | Ccompuimm _ _ => R5 :: R6 :: nil
  | Ccompf  _    | Cnotcompf  _
  | Ccompfs _    | Cnotcompfs _  => R5 :: nil
  | _                            => nil
  end.

Definition destroyed_by_jumptable: list mreg := R5 :: R6 :: nil.

Fixpoint destroyed_by_clobber (cl: list string): list mreg :=
  match cl with
  | nil => nil
  | c1 :: cl =>
      match register_by_name c1 with
      | Some r => r :: destroyed_by_clobber cl
      | None   => destroyed_by_clobber cl
      end
  end.

Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | EF_memcpy sz al => R5 :: R6 :: R7 :: FR0 :: nil
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg := nil.

Definition destroyed_at_function_entry: list mreg := R30 :: nil.

Definition temp_for_parent_frame: mreg := R30.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg := (nil, None).

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list(option mreg) :=
  (* TODO *)
  match ef with
  | _ => (nil, nil)
  end.

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation].  There are none for ARM. *)

Definition two_address_op (op: operation) : bool :=
  false.

Global Opaque two_address_op.

(* Constraints on constant propagation for builtins *)

Definition builtin_constraints (ef: external_function) :
                                       list builtin_arg_constraint :=
  match ef with
  | EF_vload _ => OK_addrany :: nil
  | EF_vstore _ => OK_addrany :: OK_default :: nil
  | EF_memcpy _ _ => OK_addrstack :: OK_addrstack :: nil
  | EF_annot txt targs => map (fun _ => OK_all) targs
  | EF_debug kind txt targs => map (fun _ => OK_all) targs
  | _ => nil
  end.
