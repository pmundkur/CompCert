(* Type inference for RTL *)

open Datatypes
open CList
open Camlcoq
open Maps
open AST
open Op
open Registers
open RTL

exception Type_error of string

let env = ref (PTree.empty : typ PTree.t)

let set_type r ty =
  match PTree.get r !env with
  | None -> env := PTree.set r ty !env
  | Some ty' -> if ty <> ty' then raise (Type_error "type mismatch")

let rec set_types rl tyl =
  match rl, tyl with
  | Coq_nil, Coq_nil -> ()
  | Coq_cons(r1, rs), Coq_cons(ty1, tys) -> set_type r1 ty1; set_types rs tys
  | _, _ -> raise (Type_error "arity mismatch")

(* First pass: process constraints of the form typeof(r) = ty *)

let type_instr retty (Coq_pair(pc, i)) =
  match i with
  | Inop(_) ->
      ()
  | Iop(Omove, _, _, _) -> 
      ()
  | Iop(Oundef, Coq_nil, res, _) ->
      ()
  | Iop(Oundef, _, _, _) ->
      raise (Type_error "wrong Oundef")
  | Iop(op, args, res, _) ->
      let (Coq_pair(targs, tres)) = type_of_operation op in
      set_types args targs; set_type res tres
  | Iload(chunk, addr, args, dst, _) ->
      set_types args (type_of_addressing addr);
      set_type dst (type_of_chunk chunk)
  | Istore(chunk, addr, args, src, _) ->
      set_types args (type_of_addressing addr);
      set_type src (type_of_chunk chunk)
  | Icall(sg, ros, args, res, _) ->
      begin match ros with
      | Coq_inl r -> set_type r Tint
      | Coq_inr _ -> ()
      end;
      set_types args sg.sig_args;
      set_type res (match sg.sig_res with None -> Tint | Some ty -> ty)
  | Ialloc(arg, res, _) ->
      set_type arg Tint; set_type res Tint
  | Icond(cond, args, _, _) ->
      set_types args (type_of_condition cond)
  | Ireturn(optres) ->
      begin match optres, retty with
      | None, None -> ()
      | Some r, Some ty -> set_type r ty
      | _, _ -> raise (Type_error "type mismatch in Ireturn")
      end

let type_pass1 retty instrs = 
  coqlist_iter (type_instr retty) instrs

(* Second pass: extract move constraints typeof(r1) = typeof(r2)
   and solve them iteratively *)

let rec extract_moves = function
  | Coq_nil -> []
  | Coq_cons(Coq_pair(pc, i), rem) ->
      match i with
      | Iop(Omove, Coq_cons(r1, Coq_nil), r2, _) ->
          (r1, r2) :: extract_moves rem
      | Iop(Omove, _, _, _) ->
          raise (Type_error "wrong Omove")
      | _ ->
          extract_moves rem

let changed = ref false

let rec solve_moves = function
  | [] -> []
  | (r1, r2) :: rem ->
      match (PTree.get r1 !env, PTree.get r2 !env) with
      | Some ty1, Some ty2 ->
          if ty1 = ty2 
          then (changed := true; solve_moves rem)
          else raise (Type_error "type mismatch in Omove")
      | Some ty1, None ->
          env := PTree.set r2 ty1 !env; changed := true; solve_moves rem
      | None, Some ty2 ->
          env := PTree.set r1 ty2 !env; changed := true; solve_moves rem
      | None, None ->
          (r1, r2) :: solve_moves rem

let rec iter_solve_moves mvs =
  changed := false;
  let mvs' = solve_moves mvs in
  if !changed then iter_solve_moves mvs'

let type_pass2 instrs =
  iter_solve_moves (extract_moves instrs)

let typeof e r =
  match PTree.get r e with Some ty -> ty | None -> Tint

let infer_type_environment f instrs =
  try
    env := PTree.empty;
    set_types f.fn_params f.fn_sig.sig_args;
    type_pass1 f.fn_sig.sig_res instrs;
    type_pass2 instrs;
    let e = !env in
    env := PTree.empty;
    Some(typeof e)
  with Type_error msg ->
    Printf.eprintf "Error during RTL type inference: %s\n" msg;
    None