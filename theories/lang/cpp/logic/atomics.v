(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.Lists.List.

From iris.base_logic.lib Require Import
     fancy_updates invariants cancelable_invariants wsat.
Import invG.

From bedrock Require Import ChargeCompat.
From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp call cclogic.

Local Open Scope Z_scope.

Section with_Σ.
  Context `{Σ : cpp_logic thread_info, !invG Σ} {resolve:genv}.
  Variables (M : coPset) (ti : thread_info) (ρ : region).

  Local Notation wp_prval := (wp_prval (resolve:=resolve) M ti ρ).
  Local Notation wp_args := (wp_args (σ:=resolve) M ti ρ).

  Local Notation glob_def := (glob_def resolve) (only parsing).
  Local Notation eval_unop := (@eval_unop resolve) (only parsing).
  Local Notation eval_binop := (@eval_binop resolve) (only parsing).
  Local Notation size_of := (@size_of resolve) (only parsing).
  Local Notation align_of := (@align_of resolve) (only parsing).
  Local Notation primR := (@primR _ _ resolve) (only parsing).
  Local Notation anyR := (@anyR _ _ resolve) (only parsing).

  Definition wrap_shift (F : (val -> mpred) -> mpred) (Q : val -> mpred) : mpred :=
    Exists mid, (|={M,mid}=> F (fun result => |={mid,M}=> Q result))%I.

  (* semantics of atomic builtins
   * https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
   *)
  (****** Wp Semantics for atomic operations
   * These are given in the style of function call axioms
   *)
  Parameter wp_atom :
      forall {resolve:genv}, coPset -> thread_info ->
        AtomicOp -> type (* the access type of the atomic operation *) ->
        list val -> (val -> mpred) -> mpred.

  Local Notation wp_atom' := (@wp_atom resolve M ti) (only parsing).

  Definition pointee_type (t : type) : option type :=
    match t with
    | Tpointer t => Some t
    | _ => None
    end.

  Definition get_acc_type (ao : AtomicOp) (ret : type) (ts : list type) : option type :=
    match ts with
    | t :: _ => pointee_type (erase_qualifiers t)
    | _ => None
    end.

  (* note that this rule captures all of the interesting reasoning about atomics
   * through the use of [wp_shift]
   *)
  Axiom wp_prval_atomic: forall ao es ty Q,
      match get_acc_type ao ty (map (fun x => type_of (snd x)) es) with
      | None => lfalse
      | Some acc_type =>
        wp_args es (fun (vs : list val) (free : FreeTemps) =>
          wrap_shift (wp_atom' ao acc_type vs) (fun v => Q v free))
      end
      |-- wp_prval (Eatomic ao es ty) Q.

  (* Memory Ordering Patterns: Now we only have _SEQ_CST *)
  Definition _SEQ_CST := Vint 5.

  (* note: the following axioms have laters earlier than they should be.
   * it is ok, because these are provable given the timelessness of points
   * to, but in truth, these should be proven from more primitive axioms.
   *)

  (* note(gmm): these are used for reading and writing values shared between
   * threads.
   * note(gmm): these look exactly like the standard read and write assertions
   * because all of the invariant reasoning is encapsulated in [wp_shift].
   *)
  Axiom wp_atom_load_cst
  : forall q memorder (acc_type:type) (l : val) (Q : val -> mpred),
      [| memorder = _SEQ_CST |] **
      |> (Exists v, (_at (_eqv l) (primR acc_type q v) **
                     (_at (_eqv l) (primR acc_type q v) -* Q v)))
      |-- wp_atom' AO__atomic_load_n acc_type (l :: memorder :: nil) Q.

  Axiom wp_atom_store_cst
  : forall memorder acc_type l Q v,
      [| memorder = _SEQ_CST |] **
      [| has_type v acc_type |] **
      |> (_at (_eqv l) (anyR acc_type 1) **
         (_at (_eqv l) (primR acc_type 1 v) -* Q Vundef))
      |-- wp_atom' AO__atomic_store_n acc_type (l :: memorder :: v :: nil) Q.

  (* atomic compare and exchange n *)
  Axiom wp_atom_compare_exchange_n_suc:
    forall val_p expected_p desired wk succmemord failmemord Q' ty v,
      [| wk = Vbool false |] ** [| succmemord = _SEQ_CST |] **
      [| failmemord = _SEQ_CST |] **
      |> (_at (_eqv expected_p) (primR ty 1 v) **
          _at (_eqv val_p) (primR ty 1 v) **
          ((_at (_eqv expected_p) (primR ty 1 v) **
            _at (_eqv val_p) (primR ty 1 desired)) -* Q' (Vbool true)))
      |-- wp_atom' AO__atomic_compare_exchange_n ty
                  (val_p::succmemord::expected_p::failmemord::desired::wk::nil) Q'.

  Axiom wp_atom_compare_exchange_n_fail:
    forall val_p expected_p desired wk succmemord failmemord Q'
           (ty : type) v expected,
      [|wk = Vbool false|] ** [|succmemord = _SEQ_CST|] ** [| failmemord = _SEQ_CST |] **
      [| v <> expected |] **
      |> (_at (_eqv expected_p) (primR ty 1 expected) **
          _at (_eqv val_p) (primR ty 1 v) **
          ((_at (_eqv expected_p) (primR ty 1 v) **
            _at (_eqv val_p) (primR ty 1 v)) -* Q' (Vbool false)))
      |-- wp_atom' AO__atomic_compare_exchange_n ty
                  (val_p::succmemord::expected_p::failmemord::desired::wk::nil) Q'.

  Axiom wp_atom_compare_exchange_n_weak:
    forall val_p expected_p expected desired wk succmemord failmemord Q' ty v,
      [| wk = Vbool true |] ** [| succmemord = _SEQ_CST |] **
      [| failmemord = _SEQ_CST |] **
      |> (_at (_eqv expected_p) (primR ty 1 expected) **
          _at (_eqv val_p) (primR ty 1 v) **
          (((_at (_eqv expected_p) (primR ty 1 expected) **
             _at (_eqv val_p) (primR ty 1 desired) **
             [| v = expected |]) -* Q' (Vbool true)) //\\
           ((_at (_eqv expected_p) (primR ty 1 v) **
             _at (_eqv val_p) (primR ty 1 v)) -* Q' (Vbool false))))
      |-- wp_atom' AO__atomic_compare_exchange_n ty
                  (val_p::succmemord::expected_p::failmemord::desired::wk::nil) Q'.

  (* atomic compare and exchange *)
  Axiom wp_atom_compare_exchange_suc :
    forall q val_p expected_p desired_p wk succmemord failmemord Q
      (ty : type)
      expected desired,
      [|wk = Vbool false|] ** [|succmemord = _SEQ_CST|] ** [| failmemord = _SEQ_CST |] **
      |> ((_at (_eqv expected_p) (primR ty 1 expected) **
           _at (_eqv desired_p) (primR ty q desired) **
           _at (_eqv val_p) (primR ty 1 expected)) **
         ((_at (_eqv expected_p) (primR ty 1 expected) **
           _at (_eqv desired_p) (primR ty q desired) **
           _at (_eqv val_p) (primR ty 1 desired)) -* Q (Vbool true)))
      |-- wp_atom' AO__atomic_compare_exchange ty
                  (val_p::succmemord::expected_p::failmemord::desired_p::wk::nil) Q.

  Axiom wp_atom_compare_exchange_fail :
    forall q val_p expected_p desired_p wk succmemord failmemord Q
      (ty : type)
      actual expected desired,
      expected <> actual ->
      [|wk = Vbool false|] ** [|succmemord = _SEQ_CST|] ** [| failmemord = _SEQ_CST |] **
      |> ((_at (_eqv expected_p) (primR ty 1 expected) **
           _at (_eqv desired_p) (primR ty q desired) **
           _at (_eqv val_p) (primR ty 1 actual)) **
          ((_at (_eqv expected_p) (primR ty 1 actual) **
            _at (_eqv desired_p) (primR ty q desired) **
            _at (_eqv val_p) (primR ty 1 actual)) -* Q (Vbool false)))
      |-- wp_atom' AO__atomic_compare_exchange ty
                  (val_p::succmemord::expected_p::failmemord::desired_p::wk::nil) Q.

  Axiom wp_atom_compare_exchange_weak :
    forall q val_p expected_p desired_p wk succmemord failmemord Q
      (ty : type)
      actual expected desired,
      [|wk = Vbool true|] ** [|succmemord = _SEQ_CST|] ** [| failmemord = _SEQ_CST |] **
      |> ((_at (_eqv expected_p) (primR ty 1 expected) **
           _at (_eqv desired_p) (primR ty q desired) **
           _at (_eqv val_p) (primR ty 1 actual)) **
          (((_at (_eqv expected_p) (primR ty 1 expected) **
             _at (_eqv desired_p) (primR ty q desired) **
             _at (_eqv val_p) (primR ty 1 desired)) **
             [| actual = expected |] -* Q (Vbool true)) //\\
           ((_at (_eqv expected_p) (primR ty 1 actual) **
             _at (_eqv desired_p) (primR ty q desired) **
             _at (_eqv val_p) (primR ty 1 actual)) -* Q (Vbool false))))
      |-- wp_atom' AO__atomic_compare_exchange ty
                  (val_p::succmemord::expected_p::failmemord::desired_p::wk::nil) Q.

  (* atomic fetch and xxx rule *)
  Definition wp_fetch_xxx ao (op : Z -> Z -> Z) : Prop :=
    forall E pls memorder Q sz sgn,
      let acc_type := Tint sz sgn in
      ([| memorder = _SEQ_CST |] **
       Exists v,
       |> _at (_eqv E) (primR acc_type 1 (Vint v)) **
       |> let v' :=
              let v' := op (to_unsigned (bitsN sz) v) pls in
              if sgn then to_signed sz v' else to_unsigned (bitsN sz) v'
          in
          _at (_eqv E) (primR acc_type 1 (Vint v')) -* Q (Vint v))
      |-- wp_atom' ao acc_type (E::memorder::Vint pls::nil) Q.

  Ltac fetch_xxx ao op :=
    let G := eval unfold wp_fetch_xxx in (wp_fetch_xxx ao op) in exact G.

  Let nand (a b : Z) : Z := Z.lnot (Z.land a b).

  Axiom wp_atom_fetch_add  : ltac:(fetch_xxx AO__atomic_fetch_add Z.add).
  Axiom wp_atom_fetch_sub  : ltac:(fetch_xxx AO__atomic_fetch_sub Z.sub).
  Axiom wp_atom_fetch_and  : ltac:(fetch_xxx AO__atomic_fetch_and Z.land).
  Axiom wp_atom_fetch_xor  : ltac:(fetch_xxx AO__atomic_fetch_xor Z.lxor).
  Axiom wp_atom_fetch_or   : ltac:(fetch_xxx AO__atomic_fetch_or  Z.lor).
  Axiom wp_atom_fetch_nand : ltac:(fetch_xxx AO__atomic_fetch_or  nand).

  (* atomic xxx and fetch rule *)
  Definition wp_xxx_fetch ao (op : Z -> Z -> Z) : Prop :=
    forall E pls memorder Q sz sgn,
      let acc_type := Tint sz sgn in
      ([| memorder = _SEQ_CST |] **
       Exists v,
       |> _at (_eqv E) (primR acc_type 1 (Vint v)) **
       |> let v' :=
              let v' := op (to_unsigned (bitsN sz) v) pls in
              if sgn then to_signed sz v' else to_unsigned (bitsN sz) v'
          in
          _at (_eqv E) (primR acc_type 1 (Vint v')) -* Q (Vint v'))
      |-- wp_atom' ao acc_type (E::memorder::Vint pls::nil) Q.

  Ltac xxx_fetch ao op :=
    let G := eval unfold wp_xxx_fetch in (wp_xxx_fetch ao op) in exact G.

  Axiom wp_atom_add_fetch : ltac:(xxx_fetch AO__atomic_add_fetch Z.add).
  Axiom wp_atom_sub_fetch : ltac:(xxx_fetch AO__atomic_sub_fetch Z.sub).
  Axiom wp_atom_and_fetch : ltac:(xxx_fetch AO__atomic_and_fetch Z.land).
  Axiom wp_atom_xor_fetch : ltac:(xxx_fetch AO__atomic_xor_fetch Z.lxor).
  Axiom wp_atom_or_fetch  : ltac:(xxx_fetch AO__atomic_or_fetch  Z.lor).
  Axiom wp_atom_nand_fetch : ltac:(fetch_xxx AO__atomic_fetch_or nand).

End with_Σ.
