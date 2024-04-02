(*
 * Copyright (C) BedRock Systems Inc. 2020-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import iris.proofmode.tactics.
Require Import bedrock.prelude.bytestring.
Require Export bedrock.prelude.tactics.base_dbs.
Require Ltac2.Ltac2.

(** NamedBinder is a type wrapper that can be used to record the name
    of a binder in a persistent way that is not affected by any computation.

    Existentials/universals of type [NamedBinder A str] are always
    eliminated/introduced directly as an assumption named [str] of type [A].
 *)
Definition NamedBinder (A:Type) (name : BS.t) := A.
#[global] Arguments NamedBinder : simpl never.
#[global] Hint Opaque NamedBinder : typeclass_instances br_opacity.

Module Binder.
  Import Ltac2.
  Import Ltac2.Printf.
  Import Ltac2.Constr.
  Import Ltac2.Constr.Unsafe.

  Ltac2 int_of_byte (b : constr) :=
    match kind b with
    | Constructor c _ => Constructor.index c
    | _ => Control.throw (Invalid_argument (Some (Message.of_constr b)))
    end.

  Ltac2 str_of_bs (bs : constr) : string :=
    let rec go bs n acc :=
      lazy_match! bs with
      | BS.EmptyString => (n, acc)
      | BS.String ?b ?bs =>
        let char := Char.of_int (int_of_byte b) in
        go bs (Int.add n 1) (char :: acc)
      end
    in
    let (len, chars) := go bs 0 [] in
    let str := String.make len (Char.of_int 0) in
    let n := Int.sub len 1 in
    List.iteri (fun i char => String.set str (Int.sub n i) char) chars;
    str.

  Ltac2 to_id_fun (bs : constr) : unit :=
    let str := str_of_bs bs in
    let id := Ident.of_string str in
    let binder := Constr.Binder.make id 'unit in
    let f := Constr.Unsafe.make (
        Constr.Unsafe.Lambda binder (Constr.Unsafe.make (Constr.Unsafe.Rel 1))
      )
    in
    refine f.

  Ltac id_of_bs := ltac2:(bs |- to_id_fun (Option.get (Ltac1.to_constr bs))).
End Binder.

(* [TCForceEq] disregards typeclass_instances opacity.  *)
Inductive TCForceEq {A : Type} (x : A) : A → Prop :=  TCForceEq_refl : TCForceEq x x.
Existing Class TCForceEq.
#[global] Hint Extern 100 (TCForceEq ?x _) => refine (TCForceEq_refl x) : typeclass_instances.

Class IdOfBS (name : BS.t) (ident : () -> ()) := ID_OF_BS {}.
#[global] Arguments IdOfBS name%_bs_scope _%_function_scope.
#[global] Hint Mode IdOfBS ! - : typeclass_instances.

#[global] Hint Extern 100 (IdOfBS ?name _) =>
  refine (@ID_OF_BS name ltac:(Binder.id_of_bs name)) : typeclass_instances.

#[global] Instance from_forall_named_binder {PROP:bi} {A} {name} {id}
  {Φ : NamedBinder A name -> PROP}
  {Φ' : A -> PROP} :
  IdOfBS name id ->
  TCForceEq Φ Φ' ->
  FromForall (∀ x : NamedBinder A name, Φ x) Φ' id | 0.
Proof. move => _ ->. by rewrite /FromForall. Qed.

#[global] Instance into_exist_named_binder {PROP:bi} {A} {name} {id}
  {Φ : NamedBinder A name -> PROP}
  {Φ' : A -> PROP} :
  IdOfBS name id ->
  TCForceEq Φ Φ' ->
  IntoExist (∃ x : NamedBinder A name, Φ x) Φ' id | 0.
Proof. move => _ ->. by rewrite /IntoExist. Qed.

Module Type Test.
  Tactic Notation "test" ident(name) := (assert (name = ()) by (destruct name; reflexivity)).

  Goal forall {PROP:bi}, ⊢@{PROP} ∀ x : NamedBinder unit "name"%bs, False.
  Proof.
    intros PROP.
    (* The name returned in [FromForall] is only honored if we explicitly introduce [(?)] *)
    assert_fails (iIntros; test name).
    assert_succeeds (iIntros (?); test name).
  Abort.

  Goal forall {PROP:bi}, (∃ x : NamedBinder unit "name"%bs, False) ⊢@{PROP} False.
  Proof.
    intros PROP.
    assert_succeeds (iIntros "[% ?]"; test name).
    assert_succeeds (iIntros "H"; iDestruct "H" as (?) "H"; test name).
  Abort.
End Test.
