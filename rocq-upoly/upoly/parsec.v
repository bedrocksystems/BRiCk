(*
 * Copyright (C) BlueRock Security Inc. 2023-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.decidable.
Require Import bedrock.upoly.prelude.
Require Import bedrock.upoly.upoly.
Require Import bedrock.upoly.optionT.
Require Import bedrock.upoly.stateT.

Import UPoly.

Class Next (STREAM TKN : Type) := {
  next : STREAM -> option (TKN * STREAM);
}.

(** ** parsec
    Simple implementation of a parser combinator library.

    NOTE: [M] is a monad transformer so additional state can be
          threaded through the parsing.
 *)
Section parsec.
  Context `{N : Next STREAM TKN} {F : Type -> Type} {MR : MRet F} {FM : FMap F} {MB : MBind F}.

  Definition M (T : Type) : Type :=
    stateT.M STREAM (optionT.M F) T.

  Definition run {T} (m : M T) : STREAM -> F _ :=
    fun str => optionT.run (stateT.run m str).

  #[global] Instance MRet_M : MRet M := @stateT.ret _ _ _.
  #[global] Instance FMap_M : FMap M := @stateT.map _ _ _.
  #[global] Instance MBind_M : MBind M := @stateT.bind _ _ _. (* prefer not to use this *)
  #[global] Instance Ap_M : Ap M := _.
  #[global] Instance MFail_M : MFail M := @stateT.fail _ _ _.
  #[global] Instance MLift_M : MLift F M := fun _ m => lift (optionT.lift m).
  #[global] Instance M_Alternative : Alternative M :=
    fun _ pl pr =>
      stateT.mk (fun s => alternative (stateT.runp pl s) (fun tt => stateT.runp (pr tt) s)).

  #[global] Hint Opaque M : typeclass_instances.
  #[local] Open Scope monad_scope.

  Definition any : M TKN :=
    let* l := stateT.get in
    match next l with
    | None => mfail
    | Some (b, bs) => const b <$> stateT.put bs
    end.

  (* end-of-stream *)
  Definition eos : M unit :=
    let* l := stateT.get in
    match next l with
    | None => mret tt
    | _ => mfail
    end.

  Definition run_full {T} (m : M T) : STREAM -> F (option T) :=
    fun str =>
      (fun x => match x with
             | Some (l, x) => match next l with None => Some x | Some _ => None end
             | _ => None
             end) <$> optionT.run (stateT.run ((fun x _ => x) <$> m <*> eos) str).

  Definition char (P : TKN -> bool) : M TKN :=
    let* c := any in
    if P c then mret c else mfail.

  Definition charP (P : TKN -> Prop) {_ : forall x, Decision (P x)} : M TKN :=
    char (fun x => bool_decide (P x)).

  Definition epsilon : M unit := mret tt.

  Definition or {T} (pl pr : M T) : M T :=
    pl <|> pr.

  Fixpoint anyOf {T} (ls : list (M T)) : M T :=
    match ls with
    | nil => mfail
    | l :: ls => l <|> anyOf ls
    end.

  (* NOTE: this is basically [sequence]/[transpose] *)
  Definition seqs {T} (ls : list (M T)) : M (list T) :=
    sequence ls.

  Definition optional {T} (p : M T) : M (option T) :=
    (Some <$> p) <|> mret None.

  Fixpoint star_ (fuel : nat) {T} (p : M T) : M (list T) :=
    let* x := optional p in
    match x with
    | None => mret nil
    | Some v =>
        match fuel with
        | 0 => mfail (* This is usually the programmers fault *)
        | S fuel => cons v <$> star_ fuel p
        end
    end.

  Definition star : forall {T}, _ := @star_ 1000.

  Definition plus {T} (p : M T) : M (list T) :=
    cons <$> p <*> star p.

  Definition peek : M (option TKN) :=
    let k l :=
      match next l with
      | None => None
      | Some (x, _) => Some x
      end
    in
    k <$> stateT.get.

  Definition sepBy {T} (sep : M unit) (p : M T) : M (list T) :=
    (cons <$> p <*> (star ((fun _ x => x) <$> sep <*> p))) <|> mret nil.

  #[local]
  Fixpoint exact_ {_ : EqDecision TKN} (b : list TKN) (input : STREAM) {struct b}
      : optionT.M F (UTypes.prod STREAM unit) :=
    match b with
    | nil => mret (UTypes.pair input tt)
    | x :: xs =>
        match next input with
        | Some (y, ys) =>
            if bool_decide (x = y) then
              exact_ xs ys
            else mfail
        | None => mfail
        end
    end.

  Definition exact {_ : EqDecision TKN} (b : list TKN) : M unit :=
    stateT.mk $ exact_ b.

   Definition not {T} (p : M T) : M unit :=
    stateT.mk $ fun bs => optionT.mk $
      let* v := parsec.run p bs in
      if v is None then mret (UTypes.Some $ UTypes.pair bs tt) else mret UTypes.None.
End parsec.

Arguments M _ _ _ : clear implicits.
