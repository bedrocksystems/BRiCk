From bedrock.prelude Require Import base.
From bedrock.prelude Require Export list numbers.

#[local] Open Scope N_scope.

Definition seqN (from count : N) : list N :=
  N.of_nat <$> seq (N.to_nat from) (N.to_nat count).
#[global] Arguments seqN : simpl never.

Definition replicateN {A} (count : N) (x : A) : list A :=
  replicate (N.to_nat count) x.
#[global] Arguments replicateN : simpl never.
#[deprecated(since="2021-05-26",note="use [replicateN]")]
Notation repeatN := (flip replicateN) (only parsing).

Definition dropN {A} n := drop (A := A) (N.to_nat n).
Definition takeN {A} n := take (A := A) (N.to_nat n).
Definition lengthN {A} xs := N.of_nat (length (A := A) xs).
Definition resizeN {A} n := resize (A := A) (N.to_nat n).
Definition rotateN {A} n xs :=
  dropN (A := A) (n mod lengthN xs) xs ++ takeN (A := A) (n mod lengthN xs) xs.

Lemma fmap_lengthN {A B} (f : A → B) (l : list A) :
  lengthN (f <$> l) = lengthN l.
Proof. by rewrite /lengthN fmap_length. Qed.

Lemma length_lengthN {A} (xs : list A) :
  length xs = N.to_nat (lengthN xs).
Proof. by rewrite /lengthN Nat2N.id. Qed.

Section seqN.
  Lemma cons_seqN len start :
    start :: seqN (N.succ start) len = seqN start (N.succ len).
  Proof. by rewrite /seqN !N2Nat.inj_succ -cons_seq fmap_cons N2Nat.id. Qed.

  (* Lifts stdpp's [seq_S_end_app] aka stdlib's [seq_S] *)
  Lemma seqN_S_end_app start len :
    seqN start (N.succ len) = seqN start len ++ [start + len].
  Proof.
    rewrite /seqN !N2Nat.inj_succ seq_S_end_app fmap_app /=.
    by rewrite -N2Nat.inj_add N2Nat.id.
  Qed.

  Lemma cons_seqN' [len start] sstart :
    sstart = N.succ start ->
    start :: seqN sstart len = seqN start (N.succ len).
  Proof. move->. apply cons_seqN. Qed.

  Lemma seqN_S_end_app' [w n] sn :
    sn = N.succ n ->
    seqN w sn = seqN w n ++ [w + n].
  Proof. move->. apply seqN_S_end_app. Qed.

  Lemma seqN_lengthN len start : lengthN (seqN start len) = len.
  Proof. by rewrite /seqN fmap_lengthN /lengthN seq_length N2Nat.id. Qed.

  Lemma NoDup_seqN j n : NoDup (seqN j n).
  Proof. apply /NoDup_fmap_2 /NoDup_seq. Qed.
End seqN.

Lemma repeatN_replicateN {A} (x : A) n :
  repeat x (N.to_nat n) = replicateN n x.
Proof. apply repeat_replicate. Qed.

Lemma repeat_replicateN {A} (x : A) n :
  repeat x n = replicateN (N.of_nat n) x.
Proof. by rewrite repeat_replicate /replicateN Nat2N.id. Qed.

Lemma replicateN_0 {A} (x : A) : replicateN 0 x = [].
Proof. done. Qed.

Lemma replicateN_S {A} (x : A) n : replicateN (N.succ n) x = x :: replicateN n x.
Proof. by rewrite /replicateN/= N2Nat.inj_succ. Qed.

Lemma elem_of_replicateN {A} (count : N) (b a : A) : a ∈ replicateN count b → b = a.
Proof. by intros [-> _]%elem_of_replicate. Qed.

Section listN.
  Context {A : Type}.

  Implicit Type (x : A) (n m : N).

  Lemma N2Nat_inj_le n m :
    n ≤ m ->
    (N.to_nat n <= N.to_nat m)%nat.
  Proof. lia. Qed.

  Lemma elem_of_seqN (len start n : N) :
    n ∈ seqN start len ↔ start <= n < start + len.
  Proof.
    rewrite /seqN -{1} (N2Nat.id n) elem_of_list_fmap_inj.
    rewrite elem_of_seq. lia.
  Qed.

  Lemma Forall_seqN P (i n : N) :
    List.Forall P (seqN i n) ↔ (∀ j : N, i <= j < i + n → P j).
  Proof. rewrite Forall_forall. by setoid_rewrite elem_of_seqN. Qed.

  (* TODO: extend the theory of [lengthN], we have few lemmas here. *)
  Lemma nil_lengthN :
    lengthN (A := A) [] = 0.
  Proof. done. Qed.

  Lemma cons_lengthN x xs :
    lengthN (x :: xs) = N.succ (lengthN xs).
  Proof. by rewrite /lengthN cons_length Nat2N.inj_succ. Qed.

  (* Lift all theory about [drop] and [replicate] interaction. *)
  Lemma dropN_replicateN n m x :
    dropN n (replicateN m x) = replicateN (m - n) x.
  Proof. by rewrite /dropN /replicateN drop_replicate N2Nat.inj_sub. Qed.

  Lemma dropN_replicateN_plus n m x :
    dropN n (replicateN (n + m) x) = replicateN m x.
  Proof. by rewrite /dropN /replicateN N2Nat.inj_add drop_replicate_plus. Qed.

  (* Lift all theory about [take] and [replicate] interaction. *)
  Lemma takeN_replicateN n m x :
    takeN n (replicateN m x) = replicateN (n `min` m) x.
  Proof. by rewrite /takeN /replicateN take_replicate N2Nat.inj_min. Qed.

  Lemma takeN_replicateN_plus n m x :
    takeN n (replicateN (n + m) x) = replicateN n x.
  Proof. by rewrite /takeN /replicateN N2Nat.inj_add take_replicate_plus. Qed.

  Lemma resizeN_spec l n x :
    resizeN n x l = takeN n l ++ replicateN (n - lengthN l) x.
  Proof.
    by rewrite /resizeN /replicateN resize_spec !N2Nat.inj_sub Nat2N.id.
  Qed.

  (* Part of the theory of [resize], it's rather large. *)
  Lemma resizeN_all l x : resizeN (lengthN l) x l = l.
  Proof. by rewrite /resizeN /lengthN Nat2N.id resize_all. Qed.

  Lemma resizeN_0 l x : resizeN 0 x l = [].
  Proof. by rewrite /resizeN resize_0. Qed.

  Lemma resizeN_lengthN l n x :
    lengthN (resizeN n x l) = n.
  Proof. by rewrite /lengthN /resizeN /= resize_length N2Nat.id. Qed.

  Lemma resizeN_nil n x : resizeN n x [] = replicateN n x.
  Proof. apply resize_nil. Qed.

  Lemma resizeN_replicateN x n m:
    resizeN n x (replicateN m x) = replicateN n x.
  Proof. by rewrite /resizeN /replicateN resize_replicate. Qed.

  Lemma resizeN_idemp l n x :
    resizeN n x (resizeN n x l) = resizeN n x l.
  Proof. apply resize_idemp. Qed.

  (* Lift all theory about [drop] and [resize] interaction. *)
  Lemma dropN_resizeN_plus l m n x :
    dropN n (resizeN (n + m) x l) = resizeN m x (dropN n l).
  Proof. by rewrite /dropN /resizeN N2Nat.inj_add drop_resize_plus. Qed.

  Lemma dropN_resizeN_le l n m x :
    n <= m →
    dropN n (resizeN m x l) = resizeN (m - n) x (dropN n l).
  Proof.
    move=> /N2Nat_inj_le Hle.
    by rewrite /dropN /resizeN drop_resize_le // N2Nat.inj_sub.
  Qed.

  Lemma resizeN_plusN l n m x :
    resizeN (n + m) x l = resizeN n x l ++ resizeN m x (dropN n l).
  Proof. by rewrite /resizeN /dropN N2Nat.inj_add resize_plus. Qed.

  (* Lift all theory about [take] and [resize] interaction. *)
  Lemma takeN_resizeN_eq l n x :
    takeN n (resizeN n x l) = resizeN n x l.
  Proof. apply take_resize_eq. Qed.

  Lemma resizeN_takeN_eq l n x :
    resizeN n x (takeN n l) = resizeN n x l.
  Proof. apply resize_take_eq. Qed.

  Lemma takeN_resizeN l n m x :
    takeN n (resizeN m x l) = resizeN (n `min` m) x l.
  Proof. by rewrite /takeN /resizeN take_resize N2Nat.inj_min. Qed.

  Lemma takeN_resizeN_plus l n m x :
    takeN n (resizeN (n + m) x l) = resizeN n x l.
  Proof. by rewrite /takeN /resizeN N2Nat.inj_add take_resize_plus. Qed.

  Lemma to_nat_lengthN (l : list A) :
    N.to_nat (lengthN l) = length l.
  Proof. by rewrite /lengthN Nat2N.id. Qed.

  Lemma resizeN_le l n x :
    n <= lengthN l ->
    resizeN n x l = takeN n l.
  Proof. move=> /N2Nat_inj_le. rewrite to_nat_lengthN. apply resize_le. Qed.

  Lemma takeN_resizeN_le l n m x  :
    n ≤ m →
    takeN n (resizeN m x l) = resizeN n x l.
  Proof. move=> /N2Nat_inj_le. apply take_resize_le. Qed.

  Lemma resizeN_takeN_le l n m x :
    (n <= m) → resizeN n x (takeN m l) = resizeN n x l.
  Proof. move=> /N2Nat_inj_le. apply resize_take_le. Qed.

  (* resizeN_spec is above *)
End listN.

(* Not necessarily restricted to [Finite] *)
Lemma nat_fin_iter_lt (c : nat) (P : nat -> Prop) :
  Forall P (seq 0 c) ->
  forall i, (i < c)%nat -> P i.
Proof. move=>/Forall_seq /= F. eauto with lia. Qed.

Lemma nat_fin_iter_le (c : nat) (P : nat -> Prop) :
  Forall P (seq 0 (S c)) ->
  forall i, (i <= c)%nat -> P i.
Proof. move=> F i Hle. eapply nat_fin_iter_lt; [done | lia]. Qed.

Lemma N_fin_iter_lt (c : N) (P : N -> Prop) :
  Forall P (seqN 0 c) ->
  forall i, i < c -> P i.
Proof.
  move=> F i Hle. rewrite -(N2Nat.id i).
  apply (nat_fin_iter_lt (N.to_nat c) (P ∘ N.of_nat)); [| lia] => {i Hle}.
  rewrite -Forall_fmap. apply F.
Qed.

Lemma N_fin_iter_le (c : N) (P : N -> Prop) :
  Forall P (seqN 0 (N.succ c)) ->
  forall i, i <= c -> P i.
Proof. move=> F i Hle. eapply N_fin_iter_lt; [done | lia]. Qed.
