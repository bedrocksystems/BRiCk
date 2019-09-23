Require Import Cpp.Auto.
Require Import Cpp.Auto.Lemmas.

Lemma _at_ticptr_cglob {resolve} : forall gn s s' ti P,
    s = s' ->
        _at (_global gn) (ticptr s) ** P
    |-- (|> cglob (resolve:=resolve) gn ti s') ** ltrue.
Proof. Admitted.
Lemma later_at_ticptr_cglob {resolve} : forall gn s s' ti P,
    s = s' ->
        (|> _at (_global gn) (ticptr s)) ** P
    |-- (|> cglob (resolve:=resolve) gn ti s') ** ltrue.
Proof. Admitted.

Ltac find_left tac :=
  let rec perm :=
      lazymatch goal with
      | |- (?A ** ?B) ** ?C |-- _ => first
          [ simple eapply Discharge.focus_ll; perm
          | simple eapply Discharge.focus_lr; perm ]
      | |- _ => tac
      end
  in
  lazymatch goal with
  | |- _ ** _ |-- _ => first
    [ perm | simple eapply Discharge.focus_lswap; perm ]
  | |- empSP |-- _ => fail
  | |- _ |-- _ => simple eapply Discharge.focus_lstart; tac
  end.

(* this tactic solves goals of the form
 *
 *   F |-- |> cglob' f ti s ** ltrue
 *
 * which arise from various forms of calls.
 *)
Ltac find_spec :=
  let prove_eq :=
      solve [ reflexivity
            | eapply (@Lemmas.unify_SFunction _ _ _ _ _ _ eq_refl eq_refl eq_refl) ]
  in
  let try_this_one :=
      first [ simple eapply Lemmas.cglob_by_cglob_gen;
              prove_eq
            | simple eapply Lemmas.cglob_by_ti_cglob_gen; prove_eq
            | simple eapply Lemmas.cglob_by_later_cglob_gen; prove_eq
            | simple eapply Lemmas.cglob_by_later_ti_cglob_gen; prove_eq
            | simple eapply Lemmas.cglob_by_make_signature_ti_gen;
              [ reflexivity
              | prove_eq ]
            | simple eapply Lemmas.cglob_by_later_make_signature_ti_gen;
              [ reflexivity | prove_eq
              ]
            | eapply later_at_ticptr_cglob; prove_eq
            | eapply _at_ticptr_cglob; prove_eq
            ]
  in
  solve [ find_left try_this_one ].
