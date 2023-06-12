From bedrock.lang.cpp Require Import logic.

Section with_Σ.
  Context `{Σ : cpp_logic}.
  Section bi_inference.
    Definition mpred_sep (P Q : mpred) := P ** Q.
    Definition rep_sep (P Q : Rep) := P ** Q.
  End bi_inference.
End with_Σ.

About mpred_sep.
About rep_sep.

(* Test suite *)
Module Type TEST_SUITE.
Section test_suite.
  Context {σ : genv} `{Σ : cpp_logic} (R : Rep) (f g : field) (o : offset) (p : ptr) (v : val).

  #[local] Ltac syntactically_equal :=
    lazymatch goal with
    | _ : _ |- ?X = ?X => idtac
    end;
    reflexivity.

  Goal o ., f = o ,, _field f.
  Proof. syntactically_equal. Qed.

  Goal p |-> R = _at p R.
  Proof. syntactically_equal. Qed.

  Goal o |-> R = _offsetR o R.
  Proof. syntactically_equal. Qed.

  (*Example _0 := |> p |-> R.

  Example _1 := |> p ., f |-> R.

  Example _1' := |> _eqv v ., f |-> R.*)

  Example _2 := p |-> _field f |-> R.

  Example _3 := p .[ Tint ! 0 ] |-> R.

  Example _4 := p |-> _field f .[ Tint ! 0 ] |-> R.

  Example _4a := p ., f |-> R.

  Example _4b : p ., f .[ Tint ! 0] = (p ., f) .[ Tint ! 0].
  Proof. syntactically_equal. Qed.

  Example _5 := p .[ Tint ! 0 ] .[ Tint ! 3 ] |-> R.

  Example _6 := p ., f .[ Tint ! 0 ] ., g |-> R.

  Example _7 := p ., g ., f .[ Tint ! 1 ] .[ Tint ! 0 ] ., f |-> _field f |-> R.

  Example _8 := p ., g ., f .[ Tint ! 1 ] .[ Tint ! 0 ] ., f |-> .[ Tint ! 1 ] |-> R.

  Example _9 := o ., g ., f .[ Tint ! 1 ] .[ Tint ! 0 ] ., f |-> R.

  Example _11 := o .[ Tint ! 1 ] |-> R.

  (*Example _13 := _eqv v .[ Tint ! 1 ] |-> R.

  Example _13' := _eqv v |-> R.*)

  Example _14 := .[ Tint ! 1 ] |-> R.

  (*Example _15 := |> .[ Tint ! 1 ] |-> |> R.*)

  Example _16 := p .[ Tint ! 1] |-> _offsetR (_field f) R.

  (*backwards compatibility*)
  Example b0 := _at p R.

  Example b1 := _offsetR (_field f) R.

  Example b2 := _at (p .[ Tint ! 1]) R.

  Example b3 := _at (p .[ Tint ! 1]) (_offsetR (_field f) R).

  (*failure cases*)
  (*Fail Example fail0 := p |-> ▷ R ∗ R.
  (*Fail Example fail1 := p |-> |> R ** R. (* requires parsing as [(p |-> |> R) ** R] *)*)

  Fail Example fail2 := p |-> R ** R.*) (* requires parsing as [(p |-> R) ** R] *)

  Fail Example fail3 := p |-> R q.
End test_suite.
End TEST_SUITE.
