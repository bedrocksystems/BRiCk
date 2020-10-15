From iris Require Import bi.bi.
From bedrock Require Import IrisBridge.
Import ChargeNotation.
Open Scope N_scope.
Section lift.
  Context {PROP: bi}.
  Notation paddr := N.
  Variable byte_at : forall (hpa:paddr) (hpaFrac : Qp) (value : N), PROP.

  Fixpoint lift n (pa : paddr) (q:Qp) (v : N) :=
    match n with
    | O => byte_at pa q v
    | S n => let bytesize :N := (2^(N.of_nat n)) in
            let bitsize := (8*bytesize)%N in
            lift n pa q (N.land v (2^bitsize - 1))
            ** lift n (pa+bytesize) q (N.shiftr v bitsize)
    end.

  Section test.

    Local Definition short_at (pa : paddr) (q:Qp) (v : N) : PROP :=
      byte_at pa q (N.land v (2^8 - 1))%N **
              byte_at (pa + 1)%N q (N.shiftr v 8).

    Local Definition word_at (pa : paddr) (q : Qp) (v : N) : PROP :=
      short_at pa q (N.land v (2^16 - 1))**
               short_at (pa + 2)%N q (N.shiftr v 16).

    Example t1 pa q v : short_at pa q v = lift 1 pa q v.
    reflexivity.
    Qed.
    Example t2 pa q v : word_at pa q v = lift 2 pa q v.
    reflexivity.
    Qed.
  End test.

End lift.
