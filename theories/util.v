From iris Require Import bi.bi.
From bedrock Require Import IrisBridge.
Import ChargeNotation.
Section lift.
  Context {PROP: bi}.
  Notation paddr := N.
  Variable byte_at : forall (hpa:paddr) (hpaFrac : Qp) (value : N), PROP.

  Definition short_at (pa : paddr) (q:Qp) (v : N) : PROP :=
    byte_at pa q (N.land v (2^8 - 1)) **
            byte_at (pa + 1)%N q (N.shiftr v 8).

  Definition word_at (pa : paddr) (q : Qp) (v : N) : PROP :=
    short_at pa q (N.land v (2^16 - 1))**
             short_at (pa + 2)%N q (N.shiftr v 16).

  Definition dword_at (pa : paddr) (q : Qp) (v : N) : PROP :=
    word_at pa q (N.land v (2^32 - 1))**
            word_at (pa + 4)%N q (N.shiftr v 32).
End lift.
