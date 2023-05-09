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
