(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
(** *)

From iris.bi Require Import bi.
From iris.proofmode Require Import tactics.

(**
Derived BI laws, similarly to iris.bi.derived_laws.

They should be upstreamed if appropriate.
When upstreaming, add a comment (with the upstream name if different).
When bumping Iris, drop lemmas that are now upstream.
*)

Section derived_laws.
  Context {PROP : bi}.

  (* Upstream as [exist_exist], https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/552 *)
  Lemma exist_comm {A B} (Φ : A → B → PROP) :
    (∃ a b, Φ a b) ⊣⊢ (∃ b a, Φ a b).
  Proof. iSplit; iDestruct 1 as (??) "H"; eauto. Qed.

  (* Upstream as [exist_forall], ditto. *)
  Lemma exist_forall_comm {A B} (Φ : A → B → PROP) :
    (∃ a, ∀ b, Φ a b) ⊢ (∀ b, ∃ a, Φ a b).
  Proof. iDestruct 1 as (a) "H". iIntros (b). iExists a. by iApply "H". Qed.
End derived_laws.
