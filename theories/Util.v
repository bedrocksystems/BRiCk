(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Lists.List.

(* note(gmm): this file should be eliminated in favor of definitions defined elsewhere, e.g. in ExtLib *)

Section find_in_list.
  Context {T U : Type}.
  Variable f : T -> option U.

  Fixpoint find_in_list (ls : list T) : option U :=
    match ls with
    | nil => None
    | l :: ls =>
      match f l with
      | None => find_in_list ls
      | x => x
      end
    end.
End find_in_list.
