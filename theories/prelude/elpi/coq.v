(*
 * Copyright (C) BedRock Systems Inc. 2024
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require Import elpi.elpi.

(* depends on `coq-builtin.elpi.` *)
Elpi Db bedrock.coq.db lp:{{
  namespace coq {
    % [fold TM FUN ACC ACC']: fold FUN over coq term TM, accumulating ACC'.
    % Expects FUN to be total (i.e., to never reject terms).
    pred fold i:term, i:term -> A -> A -> prop, i:A, o:A.
    fold (sort _ as TM) F A A' :- !, F TM A A'.
    fold (global _ as TM) F A A' :- !, F TM A A'.
    fold (pglobal _ _ as TM) F A A' :- !, F TM A A'.
    fold (fun _ T FUN as TM) F A A' :- !, F TM A A1,
        pi X\ fold (FUN X) F {fold T F A1} A'.
    fold (prod _ T FUN as TM) F A A' :- !, F TM A A1,
        pi X\ fold (FUN X) F {fold T F A1} A'.
    fold (let _ T1 T2 FUN as TM) F A A' :- !, F TM A A1,
        pi X\ fold (FUN X) F {fold T2 F {fold T1 F A1} } A'.
    fold (app L as TM) F A A' :- !, F TM A A1, fold-list L F A1 A'.
    fold (match T1 T2 L as TM) F A A' :- !, F TM A A1,
        fold-list L F {fold T2 F {fold T1 F A1} } A'.
    fold (fix _ _ T FUN as TM) F A A' :- !, F TM A A1,
        pi X\ fold (FUN X) F {fold T F A1} A'.
    fold (primitive _ as TM) F A A' :- !, F TM A A'.
    fold (uvar _ L as TM) F A A' :- !, F TM A A1, fold-list L F A1 A'.
    fold X _ A A :- !, name X. %pi-bound variables c0, c1, etc.

    pred fold-list i:list term, i:term -> A -> A -> prop, i:A, o:A.
    fold-list [] _ A A.
    fold-list [X|L] F A A' :- fold-list L F {fold X F A} A'.
  } %namespace coq
}}.
