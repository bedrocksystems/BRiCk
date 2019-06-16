(* todo(gmm): this file should be pulled out of `Auto`
 *)
Require Import Cpp.Sem.

Local Definition mkWpp {ts : tele} (f : teleF (mpred * (val -> mpred)) ts) : WithPrePost :=
  {| wpp_with := ts
   ; wpp_pre := teleF_map fst f
   ; wpp_post := teleF_map snd f
   |}.

(* todo(gmm): these should be put in an interpretation scope *)
Notation "'\with' x .. y '\pre' pre '\post' [ r ] post" :=
  (@mkWpp (tcons (fun x => .. (tcons (fun y => tdone)) ..))
         (fun x => .. (fun y => (pre, fun (r : val) => post)) ..))
  (at level 10, x closed binder, y closed binder, r ident, no associativity,
   pre at level 200, post at level 200,
   format "'[v' '\with'  '[' x .. y ']' '//' '\pre'     '[hv  '  pre  ']' '//' '\post' [ r ]  '[hv ' post ']' ']'").
Notation "'\with' x .. y '\pre' pre '\post' post" :=
  (@mkWpp (tcons (fun x => .. (tcons (fun y => tdone)) ..))
         (fun x => .. (fun y => (pre, fun (_ : val) => post)) ..))
  (at level 10, x closed binder, y closed binder, no associativity,
   pre at level 200, post at level 200,
   format "'[v' '\with'  '[' x .. y ']' '//' '\pre'  '[hv  '  pre  ']' '//' '\post'  '[hv ' post ']' ']'").

(*
Goal WithPrePost.
refine (
  \with (x : nat)
  \pre Exists y, [| x = 3 |] ** [| x = y |] ** empSP
  \post [r] Exists z : nat, [| r = Vptr nullptr |] ** empSP ** [| x = 0 |] ** [| z = 0 |]).
Show Proof.
Defined.

Goal WithPrePost.
refine (
  \with (x : nat)
  \pre Exists y, [| x = 3 |] ** [| x = y |] -* empSP
  \post Exists z : nat, empSP ** [| z = 0 |] -* empSP).
Show Proof.
Defined.
*)

Notation "'\pre' pre '\post' [ r ] post" :=
  (@mkWpp tdone (pre, fun (r : val) => post))
  (at level 10, r ident, no associativity,
   pre at level 200, post at level 200,
   format "'[v' '\pre'     '[hv  '  pre   ']' '//' '\post' [ r ]  '[hv ' post ']' ']'").

Notation "'\pre' pre '\post' post" :=
  (@mkWpp tdone (pre, fun (_ : val) => post))
  (at level 10, no associativity,
   pre at level 200, post at level 200,
   format "'[v' '\pre' '[hv  '   pre   ']' '//' '\post'  '[hv ' post ']' ']'").

(*
Goal WithPrePost.
refine (
    \pre empSP ** Exists y : nat, [| y = 3 |]
    \post empSP).
Show Proof.
Defined.
Goal WithPrePost.
refine (
    \pre empSP ** Exists y : nat, [| y = 3 |]
    \post [r] [| r = Vptr nullptr |]).
Show Proof.
Defined.
*)
