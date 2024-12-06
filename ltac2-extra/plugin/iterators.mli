(*
 * Copyright (C) BlueRock Security Inc. 2022
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
We document these iterators in BedRock's [Constr.Unsafe] Coq module.
Briefly, they visit a term's immediate subterms from left to right.
While they are not recursive, they can be useful in defining recursive
iterators.

These iterators take functions in the monad [ProofView.tactic]. Like
similar iterators in Coq, they promote sharing using OCaml's [==].
*)

module ListTac : sig
  val smart_map :
    ('a -> 'a Proofview.tactic) -> 'a list -> 'a list Proofview.tactic
end

module ArrayTac : sig
  val smart_map :
    ('a -> 'a Proofview.tactic) -> 'a array -> 'a array Proofview.tactic
  (**
  Analogous to [CArray.Smart.map]: Returns the original array if
  nothing changed.
  *)
end

module ConstrTac : sig
  open Constr

  val map_invert : ('constr -> 'constr Proofview.tactic) ->
    'constr pcase_invert -> 'constr pcase_invert Proofview.tactic

  val map_return_predicate : ('types -> 'types Proofview.tactic) ->
    ('types, 'r) pcase_return -> ('types, 'r) pcase_return Proofview.tactic
  val map_return_predicate_with_binders :
    ('c -> 'c) -> ('c -> 'types -> 'types Proofview.tactic) ->
    'c -> ('types, 'r) pcase_return -> ('types, 'r) pcase_return Proofview.tactic

  val map_branches : ('constr -> 'constr Proofview.tactic) ->
    ('constr, 'r) pcase_branch array -> ('constr, 'r) pcase_branch array Proofview.tactic
  val map_branches_with_binders :
    ('c -> 'c) -> ('c -> 'constr -> 'constr Proofview.tactic) ->
    'c -> ('constr, 'r) pcase_branch array ->
    ('constr, 'r) pcase_branch array Proofview.tactic

  val map_rec_declaration : ('a -> 'a Proofview.tactic) ->
    ('a,'a,'r) prec_declaration -> ('a,'a,'r) prec_declaration Proofview.tactic
  val map_rec_declaration_with_binders :
    ('c -> 'c) -> ('c -> 'a -> 'a Proofview.tactic) ->
    'c -> ('a,'a,'r) prec_declaration -> ('a,'a,'r) prec_declaration Proofview.tactic
  val map_rec_declaration_with_full_binders :
    (('a,'a,'r) Context.Rel.Declaration.pt -> 'c -> 'c) ->
    ('c -> 'a -> 'a Proofview.tactic) ->
    'c -> ('a,'a,'r) prec_declaration -> ('a,'a,'r) prec_declaration Proofview.tactic

  val map : (t -> t Proofview.tactic) -> t -> t Proofview.tactic
  val map_with_binders :
    ('c -> 'c) -> ('c -> t -> t Proofview.tactic) ->
    'c -> t -> t Proofview.tactic
  val map_with_full_binders : Environ.env ->
    (rel_declaration -> 'c -> 'c) -> ('c -> t -> t Proofview.tactic) ->
    'c -> t -> t Proofview.tactic
end

module EConstrTac : sig
  open EConstr

  (**
  Orthogonal to Ltac2: Abandon the OCaml/Coq convention whereby a
  fold's arguments reflect its direction.
  *)
  val fold : Evd.evar_map -> (t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_with_binders : Evd.evar_map ->
    ('c -> 'c) -> ('c -> t -> 'a -> 'a) -> 'c -> t -> 'a -> 'a
  val fold_with_full_binders : Environ.env -> Evd.evar_map ->
    (rel_declaration -> 'c -> 'c) -> ('c -> t -> 'a -> 'a) ->
    'c -> t -> 'a -> 'a

  val map : Evd.evar_map -> (t -> t Proofview.tactic) ->
    t -> t Proofview.tactic
  val map_with_binders : Evd.evar_map ->
    ('c -> 'c) -> ('c -> t -> t Proofview.tactic) ->
    'c -> t -> t Proofview.tactic
  val map_with_full_binders : Environ.env -> Evd.evar_map ->
    (rel_declaration -> 'c -> 'c) -> ('c -> t -> t Proofview.tactic) ->
    'c -> t -> t Proofview.tactic
end
