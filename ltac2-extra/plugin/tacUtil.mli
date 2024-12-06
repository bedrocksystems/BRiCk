(*
 * Copyright (C) BlueRock Security Inc. 2022
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

open Ltac2_plugin

val with_evarmap : (Evd.evar_map -> 'a Proofview.tactic) -> 'a Proofview.tactic
val evar_map : Evd.evar_map Proofview.tactic
val env : Environ.env Proofview.tactic

module Notations : sig
  val return : 'a -> 'a Proofview.tactic
  val (>>=) : 'a Proofview.tactic -> ('a -> 'b Proofview.tactic) -> 'b Proofview.tactic
  val (<*>) : unit Proofview.tactic -> 'a Proofview.tactic -> 'a Proofview.tactic
end

module Value : sig
  include module type of Tac2ffi
  include module type of Tac2val

  val thaw1_poly : valexpr -> valexpr Proofview.tactic -> valexpr Proofview.tactic

  val thaw1 : 'a repr -> 'b repr -> valexpr -> 'a -> 'b Proofview.tactic
  val thaw2 : 'a repr -> 'b repr -> 'c repr -> valexpr -> 'a -> 'b -> 'c Proofview.tactic
  val thaw3 : 'a repr -> 'b repr -> 'c repr -> 'd repr -> valexpr ->
    'a -> 'b -> 'c -> 'd Proofview.tactic

  type binder = Names.Name.t EConstr.binder_annot * EConstr.types

  val of_binder : binder -> valexpr
  val to_binder : valexpr -> binder
  val binder : binder repr

  val of_rel_declaration : EConstr.rel_declaration -> valexpr
  val to_rel_declaration : valexpr -> EConstr.rel_declaration
  val rel_declaration : EConstr.rel_declaration repr

  (** Goal-insensitive [Constr.t] instead of [EConstr.t] *)
  module RawConstr : sig
    val to_constr : Evd.evar_map -> valexpr -> Constr.t
    val of_constr : Constr.t -> valexpr
  end

end

(** [timed tac] is a tactic that runs as [tac], but the running time of [tac]
    is recorded, and reported together with the result (in seconds). *)
val timed : 'a Proofview.tactic -> (float * 'a) Proofview.tactic
