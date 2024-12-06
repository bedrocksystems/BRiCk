(*
 * Copyright (C) BlueRock Security Inc. 2022
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
open Ltac2_plugin
open Tac2ffi
open Tac2val
open Tac2externals

let define s =
  define Tac2expr.{ mltac_plugin = "ltac2_extensions"; mltac_tactic = s }

module StateMap = Map.Make (Names.KerName)
type elem = Tac2val.valexpr StateMap.t

open Proofview.Notations

let field : elem Proofview_monad.StateStore.field = Proofview_monad.StateStore.field "ltac2_generic_goal_state"

(* TODO: populate field with empty map when it doesn't exist yet? *)
let get_map () : elem option Proofview.tactic = Proofview.Goal.enter_one (fun gl ->
    let state = Proofview.Goal.state gl in
    Proofview.tclUNIT (Proofview_monad.StateStore.get state field)
  )

let set_map (update : elem -> elem) : unit Proofview.tactic = Proofview.Goal.enter_one (fun gl ->
    let state = Proofview.Goal.state gl in
    get_map () >>= fun map ->
    let state = match map with
      | None ->
        Proofview_monad.StateStore.set state field (update (StateMap.empty))
      | Some map ->
        Proofview_monad.StateStore.set state field (update map)
    in
    let gl = Proofview.goal_with_state (Proofview.Goal.goal gl) state in
    Proofview.Unsafe.tclSETGOALS [gl]
  )

let find (kn : Names.KerName.t) : valexpr option Proofview.tactic =
  get_map () >>= fun map ->
  match map with
  | None -> Proofview.tclUNIT None
  | Some map -> Proofview.tclUNIT (StateMap.find_opt kn map)

let set (kn : Names.KerName.t) (v : valexpr) : unit Proofview.tactic =
  set_map (StateMap.add kn v)

let _ =
  define "get_goal_state" (valexpr @-> tac (option valexpr)) @@ fun v ->
  let (kn, args) = Tac2ffi.to_open v in
  assert (Array.length args = 0);
  find kn

let _ =
  define "set_goal_state" (valexpr @-> valexpr @-> tac unit) @@ fun k v ->
  let (kn, args) = Tac2ffi.to_open k in
  assert (Array.length args = 0);
  set kn v

let _ =
  define "new_goals_w_state" (valexpr @-> tac unit) @@ fun evs ->
  let evs = Tac2ffi.to_list (fun ev -> Tac2ffi.to_evar ev) evs in
  Proofview.Goal.enter_one @@ fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  if List.for_all (Evd.mem sigma) evs then
    let state = Proofview.Goal.state gl in
    let new_gls = List.map (fun ev -> Proofview.goal_with_state ev state) evs in
    Proofview.Unsafe.tclNEWGOALS new_gls <*> Proofview.tclUNIT ()
  else
    assert false
