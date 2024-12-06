(*
 * Copyright (C) BlueRock Security Inc. 2024
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

include TransparentState

let inter : t -> t -> t = fun ts1 ts2 ->
  let tr_var = Names.Id.Pred.inter ts1.tr_var ts2.tr_var in
  let tr_cst = Names.Cpred.inter ts1.tr_cst ts2.tr_cst in
  let tr_prj = Names.PRpred.inter ts1.tr_prj ts2.tr_prj in
  { tr_var; tr_cst ; tr_prj }

let remove_var : t -> Names.Id.t -> t = fun ts x ->
  { ts with tr_var = Names.Id.Pred.remove x ts.tr_var }

let remove_cst : t -> Names.Constant.t -> t = fun ts c ->
  { ts with tr_cst = Names.Cpred.remove c ts.tr_cst }

let remove_prj : t -> Names.Projection.Repr.t -> t = fun ts p ->
  { ts with tr_prj = Names.PRpred.remove p ts.tr_prj }

let add_var : t -> Names.Id.t -> t = fun ts x ->
  { ts with tr_var = Names.Id.Pred.add x ts.tr_var }

let add_cst : t -> Names.Constant.t -> t = fun ts c ->
  { ts with tr_cst = Names.Cpred.add c ts.tr_cst }

let add_prj : t -> Names.Projection.Repr.t -> t = fun ts p ->
  { ts with tr_prj = Names.PRpred.add p ts.tr_prj }

let pp : Format.formatter -> t -> unit = fun ff {tr_var; tr_cst; tr_prj} ->
  ignore tr_prj; (* FIXME *)
  let (b_var, list_var) = Names.Id.Pred.elements tr_var in
  let (b_cst, list_cst) = Names.Cpred.elements tr_cst in
  let complement_of b = if b then " complement of" else "" in
  Format.fprintf ff "tr_var =%s " (complement_of b_var);
  let _ =
    match list_var with
    | [] -> Format.fprintf ff "∅"
    | _  ->
    Format.fprintf ff "{\n";
    let pp_v ff x = Format.fprintf ff "%s" (Names.Id.to_string x) in
    List.iter (Format.fprintf ff "  %a,\n" pp_v) list_var;
    Format.fprintf ff "}"
  in
  Format.fprintf ff "\n";
  Format.fprintf ff "tr_cst =%s " (complement_of b_cst);
  let _ =
    match list_cst with
    | [] -> Format.fprintf ff "∅"
    | _  ->
    Format.fprintf ff "{\n";
    let pp_c ff c = Format.fprintf ff "%s" (Names.Constant.to_string c) in
    List.iter (Format.fprintf ff "  %a,\n" pp_c) list_cst;
    Format.fprintf ff "}"
  in
  Format.fprintf ff "\n"
