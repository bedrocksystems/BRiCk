(*
 * Copyright (C) BlueRock Security Inc. 2023-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Pattern

type t = constr_pattern

let map_w_binders : ('a -> int -> 'a) -> ('a -> t -> t) -> 'a -> t -> 'b =
  fun g f n p ->
  match p with
  | PRef(_)
  | PVar(_)
  | PEvar(_)
  | PRel(_)
  | PSort(_)
  | PMeta(_)
  | PInt(_)
  | PString(_)
  | PFloat(_) -> p
  | PApp(p, ps) ->
      let p = f n p in
      let ps = Array.map (f n) ps in
      PApp(p, ps)
  | PSoApp(v, ps) ->
      let ps = List.map (f n) ps in
      PSoApp(v, ps)
  | PProj(j,p) ->
      PProj(j, f n p)
  | PLambda(x, p1, p2) ->
      let p1 = f n p1 in
      let p2 = f (g n 1) p2 in
      PLambda(x, p1, p2)
  | PProd(x, p1, p2) ->
      let p1 = f n p1 in
      let p2 = f (g n 1) p2 in
      PProd(x, p1, p2)
  | PLetIn(x, p1, po, p2) ->
      let p1 = f n p1 in
      let po = Option.map (f n) po in
      let p2 = f (g n 1) p2 in
      PLetIn(x, p1, po, p2)
  | PIf(pi, pt, pe) ->
      let pi = f n pi in
      let pt = f n pt in
      let pe = f n pe in
      PIf(pi, pt, pe)
  | PCase(cip, o, p, cases) ->
      let o =
        Option.map (fun (ns, p) ->
          (ns, f (g n (Array.length ns)) p)
        ) o
      in
      let p = f n p in
      let cases =
        let f (i, ns, p) =
          (i, ns, f (g n (Array.length ns)) p)
        in
        List.map f cases
      in
      PCase(cip, o, p, cases)
  | PFix(r, (ns, ps1, ps2)) ->
      let ps1 = Array.map (f n) ps1 in
      let ps2 = Array.map (f (g n (Array.length ns))) ps2 in
      PFix(r, (ns, ps1, ps2))
  | PCoFix(i, (ns, ps1, ps2)) ->
      let ps1 = Array.map (f n) ps1 in
      let ps2 = Array.map (f (g n (Array.length ns))) ps2 in
      PCoFix(i, (ns, ps1, ps2))
  | PArray(ps, p1, p2) ->
      let ps = Array.map (f n) ps in
      let p1 = f n p1 in
      let p2 = f n p2 in
      PArray(ps, p1, p2)
  | PUninstantiated(_) -> .

let fold_with_binders : type a b. (a -> int -> a) -> (a -> b -> t -> b) -> a -> b -> t -> b =
  fun g f n acc p ->
  match p with
  | PRef(_)
  | PVar(_)
  | PEvar(_)
  | PRel(_)
  | PSort(_)
  | PMeta(_)
  | PInt(_)
  | PFloat(_) 
  | PString(_) -> acc
  | PApp(p, ps) ->
      f n (Array.fold_left (f n) acc ps) p
  | PSoApp(_, ps) ->
      List.fold_left (f n) acc ps
  | PProj(_,p) ->
      f n acc p
  | PLambda(_, p1, p2) ->
      f n (f (g n 1) acc p2) p1
  | PProd(_, p1, p2) ->
      f n (f (g n 1) acc p2) p1
  | PLetIn(_, p1, po, p2) ->
    let acc = f (g n 1) acc p2 in
    let acc = match po with
      | Some p -> f n acc p
      | None -> acc
    in
    f n acc p1
  | PIf(pi, pt, pe) ->
      let acc = f n acc pi in
      let acc = f n acc pt in
      let acc = f n acc pe in
      acc
  | PCase(_, o, p, cases) ->
      let acc =
        match o with
        | Some (ns, p) ->
          f (g n (Array.length ns)) acc p
        | None -> acc
      in
      let acc = f n acc p in
      let acc =
        let f acc (_, ns, p) =
          f (g n (Array.length ns)) acc p
        in
        List.fold_left f acc cases
      in
      acc
  | PFix(_, (ns, ps1, ps2)) ->
      let acc = Array.fold_left (f n) acc ps1 in
      let acc = Array.fold_left (f (g n (Array.length ns))) acc ps2 in
      acc
  | PCoFix(_, (ns, ps1, ps2)) ->
      let acc = Array.fold_left (f n) acc ps1 in
      let acc = Array.fold_left (f (g n (Array.length ns))) acc ps2 in
      acc
  | PArray(ps, p1, p2) ->
      let acc = Array.fold_left (f n) acc ps in
      let acc = f n acc p1 in
      let acc = f n acc p2 in
      acc
  | PUninstantiated(_) -> .

let rec subst : offset:int -> t -> t array -> t = fun ~offset p args ->
  let fun_subst offset p = subst ~offset p args in
  match p with
  | PEvar(_) -> assert false
  | PRel(i) ->
      let ind = i - offset - 1 in
      if 0 <= ind && ind < Array.length args then args.(ind) else p
  | _ ->
      map_w_binders (fun offset binders -> offset + binders) fun_subst offset p
