(*
 * This file is part of the rocq-lens-elpi package.
 * Copyright (C) 2021-2022 Enrico Tassi
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
 * for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USAQ
 *)

Require Import Lens.Lens.

From elpi.apps.derive.elpi Extra Dependency "lens.elpi" as lens.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.

Require Import elpi.elpi.
Require Import elpi.apps.derive.derive.

Import LensNotations.
#[local] Open Scope lens_scope.

Register Build_Lens as elpi.derive.lens.make.
Register set as elpi.derive.lens.set.
Register view as elpi.derive.lens.view.

(* Links the record, a field name and the lens focusing on that field *)
Elpi Db derive.lens.db lp:{{
  pred lens-db o:inductive, o:string, o:constant.
}}.

(* standalone command *)
Elpi Command derive.lens.
Elpi Accumulate Db Header derive.lens.db.
Elpi Accumulate File derive_hook.
Elpi Accumulate File lens.
Elpi Accumulate Db derive.lens.db.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.lens.main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.lens.main GR "_" _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.lens <record name> [<output prefix>]".
}}.

(* hook into derive *)
#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "lens" (cl\ cl = []) true).
}}.

Elpi Accumulate derive Db derive.lens.db.
Elpi Accumulate derive File lens.
Elpi Accumulate derive lp:{{
  derivation (indt T) _Prefix ff
    (derive "lens" (derive.lens.main T N) (lens-db T _ _)) :- N is "_".
}}.
