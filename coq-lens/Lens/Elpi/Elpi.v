(* TODO copyright header. *)
Require Import Lens.Lens.

(* A lens, to see better.

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)
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
Elpi Accumulate File derive_hook.
Elpi Accumulate File lens.
Elpi Accumulate Db derive.lens.db.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.lens.main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.lens.main GR "_" _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.lens <record name> [<output prefix>]".
}}.
Elpi Typecheck.

(* hook into derive *)
#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "lens" (cl\ cl = []) true).
}}.

Elpi Accumulate derive Db derive.lens.db.
Elpi Accumulate derive File lens.
Elpi Accumulate derive lp:{{
  derivation (indt T) _Prefix ff (derive "lens" (derive.lens.main T N) (lens-db T _ _)) :- N is "_".
}}.
