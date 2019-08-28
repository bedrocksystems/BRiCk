(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Classes.DecidableClass.
Require Import Cpp.Syntax.Ast.

Fixpoint type_of (e : Expr) : type :=
  match e with
  | Econst_ref _ t
  | Evar _ t
  | Echar _ t
  | Estring _ t
  | Eint _ t => t
  | Ebool _ => Tbool
  | Eunop _ _ t
  | Ebinop _ _ _ t
  | Ederef _ t
  | Eaddrof _ t
  | Eassign _ _ t
  | Eassign_op _ _ _ t
  | Epreinc _ t
  | Epostinc _ t
  | Epredec _ t
  | Epostdec _ t
  | Eseqand _ _ t
  | Eseqor _ _ t
  | Ecomma _ _ _ t
  | Ecall _ _ t
  | Ecast _ _ t
  | Emember _ _ t
  | Emember_call _ _ _ _ t
  | Esubscript _ _ t
  | Esize_of _ t
  | Ealign_of _ t
  | Econstructor _ _ t
  | Eimplicit _ t
  | Eif _ _ _ t
  | Ethis t => t
  | Enull => Tpointer Tvoid
  (* todo(gmm): c++ seems to have a special nullptr type *)
  | Einitlist _ t => t
  | Enew _ _ _ t
  | Edelete _ _ _ t
  | Eandclean _ t
  | Ematerialize_temp _ t => t
  | Eatomic _ _ t => t
  | Eva_arg _ t => t
  | Eunsupported _ t => t
  end.

Fixpoint erase_qualifiers (t : type) : type :=
  match t with
  | Tpointer t => Tpointer (erase_qualifiers t)
  | Treference t => Treference (erase_qualifiers t)
  | Trv_reference t => Trv_reference (erase_qualifiers t)
  | Tint _ _
  | Tchar _ _
  | Tbool
  | Tvoid
  | Tref _ => t
  | Tarray t sz => Tarray (erase_qualifiers t) sz
  | Tfunction t ts => Tfunction (erase_qualifiers t) (List.map erase_qualifiers ts)
  | Tqualified _ t => erase_qualifiers t
  end.

Fixpoint drop_qualifiers (t : type) : type :=
  match t with
  | Tqualified _ t => drop_qualifiers t
  | _ => t
  end.

Section decidable.

  Global Instance Decidable_type (a b : type) : Decidable (a = b).
  refine
    {| Decidable_witness := if type_eq_dec a b then true else false
     ; Decidable_spec := _ |}.
  destruct (type_eq_dec a b); split; congruence.
  Defined.

End decidable.
