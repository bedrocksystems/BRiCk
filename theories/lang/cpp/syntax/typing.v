(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From bedrock.lang.cpp.syntax Require Import names expr types.

Definition type_of (e : Expr) : type :=
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
  | Emember _ _ _ t
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
  | Einitlist _ _ t
  | Eimplicit_init t
  | Enew _ _ _ _ _ t
  | Edelete _ _ _ _ _ t
  | Eandclean _ t
  | Ematerialize_temp _ t => t
  | Ebind_temp _ _ t => t
  | Ebuiltin _ t => t
  | Eatomic _ _ t => t
  | Eva_arg _ t => t
  | Epseudo_destructor _ _ => Tvoid
  | Earrayloop_init _ _ _ _ _ t => t
  | Earrayloop_index _ t => t
  | Eopaque_ref _ t => t
  | Eunsupported _ t => t
  end.

Fixpoint erase_qualifiers (t : type) : type :=
  match t with
  | Tpointer t => Tpointer (erase_qualifiers t)
  | Treference t => Treference (erase_qualifiers t)
  | Trv_reference t => Trv_reference (erase_qualifiers t)
  | Tint _ _
  | Tbool
  | Tvoid
  | Tfloat _
  | Tnamed _ => t
  | Tarray t sz => Tarray (erase_qualifiers t) sz
  | @Tfunction cc t ts => Tfunction (cc:=cc) (erase_qualifiers t) (List.map erase_qualifiers ts)
  | Tmember_pointer cls t => Tmember_pointer cls (erase_qualifiers t)
  | Tqualified _ t => erase_qualifiers t
  | Tnullptr => Tnullptr
  | Tarch sz nm => Tarch sz nm
  end.

Fixpoint drop_qualifiers (t : type) : type :=
  match t with
  | Tqualified _ t => drop_qualifiers t
  | _ => t
  end.
