(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.lang.cpp.syntax Require Import names expr types.

(** [type_of e] returns the type of the expression [e]. *)
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
  | Enull => Tnullptr
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

(** [erase_qualifiers t] erases *all* qualifiers that occur everywhere in the type.

    NOTE we currently use this because we do not track [const]ness in the logic, this
    is somewhat reasonable because we often opt to express this in separation logic.
    And the type system also enforces some of the other criteria.
 *)
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

(** [drop_qualifiers t] drops all the *leading* quallifiers of the type [t].
    e.g. [drop_qualifiers (Qconst (Qmut t)) = t]
 *)
Fixpoint drop_qualifiers (t : type) : type :=
  match t with
  | Tqualified _ t => drop_qualifiers t
  | _ => t
  end.

(** [unptr t] returns the type of the object that a value of type [t] points to
    or [None] if [t] is not a pointer type.
 *)
Definition unptr (t : type) : option type :=
  match drop_qualifiers t with
  | Tptr p => Some (drop_qualifiers p)
  | _ => None
  end.

(** [class_type t] returns the name of the class that this type refers to
 *)
Definition class_type (t : type) : option globname :=
  match drop_qualifiers t with
  | Tnamed gn => Some gn
(*  | Tpointer t
  | Treference t
  | Trv_reference t => class_type t
*)
  | _ => None
  end.

