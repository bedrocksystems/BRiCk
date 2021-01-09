(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.Lists.List.

Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred call wp.
Require Import bedrock.lang.cpp.heap_notations.

Module Type Init.

  Section with_resolve.
    Context `{Σ : cpp_logic thread_info} {σ:genv}.
    Variables (M : coPset) (ti : thread_info) (ρ : region).

    Local Notation wp := (wp (resolve:=σ) M ti ρ).
    Local Notation wpi := (wpi (resolve:=σ) M ti ρ).
    (*Local Notation wpe := (wpe (resolve:=σ) M ti ρ).*)
    Local Notation wp_lval := (wp_lval (resolve:=σ) M ti ρ).
    Local Notation wp_rval := (wp_rval (resolve:=σ) M ti ρ).
    Local Notation wp_prval := (wp_prval (resolve:=σ) M ti ρ).
    Local Notation wp_xval := (wp_xval (resolve:=σ) M ti ρ).
    Local Notation wp_init := (wp_init (resolve:=σ) M ti ρ).
    Local Notation wp_args := (wp_args (σ:=σ) M ti ρ).
    Local Notation fspec := (@fspec _ Σ σ.(genv_tu).(globals)).

    Local Notation primR := (primR (resolve:=σ)) (only parsing).
    Local Notation tblockR := (tblockR (σ:=σ)) (only parsing).
    Local Notation anyR := (anyR (resolve:=σ)) (only parsing).
    Local Notation offset_for := (offset_for σ) (only parsing).

    (* [wp_initialize] provides "constructor" semantics for types.
     * For aggregates, simply delegates to [wp_init], but for primitives,
     * the semantics is to evaluate the primitive and initialize the location
     * with the value.
     *
     * NOTE this is written as a recursive function rather than by using [decompose_type] because
     * we want simplification to reduce it.
     *)
    Fixpoint wp_initialize (ty : type) (addr : ptr) (init : Expr) (k : FreeTemps -> mpred) : mpred :=
      match ty with
      | Tvoid => False
      | Tpointer _ as ty
      | Tmember_pointer _ _ as ty
      | Tbool as ty
      | Tint _ _ as ty =>
        wp_prval init (fun v free =>
                         addr |-> anyR ty 1 (* TODO backwards compat [tblockR ty 1] *) **
                         (   addr |-> primR ty 1 v
                          -* k free))

        (* non-primitives are handled via prvalue-initialization semantics *)
      | Tarray _ _
      | Tnamed _ => wp_init ty addr (not_mine init) k

      | Treference t => False (* reference fields are not supported *)
      | Trv_reference t => False (* reference fields are not supported *)
      | Tfunction _ _ => False (* functions not supported *)

      | Tqualified _ ty => wp_initialize ty addr init k
      | Tnullptr => False (* nullptr fields are not supported *)
      | Tarch _ _ => False (* vendor-specific types are not supported *)
      | Tfloat _ => False (* floating point numbers are not supported *)
      end.

    Axiom wpi_initialize : forall (thisp : ptr) i cls Q,
        let p' := thisp ., offset_for cls i.(init_path) in
          wp_initialize (erase_qualifiers i.(init_type)) p' i.(init_init) Q
      |-- wpi cls thisp i Q.

    Fixpoint wpis (cls : globname) (this : ptr)
             (inits : list Initializer)
             (Q : mpred -> mpred) : mpred :=
      match inits with
      | nil => Q empSP
      | i :: is' => wpi cls this i (fun f => f ** wpis cls this is' Q)
      end.

    Axiom wp_init_constructor : forall cls addr cnd es Q ty,
      wp_args es (fun ls free =>
           match σ.(genv_tu) !! cnd with
           | Some cv =>
             |> fspec (type_of_value cv) ti (Vptr $ _global cnd) (Vptr addr :: ls) (fun _ => Q free)
           | _ => False
           end)
      |-- wp_init (Tnamed cls) addr (Econstructor cnd es ty) Q.

    Definition build_array (es : list Expr) (fill : option Expr) (sz : nat)
    : option (list (Z * Expr)) :=
      let len := List.length es in
      let idxs := List.map Z.of_nat (seq 0 sz) in
      match Nat.compare sz len with
      (* <http://eel.is/c++draft/dcl.init.general#16.5>

         Programs which contain more initializer expressions than
         array-members are ill-formed.
       *)
      | Lt => None
      | Eq => Some (List.combine idxs es)
      | Gt => match fill with
             | None => None
             | Some f =>
               Some (List.combine idxs (List.app es (map (fun _ => f) (seq 0 (sz - len)))))
             end
      end.

    Fixpoint wp_array_init (ety : type) (base : ptr) (es : list (Z * Expr)) (Q : mpred -> mpred) : mpred :=
      match es with
      | nil => Q empSP
      | (i,e) :: es =>
          (* NOTE: We nest the recursive calls to `wp_array_init` within
               the continuation of the `wp_initialize` statement to
               reflect the fact that the C++ Standard introduces
               sequence-points between all of the elements of an
               initializer list (c.f. http://eel.is/c++draft/dcl.init.list#4)
           *)
          wp_initialize ety (base .[ ety ! i ]) e (fun free => free ** wp_array_init ety base es Q)
      end.

    Axiom wp_init_initlist_array :forall ls fill ety sz addr Q,
      match build_array ls fill (N.to_nat sz) with
      | None => False
      | Some array_list =>
        (* _at (_eqv addr) (anyR (erase_qualifiers (Tarray ety sz)) 1) ** *)
        wp_array_init ety addr array_list (fun free => Q free)
      end
      |-- wp_init (Tarray ety sz) addr (Einitlist ls fill (Tarray ety sz)) Q.

    Axiom wp_prval_initlist_default : forall t Q,
          match get_default t with
          | None => False
          | Some v => Q v emp
          end
      |-- wp_prval (Einitlist nil None t) Q.

    Axiom wp_prval_initlist_prim : forall t e Q,
          (if prim_initializable t
           then wp_prval e Q
           else False)
      |-- wp_prval (Einitlist (e :: nil) None t) Q.

    Axiom wp_init_cast_noop : forall e ty addr ty' Q,
        wp_init ty addr e Q
        |-- wp_init ty addr (Ecast Cnoop (Prvalue, e) ty') Q.

    Axiom wp_init_clean : forall e ty ty' addr Q,
        wp_init ty' addr e Q
        |-- wp_init ty' addr (Eandclean e ty) Q.
    Axiom wp_init_const : forall ty addr e Q,
        wp_init ty addr e Q
        |-- wp_init (Qconst ty) addr e Q.
    Axiom wp_init_mut : forall ty addr e Q,
        wp_init ty addr e Q
        |-- wp_init (Qmut ty) addr e Q.

  End with_resolve.

End Init.

Declare Module IN : Init.

Export IN.
