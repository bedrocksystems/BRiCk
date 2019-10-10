Require Import Coq.Classes.DecidableClass.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Bool.Bool.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Map.FMapAList.

From Coq.Strings Require Import
     Ascii String.

Require Import Cpp.Util.
From Cpp.Syntax Require Import Names Expr Stmt Types.

Set Primitive Projections.

Record LayoutInfo : Set :=
{ li_offset : Z }.

Record Ctor : Set :=
{ c_class  : globname
; c_params : list (ident * type)
; c_body   : option (OrDefault (list Initializer * Stmt))
}.

Record Dtor : Set :=
{ d_class  : globname
; d_body   : option (OrDefault (Stmt * list (FieldOrBase * obj_name)))
; d_virtual : bool
}.

Record Func : Set :=
{ f_return : type
; f_params : list (ident * type)
; f_body   : option Stmt
}.

Record Method : Set :=
{ m_return  : type
; m_class   : globname
; m_this_qual : type_qualifiers
; m_params  : list (ident * type)
; m_body    : option Stmt
; m_virtual : bool
}.

Record Union : Set :=
{ u_fields : list (ident * type * LayoutInfo)
  (* ^ fields with layout information *)
; u_size : N
  (* ^ size of the union (including padding) *)
}.

Variant LayoutType : Set := POD | Standard | Unspecified.

Record Struct : Set :=
{ s_bases : list (globname * LayoutInfo)
  (* ^ base classes *)
; s_fields : list (ident * type * LayoutInfo)
  (* ^ fields with layout information *)
; s_layout : LayoutType
  (* ^ the type of layout semantics *)
; s_size : N
  (* ^ size of the structure (including padding) *)
}.

Variant Ctor_type : Set := Ct_Complete | Ct_Base | Ct_Comdat.

(* Definition ctor_name (type : Ctor_type) (cls : globname) : obj_name := *)
(*   match cls with *)
(*   | String _ (String _ s) => *)
(*     "_ZN" ++ s ++ "C" ++ (match type with *)
(*                           | Ct_Complete => "1" *)
(*                           | Ct_Base => "2" *)
(*                           | Ct_Comdat => "5" *)
(*                           end) ++ "Ev" *)
(*   | _ => "" *)
(*   end%string. *)

Variant Dtor_type : Set := Dt_Deleting | Dt_Complete | Dt_Base | Dt_Comdat.

Definition dtor_name (type : Dtor_type) (cls : globname) : obj_name :=
  match cls with
  | String _ (String _ s) =>
    "_ZN" ++ s ++ "D" ++ ("0" (*match type with
                          | Dt_Deleting => "0"
                          | Dt_Complete => "1"
                          | Dt_Base => "2"
                          | Dt_Comdat => "5"
                          end *)) ++ "Ev"
  | _ => ""
  end%string.

Global Instance Decidable_eq_N (a b : N) : Decidable (a = b) :=
  dec_Decidable (BinNat.N.eq_dec a b).

Global Instance Decidable_eq_LayoutType (a b : LayoutType) : Decidable (a = b).
Proof.
  refine {| Decidable_witness :=
              match a , b with
              | POD , POD => true
              | Standard , Standard => true
              | Unspecified , Unspecified => true
              | _ , _ => false
              end |}.
  destruct a; destruct b; try solve [ split; congruence ].
Defined.


Global Instance Decidable_eq_LayoutInfo (a b : LayoutInfo) : Decidable (a = b).
Proof.
  refine {| Decidable_witness :=
              decide (a.(li_offset) = b.(li_offset)) |}.
  destruct a; destruct b; try solve [ split; congruence ].
  rewrite decide_ok. simpl. split; intros; subst; eauto.
  inversion H. reflexivity.
Defined.


Section Decidable_or_default.
  Context {T : Set} (dec : resolve (forall a b : T, Decidable (a = b))).
  Global Instance Decidable_eq_OrDefault (a b : OrDefault T) : Decidable (a = b).
  Proof.
    refine {| Decidable_witness :=
                match a , b with
                | Defaulted , Defaulted => true
                | UserDefined a , UserDefined b => decide (a = b)
                | _ , _ => false
                end |}.
    destruct a; destruct b; try solve [ split; congruence ].
    rewrite decide_ok. split; congruence.
    Unshelve. eapply dec.
  Defined.
End Decidable_or_default.

Global Instance Decidable_eq_Func (a b : Func) : Decidable (a = b).
Proof.
  refine
    {| Decidable_witness :=
         decide (a.(f_return) = b.(f_return)) &&
                decide (a.(f_params) = b.(f_params)) &&
                decide (a.(f_body) = b.(f_body))
    |}.
  repeat rewrite Bool.andb_true_iff.
  repeat rewrite Decidable_spec.
  destruct a; destruct b; simpl; firstorder; try congruence.
Defined.

Global Instance Decidable_eq_Method (a b : Method) : Decidable (a = b).
Proof.
  refine
    {| Decidable_witness :=
         decide (a.(m_return) = b.(m_return)) &&
                decide (a.(m_class) = b.(m_class)) &&
                decide (a.(m_this_qual) = b.(m_this_qual)) &&
                decide (a.(m_params) = b.(m_params)) &&
                decide (a.(m_body) = b.(m_body)) &&
                decide (a.(m_virtual) = b.(m_virtual))
    |}.
  repeat rewrite Bool.andb_true_iff.
  repeat rewrite Decidable_spec.
  destruct a; destruct b; simpl; firstorder; try congruence.
Defined.

Global Instance Decidable_eq_Initializer (a b : Initializer) : Decidable (a = b).
refine
  {| Decidable_witness :=
       decide (a.(init_path) = b.(init_path)) &&
       decide (a.(init_type) = b.(init_type)) &&
       decide (a.(init_init) = b.(init_init)) |}.
repeat rewrite Bool.andb_true_iff.
repeat rewrite Decidable_spec.
destruct a; destruct b; simpl; firstorder; try congruence.
Defined.

Global Instance Decidable_eq_Ctor (a b : Ctor) : Decidable (a = b).
refine
  {| Decidable_witness :=
       decide (a.(c_class) = b.(c_class)) &&
              decide (a.(c_params) = b.(c_params)) &&
              decide (a.(c_body) = b.(c_body))
  |}.
repeat rewrite Bool.andb_true_iff.
repeat rewrite Decidable_spec.
destruct a; destruct b; simpl; firstorder; try congruence.
Defined.

Global Instance Decidable_eq_Dtor (a b : Dtor) : Decidable (a = b).
Proof.
  refine
    {| Decidable_witness :=
         decide (a.(d_class) = b.(d_class)) &&
         decide (a.(d_body) = b.(d_body)) &&
         decide (a.(d_virtual) = b.(d_virtual))
    |}.
  repeat rewrite Bool.andb_true_iff.
  repeat rewrite Decidable_spec.
  destruct a; destruct b; simpl; firstorder; try congruence.
Defined.


Global Instance Decidable_eq_Union (a b : Union) : Decidable (a = b).
Proof.
  refine
    {| Decidable_witness := decide (a.(u_fields) = b.(u_fields)) && decide (a.(u_size) = b.(u_size))
    |}.
  rewrite Bool.andb_true_iff.
  do 2 rewrite decide_ok.
  destruct a; destruct b. simpl.
  split.
  { destruct 1. f_equal; auto. }
  { inversion 1; auto. }
Defined.

Global Instance Decidable_eq_struct (a b : Struct) : Decidable (a = b).
Proof.
  refine
    {| Decidable_witness :=
         decide (a.(s_fields) = b.(s_fields)) &&
         decide (a.(s_bases) = b.(s_bases)) &&
         decide (a.(s_layout) = b.(s_layout)) &&
         decide (a.(s_size) = b.(s_size))
    |}.
  repeat rewrite Bool.andb_true_iff.
  do 4 rewrite decide_ok.
  destruct a; destruct b; simpl; firstorder; try congruence.
Defined.



(* these can be externed *)
Variant ObjValue : Set :=
| Ovar         (_ : type) (_ : option Expr)
| Ofunction    (_ : Func)
| Omethod      (_ : Method)
| Oconstructor (_ : Ctor)
| Odestructor  (_ : Dtor)
.

Definition ObjValue_eq_dec : forall a b : ObjValue, {a = b} + {a <> b}.
Proof.
  generalize Expr_eq_dec.
  generalize type_eq_dec.
  decide equality.
  eapply Decidable_dec; eauto with typeclass_instances.
  eapply Decidable_dec; eauto with typeclass_instances.
  eapply Decidable_dec; eauto with typeclass_instances.
  eapply Decidable_dec; eauto with typeclass_instances.
  eapply Decidable_dec; eauto with typeclass_instances.
Defined.

Global Instance Decidable_eq_ObjValue (a b : ObjValue) : Decidable (a = b) :=
  dec_Decidable (ObjValue_eq_dec a b).


Import MonadNotation.


Definition require (o : bool) : option unit :=
  if o then Some tt else None.

Variant Direction : Set := GT | LT | Either.

Definition option_merge {T} (f : Direction -> T -> T -> option T) (d : Direction) (a b : option T) : option T :=
  match a , b with
  | None , _ => match d with
               | LT | Either => b
               | _ => None
               end
  | _ , None => match d with
               | GT | Either => a
               | _ => None
               end
  | Some a , Some b => f d a b
  end.

Definition ObjValue_merge (d : Direction) (a b : ObjValue) : option ObjValue :=
  match a , b with
  | Ovar t oe , Ovar t' oe' =>
    require (decide (t = t')) ;;
    match oe , oe' with
    | None , None => Some a
    | None , _ =>
      match d with
      | LT | Either => Some b
      | _ => None
      end
    | _ , None =>
      match d with
      | GT | Either => Some a
      | _ => None
      end
    | Some _ , Some _ => None
    end
  | Ofunction f , Ofunction f' =>
    require (decide (f.(f_return) = f'.(f_return))) ;;
    require (decide (List.map snd f.(f_params) = List.map snd f'.(f_params))) ;;
    match f.(f_body) , f'.(f_body) with
    | None , None => Some a
    | Some b , Some b' =>
      require (decide (f.(f_params) = f'.(f_params))) ;;
      require (decide (b = b')) ;;
      Some a
    | None , _ =>
      match d with
      | LT | Either => Some b
      | _ => None
      end
    | _ , None =>
      match d with
      | GT | Either => Some a
      | _ => None
      end
    end
  | Omethod m , Omethod m' =>
    require (decide (m.(m_return) = m'.(m_return))) ;;
    require (decide (m.(m_class) = m'.(m_class))) ;;
    require (decide (m.(m_this_qual) = m'.(m_this_qual))) ;;
    require (decide (List.map snd m.(m_params) = List.map snd m'.(m_params))) ;;
    match m.(m_body) , m'.(m_body) with
    | None , None => Some a
    | Some b , Some b' =>
      require (decide (m.(m_params) = m'.(m_params))) ;;
      require (decide (b = b')) ;;
      Some a
    | None , _ =>
      match d with
      | LT | Either => Some b
      | _ => None
      end
    | _ , None =>
      match d with
      | GT | Either => Some a
      | _ => None
      end
    end
  | Oconstructor c , Oconstructor c' =>
    require (decide (c.(c_class) = c'.(c_class))) ;;
    require (decide (List.map snd c.(c_params) = List.map snd c'.(c_params))) ;;
    match c.(c_body) , c'.(c_body) with
    | None , None => Some a
    | None , _ =>
      match d with
      | LT | Either => Some b
      | _ => None
      end
    | _ , None =>
      match d with
      | GT | Either => Some a
      | _ => None
      end
    | Some x , Some y =>
      require (decide (c.(c_params) = c'.(c_params))) ;;
      require (decide (x = y)) ;; Some a
    end
  | Odestructor dd , Odestructor dd' =>
    require (decide (dd.(d_class) = dd'.(d_class))) ;;
    match dd.(d_body) , dd'.(d_body) with
    | None , None => Some a
    | None , _ =>
      match d with
      | LT | Either => Some b
      | _ => None
      end
    | _ , None =>
      match d with
      | GT | Either => Some a
      | _ => None
      end
    | Some x , Some y =>
      require (decide (x = y)) ;; Some a
    end
  | _ , _ => None
  end%monad.

Variant GlobDecl : Set :=
| Gtype
| Gunion    (_ : Union)
| Gstruct   (_ : Struct)
| Genum     (_ : type)
| Gconstant (_ : type) (_ : Expr)
| Gtypedef  (_ : type)
| Gtypedec  (* this is a type declaration, but not a definition *)
.

Definition GlobDecl_eq_dec : forall a b : GlobDecl, {a = b} + {a <> b}.
Proof.
  generalize Expr_eq_dec.
  generalize type_eq_dec.
  decide equality.
  eapply Decidable_dec; eauto with typeclass_instances.
  eapply Decidable_dec; eauto with typeclass_instances.
Defined.

Global Instance Decidable_eq_GlobDecl (a b : GlobDecl) : Decidable (a = b) :=
  dec_Decidable (GlobDecl_eq_dec a b).


Definition GlobDecl_merge (a b : GlobDecl) : option GlobDecl :=
  match a , b with
  | Gtype , Gunion _
  | Gtype , Gstruct _ => Some b
  | Gunion _ , Gtype
  | Gstruct _ , Gtype => Some a
  | Gunion u , Gunion u' =>
    require (decide (u = u')) ;;
    Some a
  | Gstruct s , Gstruct s' =>
    require (decide (s = s')) ;;
    Some a
  | Genum e , Genum e' =>
    require (decide (e = e')) ;;
    Some a
  | Gconstant t e , Gconstant t' e' =>
    require (decide (t = t')) ;;
    require (decide (e = e')) ;;
    Some a
  | Gtypedef t , Gtypedef t' =>
    require (decide (t = t')) ;;
    Some a
  | Gtypedec , Gunion _
  | Gtypedec , Gstruct _
  | Gtypedec , Genum _ => Some b
  | Gunion _ , Gtypedec
  | Gstruct _ , Gtypedec
  | Genum _ , Gtypedec
  | Gtypedec , Gtypedec => Some a
  | _ , _ => None
  end%monad.



(* if these were association lists, then... *)
Record compilation_unit : Set :=
{ symbols : list (obj_name * ObjValue)
; globals : list (globname * GlobDecl)
}.

Section merge.
  Context {K V : Type} (dec : forall a b : K, Decidable (a = b)).

  Definition RelDec_eq_K : RelDec.RelDec (@eq K) :=
    {| RelDec.rel_dec a b := decide (a = b) |}.
  Existing Instance RelDec_eq_K.

  Definition alist_merge (f : V -> V -> option V)
             (l r : alist K V) : option (alist K V) :=
    fold_alist (fun k v acc =>
                  match acc with
                  | None => None
                  | Some acc =>
                    match @alist_find _ _ _ _  k acc with
                    | None => Some (alist_add _ k v acc)
                    | Some v' =>
                      match f v v' with
                      | None => None
                      | Some v => Some (alist_add _ k v acc)
                      end
                    end
                  end) (Some r) l.
End merge.

Definition link (a b : compilation_unit) : option compilation_unit :=
  (g <- alist_merge _ GlobDecl_merge a.(globals) b.(globals) ;;
   s <- alist_merge _ (ObjValue_merge Either) a.(symbols) b.(symbols) ;;
   ret {| globals := g ; symbols := s |})%monad.

Definition lookup_global (m : compilation_unit) (n : globname) : option GlobDecl :=
  alist_find (R:=eq) (RelDec_eq_K _) n m.(globals).

Definition lookup_symbol (m : compilation_unit) (n : obj_name) : option ObjValue :=
  alist_find (R:=eq) (RelDec_eq_K _) n m.(symbols).

Definition module_le (a b : compilation_unit) : bool :=
  List.forallb (fun x =>
                  List.existsb (fun y => decide (x = y)) b.(globals)) a.(globals) &&
  List.forallb (fun x =>
                  List.existsb (fun y => decide (fst x = fst y) &&
                                       match ObjValue_merge LT (snd x) (snd y) with
                                      | Some _ => true
                                      | _ => false
                                      end) b.(symbols)) a.(symbols).

Definition compilation_unit_eq (a b : compilation_unit) : bool :=
  module_le a b && module_le b a.


Definition Dvar (name : obj_name) (t : type) (init : option Expr) : compilation_unit :=
  {| symbols := (name, Ovar t init) :: nil
   ; globals := nil |}.

Definition Dfunction    (name : obj_name) (f : Func) : compilation_unit :=
  {| symbols := (name, Ofunction f) :: nil
   ; globals := nil |}.
Definition Dmethod    (name : obj_name) (f : Method) : compilation_unit :=
  {| symbols := (name, Omethod f) :: nil
   ; globals := nil |}.
Definition Dconstructor    (name : obj_name) (f : Ctor) : compilation_unit :=
  {| symbols := (name, Oconstructor f) :: nil
   ; globals := nil |}.
Definition Ddestructor    (name : obj_name) (f : Dtor) : compilation_unit :=
  {| symbols := (name, Odestructor f) :: nil
   ; globals := nil |}.
Definition Dunion (name : globname) (o : option Union) : compilation_unit :=
  {| symbols := nil
   ; globals := (name, match o with
                       | None => Gtypedec
                       | Some u => Gunion u
                       end) :: nil |}.
Definition Dstruct (name : globname) (o : option Struct) : compilation_unit :=
  {| symbols := nil
   ; globals := (name, match o with
                       | None => Gtypedec
                       | Some u => Gstruct u
                       end) :: nil |}.
Definition Denum (name : globname) (t : option type) (branches : list (ident * BinNums.Z)) : compilation_unit :=
  {| symbols := nil
   ; globals :=
       let ty := match t with
                 | None => Tref name
                 | Some t => Talias t name
                 end
       in
       match t with
       | Some t =>  (name, Genum t) :: nil
       | None => nil
       end ++
       List.map (fun '(nm, oe) => (nm, Gconstant ty (Eint oe ty))) branches |}.
  (* ^ enumerations (the initializers need to be constant expressions) *)

Definition Dconstant    (name : globname) (t : type) (e : Expr) : compilation_unit :=
  {| symbols := nil
   ; globals := (name, Gconstant t e) :: nil |}.
Definition Dtypedef     (name : globname) (t : type) : compilation_unit :=
  {| symbols := nil
   ; globals := (name, Gtypedef t) :: nil |}.
Definition Dtype (name : globname) : compilation_unit :=
  {| symbols := nil
   ; globals := (name, Gtype) :: nil |}.


Fixpoint decls (ls : list compilation_unit) : compilation_unit :=
  match ls with
  | nil => {| symbols := nil ; globals := nil |}
  | m :: ms =>
    let res := decls ms in
    {| symbols := m.(symbols) ++ res.(symbols)
     ; globals := m.(globals) ++ res.(globals) |}
  end%list.

Declare Reduction reduce_compilation_unit :=
  cbv beta iota zeta delta [ decls List.app symbols globals
                             Dvar Dfunction Dmethod Dconstructor Ddestructor
                             Dstruct Denum Dunion Dconstant Dtypedef Dtype ].
