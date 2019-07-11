Require Import Coq.Classes.DecidableClass.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.OptionMonad.

From Coq.Strings Require Import
     Ascii String.

Require Import Cpp.Util.
Require Import Cpp.Syntax.Ast.

Definition VarRef_eq_dec : forall a b : VarRef, {a = b} + {a <> b}.
Proof.
  decide equality.
  eapply string_dec.
  eapply string_dec.
Defined.

Definition UnOp_eq_dec : forall a b : UnOp, {a = b} + {a <> b}.
decide equality.
eapply string_dec.
Defined.

Definition BinOp_eq_dec : forall a b : BinOp, {a = b} + {a <> b}.
decide equality.
Defined.

Definition ValCat_eq_dec : forall a b : ValCat, {a = b} + {a <> b}.
decide equality.
Defined.

Definition Expr_eq_dec : forall a b : Expr, {a = b} + {a <> b}.
Proof.
  generalize type_eq_dec.
  generalize VarRef_eq_dec.
  generalize BinInt.Z.eq_dec.
  generalize ascii_dec.
  generalize string_dec.
  generalize Bool.bool_dec.
  generalize UnOp_eq_dec.
  generalize BinOp_eq_dec.
  generalize ValCat_eq_dec.
  do 9 intro.
  refine (fix Expr_dec a b : {a = b} + {a <> b} :=
            _).
  decide equality.
  all: try eapply List.list_eq_dec.
  all: decide equality.
  all: decide equality.
  all: decide equality.
Defined.

Definition Stmt_eq_dec : forall a b : Stmt, {a = b} + {a <> b}.
Proof.
  generalize type_eq_dec.
  generalize VarRef_eq_dec.
  generalize BinInt.Z.eq_dec.
  generalize ascii_dec.
  generalize string_dec.
  generalize Bool.bool_dec.
  generalize UnOp_eq_dec.
  generalize BinOp_eq_dec.
  generalize ValCat_eq_dec.
  generalize Expr_eq_dec.
  do 10 intro.
  refine (fix Stmt_dec a b : {a = b} + {a <> b} :=
            _).
  decide equality.
  all: try eapply List.list_eq_dec.
  all: try eassumption.
  all: decide equality.
  all: decide equality.
  all: decide equality.
Defined.

Definition Decidable_dec {T} (a b : T) {Dec : Decidable (a = b)}
  : {a = b} + {a <> b}.
destruct Dec.
destruct Decidable_witness.
- left. apply Decidable_spec. reflexivity.
- right. intro. apply Decidable_spec in H. congruence.
Defined.

Definition dec_Decidable {T} {a b : T} (Dec : {a = b} + {a <> b})
  : Decidable (a = b).
Proof.
  refine {| Decidable_witness := if Dec then true else false |}.
  destruct Dec; split; congruence.
Defined.


Global Instance Decidable_eq_type_qualifiers (a b : type_qualifiers) : Decidable (a = b).
refine
  {| Decidable_witness := decide (a.(q_const) = b.(q_const)) && decide (a.(q_volatile) = b.(q_volatile))
   |}.
rewrite Bool.andb_true_iff.
rewrite (Decidable_eq_bool _ _).(@Decidable_spec _).
rewrite (Decidable_eq_bool _ _).(@Decidable_spec _).
destruct a; destruct b; simpl; firstorder; congruence.
Defined.
Global Instance Decidable_eq_type (a b : type) : Decidable (a = b) :=
  dec_Decidable (type_eq_dec a b).
Global Instance Decidable_eq_expr (a b : Expr) : Decidable (a = b) :=
  dec_Decidable (Expr_eq_dec a b).

Global Instance Decidable_eq_stmt (a b : Stmt) : Decidable (a = b) :=
  dec_Decidable (Stmt_eq_dec a b).

Lemma decide_ok : forall P {ok : Decidable P}, decide P = true <-> P.
Proof.
  intros. eapply Decidable_spec.
Qed.

Section Decidable_or_default.
  Context {T : Set} (dec : forall a b : T, Decidable (a = b)).
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
  Defined.
End Decidable_or_default.

Global Instance Decidable_FieldOrBase (a b : FieldOrBase) : Decidable (a = b).
refine {| Decidable_witness :=
            match a , b with
            | Base a , Base b => decide (a = b)
            | Field a , Field b => decide (a = b)
            | Indirect a a' , Indirect b b' => decide (a = b) && decide (a' = b')
            | _ , _ => false
            end |}.
destruct a; destruct b; repeat rewrite Bool.andb_true_iff; repeat rewrite decide_ok; try solve [ split; congruence ].
firstorder; congruence.
Defined.

Global Instance Decidable_eq_Func (a b : Func) : Decidable (a = b).
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
refine
  {| Decidable_witness :=
       decide (a.(m_return) = b.(m_return)) &&
       decide (a.(m_class) = b.(m_class)) &&
       decide (a.(m_this_qual) = b.(m_this_qual)) &&
       decide (a.(m_params) = b.(m_params)) &&
       decide (a.(m_body) = b.(m_body))
   |}.
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
refine
  {| Decidable_witness :=
       decide (a.(d_class) = b.(d_class)) &&
       decide (a.(d_body) = b.(d_body))
   |}.
repeat rewrite Bool.andb_true_iff.
repeat rewrite Decidable_spec.
destruct a; destruct b; simpl; firstorder; try congruence.
Defined.


Global Instance Decidable_eq_union (a b : Union) : Decidable (a = b).
refine
  {| Decidable_witness := decide (a.(u_fields) = b.(u_fields))
   |}.
simpl.
rewrite dec_list_ok.
destruct a; destruct b. simpl.
split; congruence.
Defined.
Global Instance Decidable_eq_struct (a b : Struct) : Decidable (a = b).
refine
  {| Decidable_witness := decide (a.(s_fields) = b.(s_fields)) && decide (a.(s_bases) = b.(s_bases))
   |}.
simpl.
rewrite Bool.andb_true_iff.
do 2 rewrite dec_list_ok.
destruct a; destruct b; simpl; firstorder; congruence.
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


Definition ObjValue_merge (a b : ObjValue) : option ObjValue :=
  match a , b with
  | Ovar t oe , Ovar t' oe' =>
    require (decide (t = t')) ;;
    match oe with
    | None => Some b
    | Some e => match oe' with
               | None => Some a
               | _ => None
               end
    end
  | Ofunction f , Ofunction f' =>
    require (decide (f.(f_return) = f'.(f_return))) ;;
    require (decide (f.(f_params) = f'.(f_params))) ;;
    match f.(f_body) , f'.(f_body) with
    | Some b , Some b' =>
      (* require (decide (b = b')) ;;
      Some a *) None
    | None , _ => Some b
    | _ , None => Some a
    end
  | Omethod m , Omethod m' =>
    require (decide (m.(m_return) = m'.(m_return))) ;;
    require (decide (m.(m_class) = m'.(m_class))) ;;
    require (decide (m.(m_this_qual) = m'.(m_this_qual))) ;;
    require (decide (m.(m_params) = m'.(m_params))) ;;
    match m.(m_body) , m'.(m_body) with
    | Some b , Some b' =>
      (* require (decide (b = b')) ;;
      Some a *) None
    | None , _ => Some b
    | _ , None => Some a
    end
  | Oconstructor c , Oconstructor c' =>
    require (decide (c.(c_class) = c'.(c_class))) ;;
    require (decide (c.(c_params) = c'.(c_params))) ;;
    match c.(c_body) , c'.(c_body) with
    | None , _ => Some b
    | _ , None => Some a
    | Some _ , Some _ => None
    end
  | Odestructor d , Odestructor d' =>
    require (decide (d.(d_class) = d'.(d_class))) ;;
    match d.(d_body) , d'.(d_body) with
    | None , _ => Some b
    | _ , None => Some a
    | Some _ , Some _ => None
    end
  | _ , _ => None
  end%monad.

Variant GlobDecl : Set :=
| Gunion    (_ : Union)
| Gstruct   (_ : Struct)
| Genum     (_ : type)
| Gconstant (_ : type) (_ : Expr)
| Gtypedef  (_ : type)
| Gtypedec  (* this is a type declaration, but not a definition *)
.

Definition GlobDecl_eq_dec : forall a b : GlobDecl, {a = b} + {a <> b}.
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

Require Import ExtLib.Data.Map.FMapAList.

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
             (l r : alist K V) : option (alist K V).
    refine
      (fold_alist (fun k v acc =>
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
                     end) (Some r) l).
  Defined.
End merge.

Definition link (a b : compilation_unit) : option compilation_unit :=
  (g <- alist_merge _ GlobDecl_merge a.(globals) b.(globals) ;;
   s <- alist_merge _ ObjValue_merge a.(symbols) b.(symbols) ;;
   ret {| globals := g ; symbols := s |})%monad.

Definition lookup_global (m : compilation_unit) (n : globname) : option GlobDecl :=
  alist_find (R:=eq) (RelDec_eq_K _) n m.(globals).

Definition lookup_symbol (m : compilation_unit) (n : obj_name) : option ObjValue :=
  alist_find (R:=eq) (RelDec_eq_K _) n m.(symbols).

Definition module_le (a b : compilation_unit) : bool :=
  List.forallb (fun x =>
                  List.existsb (fun y => decide (x = y)) b.(globals)) a.(globals) &&
  List.forallb (fun x =>
                  List.existsb (fun y => decide (x = y)) b.(symbols)) a.(symbols).

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
                             Dstruct Denum Dunion Dconstant Dtypedef ].
