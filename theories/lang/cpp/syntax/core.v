(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.syntax.prelude.
Require Export bedrock.lang.cpp.syntax.preliminary.
Require Export bedrock.lang.cpp.syntax.overloadable.
Require Import bedrock.lang.cpp.syntax.notations.

#[local] Set Primitive Projections.

#[local] Notation EqDecision1 T := (∀ (A : Set), EqDecision A -> EqDecision (T A)) (only parsing).
#[local] Notation EqDecision2 T := (∀ (A : Set), EqDecision A -> EqDecision1 (T A)) (only parsing).
#[local] Notation EqDecision3 T := (∀ (A : Set), EqDecision A -> EqDecision2 (T A)) (only parsing).
#[local] Tactic Notation "solve_decision" := intros; solve_decision.


(* The stages of a C++ program *)
Module lang.
  Variant t : Set :=
    | cpp (* concrete, non-templated code *)
    | temp. (* meta, templated code *)
End lang.

(** ** Function types *)
(**
TODO: Prefer [function_type] over [functype]. This is complicated by
the several function-like things in the language, with quirky rules
(e.g., member functions may be adorned with qualifiers governing how
<<this>> works and constructors/destructors aren't member functions).
*)
Record function_type_ {decltype : Set} : Set := FunctionType {
  ft_cc : calling_conv;
  ft_arity : function_arity;
  ft_return : decltype;
  ft_params : list decltype;
}.
Add Printing Constructor function_type_.
#[global] Arguments function_type_ : clear implicits.
#[global] Arguments FunctionType {_ _ _} _ _ : assert.
#[global] Instance function_type__inhabited {A : Set} {_ : Inhabited A} : Inhabited (function_type_ A).
Proof. solve_inhabited. Qed.
#[global] Instance function_type__eq_dec {A : Set} {_ : EqDecision A} : EqDecision (function_type_ A).
Proof. solve_decision. Defined.

Module function_type.
  Import UPoly.
  Definition existsb {decltype : Set} (f : decltype -> bool)
      (ft : function_type_ decltype) : bool :=
    f ft.(ft_return) || existsb f ft.(ft_params).

  Definition fmap {decltype decltype' : Set} (f : decltype -> decltype')
    (ft : function_type_ decltype) : function_type_ decltype' :=
    @FunctionType _ ft.(ft_cc) ft.(ft_arity) (f ft.(ft_return)) (f <$> ft.(ft_params)).
  #[global] Arguments fmap _ _ _ & _ : assert.
  #[global] Hint Opaque fmap : typeclass_instances.

  #[universes(polymorphic)]
  Definition traverse@{u | } {F : Set -> Type@{u}} `{!FMap F, !MRet F, AP : !Ap F}
  {decltype decltype' : Set} (f : decltype -> F decltype')
  (ft : function_type_ decltype) : F (function_type_ decltype') :=
    @FunctionType _ ft.(ft_cc) ft.(ft_arity)
                                    <$> f ft.(ft_return) <*> traverse (T:=eta list) f ft.(ft_params).
  #[global] Arguments traverse _ _ _ _ _ _ & _ _ : assert.
  #[global] Hint Opaque traverse : typeclass_instances.
End function_type.

(** ** Templates *)

Variant temp_param_ {type : Set} : Set :=
| Ptype (_ : ident)
| Pvalue (_ : ident) (_ : type)
| Punsupported (_ : bs).
#[global] Arguments temp_param_ : clear implicits.
#[global] Instance temp_param__inhabited {A} : Inhabited (temp_param_ A).
Proof. solve_inhabited. Qed.
#[global] Instance temp_param_eq_dec {A : Set} `{!EqDecision A} : EqDecision (temp_param_ A).
Proof. solve_decision. Defined.

Module temp_param.
  Import UPoly.
  Definition existsb {type : Set} (f : type -> bool) (p : temp_param_ type) : bool :=
    if p is Pvalue _ t then f t else false.

  Definition fmap {type type' : Set} (f : type -> type')
    (p : temp_param_ type) : temp_param_ type' :=
    match p with
    | Ptype id => Ptype id
    | Pvalue id t => Pvalue id (f t)
    | Punsupported msg => Punsupported msg
    end.
  #[global] Arguments fmap _ _ _ & _ : assert.
  #[global] Hint Opaque fmap : typeclass_instances.

  Section traverse.
    #[local] Set Universe Polymorphism.
    #[local] Unset Auto Template Polymorphism.
    #[local] Unset Universe Minimization ToSet.
    Universe u.
    Context {F : Set -> Type@{u}} `{!FMap F, !MRet F, AP : !Ap F}.
    Context {type type' : Set}.

    Definition traverse (f : type -> F type') (p : temp_param_ type)
      : F (temp_param_ type') :=
      match p with
      | Ptype id => mret $ Ptype id
      | Pvalue id t => Pvalue id <$> f t
      | Punsupported msg => mret $ Punsupported msg
      end.
    #[global] Arguments traverse _ & _ : assert.
    #[global] Hint Opaque traverse : typeclass_instances.
  End traverse.

End temp_param.

Inductive temp_arg_ {decltype Expr : Set} : Set :=
| Atype (_ : decltype)
| Avalue (_ : Expr)
| Apack (_ : list temp_arg_)
| Aunsupported (_ : bs).
Arguments temp_arg_ : clear implicits.
#[global] Instance temp_arg__inhabited {A B : Set} {_ : Inhabited A} : Inhabited (temp_arg_ A B).
Proof. solve_inhabited. Qed.
(*
#[global] Instance temp_arg__eq_dec {A B : Set} {_ : EqDecision A} {_ : EqDecision B} : EqDecision (temp_arg_ A B).
Proof. solve_decision. Defined.
*)

Module temp_arg.
  Import UPoly.
  Section existsb.
    Context {type Expr : Set} (f : type -> bool) (g : Expr -> bool).

    Fixpoint existsb (a : temp_arg_ type Expr) : bool :=
      match a with
      | Atype t => f t
      | Avalue e => g e
      | Apack ls => List.existsb existsb ls
      | Aunsupported _ => false
      end.
  End existsb.

  Section fmap.
    Context {type type' Expr Expr' : Set}
      (f : type -> type') (g : Expr -> Expr').

    Fixpoint fmap (a : temp_arg_ type Expr) : temp_arg_ type' Expr' :=
      match a with
      | Atype t => Atype (f t)
      | Avalue e => Avalue (g e)
      | Apack ls => Apack $ fmap <$> ls
      | Aunsupported msg => Aunsupported msg
      end.
  End fmap.
  #[global] Arguments fmap _ _ _ _ _ _ & _ : assert.

  Section traverse.
    #[local] Set Universe Polymorphism.
    #[local] Unset Auto Template Polymorphism.
    #[local] Unset Universe Minimization ToSet.
    Universe u.
    Context {F : Set -> Type@{u}} `{!FMap F, !MRet F, AP : !Ap F}.
    Context {type type' Expr Expr' : Set} (f : type -> F type')
      (g : Expr -> F Expr').

    Fixpoint traverse (a : temp_arg_ type Expr) : F (temp_arg_ type' Expr') :=
      match a with
      | Atype t => Atype <$> f t
      | Avalue e => Avalue <$> g e
      | Apack ls => Apack <$> UPoly.traverse (T:=eta list) (F:=F) traverse ls
      | Aunsupported msg => mret $ Aunsupported msg
      end.
    #[global] Arguments traverse & _ : assert.
    #[global] Hint Opaque traverse : typeclass_instances.
  End traverse.

End temp_arg.

(** ** Function names and qualifiers *)
Variant function_name_ {type : Set} : Set :=
| Nf (_ : ident)
| Nctor
| Ndtor
| Nop (_ : OverloadableOperator)
| Nop_conv (_ : type)
| Nop_lit (_ : ident)
| Nunsupported_function (_ : bs).
#[global] Arguments function_name_ : clear implicits.
#[global] Instance function_name__inhabited {A} : Inhabited (function_name_ A).
Proof. solve_inhabited. Qed.
#[global] Instance function_name__eq_dec {A : Set} `{!EqDecision A} : EqDecision (function_name_ A).
Proof. solve_decision. Defined.

Module function_name.
  Import UPoly.

  Definition existsb {type : Set} (f : type -> bool) (n : function_name_ type) : bool :=
    if n is Nop_conv t then f t else false.

  Definition fmap {type type' : Set} (f : type -> type') (n : function_name_ type) : function_name_ type' :=
    match n in function_name_ _ with
    | Nf id => Nf id
    | Nctor => Nctor
    | Ndtor => Ndtor
    | Nop oo => Nop oo
    | Nop_conv t => Nop_conv (f t)
    | Nop_lit s => Nop_lit s
    | Nunsupported_function msg => Nunsupported_function msg
    end.
  #[global] Arguments fmap _ _ _ & _ : assert.
  #[global] Hint Opaque fmap : typeclass_instances.

  Section traverse.
    #[local] Set Universe Polymorphism.
    #[local] Unset Auto Template Polymorphism.
    #[local] Unset Universe Minimization ToSet.
    Universe u.
    Context {F : Set -> Type@{u}} `{!FMap F, !MRet F, AP : !Ap F}.
    Context {type type' : Set}.

    Definition traverse (f : type -> F type')
        (n : function_name_ type) : F (function_name_ type') :=
      match n with
      | Nf id => mret $ Nf id
      | Nctor => mret Nctor
      | Ndtor => mret Ndtor
      | Nop oo => mret $ Nop oo
      | Nop_conv t => Nop_conv <$> f t
      | Nop_lit s => mret $ Nop_lit s
      | Nunsupported_function msg => mret $ Nunsupported_function msg
      end.
    #[global] Arguments traverse _ & _ : assert.
    #[global] Hint Opaque traverse : typeclass_instances.
  End traverse.

End function_name.

Module function_qualifiers.
  (* This is a compressed tuple.
     - <<l>> means <<&>>
     - <<r>> means <<&&>>
     - <<c>> means <<const>>
     - <<v>> means <<volatile>>
   *)
  Variant t : Set :=
  | N   | Nl   | Nr
  | Nc  | Ncl  | Ncr
  | Nv  | Nvl  | Nvr
  | Ncv | Ncvl | Ncvr.

  Definition is_const (a : t) :=
    match a with
    | Nc | Ncl | Ncr | Ncv | Ncvl | Ncvr => true
    | _ => false
    end.
  Definition is_volatile (a : t) :=
    match a with
    | Nv | Nvl | Nvr | Ncv | Ncvl | Ncvr => true
    | _ => false
    end.

  (* we use [Prvalue] to represent no annotation *)
  Definition vc_of (a : t) : ValCat :=
    match a with
    | N | Nc | Nv | Ncv => Prvalue
    | Nl | Ncl | Nvl | Ncvl => Lvalue
    | Nr | Ncr | Nvr | Ncvr => Xvalue
    end.

  Definition mk (const volatile : bool) (vc : ValCat) : t :=
    match const , volatile , vc with
    | false , false , Prvalue => N
    | false , false , Lvalue => Nl
    | false , false , Xvalue => Nr
    | false , true  , Prvalue => Nv
    | false , true  , Lvalue => Nvl
    | false , true  , Xvalue => Nvr
    | true  , false , Prvalue => Nc
    | true  , false , Lvalue => Ncl
    | true  , false , Xvalue => Ncr
    | true  , true  , Prvalue => Ncv
    | true  , true  , Lvalue => Ncvl
    | true  , true  , Xvalue => Ncvr
    end.

  Definition join (a b : t) : t :=
    mk (is_const a || is_const b) (is_volatile a || is_volatile b)
      match vc_of a , vc_of b with
      | Prvalue , b => b
      | a , Prvalue => a
      | a , _ => a
      end.

  #[global] Instance t_inhabited : Inhabited t.
  Proof. solve_inhabited. Qed.

  #[prefix="", only(tag)] derive t.

  Definition compare (a b : t) : comparison :=
    Pos.compare (tag a) (tag b).

  Definition to_type_qualifiers (f : t) : type_qualifiers :=
    match f with
    | N | Nl | Nr => QM
    | Nc | Ncl | Ncr => QC
    | Nv | Nvl | Nvr => QV
    | Ncv | Ncvl | Ncvr => QCV
    end.
End function_qualifiers.

(** ** Atomic names *)
(**
Atomic names are effectively path components.
*)
Variant atomic_name_ {type : Set} : Set :=
(** Named things *)
| Nid (_ : ident)	(** namespace, struct, union, typedef, variable, member, ... *)
(**
TODO (Discuss): Do we need to distinguish templated functions by their
return types?
*)
| Nfunction (_ : function_qualifiers.t) (_ : function_name_ type) (_ : list type)
(** Unnamed things *)
| Nanon (_ : N)
  (* an anonymous namespace. Specialized b/c they are re-declarable so
     their position is not relevant *)
| Nanonymous
  (* When entities are not named, we use a heuristic that picks the
     first named declaration of the type or the first named field.
     It is important that we distinguish these from [Nid n] because
     [n] is a *type name* while the identifiers in these declarations
     are object names. Effectively in [Nfirst_decl "x"], the name
     of the type is <<decltype(x)>>.
   *)
| Nfirst_decl (_ : ident)
| Nfirst_child (_ : ident)

(** Errors *)
| Nunsupported_atomic (_ : bs).
#[global] Arguments atomic_name_ : clear implicits.
#[global] Instance atomic_name__inhabited {A} : Inhabited (atomic_name_ A).
Proof. solve_inhabited. Qed.

Module atomic_name.
  Definition existsb {type : Set} (f : type -> bool)
      (c : atomic_name_ type) : bool :=
    match c with
    | Nid _ => false
    | Nfunction _ n ts => function_name.existsb f n || List.existsb f ts
    | Nanon _
    | Nanonymous
    | Nfirst_decl _
    | Nfirst_child _
    | Nunsupported_atomic _ => false
    end.

  Import UPoly.

  Definition fmap {type type' : Set} (f : type -> type')
      (c : atomic_name_ type) : atomic_name_ type' :=
    match c with
    | Nid id => Nid id
    | Nfunction qs n ts => Nfunction qs (function_name.fmap f n) (f <$> ts)
    | Nanon n => Nanon n
    | Nanonymous => Nanonymous
    | Nfirst_decl n => Nfirst_decl n
    | Nfirst_child n => Nfirst_child n
    | Nunsupported_atomic msg => Nunsupported_atomic msg
    end.
  #[global] Arguments fmap _ _ _ & _ : assert.

  Section traverse.
    #[local] Set Universe Polymorphism.
    #[local] Unset Auto Template Polymorphism.
    #[local] Unset Universe Minimization ToSet.
    Universe u.
    Context {F : Set -> Type@{u}} `{!FMap F, !MRet F, AP : !Ap F}.
    Context {type type' : Set}.
    Context (f : type -> F type').

    #[local] Notation list_traverse := (UPoly.traverse (T:=eta list)).
    Definition traverse (c : atomic_name_ type) : F (atomic_name_ type') :=
      match c with
      | Nid id => mret $ Nid id
      | Nfunction qs n ts => Nfunction qs <$> function_name.traverse f n <*> list_traverse f ts
      | Nanon n => mret $ Nanon n
      | Nanonymous => mret Nanonymous
      | Nfirst_decl n => mret $ Nfirst_decl n
      | Nfirst_child n => mret $ Nfirst_child n

      | Nunsupported_atomic msg => mret $ Nunsupported_atomic msg
      end.
    #[global] Arguments traverse & _ : assert.
    #[global] Hint Opaque traverse : typeclass_instances.
  End traverse.

End atomic_name.

Module cast_style.
  Variant t : Set :=
  | functional
  | c
  | static | dynamic | reinterpret | const.

  #[global] Instance t_eq_dec : EqDecision t.
  Proof. solve_decision. Defined.
  #[global] Instance t_inhabited : Inhabited t.
  Proof. repeat constructor. Qed.

  #[prefix="", only(tag)] derive t.
  Definition compare (a b : t) : comparison :=
    Pos.compare (tag a) (tag b).
End cast_style.

(** ** Structured names *)
Inductive name' {lang : lang.t} : Set :=
| Ninst (c : name') (_ : list (temp_arg_ type' Expr'))
| Nglobal (c : atomic_name_ type')	(* <<::c>> *)
| Ndependent (t : type') (* <<typename t>> *)
| Nscoped (n : name') (c : atomic_name_ type')	(* <<n::c>> *)
| Nunsupported (_ : bs)

(** ** Types *)
(**
NOTE: We could eliminate [Tresult_unop], [Tresult_binop] using
[Tresult_call] because the evaluation order distinction between
operators and operator calls does not matter for typing purposes. We
do things this way for consistency, and to keep the components of
substitutions small.
*)

with type' {lang : lang.t} : Set :=
| Tparam (_ : ident)
| Tresult_param (_ : ident)
| Tresult_global (on : name')
| Tresult_unop (_ : RUnOp) (_ : type')
| Tresult_binop (_ : RBinOp) (_ _ : type')
| Tresult_call (on : name') (_ : list type')
| Tresult_member_call (on : name') (_ : type') (_ : list type')
| Tresult_parenlist (_ :type') (_ : list type')
| Tresult_member (_ : type') (_ : name')

| Tptr (t : type')
| Tref (t : type')
| Trv_ref (t : type')
| Tnum (sz : int_rank.t) (sgn : signed)
| Tchar_ (_ : char_type.t)
| Tvoid
| Tarray (t : type') (n : N)
| Tincomplete_array (t : type')
| Tvariable_array (t : type') (e : Expr')
| Tnamed (gn : name')
| Tenum (gn : name')
| Tfunction (t : function_type_ type')
| Tbool
| Tmember_pointer (gn : (* classname' *)type') (t : type')
| Tfloat_ (_ : float_type.t)
| Tqualified (q : type_qualifiers) (t : type')
| Tnullptr
| Tarch (osz : option bitsize) (name : bs)
| Tdecltype (_ : Expr')
  (* ^^ this is <<decltype(e)>> when <<e>> is an expression, including a parenthesized expression.
     (2) in <https://en.cppreference.com/w/cpp/language/decltype>
   *)
| Texprtype (_ : Expr')
  (* ^^ this is <<decltype(e)>> when <<e>> is a variable reference
     (1) in <https://en.cppreference.com/w/cpp/language/decltype>
   *)
| Tunsupported (_ : bs)

(** ** Expressions *)
(**
NOTE: We need both unresolved operators and unresolved calls because
operators like <<a = b>> use a different evaluation order than calls
like <<operator=(a, b)>>.
*)
with Expr' {lang : lang.t} : Set :=
| Eparam (_ : ident)
| Eunresolved_global (_ : name')
| Eunresolved_unop (_ : RUnOp) (e : Expr')
| Eunresolved_binop (_ : RBinOp) (l r : Expr')
| Eunresolved_call (on : name') (_ : list Expr')
| Eunresolved_member_call (on : name') (_ : Expr') (_ : list Expr')
(**
<<Eunresolved_parenlist (Some T) [arg1;…;argN]>> is the initializer
for an uninstantiated direct initializer list declaration <<T
var(arg1,…,argN)>> with dependent type <<T>>. Making the type optional
simplifies cpp2v---we set it from context in ../mparser.v.
*)
| Eunresolved_parenlist (_ : option type') (_ : list Expr')
| Eunresolved_member (_ : Expr') (_ : name')

(**
NOTE: We might need to support template parameters as object names in
a few constructors (by carrying <<Expr ≈ Eparam + Eglobal>> instead of
<<name>>).
*)

| Evar (_ : localname) (_ : type')
| Eenum_const (gn : name') (_ : ident)
| Eglobal (on : name') (_ : type')
(**
[Eglobal_member gn t] represents <<&gn>> where <<gn>>
is a non-static member of a class, e.g. a field or method.
We distinguish this from [Eaddrof (Eglobal gn)] because,
when [gn] refers to a member, <<&gn>> is not a well-formed
program because, in part, C++ has no type for references to members.
*)
| Eglobal_member (gn : name') (ty : type')

| Echar (c : N) (t : type')
| Estring (s : list N) (t : type')
| Eint (n : Z) (t : type')
| Ebool (b : bool)
| Eunop (op : UnOp) (e : Expr') (t : type')
| Ebinop (op : BinOp) (e1 e2 : Expr') (t : type')
| Ederef (e : Expr') (t : type')
| Eaddrof (e : Expr')
| Eassign (e1 e2 : Expr') (t : type')
| Eassign_op (op : BinOp) (e1 e2 : Expr') (t : type')
| Epreinc (e : Expr') (t : type')
| Epostinc (e : Expr') (t : type')
| Epredec (e : Expr') (t : type')
| Epostdec (e : Expr') (t : type')
| Eseqand (e1 e2 : Expr')
| Eseqor (e1 e2 : Expr')
| Ecomma (e1 e2 : Expr')
| Ecall (f : Expr') (es : list Expr')
| Eexplicit_cast (c : cast_style.t) (_ : type') (e : Expr')
| Ecast (c : Cast') (e : Expr')
  (* TODO: this use of [Cast_] should really use [classname] as its first argument, but
     we can not use that without a [match] which Coq rejects as not being strictly positive.
     GM: the only way I see to solve this problem is to make [lang] and index rather than
       a parameter. Doing that would allow for two different constructors for [Ecast]
   *)
| Emember (arrow : bool) (obj : Expr') (f : atomic_name_ type') (mut : bool) (t : type')
| Emember_ignore (arrow : bool) (obj : Expr') (res : Expr')
| Emember_call (arrow : bool) (method : MethodRef_ name' type' Expr') (obj : Expr') (args : list Expr')
| Eoperator_call (_ : OverloadableOperator) (_ : operator_impl.t name' type') (_ : list Expr')
| Esubscript (e1 : Expr') (e2 : Expr') (t : type')
| Esizeof (_ : type' + Expr') (t : type')
| Ealignof (_ : type' + Expr') (t : type')
(**
NOTE: [Eoffsetof] carries a type instead of a name to support
dependent types.
Should be [gn : classname]
*)
| Eoffsetof (gn : type') (_ : ident) (t : type')
| Econstructor (on : name') (args : list Expr') (t : type')
| Elambda (_ : name') (captures : list Expr')
| Eimplicit (e : Expr')
| Eimplicit_init (t : type')
| Eif (e1 e2 e3 : Expr') (t : type')
| Eif2  (n : N) (common cond thn els : Expr') (_ : type')
| Ethis (t : type')
| Enull
| Einitlist (args : list Expr') (default : option Expr') (t : type')
| Einitlist_union (_ : atomic_name_ type') (_ : option Expr') (t : type')

| Enew (new_fn : name' * type') (new_args : list Expr') (pass_align : new_form)
  (alloc_ty : type') (array_size : option Expr') (init : option Expr')
| Edelete (is_array : bool) (del_fn : name' * type')
  (arg : Expr') (deleted_type : type')
| Eandclean (e : Expr')
| Ematerialize_temp (e : Expr') (vc : ValCat)
  (* ^^ [Ematerialize_temp] is can be an lvalue in the following program:
     <<
     int x[10];
     static_cast<int*const&>(x);
     >>
     (this is true at least in c++11)
   *)
| Eatomic (op : AtomicOp) (args : list Expr') (t : type')
| Estmt (_ : Stmt') (_ : type')
| Eva_arg (e : Expr') (t : type')
  (**
  TODO: We may have to adjust cpp2v: Either [Eva_arg] should carry a
  decltype, or [valcat_of] in cpp2v-core and [decltype.of_expr] here
  are unnecessarily complicated.

  TODO: [Eva_arg _ Tdependent]

  Docs for <<__builtin_va_arg>>.
  https://clang.llvm.org/docs/LanguageExtensions.html#builtin-functions
  *)
| Epseudo_destructor (is_arrow : bool) (t : type') (e : Expr')
| Earrayloop_init (oname : N) (src : Expr') (level : N) (length : N) (init : Expr') (t : type')
| Earrayloop_index (level : N) (t : type')
| Eopaque_ref (name : N) (t : type')
| Eunsupported (s : bs) (t : type')
with Stmt' {lang : lang.t} : Set :=
| Sseq    (_ : list Stmt')
| Sdecl   (_ : list VarDecl')

| Sif     (_ : option VarDecl') (_ : Expr') (_ _ : Stmt')
| Sif_consteval (_ _ : Stmt')

| Swhile  (_ : option VarDecl') (_ : Expr') (_ : Stmt')
| Sfor    (_ : option Stmt') (_ : option Expr') (_ : option Expr') (_ : Stmt')
| Sdo     (_ : Stmt') (_ : Expr')

| Sswitch (_ : option VarDecl') (_ : Expr') (_ : Stmt')
| Scase   (_ : SwitchBranch)
| Sdefault

| Sbreak
| Scontinue

| Sreturn (_ : option Expr')

| Sexpr   (_ : Expr')

| Sattr (_ : list ident) (_ : Stmt')

| Sasm (_ : bs) (volatile : bool)
       (inputs : list (ident * Expr'))
       (outputs : list (ident * Expr'))
       (clobbers : list ident)

| Slabeled (_ : ident) (_ : Stmt')
| Sgoto (_ : ident)
| Sunsupported (_ : bs)
with VarDecl' {lang : lang.t} : Set :=
| Dvar (name : localname) (_ : type') (init : option Expr')
| Ddecompose (_ : Expr') (anon_var : ident) (_ : list BindingDecl')
  (* initialization of a function-local [static]. See https://eel.is/c++draft/stmt.dcl#3 *)
| Dinit (thread_safe : bool) (name : name') (_ : type') (init : option Expr')
with BindingDecl' {lang : lang.t} : Set :=
| Bvar (name : localname) (_ : type') (init : Expr')
| Bbind (name : localname) (_ : type') (init : Expr')
(** ** Casts *)
with Cast' {lang : lang.t} : Set :=
| Cdependent (_ : type')
| Cbitcast (_ : type')
| Clvaluebitcast	(_ : type') (** TODO (FM-3431): Drop this constructor? *)
| Cl2r
| Cl2r_bitcast (_ : type')
| Cnoop (_ : type')
| Carray2ptr
| Cfun2ptr
| Cint2ptr (_ : type')
| Cptr2int (_ : type')
| Cptr2bool
| Cintegral (_ : type')
| Cint2bool
| Cfloat2int (_ : type')
| Cint2float (_ : type')
| Cfloat (_ : type') (* conversion between floating point types *)
| Cnull2ptr (_ : type')
| Cnull2memberptr (_ : type')
| Cbuiltin2fun (_ : type') (* OPTIMIZABLE? *)
| C2void

  (* These are just annotations on the underlying expression *)
| Cctor (_ : type')
| Cuser (* this is an annotation, the actual member call is the child node *)
| Cdynamic     (to : type')
| Cderived2base (path : list type') (END : type')
| Cbase2derived (path : list type') (END : type')
(* If the sub-expression has type <START> then the arguments of
   [Cderived2base] and [Cbase2derived] contain the path between
   <START> and <END> from derived class to base class.
   For example, with
     ```c++
     class A {};
     class B : public A {};
     class C : public B {};
     class D : public C {};
     ```
     A cast from <<D>> to <<A>> will be [Cderived2base ["C";"B"] "A"].
     - <<C>> comes from the type of the sub-expression.
     A cast from <<A>> to <<D>> will be [Cbase2derived ["C";"B"] "D"].
     - <<A>> comes from the type of the sub-expression.
 *)

.
#[global] Arguments Cast' : clear implicits.
#[global] Arguments name' : clear implicits.
#[global] Arguments type' : clear implicits.
#[global] Arguments Expr' : clear implicits.
#[global] Arguments VarDecl' : clear implicits.
#[global] Arguments BindingDecl' : clear implicits.
#[global] Arguments Stmt' : clear implicits.

#[global] Instance type_inhabited {lang} : Inhabited (type' lang).
Proof. solve_inhabited. Qed.
#[global] Instance Expr_inhabited {lang} : Inhabited (Expr' lang).
Proof. solve_inhabited. Qed.
#[global] Instance name_inhabited {lang} : Inhabited (name' lang).
Proof. apply populate, Nglobal, inhabitant. Qed.
#[global] Instance VarDecl_inhabited {lang} : Inhabited (VarDecl' lang).
Proof. solve_inhabited. Qed.
#[global] Instance BindingDecl_inhabited {lang} : Inhabited (BindingDecl' lang).
Proof. solve_inhabited. Qed.
#[global] Instance Stmt_inhabited {lang} : Inhabited (Stmt' lang).
Proof. apply populate, Sseq, nil. Qed.
#[global] Instance Cast_inhabited {lang} : Inhabited (Cast' lang).
Proof. apply populate, C2void. Qed.

(*
Section eq_dec.
  Context {lang : lang.t}.
  #[local] Notation EQ_DEC T := (∀ x y : T, Decision (x = y)) (only parsing).

  Lemma name_eq_dec' : EQ_DEC (name' lang)
  with type_eq_dec' : EQ_DEC (type' lang)
  with Expr_eq_dec' : EQ_DEC (Expr' lang)
  with VarDecl_eq_dec' : EQ_DEC (VarDecl' lang)
  with BindingDecl_eq_dec' : EQ_DEC (BindingDecl' lang)
  with Stmt_eq_dec' : EQ_DEC (Stmt' lang)
  with Cast_eq_dec' : EQ_DEC (Cast' lang).
  Proof.
    all: intros x y.
    all: pose (name_eq_dec' : EqDecision _).
    all: pose (type_eq_dec' : EqDecision _).
    all: pose (Expr_eq_dec' : EqDecision _).
    all: pose (VarDecl_eq_dec' : EqDecision _).
    all: pose (BindingDecl_eq_dec' : EqDecision _).
    all: pose (Stmt_eq_dec' : EqDecision _).
    all: pose (Cast_eq_dec' : EqDecision _).
    all:unfold Decision; decide equality; solve_decision.
  Defined.

  #[global] Instance name_eq_dec : EqDecision _ := name_eq_dec'.
  #[global] Instance type_eq_dec : EqDecision _ := type_eq_dec'.
  #[global] Instance Expr_eq_dec : EqDecision _ := Expr_eq_dec'.
  #[global] Instance VarDecl_eq_dec : EqDecision _ := VarDecl_eq_dec'.
  #[global] Instance BindingDecl_eq_dec : EqDecision _ := BindingDecl_eq_dec'.
  #[global] Instance Stmt_eq_dec : EqDecision _ := Stmt_eq_dec'.
  #[global] Instance Cast_eq_dec : EqDecision _ := Cast_eq_dec'.
End eq_dec.
*)

Module Cast.
  Definition existsb {lang : lang.t}
    (T : type' lang -> bool)
    (c : Cast' lang) : bool :=
    match c with
    | Cdependent t
    | Cbitcast t
    | Clvaluebitcast t => T t
    | Cl2r => false
    | Cl2r_bitcast t => T t
    | Cnoop t => T t
    | Carray2ptr
    | Cfun2ptr => false
    | Cint2ptr t
    | Cptr2int t => T t
    | Cptr2bool => false
    | Cderived2base path t
    | Cbase2derived path t => List.existsb T path || T t
    | Cintegral t => T t
    | Cint2bool => false
    | Cfloat2int t
    | Cint2float t
    | Cfloat t
    | Cnull2ptr t
    | Cnull2memberptr t
    | Cbuiltin2fun t
    | Cctor t => T t
    | C2void => false
    | Cuser => false
    | Cdynamic t => T t
    end.

End Cast.

Definition is_implicit {lang} (e : Expr' lang) : bool :=
  if e is Eimplicit _ then true else false.

Definition globname' := name'.	(** Type names *)
Definition obj_name' := name'.	(** Function, data names *)

Definition exprtype' := type'.	(** An expression's non-reference type *)
Definition decltype' := type'.	(** Types as used in declarations (≈ ValCat × exprtype) *)
Definition functype' := type'.	(** Must be [Tfunction] *)

Notation Nenum_const gn id := (Nscoped gn (Nid id)) (only parsing).

(** ** Notations
    We aim to set up all of the types so that they look uniform.
    The convention can be viewed with the type [Expr].
    - [Expr' lang] is the syntax that is parametric in the [lang.t]
    - [Notation Expr := Expr' lang.cpp]
    - [Notation MExpr := Expr' lang.temp]
    When types are not immediately parametric in [lang.t], we
    give them names with an <<_>>, for example, see [Cast_].
 *)
Notation operator_impl' lang := (operator_impl.t (obj_name' lang) (type' lang)).
Notation MethodRef' lang := (MethodRef_ (obj_name' lang) (functype' lang) (Expr' lang)).
Notation function_type' lang := (function_type_ (decltype' lang)).
Notation function_name' lang := (function_name_ (decltype' lang)).
Notation temp_param' lang := (temp_param_ (type' lang)).
Notation temp_arg' lang := (temp_arg_ (decltype' lang) (Expr' lang)).
Notation atomic_name' lang := (atomic_name_ (type' lang)).

(**
In certain places, C++ requires a class name,
for example, for base classes.
In templates, these names do not have to be resolved, e.g. in CRTP.
<<
template<typename T>
struct Foo : T { };
>>
To support this, [classname lang.temp = type lang.temp]
*)
Definition classname' (lang : lang.t) : Set :=
  match lang with
  | lang.cpp => name' lang
  | lang.temp => type' lang
  end.
#[global] Instance classname_inh {lang} : Inhabited (classname' lang).
Proof. destruct lang; refine _. Qed.

(*
#[global] Instance classname_eq_dec {lang} : EqDecision (classname' lang).
Proof. destruct lang; solve_decision. Defined.
*)



(*
Module Import LangNotations.

  (**
  We cannot use these definitions in our notations _and_ preserve
  those notations after hitting terms with, e.g., <<eval compute>>.
  *)
  #[local] Notation decltype := type (only parsing).
  #[local] Notation exprtype := type (only parsing).
  #[local] Notation obj_name := name (only parsing).
  #[local] Notation globname := name (only parsing).

  (* in core *)
  Notation operator_impl lang := (operator_impl.t (obj_name lang) (type lang)).
  Notation MethodRef lang := (MethodRef' (obj_name lang) (type lang) (Expr lang)).

  Notation function_type lang := (function_type' (decltype lang)).
  Notation function_name lang := (function_name' (type lang)).
  Notation atomic_name lang := (atomic_name' (type lang) (Expr lang)).
(*
  Notation tpreinst lang := (tpreinst' (decltype lang) (Expr lang)).
  Notation tinst lang := (tinst' (decltype lang) (Expr lang)).

  Notation FunctionBody lang := (FunctionBody' (obj_name lang) (decltype lang) (Expr lang)).
  Notation Func lang := (Func' (obj_name lang) (decltype lang) (Expr lang)).
  Notation GlobalInit lang := (GlobalInit' (Expr lang)).
  Notation GlobalInitializer lang := (GlobalInitializer' (obj_name lang) (decltype lang) (Expr lang)).
  Notation InitializerBlock lang := (InitializerBlock' (obj_name lang) (decltype lang) (Expr lang)).
*)
End LangNotations.
*)

(** ** C++ with structured names *)
Notation name := (name' lang.cpp).
Notation globname := (globname' lang.cpp).
Notation obj_name := (obj_name' lang.cpp).
Notation type := (type' lang.cpp).
Notation exprtype := (exprtype' lang.cpp).
Notation decltype := (decltype' lang.cpp).
Notation functype := (functype' lang.cpp).
Notation classname := (classname' lang.cpp).
Notation Cast := (Cast' lang.cpp).
(*Notation operator_impl := (operator_impl' lang.cpp). *)
Notation MethodRef := (MethodRef' lang.cpp).
Notation Expr := (Expr' lang.cpp).
Notation function_type := (function_type' lang.cpp).
Notation VarDecl := (VarDecl' lang.cpp).
Notation BindingDecl := (BindingDecl' lang.cpp).
(*Notation temp_param := (temp_param lang.cpp).
Notation Stemp_arg := (temp_arg lang.cpp). *)
Notation atomic_name := (atomic_name' lang.cpp).


Module field_name.
  Definition t lang := (atomic_name' lang).
  Definition Id {lang} : bs -> t lang := Nid.
  Definition Anon {lang} : _ -> t lang := Nanon.
  Definition CaptureVar {lang} : bs -> t lang := Nid.
  Definition CaptureThis {lang} : t lang := Nid ".this".
End field_name.
Notation field_name := (field_name.t lang.cpp).

(*
#[global] Instance field_name_inh {lang} : Inhabited (field_name.t lang).
Proof. rewrite /field_name.t. refine _. Defined.
#[global] Instance field_name_eq_dec {lang} : EqDecision (field_name.t lang).
Proof. rewrite /field_name.t. refine _. Defined.
#[global] Hint Opaque field_name.t : typeclass_instances.
*)

Notation field' := name' (only parsing).
(* Definition field' lang : Set := name' lang. *)
Definition Field' {lang} : classname' lang -> field_name.t lang -> field' lang :=
  match lang with
  | lang.cpp => Nscoped
  | lang.temp => fun t c =>
    (* NOTE: this [match] implements a canonicalization to avoid
       [Ndependent (Tnamed nm)], instead rewriting it to simply [nm] *)
    match t with
    | Tenum nm
    | Tnamed nm => Nscoped nm c
    | Tparam _ | Tdecltype _ => Nscoped (Ndependent t) c
    | _ => Nunsupported "Field failed"
    end
  end.
Notation field := (field' lang.cpp) (only parsing).
Notation Field := (@Field' lang.cpp).
Definition f_type {lang} (t : field' lang) : globname' lang :=
  match t with
  | Nscoped n _ => n
  | _ => Nunsupported "not a field"
  end.
Definition f_name {lang} (t : field' lang) : atomic_name' lang :=
  match t with
  | Nscoped _ n => n
  | _ => Nunsupported_atomic "not a field"
  end.
#[global] Bind Scope cpp_field_scope with field'.
#[global] Bind Scope cpp_name_scope with name'.
#[global] Bind Scope cpp_name_scope with globname'.
#[global] Bind Scope cpp_name_scope with obj_name'.
#[global] Bind Scope cpp_name_scope with classname'.

(** ** Derived forms *)
Notation Tconst_volatile := (Tqualified QCV).
Notation Tconst := (Tqualified QC).
Notation Tvolatile := (Tqualified QV).
Notation Tmut := (Tqualified QM).
Notation Tmut_volatile := Tvolatile (only parsing).

Notation Tchar := (Tchar_ char_type.Cchar).
Notation Twchar := (Tchar_ char_type.Cwchar).
Notation Tchar8 := (Tchar_ char_type.C8).
Notation Tchar16 := (Tchar_ char_type.C16).
Notation Tchar32 := (Tchar_ char_type.C32).

#[deprecated(since="20240624", note="use [Tschar].")]
Notation Ti8 := (Tnum int_rank.Ichar Signed) (only parsing).
#[deprecated(since="20240624", note="use [Tuchar].")]
Notation Tu8 := (Tnum int_rank.Ichar Unsigned) (only parsing).
#[deprecated(since="20240624", note="use [Tshort].")]
Notation Ti16 := (Tnum int_rank.Ishort Signed) (only parsing).
#[deprecated(since="20240624", note="use [Tushort].")]
Notation Tu16 := (Tnum int_rank.Ishort Unsigned) (only parsing).
#[deprecated(since="20240624", note="use [Tint].")]
Notation Ti32 := (Tnum int_rank.Iint Signed) (only parsing).
#[deprecated(since="20240624", note="use [Tuint].")]
Notation Tu32 := (Tnum int_rank.Iint Unsigned) (only parsing).
#[deprecated(since="20240624", note="use [Tlong] or [Tlonglong].")]
Notation Ti64 := (Tnum int_rank.Ilonglong Signed) (only parsing).
#[deprecated(since="20240624", note="use [Tulong] or [Tulonglong].")]
Notation Tu64 := (Tnum int_rank.Ilonglong Unsigned) (only parsing).
#[deprecated(since="20240624", note="use [Tint128_t].")]
Notation Ti128 := (Tnum int_rank.I128 Signed) (only parsing).
#[deprecated(since="20240624", note="use [Tuint128_t].")]
Notation Tu128 := (Tnum int_rank.I128 Unsigned) (only parsing).

Notation Tschar := (Tnum int_rank.Ichar Signed).
Notation Tuchar := (Tnum int_rank.Ichar Unsigned).

Notation Tushort := (Tnum int_rank.Ishort Unsigned).
Notation Tshort := (Tnum int_rank.Ishort Signed).

Notation Tint := (Tnum int_rank.Iint Signed).
Notation Tuint := (Tnum int_rank.Iint Unsigned).

Notation Tulong := (Tnum int_rank.Ilong Unsigned) (only parsing).
Notation Tlong := (Tnum int_rank.Ilong Signed) (only parsing).

Notation Tulonglong := (Tnum int_rank.Ilonglong Unsigned).
Notation Tlonglong := (Tnum int_rank.Ilonglong Signed).

Notation Tuint128_t := (Tnum int_rank.I128 Unsigned).
Notation Tint128_t := (Tnum int_rank.I128 Signed).

Notation Tfloat16 := (Tfloat_ float_type.Ffloat16).
Notation Tfloat := (Tfloat_ float_type.Ffloat).
Notation Tdouble := (Tfloat_ float_type.Fdouble).
Notation Tlongdouble := (Tfloat_ float_type.Flongdouble).
Notation Tfloat128 := (Tfloat_ float_type.Ffloat128).

(* TODO: This is determined by the compiler. *)
Notation Tsize_t := Tulong (only parsing).
(* NOTE Use [Tbyte] when talking about the offsets for "raw bytes" *)
Notation Tbyte := (Tnum int_rank.Ichar Unsigned) (only parsing).


(** ** Dependent names, types, and terms *)

Fixpoint is_dependentN {lang} (n : name' lang) : bool :=
  match n with
  | Ninst n xs => is_dependentN n || existsb (temp_arg.existsb is_dependentT is_dependentE) xs
  | Nglobal c => atomic_name.existsb is_dependentT c
  | Ndependent t => is_dependentT t
  | Nscoped n c => is_dependentN n || atomic_name.existsb is_dependentT c
  | Nunsupported _ => false
  end

with is_dependentT {lang} (t : type' lang) : bool :=
  match t with
  | Tparam _
  | Tresult_param _
  | Tresult_global _
  | Tresult_unop _ _
  | Tresult_binop _ _ _
  | Tresult_call _ _
  | Tresult_member_call _ _ _
  | Tresult_parenlist _ _ => true
  | Tresult_member _ _ => true
  | Tptr t
  | Tref t
  | Trv_ref t => is_dependentT t
  | Tnum _ _
  | Tchar_ _
  | Tvoid => false
  | Tarray t _
  | Tincomplete_array t => is_dependentT t
  | Tvariable_array t e => is_dependentT t || is_dependentE e
  | Tnamed n
  | Tenum n => is_dependentN n
  | Tfunction ft => function_type.existsb is_dependentT ft
  | Tbool => false
  | Tmember_pointer gn t => is_dependentT gn || is_dependentT t
  | Tfloat_ _ => false
  | Tqualified _ t => is_dependentT t
  | Tnullptr
  | Tarch _ _ => false
  | Tdecltype e => is_dependentE e
  | Texprtype e => is_dependentE e
  | Tunsupported _ => false
  end

with is_dependentE {lang} (e : Expr' lang) : bool :=
  match e with
  | Eparam _
  | Eunresolved_global _
  | Eunresolved_unop _ _
  | Eunresolved_binop _ _ _
  | Eunresolved_call _ _
  | Eunresolved_member_call _ _ _
  | Eunresolved_parenlist _ _
  | Eunresolved_member _ _ => true
  | Evar _ t => is_dependentT t
  | Eenum_const n _ => is_dependentN n
  | Eglobal n t => is_dependentN n || is_dependentT t
  | Eglobal_member n t => is_dependentN n || is_dependentT t
  | Echar _ t
  | Estring _ t
  | Eint _ t => is_dependentT t
  | Ebool _ => false
  | Eunop _ e t => is_dependentE e || is_dependentT t
  | Ebinop _ e1 e2 t => is_dependentE e1 || is_dependentE e2 || is_dependentT t
  | Ederef e t => is_dependentE e || is_dependentT t
  | Eaddrof e => is_dependentE e
  | Eassign e1 e2 t => is_dependentE e1 || is_dependentE e2 || is_dependentT t
  | Eassign_op _ e1 e2 t => is_dependentE e1 || is_dependentE e2 || is_dependentT t
  | Epreinc e t => is_dependentE e || is_dependentT t
  | Epostinc e t => is_dependentE e || is_dependentT t
  | Epredec e t => is_dependentE e || is_dependentT t
  | Epostdec e t => is_dependentE e || is_dependentT t
  | Eseqand e1 e2 => is_dependentE e1 || is_dependentE e2
  | Eseqor e1 e2 => is_dependentE e1 || is_dependentE e2
  | Ecomma e1 e2 => is_dependentE e1 || is_dependentE e2
  | Ecall e es => is_dependentE e || existsb is_dependentE es
  | Eexplicit_cast _ t e => is_dependentE e || is_dependentT t
  | Ecast c e => Cast.existsb is_dependentT c || is_dependentE e
  | Emember _ e f _ t => is_dependentE e || atomic_name.existsb is_dependentT f || is_dependentT t
  | Emember_ignore _ e e' => is_dependentE e || is_dependentE e'
  | Emember_call _ m e es => MethodRef.existsb is_dependentN is_dependentT is_dependentE m || is_dependentE e || existsb is_dependentE es
  | Eoperator_call _ i es => operator_impl.existsb is_dependentN is_dependentT i || existsb is_dependentE es
  | Esubscript e1 e2 t => is_dependentE e1 || is_dependentE e2 || is_dependentT t
  | Esizeof te t
  | Ealignof te t => sum.existsb is_dependentT is_dependentE te || is_dependentT t
  | Eoffsetof gn _ t => is_dependentT gn || is_dependentT t
  | Econstructor n es t => is_dependentN n || existsb is_dependentE es || is_dependentT t
  | Elambda n es => is_dependentN n || existsb is_dependentE es
  | Eimplicit e => is_dependentE e
  | Eimplicit_init t => is_dependentT t
  | Eif e1 e2 e3 t => is_dependentE e1 || is_dependentE e2 || is_dependentE e3 || is_dependentT t
  | Eif2 _ e1 e2 e3 e4 t => is_dependentE e1 || is_dependentE e2 || is_dependentE e3 || is_dependentE e4 || is_dependentT t
  | Ethis t => is_dependentT t
  | Enull => false
  | Einitlist es eo t => existsb is_dependentE es || option.existsb is_dependentE eo || is_dependentT t
  | Einitlist_union f oe t => option.existsb is_dependentE oe || is_dependentT t

  | Enew p es _ t e1 e2 => is_dependentN p.1 || is_dependentT p.2 || existsb is_dependentE es || is_dependentT t || option.existsb is_dependentE e1 || option.existsb is_dependentE e2
  | Edelete _ p e t => is_dependentN p.1 || is_dependentT p.2 || is_dependentE e || is_dependentT t
  | Eandclean e => is_dependentE e
  | Ematerialize_temp e _ => is_dependentE e
  | Eatomic _ es t => existsb is_dependentE es || is_dependentT t
  | Estmt s t => is_dependentS s || is_dependentT t
  | Eva_arg e t => is_dependentE e || is_dependentT t
  | Epseudo_destructor _ t e => is_dependentT t || is_dependentE e
  | Earrayloop_init _ e1 _ _ e2 t => is_dependentE e1 || is_dependentE e2 || is_dependentT t
  | Earrayloop_index _ t => is_dependentT t
  | Eopaque_ref _ t => is_dependentT t
  | Eunsupported _ t => is_dependentT t
  end

with is_dependentVD {lang} (vd : VarDecl' lang) : bool :=
  match vd with
  | Dvar _ t oe => is_dependentT t || option.existsb is_dependentE oe
  | Ddecompose e _ lvd => is_dependentE e || List.existsb is_dependentBD lvd
  | Dinit _ n t oe => is_dependentN n || is_dependentT t || option.existsb is_dependentE oe
  end

with is_dependentBD {lang} (bd : BindingDecl' lang) : bool :=
  match bd with
  | Bvar _ t e
  | Bbind _ t e => is_dependentT t || is_dependentE e
  end

with is_dependentS {lang} (s : Stmt' lang) : bool :=
  match s with
  | Sseq ss => List.existsb is_dependentS ss
  | Sdecl ds => List.existsb is_dependentVD ds
  | Sif ovd e thn els =>
      option.existsb is_dependentVD ovd || is_dependentE e || is_dependentS thn || is_dependentS els
  | Sif_consteval thn els =>
      is_dependentS thn || is_dependentS els
  | Swhile ovd e b =>
      option.existsb is_dependentVD ovd || is_dependentE e || is_dependentS b
  | Sfor os oe1 oe2 s =>
      option.existsb is_dependentS os || option.existsb is_dependentE oe1 || option.existsb is_dependentE oe2 || is_dependentS s
  | Sdo b t => is_dependentS b || is_dependentE t
  | Sswitch ovd e s =>
      option.existsb is_dependentVD ovd || is_dependentE e || is_dependentS s
  | Scase _
  | Sdefault
  | Sbreak
  | Scontinue => false
  | Sreturn oe => option.existsb is_dependentE oe
  | Sexpr e => is_dependentE e
  | Sattr _ s => is_dependentS s
  | Sasm _ _ ins outs _ =>
      List.existsb (is_dependentE ∘ snd) ins || List.existsb (is_dependentE ∘ snd) outs
  | Slabeled _ s => is_dependentS s
  | Sgoto _ => false
  | Sunsupported _ => false
  end.
