(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
From bedrock.lang.cpp.syntax Require Import names types.

Set Primitive Projections.

(** Overloadable operators *)
Variant OverloadableOperator : Set :=
  (* Unary operators *)
  | OOTilde | OOExclaim
  | OOPlusPlus | OOMinusMinus
  (* Unary & Binary operators *)
  | OOStar | OOPlus | OOMinus
  (* Binary operators *)
  | OOSlash | OOPercent
  | OOCaret | OOAmp | OOPipe | OOEqual (* = *)
  | OOLessLess | OOGreaterGreater
  | OOPlusEqual | OOMinusEqual | OOStarEqual
  | OOSlashEqual | OOPercentEqual | OOCaretEqual | OOAmpEqual
  | OOPipeEqual  | OOLessLessEqual | OOGreaterGreaterEqual
  | OOEqualEqual | OOExclaimEqual
  | OOLess | OOGreater
  | OOLessEqual | OOGreaterEqual | OOSpaceship
  | OOComma
  | OOArrowStar | OOArrow
  | OOSubscript
  (* short-circuiting *)
  | OOAmpAmp | OOPipePipe
  (* n-ary *)
  | OONew (array : bool) | OODelete (array : bool) | OOCall
  | OOCoawait (* | Conditional *)
.
#[global] Instance: EqDecision OverloadableOperator := ltac:(solve_decision).

Module evaluation_order.
  Variant t : Set :=
  | nd (* fully non-deterministic *)
  | l_nd (* left then non-deterministic, calls.
            We use this for left-to-right *binary* operators *)
  | rl (* right-to-left, assignment operators (post C++17) *).

  (* The order of evaluation for each operator *when overloaded* *)
  Definition order_of (oo : OverloadableOperator) : t :=
    match oo with
    | OOTilde | OOExclaim => nd
    | OOPlusPlus | OOMinusMinus =>
      (* The evaluation order only matters for operator calls. For those, these
         are unary operators with a possible [Eint 0] as a second argument (to
         distinguish post-fix). The implicit argument is *always* a constant
         integer, so nothing is needed *)
      l_nd
    | OOStar => nd (* multiplication or deref *)
    | OOArrow => nd (* deref *)

    (* binary operators *)
    | OOPlus | OOMinus | OOSlash | OOPercent
    | OOCaret | OOAmp | OOPipe => nd

    (* shift operators are sequenced left-to-right: https://eel.is/c++draft/expr.shift#4. *)
    | OOLessLess | OOGreaterGreater => l_nd
    (* Assignment operators -- ordered right-to-left*)
    | OOEqual
    | OOPlusEqual  | OOMinusEqual | OOStarEqual
    | OOSlashEqual | OOPercentEqual | OOCaretEqual | OOAmpEqual
    | OOPipeEqual  | OOLessLessEqual | OOGreaterGreaterEqual => rl
    (* Comparison operators -- non-deterministic *)
    | OOEqualEqual | OOExclaimEqual
    | OOLess | OOGreater
    | OOLessEqual | OOGreaterEqual
    | OOSpaceship => nd

    | OOComma => l_nd (* http://eel.is/c++draft/expr.compound#expr.comma-1 *)
    | OOArrowStar => l_nd  (* left-to-right: http://eel.is/c++draft/expr.mptr.oper#4*)

    | OOSubscript => l_nd
    (* ^^ for primitives, the order is determined by the types, but when overloading
       the "object" is always on the left. http://eel.is/c++draft/expr.sub#1 *)

    (* Short circuiting *)
    | OOAmpAmp | OOPipePipe => l_nd
    (* ^^ for primitives, the evaluation is based on short-circuiting, but when
       overloading it is left-to-right. <http://eel.is/c++draft/expr.log.and#1>
       and <http://eel.is/c++draft/expr.log.and#1> *)

    | OOCall => l_nd
    (* ^^ post-C++17, the evaluation order for calls is the function first and then the
       arguments, sequenced non-deterministically. This holds for <<f(x)>> as well as
       <<(f.*foo)(x)>> (where <<(f.*foo)>> is sequenced before the evaluation of <<x>> *)
    | OONew _ | OODelete _ | OOCoawait => nd
    end.
End evaluation_order.


Variant UnOp : Set :=
| Uminus	(* - *)
| Uplus	(* + *)
| Unot	(* ! *)
| Ubnot	(* ~ *)
| Uunsupported (_ : bs).
#[global] Instance: EqDecision UnOp.
Proof. solve_decision. Defined.
#[global] Instance UnOp_countable : Countable UnOp.
Proof.
  apply (inj_countable' (fun op =>
    match op with
    | Uminus => GenNode 0 []
    | Uplus => GenNode 1 []
    | Unot => GenNode 2 []
    | Ubnot => GenNode 3 []
    | Uunsupported op => GenNode 4 [GenLeaf op]
    end) (fun t =>
    match t with
    | GenNode 0 [] => Uminus
    | GenNode 1 [] => Uplus
    | GenNode 2 [] => Unot
    | GenNode 3 [] => Ubnot
    | GenNode 4 [GenLeaf op] => Uunsupported op
    | _ => Uminus	(* dummy *)
    end)).
  abstract (by intros []).
Defined.

Variant BinOp : Set :=
| Badd	(* + *)
| Band	(* & *)
| Bcmp	(* <=> *)
| Bdiv	(* / *)
| Beq	(* == *)
| Bge	(* >= *)
| Bgt	(* > *)
| Ble	(* <= *)
| Blt	(* < *)
| Bmul	(* * *)
| Bneq	(* != *)
| Bor	(* | *)
| Bmod	(* % *)
| Bshl	(* << *)
| Bshr	(* >> *)
| Bsub	(* - *)
| Bxor	(* ^ *)
| Bdotp	(* .* *)
| Bdotip	(* ->* *)
| Bunsupported (_ : bs).
#[global] Instance: EqDecision BinOp.
Proof. solve_decision. Defined.
#[global] Instance BinOp_countable : Countable BinOp.
Proof.
  apply (inj_countable' (fun op =>
    match op with
    | Badd => GenNode 0 []
    | Band => GenNode 1 []
    | Bcmp => GenNode 2 []
    | Bdiv => GenNode 3 []
    | Beq => GenNode 4 []
    | Bge => GenNode 5 []
    | Bgt => GenNode 6 []
    | Ble => GenNode 7 []
    | Blt => GenNode 8 []
    | Bmul => GenNode 9 []
    | Bneq => GenNode 10 []
    | Bor => GenNode 11 []
    | Bmod => GenNode 12 []
    | Bshl => GenNode 13 []
    | Bshr => GenNode 14 []
    | Bsub => GenNode 15 []
    | Bxor => GenNode 16 []
    | Bdotp => GenNode 17 []
    | Bdotip => GenNode 18 []
    | Bunsupported op => GenNode 19 [GenLeaf op]
    end) (fun t =>
    match t with
    | GenNode 0 [] => Badd
    | GenNode 1 [] => Band
    | GenNode 2 [] => Bcmp
    | GenNode 3 [] => Bdiv
    | GenNode 4 [] => Beq
    | GenNode 5 [] => Bge
    | GenNode 6 [] => Bgt
    | GenNode 7 [] => Ble
    | GenNode 8 [] => Blt
    | GenNode 9 [] => Bmul
    | GenNode 10 [] => Bneq
    | GenNode 11 [] => Bor
    | GenNode 12 [] => Bmod
    | GenNode 13 [] => Bshl
    | GenNode 14 [] => Bshr
    | GenNode 15 [] => Bsub
    | GenNode 16 [] => Bxor
    | GenNode 17 [] => Bdotp
    | GenNode 18 [] => Bdotip
    | GenNode 19 [GenLeaf op] => Bunsupported op
    | _ => Badd	(* dummy *)
    end)).
  abstract (by intros []).
Defined.

Variant AtomicOp : Set :=
| AO__atomic_load
| AO__atomic_load_n
| AO__atomic_store
| AO__atomic_store_n
| AO__atomic_compare_exchange
| AO__atomic_compare_exchange_n
| AO__atomic_exchange
| AO__atomic_exchange_n
| AO__atomic_fetch_add
| AO__atomic_fetch_sub
| AO__atomic_fetch_and
| AO__atomic_fetch_or
| AO__atomic_fetch_xor
| AO__atomic_fetch_nand
| AO__atomic_add_fetch
| AO__atomic_sub_fetch
| AO__atomic_and_fetch
| AO__atomic_or_fetch
| AO__atomic_xor_fetch
| AO__atomic_nand_fetch
.
#[global] Instance: EqDecision AtomicOp.
Proof. solve_decision. Defined.

Variant BuiltinFn : Set :=
| Bin_alloca
| Bin_alloca_with_align
| Bin_launder
| Bin_expect
| Bin_unreachable
| Bin_trap
| Bin_bswap16
| Bin_bswap32
| Bin_bswap64
| Bin_bswap128
| Bin_bzero
| Bin_ffs
| Bin_ffsl
| Bin_ffsll
| Bin_clz
| Bin_clzl
| Bin_clzll
| Bin_ctz
| Bin_ctzl
| Bin_ctzll
| Bin_popcount
| Bin_popcountl
| Bin_unknown (_ : bs)
.
#[global] Instance: EqDecision BuiltinFn.
Proof. solve_decision. Defined.

(** * Casts *)
Inductive Cast' {type : Set} : Set :=
| Cdependent (* this doesn't have any semantics *)
| Cbitcast	(** TODO (FM-3431): This explicit cast expression could carry the type as written *)
| Clvaluebitcast	(** TODO (FM-3431): Drop this constructor? *)
| Cl2r
| Cnoop
| Carray2ptr
| Cfun2ptr
| Cint2ptr
| Cptr2int
| Cptr2bool
  (* in [Cderived2base] and [Cbase2derived], the list is a tree
     from (top..bottom], i.e. **in both cases** the most derived
     class is not included in the list and the base class is at
     the end of the list. For example, with
     ```c++
     class A {};
     class B : public A {};
     class C : public B {};
     ```
     A cast from `C` to `A` will be [Cderived2base ["::B";"::A"]] and
       the "::C" comes from the type of the sub-expression.
     A cast from `A` to `C` will be [Cbase2derived ["::B";"::A"]] and
       the "::C" comes form the type of the expression.
   *)
| Cderived2base (_ : list globname)
| Cbase2derived (_ : list globname)
| Cintegral
| Cint2bool
| Cfloat2int
| Cnull2ptr
| Cbuiltin2fun
| Cctor
| C2void
| Cuser        (conversion_function : obj_name)	(** TODO (FM-3431): Consider just emitting the method call *)
| Creinterpret (_ : type)
| Cstatic      (_ : Cast')
| Cdynamic     (from to : globname)
| Cconst       (_ : type).
#[global] Arguments Cast' _ : clear implicits, assert.
(**
TODO (FM-3431): For the explicit casts, we could embed the type as
written and compute the value category (rather than annote `Ecast`
with a value category).
*)
#[global] Instance Cast_eq_dec {type : Set} `{!EqDecision type} : EqDecision (Cast' type).
Proof. solve_decision. Defined.
Notation Cast := (Cast' exprtype).	(** TODO (FM-3431): Should be [decltype] *)

(** * References *)
Variant VarRef : Set :=
| Lname (_ : localname)
| Gname (_ : globname).
#[global] Instance: EqDecision VarRef.
Proof. solve_decision. Defined.

Variant dispatch_type : Set := Virtual | Direct.
#[global] Instance: EqDecision dispatch_type.
Proof. solve_decision. Defined.
#[deprecated(since="20230716",note="use [dispatch_type]")]
Notation call_type := dispatch_type (only parsing).

(** Base value categories as of C++11. *)
Variant ValCat : Set := Lvalue | Prvalue | Xvalue.
#[global] Instance: EqDecision ValCat.
Proof. solve_decision. Defined.
#[global] Instance ValCat_countable : Countable ValCat.
Proof.
  apply (inj_countable
    (fun vc => match vc with Lvalue => 1 | Prvalue => 2 | Xvalue => 3 end)
    (fun n =>
    match n with
    | 1 => Some Lvalue
    | 2 => Some Prvalue
    | 3 => Some Xvalue
    | _ => None
    end)
  )%positive.
  abstract (by intros []).
Defined.

Variant OffsetInfo : Set :=
  | Oo_Field (_ : field).
#[global] Instance: EqDecision OffsetInfo.
Proof. solve_decision. Defined.

Module operator_impl.
  Variant t {type : Set} : Set :=
    | Func (fn_name : obj_name) (fn_type : type)
    | MFunc (fn_name : obj_name) (_ : dispatch_type) (fn_type : type).
  #[global] Arguments t _ : clear implicits.

  #[global] Instance: forall (type : Set), EqDecision type -> EqDecision (t type) :=
    ltac:(solve_decision).
End operator_impl.
#[global] Notation operator_impl := (operator_impl.t functype).

Inductive Expr : Set :=
| Econst_ref (_ : VarRef) (_ : exprtype)
  (* ^ these are different because they do not have addresses *)
| Evar     (_ : VarRef) (ty : decltype)
  (* ^ local and global variable reference
       [ty] is the declaration type of the variable *)

| Echar    (value : N) (_ : exprtype)
  (* ^ [value] is the unsigned character value *)
| Estring  (values : list N) (ty : exprtype) (* type = Tarray (const ty) (lengthN values) *)
  (* ^ [values] is a list of *characters*, e.g. if [ty] is a 2-byte
     character type, then each [N] in [values] represents 2 bytes. *)
| Eint     (_ : Z) (_ : exprtype)
| Ebool    (_ : bool)
  (* ^ literals *)

| Eunop    (_ : UnOp) (_ : Expr) (_ : exprtype)
| Ebinop   (_ : BinOp) (_ _ : Expr) (_ : exprtype)
 (* ^ note(gmm): overloaded operators are already resolved. so an overloaded
  * operator shows up as a function call, not a `Eunop` or `Ebinop`.
  * this includes the assignment operator for classes.
  *)
| Ederef (e : Expr) (_ : exprtype) (* XXX type = strip [Tptr] from [type_of e] *)
| Eaddrof (e : Expr) (* type = Tptr (type_of e) *)
| Eassign (e _ : Expr) (_ : exprtype) (* XXX type = type_of e *)
| Eassign_op (_ : BinOp) (e _ : Expr) (_ : exprtype) (* XXX = type_of e *)
  (* ^ these are specialized because they are common *)

| Epreinc (_ : Expr) (_ : exprtype)
| Epostinc (_ : Expr) (_ : exprtype)
| Epredec (_ : Expr) (_ : exprtype)
| Epostdec (_ : Expr) (_ : exprtype)
  (* ^ special unary operators *)

| Eseqand (_ _ : Expr) (* type = Tbool *)
| Eseqor  (_ _ : Expr) (* type = Tbool *)
| Ecomma (e1 e2 : Expr) (* type = type_of e2 *)
  (* ^ these are specialized because they have special control flow semantics *)

| Ecall    (_ : Expr) (_ : list Expr) (_ : exprtype)
| Ecast    (_ : Cast) (e : Expr) (_ : ValCat) (_ : exprtype)

| Emember  (obj : Expr) (_ : ident) (mut : bool) (ty : decltype)
  (* ^ [ty] is the type of the member, [mut] is the mutability *)
  (* TODO: maybe replace the left branch use [Expr] here? *)
| Emember_call (method : (obj_name * dispatch_type * functype) + Expr) (obj : Expr) (_ : list Expr) (_ : exprtype)

| Eoperator_call (_ : OverloadableOperator) (_ : operator_impl) (ls : list Expr) (_ : exprtype)
  (* ^^ in the case of a [Mfunc], [ls] is non-empty and the first expression is the object *)

| Esubscript (_ : Expr) (_ : Expr) (_ : exprtype)
| Esizeof (_ : decltype + Expr) (_ : exprtype)
| Ealignof (_ : decltype + Expr) (_ : exprtype)
| Eoffsetof (_ : OffsetInfo) (_ : exprtype)
| Econstructor (_ : obj_name) (_ : list Expr) (_ : exprtype)
| Eimplicit (_ : Expr)
| Eimplicit_init (_ : exprtype)
| Eif       (_ _ _ : Expr) (_ : ValCat) (_ : exprtype)
| Eif2  (name : N) (common cond thn els : Expr) (_ : ValCat) (_ : exprtype)

| Ethis (_ : exprtype)
| Enull
| Einitlist (_ : list Expr) (_ : option Expr) (_ : exprtype)

| Enew (new_fn : obj_name * functype) (new_args : list Expr)
       (alloc_ty : exprtype)
       (array_size : option Expr) (init : option Expr) (* type = Tptr alloc_ty *)
| Edelete (is_array : bool) (del_fn : obj_name * functype)
          (* When [deleted_type] is a class with a [virtual] destructor and the
             most derived class has an [operator delete], [del_fn] will be
             ignored. *)
          (arg : Expr) (deleted_type : decltype) (* type = Tvoid *)

| Eandclean (_ : Expr)
| Ematerialize_temp (_ : Expr) (_ : ValCat)

| Eatomic (_ : AtomicOp) (_ : list Expr) (_ : exprtype)
| Eva_arg (_ : Expr) (_ : exprtype)
| Epseudo_destructor (_ : decltype) (_ : Expr)

| Earrayloop_init (oname : N) (src : Expr) (level : N) (length : N) (init : Expr) (_ : exprtype)
| Earrayloop_index (level : N) (_ : exprtype)
| Eopaque_ref (name : N) (_ : ValCat) (_ : exprtype)
| Eunsupported (_ : bs) (_ : ValCat) (_ : exprtype)
.
Notation MethodRef := ((obj_name * dispatch_type * functype) + Expr)%type (only parsing).

#[global] Instance expr_inhabited : Inhabited Expr.
Proof. exact (populate Enull). Qed.

#[global] Instance Expr_eq_dec : EqDecision Expr.
Proof.
  rewrite /RelDecision /Decision.
  fix IHe 1.
  rewrite -{1}/(EqDecision Expr) in IHe.
  decide equality; try solve_trivial_decision.
Defined.

Definition Edefault_init_expr (e : Expr) : Expr := e.
