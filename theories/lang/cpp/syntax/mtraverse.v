(*
 * Copyright (c) 2023-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.syntax.prelude.
Require Import bedrock.lang.cpp.syntax.core.
Require Export bedrock.lang.cpp.syntax.handler.
Require Import bedrock.lang.cpp.syntax.decl.
Require Import bedrock.lang.cpp.syntax.translation_unit.

Import UPoly.

#[local] Set Printing Implicit.

#[local] Set Universe Polymorphism.
#[local] Set Polymorphic Inductive Cumulativity.
#[local] Unset Auto Template Polymorphism.
#[local] Unset Universe Minimization ToSet.

(* We factor a traversal of the abstract syntax tree in order
   to reduce duplication between a variety of traversals that
   occur on the syntax.
 *)


(* TODO (upstream): lift these definitions *)
Module prod.
  Definition fmap {A B A' B' : Set} (f : A -> B) (g : A' -> B') (p : A * A') : B * B' :=
    (f p.1, g p.2).
  #[global] Arguments fmap _ _ _ _ _ _ & _ : assert.
  #[global] Hint Opaque fmap : typeclass_instances.

  #[universes(polymorphic)]
  Definition traverse@{u | } {F : Set -> Type@{u}} `{!FMap F, !MRet F, AP : !Ap F}
      {A B A' B' : Set} (f : A -> F B) (g : A' -> F B') (p : prod A A') : F (prod B B') :=
    pair <$> f p.1 <*> g p.2.
  #[global] Arguments traverse _ _ _ _ _ _ _ _ _ & _ _ : assert.
  #[global] Hint Opaque traverse : typeclass_instances.
End prod.

Section option.
  Universes u1 u2 uA uB.
  Constraint u1 <= u2 , uA <= u1 , uB <= u1.
  Constraint uA <= option.u0 , uB <= option.u0.

  Context {F : Type@{u1} -> Type@{u2}}.
  Context `{!FMap@{u1 u2 uB} F}.
  Context `{!MRet F, !MFail F}.
  Context `{AP : !Ap@{u1 u2 uA uB} F}.

  Definition option_traverse2@{uC | uC <= uA , uC <= uB}
      {A : Type@{uA}} {B : Type@{uB}} {C : Type@{uC}}
      (f : A -> B -> F C) :=
    fix option_traverse2 (xs : option A) (ys : option B) : F (option C) :=
      match xs , ys with
      | None , None => mret None
      | Some x , Some y => Some <$> f x y
      | _ , _ => mfail
      end.

  Definition option_iter2@{} {A : Type@{uA}} {B : Type@{uB}} (f : A -> B -> F unit) :=
    fix option_iter2 (xs : option A) (ys : option B) : F unit :=
      match xs , ys with
      | None , None => mret ()
      | Some x , Some y => const1 () <$> f x y
      | _ , _ => mfail
      end.
End option.

Section list.
  Universes u1 u2 uA uB.
  Constraint u1 <= u2 , uA <= u1 , uB <= u1.
  Constraint uA <= list.u0 , uB <= list.u0.

  Context {F : Type@{u1} -> Type@{u2}}.
  Context `{!FMap@{u1 u2 uB} F}.
  Context `{!MRet F, !MFail F}.
  Context `{AP : !Ap@{u1 u2 uA uB} F}.

  Definition list_traverse2@{uC | uC <= uA , uC <= uB}
      {A : Type@{uA}} {B : Type@{uB}} {C : Type@{uC}}
      (f : A -> B -> F C) :=
    fix list_traverse2 (xs : list A) (ys : list B) : F (list C) :=
      match xs , ys with
      | nil , nil => mret nil
      | x :: xs , y :: ys => cons <$> f x y <*> list_traverse2 xs ys
      | _ , _ => mfail
      end.

  Definition list_iter2@{} {A : Type@{uA}} {B : Type@{uB}} (f : A -> B -> F unit) :=
    fix list_iter2 (xs : list A) (ys : list B) : F unit :=
      match xs , ys with
      | nil , nil => mret ()
      | x :: xs , y :: ys => const2 () <$> f x y <*> list_iter2 xs ys
      | _ , _ => mfail
      end.

  Definition list_iter3@{uC | uC <= list.u0 }
      {A : Type@{uA}} {B : Type@{uB}} {C : Type@{uC}}
      (f : A -> B -> C -> F unit) :=
    fix list_iter3 (xs : list A) (ys : list B) (zs : list C) : F unit :=
      match xs , ys , zs with
      | nil , nil , nil => mret ()
      | x :: xs , y :: ys , z :: zs => const2 () <$> f x y z <*> list_iter3 xs ys zs
      | _ , _ , _ => mfail
      end.
End list.

Definition alterF {K A M : Type} `{!Lookup K A M, !PartialAlter K A M}
    {F : Type -> Type} `{!FMap F}
    (f : option A -> F (option A)) (k : K) (m : M) : F M :=
  match m !! k with
  | None =>
    (
      fun v =>
      match v with
      | None => m
      | Some v => partial_alter (fun _ => Some v) k m
      end
    ) <$> f None
  | Some cur =>
    (fun x => partial_alter (fun _ => x) k m) <$> f (Some cur)
  end.

(** * Traversals on template language syntax *)

Module MTraverse.

  Section traverse.
    Universe u.
    Context {F : Set -> Type@{u}}.
    Context `{!UPoly.FMap F, !UPoly.MRet F, !UPoly.MBind F, AP : !UPoly.Ap F}.
    Context {lang1 lang2 : lang.t}.
    Context (hT : type_handler lang1 lang2 F).
    Context (hE : expr_handler lang1 lang2 F).

    #[local] Notation ET := (hE.(handle_expr_type)) (only parsing).

    Fixpoint traverseN (n : name' lang1) : F (name' lang2) :=
      match n with
      | Ninst n xs => Ninst <$> traverseN n <*> traverse (T:=eta list) (temp_arg.traverse traverseT traverseE) xs
      | Nglobal c => Nglobal <$> atomic_name.traverse traverseT c
      | Ndependent t => Ndependent <$> traverseT t
      | Nscoped n c => Nscoped <$> traverseN n <*> atomic_name.traverse traverseT c
      | Nunsupported msg => mret $ Nunsupported msg
      end

    with traverseT (t : type' lang1) : F (type' lang2) :=
      match t with
      | Tparam T => hT.(handle_Tparam) T
      | Tresult_param X => hT.(handle_Tresult_param) X
      | Tresult_global on => hT.(handle_Tresult_global) on (fun _ => traverseN on)
      | Tresult_unop o t => hT.(handle_Tresult_unop) o t (fun _ => traverseT t)
      | Tresult_binop o l r => hT.(handle_Tresult_binop) o l r (fun _ => traverseT l) (fun _ => traverseT r)
      | Tresult_call on ts => hT.(handle_Tresult_call) on ts (fun _ => traverseN on) (fun _ => traverseT <$> ts)
      | Tresult_member_call on o ts => hT.(handle_Tresult_member_call) on o ts (fun _ => traverseN on) (fun _ => traverseT o) (fun _ => traverseT <$> ts)
      | Tresult_parenlist t ts => hT.(handle_Tresult_parenlist) t ts (fun _ => traverseT t) (fun _ => traverseT <$> ts)
      | Tresult_member o id => hT.(handle_Tresult_member) o id (fun _ => traverseT o)
      | Tnamed gn => hT.(handle_Tnamed) gn (fun _ => traverseN gn)
      | Tref t => hT.(handle_Tref) t (fun _ => traverseT t)
      | Trv_ref t => hT.(handle_Trv_ref) t (fun _ => traverseT t)
      | Tqualified cv t => hT.(handle_Tqualified) cv t (fun _ => traverseT t)

      (**
      Everything else is structural
      *)

      | Tptr t => Tptr <$> traverseT t
      | Tnum sz sgn => mret $ Tnum sz sgn
      | Tchar_ t => mret $ Tchar_ t
      | Tvoid => mret Tvoid
      | Tarray t n => Tarray <$> traverseT t <*> mret n
      | Tincomplete_array t => Tincomplete_array <$> traverseT t
      | Tvariable_array t e => Tvariable_array <$> traverseT t <*> traverseE e
      | Tenum gn => Tenum <$> traverseN gn
      | Tfunction ft => Tfunction <$> function_type.traverse traverseT ft
      | Tbool => mret Tbool
      | Tmember_pointer gn t => Tmember_pointer <$> traverseT gn <*> traverseT t
      | Tfloat_ t => mret $ Tfloat_ t
      | Tnullptr => mret Tnullptr
      | Tarch sz t => mret $ Tarch sz t
      | Tdecltype e => Tdecltype <$> traverseE e
      | Texprtype e => Texprtype <$> traverseE e
      | Tunsupported msg => mret $ Tunsupported msg
      end

    with traverseE (e : Expr' lang1) : F (Expr' lang2) :=
      match e with
      | Eparam X => hE.(handle_Eparam) X
      | Eunresolved_global on => hE.(handle_Eunresolved_global) on (fun _ => traverseN on)
      | Eunresolved_unop o e => hE.(handle_Eunresolved_unop) o e (fun _ => traverseE e)
      | Eunresolved_binop o l r => hE.(handle_Eunresolved_binop) o l r (fun _ => traverseE l) (fun _ => traverseE r)
      | Eunresolved_call on es => hE.(handle_Eunresolved_call) on es (fun _ => traverseN on) (fun _ => traverseE <$> es)
      | Eunresolved_member_call on e es => hE.(handle_Eunresolved_member_call) on e es (fun _ => traverseN on) (fun _ => traverseE e) (fun _ => traverseE <$> es)
      | Eunresolved_parenlist t es => hE.(handle_Eunresolved_parenlist) t es (fun _ => traverseT <$> t) (fun _ => traverseE <$> es)
      | Eunresolved_member e f => hE.(handle_Eunresolved_member) e f (fun _ => traverseE e)

      (**
      Everything else is structural
      *)

      | Evar v t => Evar v <$> traverseT t
      | Eenum_const gn c => Eenum_const <$> traverseN gn <*> mret c
      | Eglobal on t => Eglobal <$> traverseN on <*> traverseT t
      | Eglobal_member on t => Eglobal_member <$> traverseN on <*> traverseT t

      | Echar c t => Echar c <$> ET (traverseT t)
      | Estring s t => Estring s <$> ET (traverseT t)
      | Eint z t => Eint z <$> ET (traverseT t)
      | Ebool b => mret $ Ebool b
      | Eunop o e t => Eunop o <$> traverseE e <*> ET (traverseT t)
      | Ebinop o e1 e2 t => Ebinop o <$> traverseE e1 <*> traverseE e2 <*> ET (traverseT t)
      | Ederef e t => Ederef <$> traverseE e <*> ET (traverseT t)
      | Eaddrof e => Eaddrof <$> traverseE e
      | Eassign e1 e2 t => Eassign <$> traverseE e1 <*> traverseE e2 <*> ET (traverseT t)
      | Eassign_op o e1 e2 t => Eassign_op o <$> traverseE e1 <*> traverseE e2 <*> ET (traverseT t)
      | Epreinc e t => Epreinc <$> traverseE e <*> ET (traverseT t)
      | Epostinc e t => Epostinc <$> traverseE e <*> ET (traverseT t)
      | Epredec e t => Epredec <$> traverseE e <*> ET (traverseT t)
      | Epostdec e t => Epostdec <$> traverseE e <*> ET (traverseT t)
      | Eseqand e1 e2 => Eseqand <$> traverseE e1 <*> traverseE e2
      | Eseqor e1 e2 => Eseqor <$> traverseE e1 <*> traverseE e2
      | Ecomma e1 e2 => Ecomma <$> traverseE e1 <*> traverseE e2
      | Ecall e es => Ecall <$> traverseE e <*> traverse (T:=eta list) traverseE es
      | Eexplicit_cast s t e => Eexplicit_cast s <$> traverseT t <*> traverseE e

      | Ecast c e => Ecast <$> traverseC c <*> traverseE e
      | Emember arrow e f mut t => Emember arrow <$> traverseE e <*> atomic_name.traverse traverseT f <*> mret mut <*> traverseT t
      | Emember_ignore arrow eobj e => Emember_ignore arrow <$> traverseE eobj <*> traverseE e
      | Emember_call arrow m o es => Emember_call arrow <$> MethodRef.traverse traverseN traverseT traverseE m <*> traverseE o <*> traverse (T:=eta list) traverseE es
      | Eoperator_call oo oi es => Eoperator_call oo <$> operator_impl.traverse traverseN traverseT oi <*> traverse (T:=eta list) traverseE es
      | Esubscript e1 e2 t => Esubscript <$> traverseE e1 <*> traverseE e2 <*> ET (traverseT t)
      | Esizeof et t => Esizeof <$> sum_traverse traverseT traverseE et <*> ET (traverseT t)
      | Ealignof et t => Ealignof <$> sum_traverse traverseT traverseE et <*> ET (traverseT t)
      | Eoffsetof gn f t => Eoffsetof <$> traverseT gn <*> mret f <*> ET (traverseT t)
      | Econstructor n es t => Econstructor <$> traverseN n <*> traverse (T:=eta list) traverseE es <*> ET (traverseT t)
      | Elambda n es => Elambda <$> traverseN n <*> traverse (T:=eta list) traverseE es

      | Eimplicit e => Eimplicit <$> traverseE e
      | Eimplicit_init t => Eimplicit_init <$> ET (traverseT t)
      | Eif a b c t => Eif <$> traverseE a <*> traverseE b <*> traverseE c <*> traverseT t
      | Eif2 n a b c d t => Eif2 n <$> traverseE a <*> traverseE b <*> traverseE c <*> traverseE d <*> traverseT t
      | Ethis t => Ethis <$> ET (traverseT t)
      | Enull => mret Enull
      | Einitlist es oe t =>
          Einitlist <$> traverse (T:=eta list) traverseE es <*> traverse (T:=eta option) traverseE oe <*> ET (traverseT t)
      | Einitlist_union fld oe t =>
          Einitlist_union <$> atomic_name.traverse traverseT fld <*> traverse (T:=eta option) traverseE oe <*> ET (traverseT t)

      | Enew fn es pass_align t sz init => Enew <$> prod.traverse traverseN traverseT fn <*> traverse (T:=eta list) traverseE es <*> mret pass_align <*> traverseT t <*> traverse (T:=eta option) traverseE sz <*> traverse (T:=eta option) traverseE init
      | Edelete a fn e t => Edelete a <$> prod.traverse traverseN traverseT fn <*> traverseE e <*> traverseT t
      | Eandclean e => Eandclean <$> traverseE e
      | Ematerialize_temp e vc => Ematerialize_temp <$> traverseE e <*> mret vc
      | Eatomic ao es t => Eatomic ao <$> traverse (T:=eta list) traverseE es <*> ET (traverseT t)
      | Estmt s t => Estmt <$> traverseS s <*> traverseT t
      | Eva_arg e t =>
          (**
        TODO: [Eva_arg] takes a declaration type while [expr.Eva_arg]
        takes an expression type.
        *)
        Eva_arg <$> traverseE e <*> ET (traverseT t)
      | Epseudo_destructor arrow dt e => Epseudo_destructor arrow <$> traverseT dt <*> traverseE e
      | Earrayloop_init n e1 from to e2 t => Earrayloop_init n <$> traverseE e1 <*> mret from <*> mret to <*> traverseE e2 <*> ET (traverseT t)
      | Earrayloop_index n t => Earrayloop_index n <$> ET (traverseT t)
      | Eopaque_ref n t => Eopaque_ref n <$> traverseT t
      | Eunsupported msg t => Eunsupported msg <$> traverseT t
      end

    with traverseD (d : VarDecl' lang1) : F (VarDecl' lang2) :=
      match d with
      | Dvar n t oe =>
          let k := hE.(handle_unresolved_init) t (fun _ => traverseT t) $ (fun e => (e, fun _ => traverseE e)) <$> oe in
          (fun '(t,oe) => Dvar n t oe) <$> k

      | Dinit ts on t oe =>
          let k := hE.(handle_unresolved_init) t (fun _ => traverseT t) $ (fun e => (e, fun _ => traverseE e)) <$> oe in
          (fun n '(t,oe) => Dinit ts n t oe) <$> traverseN on <*> k

      | Ddecompose e id ds =>
          Ddecompose <$> traverseE e <*> mret id
            <*> traverse (T:=eta list) traverseB ds
      end

    with traverseB (d : BindingDecl' lang1) : F (BindingDecl' lang2) :=
      match d with
      | Bvar n t e =>
          Bvar n <$> traverseT t <*> traverseE e
      | Bbind n t e =>
          Bbind n <$> traverseT t <*> traverseE e
      end

    with traverseS (s : Stmt' lang1) : F (Stmt' lang2) :=
      match s with
      | Sseq ss => Sseq <$> traverse (T:=eta list) traverseS ss
      | Sdecl ds => Sdecl <$> traverse (T:=eta list) traverseD ds
      | Sif d e sif selse => Sif <$> traverse (T:=eta option) traverseD d <*> traverseE e <*> traverseS sif <*> traverseS selse
      | Swhile d e s => Swhile <$> traverse (T:=eta option) traverseD d <*> traverseE e <*> traverseS s
      | Sfor i g c s => Sfor <$> traverse (T:=eta option) traverseS i <*> traverse (T:=eta option) traverseE g <*> traverse (T:=eta option) traverseE c <*> traverseS s
      | Sdo s e => Sdo <$> traverseS s <*> traverseE e
      | Sswitch d e s => Sswitch <$> traverse (T:=eta option) traverseD d <*> traverseE e <*> traverseS s
      | Scase br => mret $ Scase br
      | Sdefault => mret Sdefault
      | Sbreak => mret Sbreak
      | Scontinue => mret Scontinue
      | Sreturn e => Sreturn <$> traverse (T:=eta option) traverseE e
      | Sexpr e => Sexpr <$> traverseE e
      | Sattr a s => Sattr a <$> traverseS s
      | Sasm code v i o c => Sasm code v <$> traverse (T:=eta list) (fun '(a,b) => pair a <$> traverseE b) i
                                        <*> traverse (T:=eta list) (fun '(a,b) => pair a <$> traverseE b) o <*> mret c
      | Slabeled l s => Slabeled l <$> traverseS s
      | Sgoto id => mret $ Sgoto id
      | Sunsupported msg => mret $ Sunsupported msg
      end

    with traverseC (c : Cast' lang1) : F (Cast' lang2) :=
      match c with
      (**
      TODO (FM-4319): Does <<Cdependent>> have something to do with
      clang's notion of dependent types? If so, we must take more care.
      *)
      | Cdependent t => Cdependent <$> traverseT t
      | Cbitcast t => Cbitcast <$> traverseT t
      | Clvaluebitcast t => Clvaluebitcast <$> traverseT t
      | Cl2r => mret Cl2r
      | Cnoop t => Cnoop <$> traverseT t
      | Carray2ptr => mret Carray2ptr
      | Cfun2ptr => mret Cfun2ptr
      | Cint2ptr t => Cint2ptr <$> traverseT t
      | Cptr2int t => Cptr2int <$> traverseT t
      | Cptr2bool => mret Cptr2bool
      | Cderived2base path t => Cderived2base <$> traverse (T:=eta list) traverseT path <*> traverseT t
      | Cbase2derived path t => Cbase2derived <$> traverse (T:=eta list) traverseT path <*> traverseT t
      | Cintegral t => Cintegral <$> traverseT t
      | Cint2bool => mret Cint2bool
      | Cfloat2int t => Cfloat2int <$> traverseT t
      | Cnull2ptr t => Cnull2ptr <$> traverseT t
      | Cnull2memberptr t => Cnull2memberptr <$> traverseT t
      | Cbuiltin2fun t => Cbuiltin2fun <$> traverseT t
      | Cctor t => Cctor <$> traverseT t
      | C2void => mret C2void
      | Cuser => mret Cuser
      | Cdynamic gn => Cdynamic <$> traverseT gn
      end.

    Definition traverseCN : classname' lang1 -> F (classname' lang2) :=
      match lang1 as lang1 , lang2 as lang2
            return (name' lang1 -> F (name' lang2)) ->
                   (type' lang1 -> F (type' lang2)) ->
                   classname' lang1 -> F (classname' lang2)
      with
      | lang.cpp , lang.cpp => fun tN _ => tN
      | lang.temp , lang.temp => fun _ tT => tT
      | lang.cpp , lang.temp => fun tN _ nm => Tnamed <$> tN nm
      | lang.temp , lang.cpp => fun _ tT ty =>
          (fun ty => match ty with
                      | Tnamed nm => nm
                      | _ => Nunsupported "??" (* TODO: this is not implementable, but I don't think we actually use this *)
                      end) <$> tT ty
      end traverseN traverseT.

    Definition mk_core_traversal : core_traversal lang1 lang2 F :=
    {| handle_traverseN := traverseN
     ; handle_traverseT := traverseT
     ; handle_traverseE := traverseE
     ; handle_traverseS := traverseS
     ; handle_classname := traverseCN
     ; handle_traverseE_init ty oe :=
         let oe' :=
           match oe with
           | None => None
           | Some e => Some (e, fun _ => traverseE e)
           end
         in
         hE.(handle_unresolved_init) ty (fun _ => traverseT ty) oe'
     |}.

  End traverse.

  Section traverse.
    Universe u.
    Context {F : Set -> Type@{u}}.
    Context `{!UPoly.FMap F, !UPoly.MRet F, AP : !Ap F}.
    Context {lang1 lang2 : lang.t}.
    Context (hD : core_traversal lang1 lang2 F).

    #[local] Notation traverseN := (hD.(handle_traverseN)).
    #[local] Notation traverseT := (hD.(handle_traverseT)).
    #[local] Notation traverseE := (hD.(handle_traverseE)).
    #[local] Notation traverseS := (hD.(handle_traverseS)).
    #[local] Notation traverseCN := (hD.(handle_classname)).
    #[local] Notation traverseE_init := (hD.(handle_traverseE_init)).

    Definition traverseF_bodyS (f : FunctionBody' lang1) : F (FunctionBody' lang2) :=
      match f with
      | Impl s => Impl <$> traverseS s
      | Builtin f => mret $ Builtin f
      end.

    Definition traverseF (f : Func' lang1) : F (Func' lang2) :=
      Build_Func
        <$> traverseT f.(f_return)
        <*> traverse (T:=eta list) (prod.traverse mret traverseT) f.(f_params)
        <*> mret f.(f_cc) <*> mret f.(f_arity)
        <*> traverse (T:=eta option) traverseF_bodyS f.(f_body).

    Definition traverseM (f : Method' lang1) : F (Method' lang2) :=
      Build_Method <$> traverseT f.(m_return)
                   <*> traverseCN f.(m_class)
                   <*> mret f.(m_this_qual)
                   <*> traverse (T:=eta list) (prod.traverse mret traverseT) f.(m_params)
                   <*> mret f.(m_cc)
                   <*> mret f.(m_arity)
                   <*> traverse (T:=eta option) (traverse (T:=eta OrDefault) traverseS) f.(m_body).

    Definition traverseP (i : InitPath' lang1) : F (InitPath' lang2) :=
      match i with
      | InitBase b => InitBase <$> traverseCN b
      | InitField f =>
          InitField (lang:=lang2) <$> atomic_name.traverse (F:=F) traverseT f
      | InitIndirect path f =>
          let elemF '(a,b) :=
            pair <$> atomic_name.traverse (F:=F) traverseT a <*> traverseCN b
          in
          InitIndirect <$> traverse (F:=F) (T:=eta list) elemF path
            <*> (atomic_name.traverse (F:=F) traverseT f)
      | InitThis => mret (M:=F) $ InitThis (lang:=lang2)
      end.

    Definition traverseI (i : Initializer' lang1) : F (Initializer' lang2) :=
      Build_Initializer <$> traverseP i.(init_path)
                        <*> traverseE i.(init_init).

    Definition traverseCtor (c : Ctor' lang1) : F (Ctor' lang2) :=
      Build_Ctor
        <$> traverseCN c.(c_class)
        <*> traverse (T:=eta list) (traverse (T:=eta (prod _)) traverseT) c.(c_params)
        <*> mret c.(c_cc)
        <*> mret c.(c_arity)
        <*> traverse (T:=eta option) (traverse (T:=eta OrDefault) (prod.traverse (traverse (T:=eta list) traverseI) traverseS)) c.(c_body).

    Definition traverseDtor (d : Dtor' lang1) : F (Dtor' lang2) :=
      Build_Dtor
        <$> traverseCN d.(d_class)
        <*> mret d.(d_cc)
        <*> traverse (T:=eta option) (traverse (T:=eta OrDefault) traverseS) d.(d_body).

    Definition traverseMember (m : Member' lang1) : F (Member' lang2) :=
      mkMember
        <$> atomic_name.traverse traverseT m.(mem_name)
        <*> traverseT m.(mem_type)
        <*> mret m.(mem_mutable)
        <*> traverse (T:=eta option) traverseE m.(mem_init)
        <*> mret m.(mem_layout).

    Definition traverseUnion (u : Union' lang1) : F (Union' lang2) :=
      Build_Union
        <$> traverse (T:=eta list) traverseMember u.(u_fields)
        <*> traverseN u.(u_dtor)
        <*> mret u.(u_trivially_destructible)
        <*> traverse (T:=eta option) traverseN u.(u_delete)
        <*> mret u.(u_size)
        <*> mret u.(u_alignment).

    Definition traverseStruct (s : Struct' lang1) : F (Struct' lang2) :=
      Build_Struct
        <$> traverse (T:=eta list) (prod.traverse traverseCN mret) s.(s_bases)
        <*> traverse (T:=eta list) traverseMember s.(s_fields)
        <*> traverse (T:=eta list) (prod.traverse traverseN (traverse (T:=eta option) traverseN))
               s.(s_virtuals)
        <*> traverse (T:=eta list) (prod.traverse traverseN traverseN) s.(s_overrides)
        <*> traverseN s.(s_dtor)
        <*> mret s.(s_trivially_destructible)
        <*> traverse (T:=eta option) traverseN s.(s_delete)
        <*> mret s.(s_layout)
        <*> mret s.(s_size)
        <*> mret s.(s_alignment).

    Definition traverseGD (gd : GlobDecl' lang1) : F (GlobDecl' lang2) :=
      match gd with
      | Gtype => mret Gtype
      | Gunion u => Gunion <$> traverseUnion u
      | Gstruct s => Gstruct <$> traverseStruct s
      | Genum t ids => Genum <$> traverseT t <*> mret ids
      | Gconstant t oe => Gconstant <$> traverseT t <*> traverse (T:=eta option) traverseE oe
      | Gtypedef t => Gtypedef <$> traverseT t
      end.

  End traverse.

End MTraverse.
