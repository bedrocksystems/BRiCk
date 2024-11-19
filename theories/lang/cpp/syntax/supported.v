Require Import bedrock.prelude.base.
Require Import bedrock.lang.cpp.syntax.core.
Require Import bedrock.lang.cpp.syntax.translation_unit.

Module check.
Section with_monad.


  Definition M := bool.
  Definition op := andb.
  Definition OK : M := true.
  Definition FAIL : M := false.

  #[local] Infix "<+>" := op (at level 30).
  #[local] Notation opt f := (from_option f OK).
  #[local] Notation lst f := (List.forallb f).

  Section with_lang.

    Context {lang : lang.t}.
  Definition function_name (type : type' lang -> M) (fn : function_name' lang) : M :=
    match fn with
    | Nf _ | Nctor | Ndtor | Nop _ | Nop_lit _ => OK
    | Nunsupported_function _ => FAIL
    | Nop_conv t => type t
    end.
  Definition atomic_name (type : type' lang -> M) (an : atomic_name' lang) : M :=
    match an with
    | Nid _ => OK
    | Nfunction _ fn ts => function_name type fn <+> List.forallb type ts
    | Nanon _
    | Nanonymous
    | Nfirst_decl _ | Nfirst_child _ => OK
    | Nunsupported_atomic _ => FAIL
    end.

  Section temp_arg.
    Context (type : type' lang -> M) (expr : Expr' lang -> M).
    Fixpoint temp_arg  (a : temp_arg' lang) : M :=
      match a with
      | Atype t => type t
      | Avalue e => expr e
      | Apack xs => List.forallb temp_arg xs
      | Aunsupported _ => FAIL
      end.
  End temp_arg.

  Fixpoint name (n : name' lang) : M :=
    match n with
    | Ninst n ii => name n <+> lst (temp_arg type expr) ii
    | Nglobal an => atomic_name type an
    | Nscoped n s => name n <+> atomic_name type s
    | Ndependent t => type t
    | Nunsupported _ => FAIL
    end
  with type (t : type' lang) : M :=
    match t with
    | Tunsupported _ => FAIL
    | Tparam _
    | Tresult_param _ => OK
    | Tresult_global n => name n
    | Tresult_unop _ t => type t
    | Tresult_binop _ t1 t2 => type t1 <+> type t2
    | Tresult_call nm ts => name nm <+> lst type ts
    | Tresult_member_call nm t ts => name nm <+> type t <+> lst type ts
    | Tresult_parenlist t ts => type t <+> lst type ts
    | Tresult_member t _ => type t
    | Tptr t | Tref t | Trv_ref t | Tarray t _ | Tincomplete_array t => type t
    | Tnum _ _ | Tchar_ _ | Tvoid | Tbool | Tfloat_ _ | Tnullptr => OK
    | Tvariable_array t e => type t <+> expr e
    | Tfunction (FunctionType t ts) => type t <+> lst type ts
    | Tmember_pointer t1 t2 => type t1 <+> type t2
    | Tqualified _ t => type t
    | Tarch _ _ => OK
    | Tdecltype e | Texprtype e => expr e
    | Tnamed n | Tenum n => name n
    end
  with expr (e : Expr' lang) : M :=
    match e with
    | Evar _ t => type t
    | Eenum_const n _ => name n
    | Eglobal n t | Eglobal_member n t => name n <+> type t
    | Echar _ t | Estring _ t | Eint _ t => type t
    | Ebool _ => OK
    | Eunop _ e t => expr e <+> type t
    | Ebinop _ e1 e2 t => expr e1 <+> type t
    | Ederef e t => expr e <+> type t
    | Eaddrof e => expr e
    | Eassign e1 e2 t | Eassign_op _ e1 e2 t => expr e1 <+> expr e2 <+> type t
    | Epreinc e t | Epostinc e t | Epredec e t | Epostdec e t => expr e <+> type t
    | Eseqand e1 e2 | Eseqor e1 e2 | Ecomma e1 e2 => expr e1 <+> expr e2
    | Ecall e es => expr e <+> lst expr es
    | Eexplicit_cast _ t e => type t <+> expr e
    | Ecast c e => cast c <+> expr e
    | Emember _ e an _ t => expr e <+> atomic_name type an <+> type t
    | Estmt s t => stmt s <+> type t
    | Enull => OK
    | Eopaque_ref _ t => type t
    | Eva_arg e t => expr e <+> type t
    | Eatomic _ es t => lst expr es <+> type t
    | Eandclean e => expr e
    | Ethis t => type t
    | Eif e1 e2 e3 t => expr e1 <+> expr e2 <+> expr e3 <+> type t
    | Eif2 _ e1 e2 e3 e4 t => expr e1 <+> expr e2 <+> expr e3 <+> expr e4 <+> type t
    | Elambda nm es => name nm <+> lst expr es
    | Econstructor nm es t => name nm <+> lst expr es <+> type t
    | Eimplicit e => expr e
    | Eimplicit_init t => type t
    | _ => OK
    end
  with stmt (s : Stmt' lang) : M :=
    match s with
    | Sseq ss => lst stmt ss
    | Sdecl ds => lst var_decl ds
    | Sif ovd e s1 s2 => opt var_decl ovd <+> expr e <+> stmt s1 <+> stmt s2
    | Swhile ovd e s => opt var_decl ovd <+> expr e <+> stmt s
    | Sdo s e => stmt s <+> expr e
    | Sfor os oe1 oe2 s =>
        opt stmt os <+> opt expr oe1 <+> opt expr oe2 <+> stmt s
    | Sswitch ovd e s => opt var_decl ovd <+> expr e <+> stmt s
    | Scase _ => OK
    | Sdefault | Sbreak | Scontinue => OK
    | Sreturn oe => opt expr oe
    | Sexpr e => expr e
    | Sasm _ _ lpe1 lpe2 _ => lst (expr ∘ snd) lpe1 <+> lst (expr ∘ snd) lpe2
    | Sattr _ s => stmt s
    | Slabeled _ s => stmt s
    | Sgoto _ => FAIL
    | Sunsupported _ => FAIL
    end
  with var_decl (v : VarDecl' lang) : M :=
    match v with
    | Dvar _ t oe => type t <+> opt expr oe
    | Ddecompose e _ bds => expr e <+> lst binding_decl bds
    | Dinit _ n t None => name n <+> type t
    | Dinit _ n t (Some e) => name n <+> type t <+> expr e
    end
  with binding_decl (b : BindingDecl' lang) : M :=
    match b with
    | Bvar _ t e => type t <+> expr e
    | Bbind _ t e => type t <+> expr e
    end
  with cast (c : Cast' lang) : M :=
    match c with
    | Cdependent t | Cbitcast t | Clvaluebitcast t | Cnoop t | Cint2ptr t | Cptr2int t
    | Cintegral t | Cfloat2int t
    | Cnull2ptr t | Cnull2memberptr t
    | Cbuiltin2fun t | Cctor t | Cdynamic t => type t
    | Cderived2base ts t | Cbase2derived ts t => lst type ts <+> type t
    | _ => OK
    end.

  Definition function_body (b : FunctionBody' lang) : M :=
    match b with
    | Impl s => stmt s
    | Builtin _ => OK
    end.
  Definition or_default {T : Set} (f : T -> M) (o : OrDefault T) : M :=
    match o with
    | Defaulted => OK
    | UserDefined v => f v
    end.

  Definition classname : classname' lang -> M :=
    match lang as lang return (name' lang -> M) -> (type' lang -> M) -> classname' lang -> M with
    | lang.cpp => fun name _ => name
    | lang.temp => fun _ type => type
    end name type.

  Definition obj_value (o : ObjValue' lang) : M :=
    match o with
    | Ovar t ie => type t
    | Ofunction (Build_Func t args _ _ ob) =>
        type t <+> lst (type ∘ snd) args <+> opt function_body ob
    | Omethod m =>
        type m.(m_return) <+> classname m.(m_class) <+> lst (type ∘ snd) m.(m_params) <+> opt (or_default stmt) m.(m_body)
    | Oconstructor c =>
        classname c.(c_class) <+> lst (type ∘ snd) c.(c_params) <+> OK (* TODO *)
    | Odestructor d =>
        classname d.(d_class) <+> opt (or_default stmt) d.(d_body)
    end.

  Definition glob_decl (gd : GlobDecl' lang) : M :=
    OK.
  End with_lang.

  Definition translation_unit (tu : translation_unit) : M :=
    let symbol '(nm, obj) := obj_value obj in
    let gd '(nm, gd) := glob_decl gd in
    lst gd (namemap.NM.elements tu.(types)) <+>
    lst symbol (namemap.NM.elements tu.(symbols)).
End with_monad.
End check.
