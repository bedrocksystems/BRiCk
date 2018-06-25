Require Import Lens.Lens.

Set Primitive Projections.

Require Import Template.monad_utils Template.Ast.
Import MonadNotation.

Record Foo : Set :=
{ foo : nat
; bar : bool }.

Require Import Template.Ast.

Declare ML Module "template_coq".

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Record Info : Set :=
{ type : ident
; ctor : ident
; fields : list (ident * term)
}.

Fixpoint countTo (n : nat) : list nat :=
  match n with
  | 0 => nil
  | S m => countTo m ++ (m :: nil)
  end.

Definition prepend (ls : string) (i : ident) : ident :=
  ls ++ i.

Quote Definition cBuild_Lens := Build_Lens.

Definition mkLens (At : term) (fields : list (ident * term)) (i : nat)
: option (ident * term) :=
  match At with
  | tInd ind args =>
    let ctor := tConstruct ind 0 args in
    match nth_error fields i with
    | None => None
    | Some (name, Bt) =>
      let p (x : nat) : projection := (ind, 0, x) in
      let get_body := tProj (p i) (tRel 0) in
      let f x :=
          let this := tProj (p x) (tRel 0) in
          if PeanoNat.Nat.eqb x i
          then tApp (tRel 1) (this :: nil)
          else this
      in
      let update_body :=
          tApp ctor (map f (countTo (List.length fields)))
      in
      Some ( prepend "_" name
           , tApp cBuild_Lens
                  (At :: At :: Bt :: Bt ::
                      tLambda nAnon At get_body ::
                      tLambda nAnon (tProd nAnon Bt Bt) (tLambda nAnon At update_body) ::
                      nil))
    end
  | _ => None
  end.

Definition getFields (mi : mutual_inductive_body)
: option Info :=
  match mi.(ind_bodies) with
  | oib :: nil =>
    match oib.(ind_ctors) with
    | ctor :: nil =>
      Some {| type := oib.(ind_name)
            ; ctor := let '(x,_,_) := ctor in x
            ; fields := oib.(ind_projs)
           |}
    | _ => None
    end
  | _ => None
  end.

Fixpoint mconcat (ls : list (TemplateMonad unit)) : TemplateMonad unit :=
  match ls with
  | nil => tmReturn tt
  | m :: ms => tmBind m (fun _ => mconcat ms)
  end.

Definition genLens (T : Type) : TemplateMonad unit :=
  ty <- tmQuote T ;;
  match ty with
  | tInd i _ =>
    let name := i.(inductive_mind) in
    ind <- tmQuoteInductive name ;;
    match getFields ind with
    | Some info =>
      let gen i :=
          match mkLens ty info.(fields) i return TemplateMonad unit with
          | None => tmFail "failed to build lens"
          | Some x =>
            tmBind (tmEval cbv x) (fun '(n,d) =>
                                     _ <- tmMkDefinition n d ;;
                                     ret tt)
          end
      in
      mconcat (map gen (countTo (List.length info.(fields))))
    | None => tmFail "failed to get info"
    end
  | _ => tmFail "given type is not inductive"
  end.

Run TemplateProgram (genLens Foo).
