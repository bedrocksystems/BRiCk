Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

From Template Require Import monad_utils Ast Loader.
Import MonadNotation.

Require Import Lens.Lens.

Set Primitive Projections.

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

Definition lensName (ls : string) (i : ident) : ident :=
  ls ++ i.

Local Quote Definition cBuild_Lens := Build_Lens.

Local Definition mkLens (At : term) (fields : list (ident * term)) (i : nat)
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
      Some ( lensName "_" name
           , tApp cBuild_Lens
                  (At :: At :: Bt :: Bt ::
                      tLambda nAnon At get_body ::
                      tLambda nAnon (tProd nAnon Bt Bt) (tLambda nAnon At update_body) ::
                      nil))
    end
  | _ => None
  end.

Local Definition getFields (mi : mutual_inductive_body) (n : nat)
: TemplateMonad Info :=
  match nth_error mi.(ind_bodies) n with
  | None => tmFail "no body for index"
  | Some oib =>
    match oib.(ind_ctors) with
    | nil => tmFail "`getFields` got empty type"
    | ctor :: nil =>
      ret {| type := oib.(ind_name)
           ; ctor := let '(x,_,_) := ctor in x
           ; fields := oib.(ind_projs)
           |}
    | _ => tmFail "`getFields` got variant type"
    end
  end.

Definition genLens (T : Type) : TemplateMonad unit :=
  ty <- tmQuote T ;;
  match ty with
  | tInd i _ =>
    let name := i.(inductive_mind) in
    ind <- tmQuoteInductive name ;;
    info <- getFields ind i.(inductive_ind) ;;
    let gen i :=
          match mkLens ty info.(fields) i return TemplateMonad unit with
          | None => tmFail "failed to build lens"
          | Some x =>
            tmBind (tmEval cbv x) (fun '(n,d) =>
                                     _ <- tmMkDefinition n d ;;
                                     ret tt)
          end
      in
      monad_map gen (countTo (List.length info.(fields))) ;;
      ret tt
  | _ => tmFail "given type is not inductive"
  end.