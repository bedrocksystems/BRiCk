Require Import Cpp.Auto.
Require Import String.
Open Scope string_scope.
Import ListNotations.
(* signatures
 * note(gmm): these should be moved out to cpp2v
 *)
Definition signature := list (obj_name * function_spec).

Definition sig {resolve} (ti : thread_info) (s : signature) : mpred :=
  sepSPs (map (fun '(f, fs) => |> cglob (resolve:=resolve) f ti fs) s).

Record Matcher : Set :=
{ matches : string -> bool }.

Local Fixpoint string_rev (acc s : string) : string :=
  match s with
  | EmptyString => acc
  | String s ss => string_rev (String s acc) ss
  end.

Local Fixpoint namespaces (seen : string) (s : string) : list string :=
  match s with
  | String ":" (String ":" s) =>
    match seen with
    | EmptyString => namespaces "" s
    | _ => string_rev "" seen :: namespaces "" s
    end
  | String s ss => namespaces (String s seen) ss
  | EmptyString =>
    match seen with
    | EmptyString => nil
    | _ => string_rev "" seen :: nil
    end
  end.

Local Fixpoint contains (start: nat) (keys: list string) (fullname: string) :bool :=
  match keys with
  | kh::ktl =>
    match index 0 kh fullname with
    | Some n => contains (n+length kh) ktl fullname
    | None => false
    end
  | [] => true
  end.

(* matchers *)
Definition has (keys : list string) : Matcher :=
  {| matches := contains 0 keys |}.

Definition name (str : string) : Matcher :=
  has (namespaces "" str).

Definition exact (s : string) : Matcher :=
  {| matches := String.eqb s |}.

Definition extMethod (o: ObjValue) : option Method :=
  match o with
  | Omethod m => Some m
  | _ => None
  end.

Definition extFunc (o: ObjValue) : option Func :=
  match o with
  | Ofunction m => Some m
  | _ => None
  end.

Definition extCtor (o: ObjValue) : option Ctor :=
  match o with
  | Oconstructor m => Some m
  | _ => None
  end.

Definition extItem {I} (ext: ObjValue -> option I) (matchName: Matcher)
           (c: compilation_unit): (string*I) + string :=
  let result :=
      List.flat_map (fun '(n, b) =>
                       match ext b with
                       | None => nil
                       | Some m => if matchName.(matches) n then (n, m) :: nil else nil
                       end)
                    (symbols c)
  in
  match result with
  | [] => inr "found no matching symbols"
  | h::[] => inl h
  | _::_::_ => inr ("Ambiguous match. The following symbols matched: " ++ String.concat ", " (List.map fst result))
  end.

Definition SMethodSpec (msig: Method)
           (PQ : val -> arrowFrom val (map snd (m_params msig)) WithPrePost) :=
  SMethod (m_class msig)
          (m_this_qual msig)
          (m_return msig)
          (map snd (m_params msig)) PQ.

Definition SFunctionSpec (msig: Func)
           (PQ : arrowFrom val (map snd (f_params msig)) WithPrePost) :=
  SFunction
          (f_return msig)
          (map snd (f_params msig)) PQ.

Definition SCtorSpec (msig: Ctor)
           (PQ : val -> arrowFrom val (map snd (c_params msig)) WithPrePost) :=
  SConstructor
          (c_class msig)
          (map snd (c_params msig)) PQ.

Ltac specItem specFun ext nameMatch module spec :=
  let t := eval hnf in (extItem ext nameMatch module) in
  let t := eval simpl in t in
  lazymatch t with
  | inr ?x => fail 1 x
  | inl ?x => exact (specFun (snd x) spec)
  end.



Ltac specMethod  := specItem SMethodSpec extMethod.
(* it is hard to identify constructors by name*)
Ltac specCtor  := specItem SCtorSpec extCtor.
Ltac specFunc  := specItem SFunctionSpec extFunc.
