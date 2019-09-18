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

Fixpoint contains (start: nat) (keys: list string) (fullname: string) :bool :=
  match keys with
  | kh::ktl =>
    match index 0 kh fullname with
    | Some n => contains (n+length kh) ktl fullname
    | None => false
    end
  | [] => true
  end.

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

Definition extItem {I} (ext: ObjValue -> option I) (matchName: string-> bool) (c: compilation_unit) (class method: string): (string*I) + string :=
  match (List.filter (fun '(n, b) =>
                       ssrbool.isSome (ext b) && matchName n)%bool
                     (symbols c)) with
  | [] => inr "not found"
  | h::[] => match ext (snd h) with
           | Some m => inl (fst h, m)
           | _ => inr "not possible"
           end
  | _::_::_ => inr "multiple matches"
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
  let t := eval simpl in t in idtac t. (*
      match t with
      | inr ?x => idtac x; exact x
      | inl ?x => exact (specFun (snd x) spec)
      end.*)

Definition has : list string -> string  -> bool := contains 0.
Ltac specMethod  := specItem SMethodSpec extMethod.
(* it is hard to identify constructors by name*)
Ltac specCtor  := specItem SCtorSpec extCtor.
Ltac specFunc  := specItem SFunctionSpec extFunc.

