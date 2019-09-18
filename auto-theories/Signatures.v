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

Definition matchName (fullname: string) (msName lsName: string) :bool :=
  match index 0 msName fullname with
  | Some n => ssrbool.isSome (index (n+length msName) lsName fullname)
  | None => false
  end.

Print ObjValue.

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

Definition extItem {I} (ext: ObjValue -> option I) (c: compilation_unit) (class method: string): (string*I) + string :=
  match (List.filter (fun '(n, b) =>
                       ssrbool.isSome (ext b) && matchName n class method)%bool
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

Ltac specItem specFun ext class method module spec :=
  let t := eval hnf in (extItem ext module class method) in
  let t := eval simpl in t in
      match t with
      | inr ?x => idtac x; exact x
      | inl ?x => exact (specFun (snd x) spec)
      end.

Ltac specMethod  := specItem SMethodSpec extMethod.
(* it is hard to identify constructors by name*)
Ltac specCtor  := specItem SCtorSpec extCtor.
Ltac specFunc  := specItem SFunctionSpec extFunc "".
