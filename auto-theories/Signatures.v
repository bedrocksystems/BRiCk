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

(*
Definition methodSig : forall (c: compilation_unit) (class method: string), (string*Method) + string :=
  extItem extMethod.
*)

Definition SMethodSig (msig: Method)
           (PQ : val -> arrowFrom val (map snd (m_params msig)) WithPrePost) :=
  SMethod (m_class msig)
          (m_this_qual msig)
          (m_return msig)
          (map snd (m_params msig)) PQ.

Definition SFunctionSig (msig: Func)
           (PQ : arrowFrom val (map snd (f_params msig)) WithPrePost) :=
  SFunction 
          (f_return msig)
          (map snd (f_params msig)) PQ.

Ltac specItem specFun ext c class method spec :=
  let t := eval hnf in (extItem ext c class method) in
  let t := eval simpl in t in
      match t with
      | inr ?x => idtac x; exact x
      | inl ?x => exact (specFun (snd x) spec)
      end.

Ltac specMethod  := specItem SMethodSig extMethod.
Ltac specFunc  := specItem SFunctionSig extFunc.
