Require Import ExtLib.Programming.Show.
Require Import Cpp.Auto.
Require Import Coq.Strings.String.
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

Fixpoint namespaces (seen : string) (s : string) : list string :=
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
    match index start kh fullname with
    | Some n => contains (n+length kh) ktl fullname
    | None => false
    end
  | [] => true
  end.

(* matchers *)
Definition has (keys : list string) : Matcher :=
  {| matches := contains 0 keys |}.

Definition nat_to_string (n : nat) : string :=
  @runShow _ {| show_mon := {| Monoid.monoid_plus := String.append
                             ; Monoid.monoid_unit := EmptyString |}
              ; show_inj a := String a EmptyString |}
           (nat_show n).

Definition name (str : string) : Matcher :=
  has (map (fun s => nat_to_string (length s) ++ s) (namespaces "" str)).

Definition exact (s : string) : Matcher :=
  {| matches := String.eqb s |}.


Definition find_symbol (matchName: Matcher) (c: compilation_unit)
: string + (obj_name * ObjValue) :=
  let result :=
      List.filter (fun '(n, _) => matchName.(matches) n) (symbols c)
  in
  match result with
  | [] => inl "found no matching symbols"
  | h::[] => inr h
  | _::_::_ => inl ("Ambiguous match. The following symbols matched: " ++ String.concat ", " (List.map fst result))
  end.

Definition SMethodSpec (msig: Method)
  : (val -> arrowFrom val (map snd (m_params msig)) WithPrePost) -> _ :=
  SMethod (m_class msig)
          (m_this_qual msig)
          (m_return msig)
          (map snd (m_params msig)).

Definition SFunctionSpec (msig: Func)
  : arrowFrom val (map snd (f_params msig)) WithPrePost -> _ :=
  SFunction
          (f_return msig)
          (map snd (f_params msig)).

Definition SCtorSpec (msig: Ctor)
  : (val -> arrowFrom val (map snd (c_params msig)) WithPrePost) -> _ :=
  SConstructor
          (c_class msig)
          (map snd (c_params msig)).

Definition spec_type (o : ObjValue) : Type :=
  match o with
  | Ovar _ _ => Rep
  | Odestructor _ => val -> WithPrePost
  | Ofunction f => arrowFrom val (map snd f.(f_params)) WithPrePost
  | Omethod m => val -> arrowFrom val (map snd m.(m_params)) WithPrePost
  | Oconstructor c => val -> arrowFrom val (map snd c.(c_params)) WithPrePost
  end.

Definition AnySpec (s : string + (obj_name * ObjValue)) :
  string + (match s return Type with
            | inl s => Empty_set
            | inr (_,s) => spec_type s
            end -> mpred) :=
  match s as s
        return string + (match s return Type with
                         | inl s => Empty_set
                         | inr (_,s) => spec_type s
                         end -> mpred)
  with
  | inl err => inl err
  | inr (nm,s) =>
    inr (fun sp =>
           _at (_global nm)
               (match s as o return spec_type o -> Rep with
                | Ovar _ _ => fun r => r
                | Odestructor d => fun r => ticptr (SDestructor d.(d_class) r)
                | Oconstructor c => fun r => ticptr (SCtorSpec c r)
                | Omethod m => fun r => ticptr (SMethodSpec m r)
                | Ofunction m => fun r => ticptr (SFunctionSpec m r)
                end sp))
  end.


Declare Reduction spec_red :=
  cbv beta iota zeta delta -
  [ T_uchar T_int T_schar T_longlong T_long T_ulonglong T_uint T_uint64 T_uint32
    T_ulong T_short T_ushort T_uint128 T_int128 T_int8 T_int16 T_uint16 T_uint8
    Talias
    Qmut_volatile Qmut Qconst Qconst_volatile
    ticptr
    SFunction TSFunction
    SMethod TSMethod
    SConstructor TSConstructor
    SDestructor TSDestructor ].

Ltac specify nameMatch module PQ :=
  let t := eval spec_red in (AnySpec (find_symbol nameMatch module)) in
  lazymatch t with
  | inl ?x => fail 1 x
  | inr ?x => let X := eval cbv beta in (x PQ) in
              exact X
  end.

Notation "nameMatch @@ module @@ PQ" :=
  ltac:(specify nameMatch module PQ) (at level 80, module at next level).
