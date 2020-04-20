(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import stdpp.stringmap.
Require Import stdpp.gmap.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.sub_module.

Class Traversable (T : Type -> Type) : Type :=
{ traverse : forall `{MBind M, MRet M} {A B}, (A -> M B) -> T A -> M (T B) }.

Instance gmap_traversable {K} {Eq : EqDecision K} {Cnt : countable.Countable K}
: Traversable (gmap K) :=
  {| traverse := fun M _ _ A B f (m : gmap K A) =>
               mapM (fun '(k,v) => f v ≫= fun v' => mret (k, v'))
                    (gmap_to_list m) ≫= fun r => mret (list_to_map r) |}.

Definition GlobDecl_merge (a b : GlobDecl) : option GlobDecl :=
  match a , b with
  | Gtype , Gtype
  | Gtype , Gunion _
  | Gtype , Gstruct _ => Some b
  | Gunion _ , Gtype
  | Gstruct _ , Gtype => Some a
  | Gunion u , Gunion u' =>
    require_eq u u' $
    Some a
  | Gstruct s , Gstruct s' =>
    require_eq s s' $
    Some a
  | Genum e _ , Genum e' _ =>
    require_eq e e' $
    Some a
  | Gconstant t (Some e) , Gconstant t' (Some e') =>
    require_eq t t' $
    require_eq e e' $
    Some a
  | Gconstant t (Some e) , Gconstant t' None =>
    require_eq t t' $
    Some a
  | Gconstant t None , Gconstant t' (Some e') =>
    require_eq t t' $
    Some b
  | Gconstant t None , Gconstant t' None =>
    require_eq t t' $
    Some a
  | Gtypedef t , Gtypedef t' =>
    require_eq t t' $
    Some a
  | _ , _ => None
  end.

Definition ObjValue_linkable (a b : ObjValue) : option ObjValue :=
  match a , b with
  | Ovar t oe , Ovar t' oe' => None
  | Ofunction f , Ofunction f' =>
    require_eq f.(f_return) f'.(f_return) $
    require_eq (List.map snd f.(f_params)) (List.map snd f'.(f_params)) $
    match f.(f_body) , f'.(f_body) with
    | None , None => Some a
    | Some b , Some b' =>
      require_eq f.(f_params) f'.(f_params) $
      require_eq b b' $
      Some a
    | None , _ => Some b
    | _ , None => Some a
    end
  | Omethod m , Omethod m' =>
    require_eq m.(m_return) m'.(m_return) $
    require_eq m.(m_class) m'.(m_class) $
    require_eq m.(m_this_qual) m'.(m_this_qual) $
    require_eq (List.map snd m.(m_params)) (List.map snd m'.(m_params)) $
    match m.(m_body) , m'.(m_body) with
    | None , None => Some a
    | Some b , Some b' =>
      require_eq m.(m_params) m'.(m_params) $
      require_eq b b' $
      Some a
    | None , _ => Some b
    | _ , None => Some a
    end
  | Oconstructor c , Oconstructor c' =>
    require_eq c.(c_class) c'.(c_class) $
    require_eq (List.map snd c.(c_params)) (List.map snd c'.(c_params)) $
    match c.(c_body) , c'.(c_body) with
    | None , None => Some a
    | None , _ => Some b
    | _ , None => Some a
    | Some x , Some y =>
      require_eq c.(c_params) c'.(c_params) $
      require_eq x y $ Some a
    end
  | Odestructor dd , Odestructor dd' =>
    require_eq dd.(d_class) dd'.(d_class) $
    match dd.(d_body) , dd'.(d_body) with
    | None , None => Some a
    | None , _ => Some b
    | _ , None => Some a
    | Some x , Some y =>
      require_eq x y $ Some a
    end
  | _ , _ => None
  end.


Definition link (a b : compilation_unit) : option compilation_unit :=
  (traverse (fun x : option _ => x)
            (merge (fun (l r : option GlobDecl) => Some
                      match l , r with
                      | Some l , Some r => GlobDecl_merge l r
                      | None , r => r
                      | l , None => l
                      end) a.(globals) b.(globals)) ≫= fun g =>
   traverse (T:=stringmap) (fun x : option _ => x)
            (merge (fun l r => Some
                      match l , r with
                      | Some l , Some r => ObjValue_linkable l r
                      | None , r => r
                      | l , None => l
                      end) a.(symbols) b.(symbols)) ≫= fun s =>
   mret {| globals := g ; symbols := s |}).
