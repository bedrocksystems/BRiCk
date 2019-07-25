Require Import Cpp.Auto.

(* signatures
 * note(gmm): these should be moved out to cpp2v
 *)
Definition signature := list (obj_name * function_spec).

Definition sig {resolve} (ti : thread_info) (s : signature) : mpred :=
  sepSPs (map (fun '(f, fs) => |> cglob (resolve:=resolve) f ti fs) s).
