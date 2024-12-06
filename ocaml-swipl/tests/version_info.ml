open Swipl

let _ =
  let version = Versions.version () in
  let v_fli = Versions.get_FLI () in
  let v_rec = Versions.get_REC () in
  let v_qlf = Versions.get_QLF () in
  let v_ld = Versions.get_QLF_LOAD () in
  let v_vm = Versions.get_VM () in

  (* Since the test is version-dependent, we hard-code 9.0.3 values. *)
  let hard_code true_value default =
    match version with
    | "9.0.3" -> true_value
    | _       -> default
  in

  Printf.printf "SWI-prolog version: %s\n%!" (hard_code version "9.0.3");
  Printf.printf "FLI: %i\n%!" (hard_code v_fli 2);
  Printf.printf "REC: %i\n%!" (hard_code v_rec 3);
  Printf.printf "QLF: %i\n%!" (hard_code v_qlf 68);
  Printf.printf "QLF_LOAD: %i\n%!" (hard_code v_ld 68);
  Printf.printf "VM: %i\n%!" (hard_code v_vm 2678345669);

  match Versions.get_BUILT_IN () with
  | None    -> Printf.printf "BUILT_IN: not initialised yet\n%!"
  | Some(_) -> Printf.printf "BUILT_IN: initialised\n%!"
