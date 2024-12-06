open Swipl
open Embedding

let _ =
  let built_in () =
    match Versions.get_BUILT_IN () with
    | None    -> Printf.printf "BUILT_IN: not initialised yet\n%!"
    | Some(_) -> Printf.printf "BUILT_IN: initialised\n%!"
  in
  built_in ();
  Printf.printf "Initialised? %b\n%!" (is_initialised ());
  Printf.printf "Initialised? %b\n%!" (is_initialised_argv () = None);
  Printf.printf "Initialising ...\n%!";
  initialise [|Sys.argv.(0); "-q"|];
  Printf.printf "Initialised.\n%!";
  Printf.printf "Initialised? %b\n%!" (is_initialised ());
  let _ =
    match is_initialised_argv () with
    | Some(argv) -> Printf.printf "Initialised with argv = %s\n%!"
                      (String.concat " " (Array.to_list argv))
    | None       -> assert false
  in
  built_in ()
