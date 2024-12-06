open Swipl
open Embedding

let _ =
  initialise [|Sys.argv.(0); "-q"|];
  Printf.printf "Running toplevel.\n%!";
  match toplevel () with
  | true -> Printf.printf "Successfully ran the toplevel!\n%!"
  | _    -> Printf.printf "Failed to run the toplevel!\n%!"
