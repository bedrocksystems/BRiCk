open SWI_prolog.API

let _ =
  initialise [|Sys.argv.(0); "-q"|];
  for i = 0 to 3 do
    Printf.printf "Init... (%i)\n%!" i;
    initialise [|Sys.argv.(0); "-q"|];
    Printf.printf "Cleanup...\n%!";
    try
      cleanup ~no_reclaim_memory:true ~no_cancel:false ~status:0;
      Printf.printf "OK...\n%!"
    with
    | Cleanup(`Cancelled) -> Printf.printf "Cancelled...\n%!"
    | Cleanup(`Failed   ) -> Printf.printf "Failed...\n%!"
    | Cleanup(_         ) -> Printf.printf "Recursive...\n%!"
  done
