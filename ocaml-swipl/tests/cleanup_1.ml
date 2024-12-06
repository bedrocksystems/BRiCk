open SWI_prolog.API

let _ =
  initialise [|Sys.argv.(0); "-q"|];
  cleanup ~no_reclaim_memory:false ~no_cancel:false ~status:42
