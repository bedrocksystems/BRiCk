open Cmdliner

open Extra
open Panic
open Project
open Coq_path

let version = "dev"

let init_cmd =
  let doc = "Initialize a default br-project.toml file." in
  Cmd.(v (info "init" ~version ~doc) Term.(const Init.command $ const ()))

let debug =
  let doc = "Enable debug printing." in
  Arg.(value & flag & info ["debug"] ~doc)

let gen_cmd =
  let doc = "Generate Coq code from C++ source files." in
  Cmd.(v (info "gen" ~version ~doc) Term.(const Gen.command $ debug))

let _ =
  let cmds = [init_cmd; gen_cmd] in
  let default = Term.(ret (const (`Help(`Pager, None)))) in
  let default_info =
    let doc = "BlueRock C++ program verification setup tool." in
    Cmd.info "br" ~version ~doc
  in
  exit (Cmd.eval (Cmd.group default_info ~default cmds))
