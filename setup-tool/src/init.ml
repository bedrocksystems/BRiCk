open Cmdliner

open Extra
open Panic
open Coq_path

let version = "dev"

let init debug =
  let open Project in
  let default = {
     brp_coq_dirpath = Coq_path.path_of_string "my.project";
     brp_coq_package = "my-project";
     brp_coq_theories = [];
     brp_clang_includes = [];
     brp_clang_flags = [];
     brp_proj_ignored = [];
  } in
  write_br_project "br-project.toml" default

let debug =
  let doc = "Enable debug printing." in
  Arg.(value & flag & info ["debug"] ~doc)

let init_cmd =
  let doc = "Initialize a default br-project.toml file." in
  Cmd.(v (info "init" ~version ~doc) Term.(const init $ debug))
