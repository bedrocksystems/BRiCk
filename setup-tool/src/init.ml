open Extra
open Coq_path
open Project

let default : Project.br_project = {
  brp_coq_dirpath = Coq_path.path_of_string "my.project";
  brp_coq_package = "my-project";
  brp_coq_theories = [];
  brp_clang_includes = [];
  brp_clang_flags = [];
  brp_proj_ignored = [];
}

let command : unit -> unit = fun () ->
  write_br_project project_file_name default
