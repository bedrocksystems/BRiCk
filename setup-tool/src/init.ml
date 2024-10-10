open Extra
open Coq_path
open Project

let command : Project.br_project -> unit = fun config ->
  write_br_project project_file_name config
