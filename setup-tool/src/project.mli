open Extra

(** Project configuration read / written to file ["br-project.toml"], which is
    also used to identify the root of the project on the file system. *)
type br_project = {
  (** Main Coq directory path for the project. *)
  brp_coq_dirpath    : Coq_path.t;
  (** Main opam package name for the project. *)
  brp_coq_package    : string;
  (** Coq theories to include in generate theories. *)
  brp_coq_theories   : string list;
  (** Clang included directories (for ["#include<...>"]). *)
  brp_clang_includes : Filepath.t list;
  (** Other clang flags, excluding ["-I"]. *)
  brp_clang_flags    : string list;
  (** C++ source files, or whole directories to ignore. *)
  brp_proj_ignored   : Filepath.t list;
}

(** Option configuration mode. *)
type config_mode =
  (** Extend the default. *)
  | Extend
  (** Override the option (ignoring the default). *)
  | Override

(** Local configuration read / written to a ["br-config.toml"] file. It can be
    used to set options in a specific subtree of the source tree. *)
type br_config = {
  (** Optional Coq directory path for files under the same directory. *)
  brc_coq_dirpath    : Coq_path.t option;
  (** Optional opam package name for for files under the same directory. *)
  brc_coq_package    : string option;
  (** Coq theories to include in generate theories. *)
  brc_coq_theories   : (config_mode * string list);
  (** Clang included directories (for ["#include<...>"]). *)
  brc_clang_includes : config_mode * Filepath.t list;
  (** Other clang flags, excluding ["-I"]. *)
  brc_clang_flags    : config_mode * string list;
  (** C++ source files, or whole directories to ignore. *)
  brc_proj_ignored   : Filepath.t list;
}

(** [read_br_project file] reads a project configuration from the given [file]
    (in Toml format). In case of failure while reading or parsing the file, an
    error message is printed, and the program fails with exit code [1]. *)
val read_br_project : Filepath.t -> br_project

(** [write_br_project file config] writes the given [config] to the [file]. In
    case of failure while writing the file, an error message is printed before
    the failure of the program with exit code [1]. *)
val write_br_project : Filepath.t -> br_project -> unit

(** [read_br_config] is similar to [read_br_project], but reads a local config
    file instead of a project config file. *)
val read_br_config : Filepath.t -> br_config

(** [write_br_config] is similar to [write_br_project], but applies to a local
    config file instead of a project config file. *)
val write_br_config : Filepath.t -> br_config -> unit

(** Name of the project configuration file (identifying the project root). *)
val project_file_name : string

(** Name of the local configuration files. *)
val config_file_name : string

(** [move_to_root ()] identifies the root of the project by finding the parent
    directory containing a file named [project_file_name], changes the current
    working directory to be the project root, and gives a relative path to the
    initial working directory (that where the program was called). If the root
    of a project cannot be located, the program fails. *)
val move_to_root : unit -> Filepath.t

type config = {
  coq_dirpath    : Coq_path.t;
  coq_package    : string;
  coq_theories   : string list;
  clang_includes : Filepath.t list;
  clang_flags    : string list;
  proj_ignored   : Filepath.t list;
}

val discover : unit -> (Filepath.t * config) list
