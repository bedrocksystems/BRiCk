(* Generated file: do not edit. *)
open Ctypes

module Types = Generated_C_types

module Functions(I : Ctypes.FOREIGN) = struct
  open I
  open Types

(**** LICENSE ****)

let license = foreign "PL_license" @@
  string @-> string @-> returning @@ void

(**** MODULES ****)

let context = foreign "PL_context" @@
  void @-> returning @@ module_t
let module_name = foreign "PL_module_name" @@
  module_t @-> returning @@ atom_t
let new_module = foreign "PL_new_module" @@
  atom_t @-> returning @@ module_t
let strip_module = foreign "PL_strip_module" @@
  term_t @-> ptr module_t @-> term_t @-> returning @@ int

(* Foreign context frames *)

let open_foreign_frame = foreign "PL_open_foreign_frame" @@
  void @-> returning @@ fid_t
let rewind_foreign_frame = foreign "PL_rewind_foreign_frame" @@
  fid_t @-> returning @@ void
let close_foreign_frame = foreign "PL_close_foreign_frame" @@
  fid_t @-> returning @@ void
let discard_foreign_frame = foreign "PL_discard_foreign_frame" @@
  fid_t @-> returning @@ void

(* Finding predicates *)

let pred = foreign "PL_pred" @@
  functor_t @-> module_t @-> returning @@ predicate_t
let predicate = foreign "PL_predicate" @@
  string @-> int @-> string @-> returning @@ predicate_t
let predicate_info = foreign "PL_predicate_info" @@
  predicate_t @-> ptr atom_t @-> ptr size_t @-> ptr module_t @-> returning @@ int

(* Call-back *)

let open_query = foreign "PL_open_query" @@
  module_t @-> int @-> predicate_t @-> term_t @-> returning @@ qid_t
let next_solution = foreign "PL_next_solution" @@
  qid_t @-> returning @@ int
let close_query = foreign "PL_close_query" @@
  qid_t @-> returning @@ int
let cut_query = foreign "PL_cut_query" @@
  qid_t @-> returning @@ int
let current_query = foreign "PL_current_query" @@
  void @-> returning @@ qid_t
let can_yield = foreign "PL_can_yield" @@
  void @-> returning @@ int

(* Simplified (but less flexible) call-back *)

let call = foreign "PL_call" @@
  term_t @-> module_t @-> returning @@ int
let call_predicate = foreign "PL_call_predicate" @@
  module_t @-> int @-> predicate_t @-> term_t @-> returning @@ int

(* Handling exceptions *)

let _exception = foreign "PL_exception" @@
  qid_t @-> returning @@ term_t
let raise_exception = foreign "PL_raise_exception" @@
  term_t @-> returning @@ int
let clear_exception = foreign "PL_clear_exception" @@
  void @-> returning @@ void

(* Engine-based coroutining *)

let yielded = foreign "PL_yielded" @@
  qid_t @-> returning @@ term_t

(**** ASSERT ****)

let _assert = foreign "PL_assert" @@
  term_t @-> module_t @-> int @-> returning @@ int

(* Creating and destroying term-refs *)

let new_term_refs = foreign "PL_new_term_refs" @@
  size_t @-> returning @@ term_t
let new_term_ref = foreign "PL_new_term_ref" @@
  void @-> returning @@ term_t
let copy_term_ref = foreign "PL_copy_term_ref" @@
  term_t @-> returning @@ term_t
let reset_term_refs = foreign "PL_reset_term_refs" @@
  term_t @-> returning @@ void

(* Constants *)

let new_atom = foreign "PL_new_atom" @@
  string @-> returning @@ atom_t
let new_atom_nchars = foreign "PL_new_atom_nchars" @@
  size_t @-> string @-> returning @@ atom_t
let new_atom_mbchars = foreign "PL_new_atom_mbchars" @@
  int @-> size_t @-> string @-> returning @@ atom_t
let atom_mbchars = foreign "PL_atom_mbchars" @@
  atom_t @-> ptr size_t @-> ptr (ptr char) @-> uint @-> returning @@ int
let register_atom = foreign "PL_register_atom" @@
  atom_t @-> returning @@ void
let unregister_atom = foreign "PL_unregister_atom" @@
  atom_t @-> returning @@ void
let new_functor = foreign "PL_new_functor" @@
  atom_t @-> size_t @-> returning @@ functor_t
let functor_name = foreign "PL_functor_name" @@
  functor_t @-> returning @@ atom_t
let functor_arity = foreign "PL_functor_arity" @@
  functor_t @-> returning @@ size_t

(* Get C-values from Prolog terms *)

let get_atom = foreign "PL_get_atom" @@
  term_t @-> ptr atom_t @-> returning @@ int
let get_bool = foreign "PL_get_bool" @@
  term_t @-> ptr int @-> returning @@ int
let get_atom_chars = foreign "PL_get_atom_chars" @@
  term_t @-> ptr (ptr char) @-> returning @@ int
let get_chars = foreign "PL_get_chars" @@
  term_t @-> ptr (ptr char) @-> uint @-> returning @@ int
let get_list_chars = foreign "PL_get_list_chars" @@
  term_t @-> ptr (ptr char) @-> uint @-> returning @@ int
let get_atom_nchars = foreign "PL_get_atom_nchars" @@
  term_t @-> ptr size_t @-> ptr (ptr char) @-> returning @@ int
let get_list_nchars = foreign "PL_get_list_nchars" @@
  term_t @-> ptr size_t @-> ptr (ptr char) @-> uint @-> returning @@ int
let get_nchars = foreign "PL_get_nchars" @@
  term_t @-> ptr size_t @-> ptr (ptr char) @-> uint @-> returning @@ int
let get_integer = foreign "PL_get_integer" @@
  term_t @-> ptr int @-> returning @@ int
let get_long = foreign "PL_get_long" @@
  term_t @-> ptr long @-> returning @@ int
let get_intptr = foreign "PL_get_intptr" @@
  term_t @-> ptr intptr_t @-> returning @@ int
let get_pointer = foreign "PL_get_pointer" @@
  term_t @-> ptr (ptr void) @-> returning @@ int
let get_float = foreign "PL_get_float" @@
  term_t @-> ptr double @-> returning @@ int
let get_functor = foreign "PL_get_functor" @@
  term_t @-> ptr functor_t @-> returning @@ int
let get_name_arity = foreign "PL_get_name_arity" @@
  term_t @-> ptr atom_t @-> ptr size_t @-> returning @@ int
let get_compound_name_arity = foreign "PL_get_compound_name_arity" @@
  term_t @-> ptr atom_t @-> ptr size_t @-> returning @@ int
let get_module = foreign "PL_get_module" @@
  term_t @-> ptr module_t @-> returning @@ int
let get_arg = foreign "PL_get_arg" @@
  size_t @-> term_t @-> term_t @-> returning @@ int
let get_dict_key = foreign "PL_get_dict_key" @@
  atom_t @-> term_t @-> term_t @-> returning @@ int
let get_list = foreign "PL_get_list" @@
  term_t @-> term_t @-> term_t @-> returning @@ int
let get_head = foreign "PL_get_head" @@
  term_t @-> term_t @-> returning @@ int
let get_tail = foreign "PL_get_tail" @@
  term_t @-> term_t @-> returning @@ int
let get_nil = foreign "PL_get_nil" @@
  term_t @-> returning @@ int
let quote = foreign "PL_quote" @@
  int @-> string @-> returning @@ ptr char

(* Verify types *)

let term_type = foreign "PL_term_type" @@
  term_t @-> returning @@ int
let is_variable = foreign "PL_is_variable" @@
  term_t @-> returning @@ int
let is_ground = foreign "PL_is_ground" @@
  term_t @-> returning @@ int
let is_atom = foreign "PL_is_atom" @@
  term_t @-> returning @@ int
let is_integer = foreign "PL_is_integer" @@
  term_t @-> returning @@ int
let is_string = foreign "PL_is_string" @@
  term_t @-> returning @@ int
let is_float = foreign "PL_is_float" @@
  term_t @-> returning @@ int
let is_rational = foreign "PL_is_rational" @@
  term_t @-> returning @@ int
let is_compound = foreign "PL_is_compound" @@
  term_t @-> returning @@ int
let is_callable = foreign "PL_is_callable" @@
  term_t @-> returning @@ int
let is_functor = foreign "PL_is_functor" @@
  term_t @-> functor_t @-> returning @@ int
let is_list = foreign "PL_is_list" @@
  term_t @-> returning @@ int
let is_dict = foreign "PL_is_dict" @@
  term_t @-> returning @@ int
let is_pair = foreign "PL_is_pair" @@
  term_t @-> returning @@ int
let is_atomic = foreign "PL_is_atomic" @@
  term_t @-> returning @@ int
let is_number = foreign "PL_is_number" @@
  term_t @-> returning @@ int
let is_acyclic = foreign "PL_is_acyclic" @@
  term_t @-> returning @@ int

(* Assign to term-references *)

let put_variable = foreign "PL_put_variable" @@
  term_t @-> returning @@ int
let put_atom = foreign "PL_put_atom" @@
  term_t @-> atom_t @-> returning @@ int
let put_bool = foreign "PL_put_bool" @@
  term_t @-> int @-> returning @@ int
let put_atom_chars = foreign "PL_put_atom_chars" @@
  term_t @-> string @-> returning @@ int
let put_string_chars = foreign "PL_put_string_chars" @@
  term_t @-> string @-> returning @@ int
let put_chars = foreign "PL_put_chars" @@
  term_t @-> int @-> size_t @-> string @-> returning @@ int
let put_list_chars = foreign "PL_put_list_chars" @@
  term_t @-> string @-> returning @@ int
let put_list_codes = foreign "PL_put_list_codes" @@
  term_t @-> string @-> returning @@ int
let put_atom_nchars = foreign "PL_put_atom_nchars" @@
  term_t @-> size_t @-> string @-> returning @@ int
let put_string_nchars = foreign "PL_put_string_nchars" @@
  term_t @-> size_t @-> string @-> returning @@ int
let put_list_nchars = foreign "PL_put_list_nchars" @@
  term_t @-> size_t @-> string @-> returning @@ int
let put_list_ncodes = foreign "PL_put_list_ncodes" @@
  term_t @-> size_t @-> string @-> returning @@ int
let put_integer = foreign "PL_put_integer" @@
  term_t @-> long @-> returning @@ int
let put_pointer = foreign "PL_put_pointer" @@
  term_t @-> ptr void @-> returning @@ int
let put_float = foreign "PL_put_float" @@
  term_t @-> double @-> returning @@ int
let put_functor = foreign "PL_put_functor" @@
  term_t @-> functor_t @-> returning @@ int
let put_list = foreign "PL_put_list" @@
  term_t @-> returning @@ int
let put_nil = foreign "PL_put_nil" @@
  term_t @-> returning @@ int
let put_term = foreign "PL_put_term" @@
  term_t @-> term_t @-> returning @@ int
let put_dict = foreign "PL_put_dict" @@
  term_t @-> atom_t @-> size_t @-> ptr (const atom_t) @-> term_t @-> returning @@ int

(* construct a functor or list-cell *)

let cons_functor_v = foreign "PL_cons_functor_v" @@
  term_t @-> functor_t @-> term_t @-> returning @@ int
let cons_list = foreign "PL_cons_list" @@
  term_t @-> term_t @-> term_t @-> returning @@ int

(* Unify term-references *)

let unify = foreign "PL_unify" @@
  term_t @-> term_t @-> returning @@ int
let unify_atom = foreign "PL_unify_atom" @@
  term_t @-> atom_t @-> returning @@ int
let unify_atom_chars = foreign "PL_unify_atom_chars" @@
  term_t @-> string @-> returning @@ int
let unify_list_chars = foreign "PL_unify_list_chars" @@
  term_t @-> string @-> returning @@ int
let unify_list_codes = foreign "PL_unify_list_codes" @@
  term_t @-> string @-> returning @@ int
let unify_string_chars = foreign "PL_unify_string_chars" @@
  term_t @-> string @-> returning @@ int
let unify_atom_nchars = foreign "PL_unify_atom_nchars" @@
  term_t @-> size_t @-> string @-> returning @@ int
let unify_list_ncodes = foreign "PL_unify_list_ncodes" @@
  term_t @-> size_t @-> string @-> returning @@ int
let unify_list_nchars = foreign "PL_unify_list_nchars" @@
  term_t @-> size_t @-> string @-> returning @@ int
let unify_string_nchars = foreign "PL_unify_string_nchars" @@
  term_t @-> size_t @-> string @-> returning @@ int
let unify_bool = foreign "PL_unify_bool" @@
  term_t @-> int @-> returning @@ int
let unify_integer = foreign "PL_unify_integer" @@
  term_t @-> intptr_t @-> returning @@ int
let unify_float = foreign "PL_unify_float" @@
  term_t @-> double @-> returning @@ int
let unify_pointer = foreign "PL_unify_pointer" @@
  term_t @-> ptr void @-> returning @@ int
let unify_functor = foreign "PL_unify_functor" @@
  term_t @-> functor_t @-> returning @@ int
let unify_compound = foreign "PL_unify_compound" @@
  term_t @-> functor_t @-> returning @@ int
let unify_list = foreign "PL_unify_list" @@
  term_t @-> term_t @-> term_t @-> returning @@ int
let unify_nil = foreign "PL_unify_nil" @@
  term_t @-> returning @@ int
let unify_arg = foreign "PL_unify_arg" @@
  size_t @-> term_t @-> term_t @-> returning @@ int
let unify_chars = foreign "PL_unify_chars" @@
  term_t @-> int @-> size_t @-> string @-> returning @@ int

(**** LISTS ****)

let skip_list = foreign "PL_skip_list" @@
  term_t @-> term_t @-> ptr size_t @-> returning @@ int

(**** WIDE CHARACTER VERSIONS ****)

let utf8_strlen = foreign "PL_utf8_strlen" @@
  string @-> size_t @-> returning @@ size_t

(**** WIDE INTEGERS ****)

let get_int64 = foreign "PL_get_int64" @@
  term_t @-> ptr int64_t @-> returning @@ int
let get_uint64 = foreign "PL_get_uint64" @@
  term_t @-> ptr uint64_t @-> returning @@ int
let unify_int64 = foreign "PL_unify_int64" @@
  term_t @-> int64_t @-> returning @@ int
let unify_uint64 = foreign "PL_unify_uint64" @@
  term_t @-> uint64_t @-> returning @@ int
let put_int64 = foreign "PL_put_int64" @@
  term_t @-> int64_t @-> returning @@ int
let put_uint64 = foreign "PL_put_uint64" @@
  term_t @-> uint64_t @-> returning @@ int

(**** ATTRIBUTED VARIABLES ****)

let is_attvar = foreign "PL_is_attvar" @@
  term_t @-> returning @@ int
let get_attr = foreign "PL_get_attr" @@
  term_t @-> term_t @-> returning @@ int

(**** ERRORS ****)

let get_atom_ex = foreign "PL_get_atom_ex" @@
  term_t @-> ptr atom_t @-> returning @@ int
let get_integer_ex = foreign "PL_get_integer_ex" @@
  term_t @-> ptr int @-> returning @@ int
let get_long_ex = foreign "PL_get_long_ex" @@
  term_t @-> ptr long @-> returning @@ int
let get_int64_ex = foreign "PL_get_int64_ex" @@
  term_t @-> ptr int64_t @-> returning @@ int
let get_uint64_ex = foreign "PL_get_uint64_ex" @@
  term_t @-> ptr uint64_t @-> returning @@ int
let get_intptr_ex = foreign "PL_get_intptr_ex" @@
  term_t @-> ptr intptr_t @-> returning @@ int
let get_size_ex = foreign "PL_get_size_ex" @@
  term_t @-> ptr size_t @-> returning @@ int
let get_bool_ex = foreign "PL_get_bool_ex" @@
  term_t @-> ptr int @-> returning @@ int
let get_float_ex = foreign "PL_get_float_ex" @@
  term_t @-> ptr double @-> returning @@ int
let get_char_ex = foreign "PL_get_char_ex" @@
  term_t @-> ptr int @-> int @-> returning @@ int
let unify_bool_ex = foreign "PL_unify_bool_ex" @@
  term_t @-> int @-> returning @@ int
let get_pointer_ex = foreign "PL_get_pointer_ex" @@
  term_t @-> ptr (ptr void) @-> returning @@ int
let unify_list_ex = foreign "PL_unify_list_ex" @@
  term_t @-> term_t @-> term_t @-> returning @@ int
let unify_nil_ex = foreign "PL_unify_nil_ex" @@
  term_t @-> returning @@ int
let get_list_ex = foreign "PL_get_list_ex" @@
  term_t @-> term_t @-> term_t @-> returning @@ int
let get_nil_ex = foreign "PL_get_nil_ex" @@
  term_t @-> returning @@ int

let instantiation_error = foreign "PL_instantiation_error" @@
  term_t @-> returning @@ int
let uninstantiation_error = foreign "PL_uninstantiation_error" @@
  term_t @-> returning @@ int
let representation_error = foreign "PL_representation_error" @@
  string @-> returning @@ int
let type_error = foreign "PL_type_error" @@
  string @-> term_t @-> returning @@ int
let domain_error = foreign "PL_domain_error" @@
  string @-> term_t @-> returning @@ int
let existence_error = foreign "PL_existence_error" @@
  string @-> term_t @-> returning @@ int
let permission_error = foreign "PL_permission_error" @@
  string @-> string @-> term_t @-> returning @@ int
let resource_error = foreign "PL_resource_error" @@
  string @-> returning @@ int

(**** FILENAME SUPPORT ****)

let get_file_name = foreign "PL_get_file_name" @@
  term_t @-> ptr (ptr char) @-> int @-> returning @@ int
let changed_cwd = foreign "PL_changed_cwd" @@
  void @-> returning @@ void
let cwd = foreign "PL_cwd" @@
  ptr char @-> size_t @-> returning @@ ptr char

(**** COMPARE ****)

let compare = foreign "PL_compare" @@
  term_t @-> term_t @-> returning @@ int
let same_compound = foreign "PL_same_compound" @@
  term_t @-> term_t @-> returning @@ int

(**** RECORDED DATABASE ****)

let record = foreign "PL_record" @@
  term_t @-> returning @@ record_t
let recorded = foreign "PL_recorded" @@
  record_t @-> term_t @-> returning @@ int
let erase = foreign "PL_erase" @@
  record_t @-> returning @@ void
let duplicate_record = foreign "PL_duplicate_record" @@
  record_t @-> returning @@ record_t

let record_external = foreign "PL_record_external" @@
  term_t @-> ptr size_t @-> returning @@ ptr char
let recorded_external = foreign "PL_recorded_external" @@
  string @-> term_t @-> returning @@ int
let erase_external = foreign "PL_erase_external" @@
  ptr char @-> returning @@ int

(**** EMBEDDING ****)

let initialise = foreign "PL_initialise" @@
  int @-> ptr (ptr char) @-> returning @@ int
let is_initialised = foreign "PL_is_initialised" @@
  ptr int @-> ptr (ptr (ptr char)) @-> returning @@ int
let toplevel = foreign "PL_toplevel" @@
  void @-> returning @@ int
let cleanup = foreign "PL_cleanup" @@
  int @-> returning @@ int
let cleanup_fork = foreign "PL_cleanup_fork" @@
  void @-> returning @@ void
let halt = foreign "PL_halt" @@
  int @-> returning @@ int

(**** VERSIONS ****)

let version_info = foreign "PL_version_info" @@
  int @-> returning @@ uint

(**** QUERY PROLOG ****)

let query = foreign "PL_query" @@
  int @-> returning @@ intptr_t

end
