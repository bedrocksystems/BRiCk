(* Generated file: do not edit. *)
module Types(I : Ctypes.TYPE) = struct
  open I

(**** TYPES ****)

(* Prolog atom *)
let atom_t = typedef uintptr_t "atom_t"

(* Name/arity pair *)
let functor_t = typedef uintptr_t "functor_t"

(* Prolog module *)
let module_t = typedef (ptr void) "module_t"

(* Prolog procedure *)
let predicate_t = typedef (ptr void) "predicate_t"

(* Prolog recorded term *)
let record_t = typedef (ptr void) "record_t"

(* opaque term handle *)
let term_t = typedef uintptr_t "term_t"

(* opaque query handle *)
let qid_t = typedef (ptr void) "qid_t"

(* opaque foreign context handle *)
let fid_t = typedef uintptr_t "fid_t"

(* return type of foreign functions *)
let foreign_t = typedef uintptr_t "foreign_t"

(* foreign language functions *)
let pl_function_t =
  let ftype = foreign_t @-> returning void in
  typedef (static_funptr ftype) "pl_function_t"

(* PL_unify_term() arguments *)

(* nothing *)
let _VARIABLE = constant "PL_VARIABLE" int

let _ATOM = constant "PL_ATOM" int

(* int *)
let _INTEGER = constant "PL_INTEGER" int

(* rational number *)
let _RATIONAL = constant "PL_RATIONAL" int

(* double *)
let _FLOAT = constant "PL_FLOAT" int

let _STRING = constant "PL_STRING" int

let _TERM = constant "PL_TERM" int

(* The constant [] *)
let _NIL = constant "PL_NIL" int

(* non-atom blob *)
let _BLOB = constant "PL_BLOB" int

(* [_|_] term *)
let _LIST_PAIR = constant "PL_LIST_PAIR" int

(* PL_unify_term() *)

(* functor_t, arg ... *)
let _FUNCTOR = constant "PL_FUNCTOR" int

(* length, arg ... *)
let _LIST = constant "PL_LIST" int

let _CHARS = constant "PL_CHARS" int

let _POINTER = constant "PL_POINTER" int

(* PlArg::PlArg(text, type) *)

(* [ascii...] *)
let _CODE_LIST = constant "PL_CODE_LIST" int

(* [h,e,l,l,o] *)
let _CHAR_LIST = constant "PL_CHAR_LIST" int

(* PL_set_prolog_flag() *)
let _BOOL = constant "PL_BOOL" int

(* PL_unify_term() *)
let _FUNCTOR_CHARS = constant "PL_FUNCTOR_CHARS" int

(* predicate_t (Procedure) *)
let __PL_PREDICATE_INDICATOR = constant "_PL_PREDICATE_INDICATOR" int

(* short *)
let _SHORT = constant "PL_SHORT" int

(* int *)
let _INT = constant "PL_INT" int

(* long *)
let _LONG = constant "PL_LONG" int

(* double *)
let _DOUBLE = constant "PL_DOUBLE" int

let _NCHARS = constant "PL_NCHARS" int

let _UTF8_CHARS = constant "PL_UTF8_CHARS" int

let _UTF8_STRING = constant "PL_UTF8_STRING" int

(* int64_t *)
let _INT64 = constant "PL_INT64" int

let _NUTF8_CHARS = constant "PL_NUTF8_CHARS" int

let _NUTF8_CODES = constant "PL_NUTF8_CODES" int

let _NUTF8_STRING = constant "PL_NUTF8_STRING" int

let _MBCHARS = constant "PL_MBCHARS" int

let _MBCODES = constant "PL_MBCODES" int

let _MBSTRING = constant "PL_MBSTRING" int

(* intptr_t *)
let _INTPTR = constant "PL_INTPTR" int

(* int *)
let _CHAR = constant "PL_CHAR" int

(* int *)
let _CODE = constant "PL_CODE" int

(* int *)
let _BYTE = constant "PL_BYTE" int

(* PL_skip_list() *)

(* a partial list *)
let _PARTIAL_LIST = constant "PL_PARTIAL_LIST" int

(* a cyclic list/term *)
let _CYCLIC_TERM = constant "PL_CYCLIC_TERM" int

(* Object is not a list *)
let _NOT_A_LIST = constant "PL_NOT_A_LIST" int

(* dicts *)

let _DICT = constant "PL_DICT" int

(* Or'ed flags for PL_set_prolog_flag() (MUST fit in a short int) *)

(* Read-only prolog flag *)
let _FF_READONLY = constant "FF_READONLY" int

(* keep prolog flag if already set *)
let _FF_KEEP = constant "FF_KEEP" int

(* Fail if flag is non-existent *)
let _FF_NOCREATE = constant "FF_NOCREATE" int

(* Force setting, overwrite READONLY *)
let _FF_FORCE = constant "FF_FORCE" int

let _FF_MASK = constant "FF_MASK" int

(**** CALL-BACK ****)

(* normal usage *)
let _Q_NORMAL = constant "PL_Q_NORMAL" int

(* use this one *)
let _Q_NODEBUG = constant "PL_Q_NODEBUG" int

(* handle exceptions in C *)
let _Q_CATCH_EXCEPTION = constant "PL_Q_CATCH_EXCEPTION" int

(* pass to parent environment *)
let _Q_PASS_EXCEPTION = constant "PL_Q_PASS_EXCEPTION" int

(* Support I_YIELD *)
let _Q_ALLOW_YIELD = constant "PL_Q_ALLOW_YIELD" int

(* Return extended status *)
let _Q_EXT_STATUS = constant "PL_Q_EXT_STATUS" int

(* PL_Q_EXT_STATUS return codes *)

(* Query raised exception *)
let _S_EXCEPTION = constant "PL_S_EXCEPTION" int

(* Query failed *)
let _S_FALSE = constant "PL_S_FALSE" int

(* Query succeeded with choicepoint *)
let _S_TRUE = constant "PL_S_TRUE" int

(* Query succeeded without CP *)
let _S_LAST = constant "PL_S_LAST" int

(* Foreign yield *)
let _S_YIELD = constant "PL_S_YIELD" int

(**** ASSERT ****)

let _ASSERTZ = constant "PL_ASSERTZ" int

let _ASSERTA = constant "PL_ASSERTA" int

let _CREATE_THREAD_LOCAL = constant "PL_CREATE_THREAD_LOCAL" int

let _CREATE_INCREMENTAL = constant "PL_CREATE_INCREMENTAL" int

(**** FILENAME SUPPORT ****)

(* return absolute path *)
let _FILE_ABSOLUTE = constant "PL_FILE_ABSOLUTE" int

(* return path in OS notation *)
let _FILE_OSPATH = constant "PL_FILE_OSPATH" int

(* use file_search_path *)
let _FILE_SEARCH = constant "PL_FILE_SEARCH" int

(* demand file to exist *)
let _FILE_EXIST = constant "PL_FILE_EXIST" int

(* demand read-access *)
let _FILE_READ = constant "PL_FILE_READ" int

(* demand write-access *)
let _FILE_WRITE = constant "PL_FILE_WRITE" int

(* demand execute-access *)
let _FILE_EXECUTE = constant "PL_FILE_EXECUTE" int

(* do not raise exceptions *)
let _FILE_NOERRORS = constant "PL_FILE_NOERRORS" int

(**** CHAR BUFFERS ****)

let _CVT_ATOM = constant "CVT_ATOM" int

let _CVT_STRING = constant "CVT_STRING" int

let _CVT_LIST = constant "CVT_LIST" int

let _CVT_INTEGER = constant "CVT_INTEGER" int

let _CVT_RATIONAL = constant "CVT_RATIONAL" int

let _CVT_FLOAT = constant "CVT_FLOAT" int

let _CVT_VARIABLE = constant "CVT_VARIABLE" int

let _CVT_NUMBER = constant "CVT_NUMBER" int

let _CVT_ATOMIC = constant "CVT_ATOMIC" int

let _CVT_WRITE = constant "CVT_WRITE" int

let _CVT_WRITE_CANONICAL = constant "CVT_WRITE_CANONICAL" int

let _CVT_WRITEQ = constant "CVT_WRITEQ" int

let _CVT_ALL = constant "CVT_ALL" int

let _CVT_MASK = constant "CVT_MASK" int

(* throw exception on error *)
let _CVT_EXCEPTION = constant "CVT_EXCEPTION" int

(* return 2 if argument is unbound *)
let _CVT_VARNOFAIL = constant "CVT_VARNOFAIL" int

(* Store in single thread-local buffer *)
let _BUF_DISCARDABLE = constant "BUF_DISCARDABLE" int

(* Store in stack of buffers *)
let _BUF_STACK = constant "BUF_STACK" int

(* Store using PL_malloc() *)
let _BUF_MALLOC = constant "BUF_MALLOC" int

(* Allow pointer into (global) stack *)
let _BUF_ALLOW_STACK = constant "BUF_ALLOW_STACK" int

(* output representation *)
let _REP_ISO_LATIN_1 = constant "REP_ISO_LATIN_1" int

let _REP_UTF8 = constant "REP_UTF8" int

let _REP_MB = constant "REP_MB" int

let _REP_FN = constant "REP_FN" int

(* PL_unify_chars() *)
let _DIFF_LIST = constant "PL_DIFF_LIST" int

(**** EMBEDDING ****)

let _CLEANUP_STATUS_MASK = constant "PL_CLEANUP_STATUS_MASK" int

let _CLEANUP_NO_RECLAIM_MEMORY = constant "PL_CLEANUP_NO_RECLAIM_MEMORY" int

let _CLEANUP_NO_CANCEL = constant "PL_CLEANUP_NO_CANCEL" int

let _CLEANUP_CANCELED = constant "PL_CLEANUP_CANCELED" int

let _CLEANUP_SUCCESS = constant "PL_CLEANUP_SUCCESS" int

let _CLEANUP_FAILED = constant "PL_CLEANUP_FAILED" int

let _CLEANUP_RECURSIVE = constant "PL_CLEANUP_RECURSIVE" int

(**** VERSIONS ****)

(* Prolog version *)
let _VERSION_SYSTEM = constant "PL_VERSION_SYSTEM" int

let _VERSION_FLI = constant "PL_VERSION_FLI" int

(* PL_record_external() compatibility *)
let _VERSION_REC = constant "PL_VERSION_REC" int

(* Saved QLF format version *)
let _VERSION_QLF = constant "PL_VERSION_QLF" int

(* Min loadable QLF format version *)
let _VERSION_QLF_LOAD = constant "PL_VERSION_QLF_LOAD" int

(* VM signature *)
let _VERSION_VM = constant "PL_VERSION_VM" int

(* Built-in predicate signature *)
let _VERSION_BUILT_IN = constant "PL_VERSION_BUILT_IN" int

(**** QUERY PROLOG ****)

(* return main() argc *)
let _QUERY_ARGC = constant "PL_QUERY_ARGC" int

(* return main() argv *)
let _QUERY_ARGV = constant "PL_QUERY_ARGV" int

(* Read character from terminal *)
let _QUERY_GETC = constant "PL_QUERY_GETC" int

(* largest integer *)
let _QUERY_MAX_INTEGER = constant "PL_QUERY_MAX_INTEGER" int

(* smallest integer *)
let _QUERY_MIN_INTEGER = constant "PL_QUERY_MIN_INTEGER" int

(* largest tagged integer *)
let _QUERY_MAX_TAGGED_INT = constant "PL_QUERY_MAX_TAGGED_INT" int

(* smallest tagged integer *)
let _QUERY_MIN_TAGGED_INT = constant "PL_QUERY_MIN_TAGGED_INT" int

(* 207006 = 2.7.6 *)
let _QUERY_VERSION = constant "PL_QUERY_VERSION" int

(* maximum thread count *)
let _QUERY_MAX_THREADS = constant "PL_QUERY_MAX_THREADS" int

(* I/O encoding *)
let _QUERY_ENCODING = constant "PL_QUERY_ENCODING" int

(* User CPU in milliseconds *)
let _QUERY_USER_CPU = constant "PL_QUERY_USER_CPU" int

(* If TRUE, we are in PL_cleanup() *)
let _QUERY_HALTING = constant "PL_QUERY_HALTING" int

end
