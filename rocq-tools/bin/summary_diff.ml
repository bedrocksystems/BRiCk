(*
 * Copyright (C) 2023-2024 BlueRock Security Inc.
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; version 2.1.
 *
 * This library is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
 * for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 *)

(*
 * Copyright (C) BlueRock Security Inc. 2022
 *)

(** Short name for a standard formatter. *)
type 'a outfmt = ('a, Format.formatter, unit) format

(** Short name for a standard formatter with continuation. *)
type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

let use_colors : bool ref = ref true

(** Format transformers (colors). *)
let with_color k fmt =
  (if !use_colors then "\027["^^k^^"m" ^^ fmt ^^ "\027[0m" else fmt) ^^ "%!"

let red    fmt = with_color "31" fmt
let green  fmt = with_color "32" fmt
let yellow fmt = with_color "33" fmt

let info : 'a outfmt -> 'a = fun fmt ->
  Format.printf (fmt ^^ "%!")

let einfo : 'a outfmt -> 'a = fun fmt ->
  Format.eprintf (fmt ^^ "%!")

let wrn : 'a outfmt -> 'a = fun fmt ->
  Format.eprintf (yellow ("[Warning] " ^^ fmt ^^ "\n"))

let panic : ('a, 'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter
    (red ("[Panic] " ^^ fmt ^^ "\n"))

let iteri_lines : (int -> string -> unit) -> string -> unit = fun f fname ->
  let ic = open_in fname in
  let i = ref 0 in
  try
    while true do f !i (input_line ic); incr i done
  with End_of_file -> close_in ic

let foldi_lines : (int -> string -> 'a -> 'a) -> string -> 'a -> 'a =
    fun fn file a ->
  let acc = ref a in iteri_lines (fun i s -> acc := fn i s !acc) file; !acc

module SMap = Map.Make(String)
module SSet = Set.Make(String)

let excluded = ref []

let add_excluded : string -> unit = fun dir ->
  excluded := dir :: !excluded

let filter_excluded : 'a SMap.t -> 'a SMap.t = fun m ->
  let excluded = !excluded in
  let not_excluded file _ =
    let not_prefix prefix = not (String.starts_with ~prefix file) in
    List.for_all not_prefix excluded
  in
  SMap.filter not_excluded m

let map_domain : 'a SMap.t -> SSet.t = fun m ->
  SMap.fold (fun k _ s -> SSet.add k s) m SSet.empty

type instr_count = int

let parse_file : string -> instr_count SMap.t = fun csv_file ->
  let add i line m =
    if i = 0 then m else
    let (file, instr) =
      match String.split_on_char ',' line with
      | file :: instr :: _ -> (String.trim file, String.trim instr)
      | _ -> panic "%s, line %i: bad number of fields" csv_file i
    in
    if SMap.mem file m then
      panic "several entries for \"%s\"" file;
    if instr = "" then m else
    let instr =
      try int_of_string instr with Invalid_argument(_) ->
        panic "%s, line %i: bad instruction count %S" csv_file i instr
    in
    SMap.add file instr m
  in
  filter_excluded (foldi_lines add csv_file SMap.empty)

type 'a by_type = {
  bt_total: 'a;
  bt_cpp2v: 'a;
  bt_other: 'a;
}

let is_cpp2v fname =
  String.ends_with ~suffix:"_hpp.v"       fname ||
  String.ends_with ~suffix:"_cpp.v"       fname ||
  String.ends_with ~suffix:"_hpp_names.v" fname ||
  String.ends_with ~suffix:"_cpp_names.v" fname

let bt_add fname (bt : instr_count by_type) (v : instr_count) =
  if is_cpp2v fname then
    {bt with
     bt_total = bt.bt_total + v;
     bt_cpp2v = bt.bt_cpp2v + v;}
  else
    {bt with
     bt_total = bt.bt_total + v;
     bt_other = bt.bt_other + v;}

let bt_zero : instr_count by_type = { bt_total = 0; bt_cpp2v = 0; bt_other = 0 }


type diff = int * float

let make_diff : instr_count -> instr_count -> diff = fun ic_ref ic_new ->
  let diff_abs = ic_new - ic_ref in
  (diff_abs, float_of_int (100 * diff_abs) /. float_of_int ic_ref)

let bt_make_diff : instr_count by_type -> instr_count by_type -> diff by_type = fun ic_ref ic_new ->
  let bt_total = make_diff ic_ref.bt_total ic_new.bt_total in
  let bt_cpp2v = make_diff ic_ref.bt_cpp2v ic_new.bt_cpp2v in
  let bt_other = make_diff ic_ref.bt_other ic_new.bt_other in
  { bt_total; bt_cpp2v; bt_other }


let default_color_threshold    = 0.5
let default_relevant_threshold = 0.1
let default_instr_threshold    = 0.5

let color_threshold    : float ref = ref default_color_threshold
let relevant_threshold : float ref = ref default_relevant_threshold
let instr_threshold    : float ref = ref default_instr_threshold
let show_everything    : bool  ref = ref false

let missing_unchanged  : bool  ref = ref false

let color diff =
  if diff < -. !color_threshold then green else
  if diff > !color_threshold then red else
  (fun x -> x)

type output_format =
  | Markdown
  | Gitlab
  | CSV

let output_format : output_format ref = ref Markdown
let diff_base_url : string option ref = ref None

let print_md_summary (total_ref, total_new, total_diff, (num_dis, total_dis), (num_app, total_app)) =
  (* Printing the totals. *)
  let print_summary infostring total_ref total_new total_diff =
    let n0 = float_of_int total_ref /. 1000000000.0 in
    let n1 = float_of_int total_new /. 1000000000.0 in
    let d = float_of_int (fst total_diff) /. 1000000000.0 in
    info ("|" ^^ color (snd total_diff) " %+7.2f%% " ^^ "| %8.1f | %8.1f | %+8.1f | %s\n")
      (snd total_diff) n0 n1 d infostring
  in
  print_summary "cpp2v-generated" total_ref.bt_cpp2v total_new.bt_cpp2v total_diff.bt_cpp2v;
  print_summary "other"           total_ref.bt_other total_new.bt_other total_diff.bt_other;
  (if num_dis > 0 then
      let disappeared_label = Printf.sprintf "disappeared files: %i" num_dis in
      print_summary disappeared_label 0 0 total_dis);
  (if num_app > 0 then
      let appeared_label = Printf.sprintf "newly appeared files: %i" num_app in
      print_summary appeared_label    0 0 total_app);
  print_summary "total"           total_ref.bt_total total_new.bt_total total_diff.bt_total

let print_md_header () =
  info "| Relative | Master   | MR       | Change   | Filename\n";
  info "|---------:|---------:|---------:|---------:|----------\n"

let print_md_data totals combined =
  print_md_header ();
  let add_url k =
    match !diff_base_url with
    | None -> k
    | Some(url) ->
        Printf.sprintf "[%s](%s/%s.html)" k url (Filename.chop_extension k)
  in
  let fn (k, (n0, n1, (d, diff))) =
    let instr_diff = float_of_int d /. 1000000000.0 in
    let relevant =
      abs_float diff >= !relevant_threshold &&
      abs_float instr_diff >= !instr_threshold

    in
    if !show_everything || relevant then
      let n0 = float_of_int n0 /. 1000000000.0 in
      let n1 = float_of_int n1 /. 1000000000.0 in
      info ("|" ^^ color diff " %+7.2f%% " ^^ "| %8.1f | %8.1f | %+8.1f | %s\n")
        diff n0 n1 instr_diff (add_url k)
  in
  List.iter fn combined;
  info "|          |          |          |          |          \n";
  print_md_summary totals

let print_gitlab_data totals combined =
  let fn url =  info "\nFull performance report URL: %s/index.html\n\n" url in
  Option.iter fn !diff_base_url;
  print_md_header ();
  print_md_summary totals;
  info "\n<details><summary>Full Results</summary>\n\n";
  print_md_data totals combined;
  info "\n</details>\n"


let print_csv_data (total_ref, total_new, total_diff, _, _) combined =
  info "Relative (%%),Master (instr),MR (instr),Change (instr),Filename\n";
  let fn (k, (n0, n1, (d, diff))) =
    info "%f,%i,%i,%i,%s\n" diff n0 n1 d k
  in
  List.iter fn combined;
  (* Printing the total. *)
  info "%f,%i,%i,%i,*\n" (snd total_diff.bt_total) total_ref.bt_total total_new.bt_total (fst total_diff.bt_total)

let analyse : string -> string list -> unit = fun file_ref files_new ->
  let data_ref = parse_file file_ref in
  let data_new = List.map parse_file files_new in
  let data_new =
    List.fold_left (SMap.union (fun _key _old_val new_val -> Some(new_val))) SMap.empty data_new
  in
  let ref_files = map_domain data_ref in
  let new_files = map_domain data_new in
  let all_files = SSet.union ref_files new_files in
  (* Warn about files that disappeared. *)
  let disappeared = SSet.diff all_files new_files in
  (* compute number of missing files and combined instruction count *)
  let num_disappeared = SSet.cardinal disappeared in
  let total_disappeared = SSet.fold (fun el acc -> acc + SMap.find el data_ref) disappeared 0 in
  let () =
    if not !missing_unchanged then
      SSet.iter (wrn "Ignoring removed file [%s].") disappeared;
  in
  (* Warn about files that appeared. *)
  let appeared = SSet.diff all_files ref_files in
  let num_appeared = SSet.cardinal appeared in
  let total_appeared = SSet.fold (fun el acc -> acc + SMap.find el data_new) appeared 0 in
  SSet.iter (wrn "Ignoring new file [%s].") appeared;
  (* Combine the data. *)
  let combined : (instr_count * instr_count * diff) SMap.t =
    let fn file file_data_ref m =
      try
        let file_data_new = SMap.find file data_new in
        let diff = make_diff file_data_ref file_data_new in
        SMap.add file (file_data_ref, file_data_new, diff) m
      with
      | Not_found when     !missing_unchanged ->
        let diff = make_diff file_data_ref file_data_ref in
        SMap.add file (file_data_ref, file_data_ref, diff) m
      | Not_found when not !missing_unchanged -> m
    in
    SMap.fold fn data_ref SMap.empty
  in
  (* Computing the total. *)
  let (total_ref, total_new) =
    let fn fname (d1,d2,_) (acc1,acc2) =
      (bt_add fname acc1 d1, bt_add fname acc2 d2)
    in
    SMap.fold fn combined (bt_zero, bt_zero)
  in
  let total_diff = bt_make_diff total_ref total_new in
  (* Calculate percentage of missing instructions *)
  let total_disappeared =
    let (instr, perc) = make_diff total_ref.bt_total (total_ref.bt_total - total_disappeared) in
    let perc =  -1.0 *. perc  in
    let instr = -1   *  instr in
    (instr, perc)
  in
  let total_appeared =
    let (instr, perc) = make_diff total_ref.bt_total (total_new.bt_total - total_appeared) in
    let perc =  -1.0 *. perc  in
    let instr = -1   *  instr in
    (instr, perc)
  in
  (* Sorting by instruction diff percentage. *)
  let combined = SMap.bindings combined in
  let cmp (_, (_, _, d1)) (_, (_, _, d2)) = compare (snd d1) (snd d2) in
  let combined = List.sort cmp combined in
  (* Printing the data. *)
  let print =
    match !output_format with
    | Markdown -> print_md_data
    | Gitlab   -> print_gitlab_data
    | CSV      -> print_csv_data
  in

  print (total_ref, total_new, total_diff, (num_disappeared, total_disappeared), (num_appeared, total_appeared)) combined

let usage : string -> bool -> 'a = fun prog_name error ->
  if error then panic "Usage: %s REF.csv NEW_1.csv .. NEW_n.csv" prog_name;
  einfo "Usage: %s REF.csv NEW_1.csv .. NEW_n.csv\n\n" prog_name;
  einfo "Output the total and per-file differences in instruction counts between \
         the reference pipeline REF.csv and multiple target pipelines NEW_i.csv.\n\n";
  einfo "By default, files only appearing in the reference pipeline or the \
         target pipelines are treated as removed or newly added, respectively, \
         and discarded for the purpose of comparison. The flag --assume-missing-unchanged \
         changes the former case by assuming that the files missing from the \
         target pipelines have the same performance as in the reference \
         pipelines and including them in the total instruction count.\n";
  einfo "NOTE: Always list NEW_i.csv files in chronological order. In case of overlap, \
         rightmost wins.\n\n";
  einfo "Supported arguments:\n";
  einfo "  --help, -h                 \tShow this help message.\n";
  einfo "  --no-colors                \tDo not output any colors.\n";
  einfo "  --show-all                 \tInclude all data in the output.\n";
  einfo "  --color-threshold FLOAT    \tMinimum difference shown in color \
                                        (in percent, default %1.1f).\n"
                                        default_color_threshold;
  einfo "  --threshold FLOAT          \tMinimum difference considered \
                                        significant (in percent, default = %1.1f\
                                        ).\n" default_relevant_threshold;
  einfo "  --instr-threshold FLOAT    \tMinimum difference considered \
                                        significant (in billions of \
                                        instructons, default %1.1f).\n"
                                        default_instr_threshold;
  einfo "  --csv                      \tPrint the full raw data in CSV.\n";
  einfo "  --gitlab                   \tMarkdown output compiled into a \
                                        small summary and a <details> section.\n";
  einfo "  --diff-base-url URL        \tSpecify the base URL for diffs.\n";
  einfo "  --assume-missing-unchanged \tTreat missing files as having unchanged \
                                        performance results.\n";
  einfo "  --exclude DIR              \tExcludes files whose path starts \
                                        with DIR.\n";
  exit 0

let main () =
  let (prog_name, args) =
    let args = List.tl (Array.to_list Sys.argv) in
    (Sys.argv.(0), args)
  in
  let rec parse_args files args =
    let is_flag arg = String.length arg > 0 && arg.[0] = '-' in
    let parse_float opt s =
      try float_of_string s with Failure(_) ->
        panic "Invalid parameter for argument \"%s\" (found \"%s\")." opt s
    in
    match args with
    | ("--help" | "-h")             :: _                     ->
        usage prog_name false
    | "--no-colors"                 :: args                  ->
        use_colors := false;
        parse_args files args
    | "--show-all"                  :: args                  ->
        show_everything := true;
        parse_args files args
    | "--color-threshold" as a      :: []                    ->
        panic "Command line argument \"%s\" expects a float." a;
    | "--color-threshold" as a :: f :: args                  ->
        color_threshold := parse_float a f;
        parse_args files args
    | "--threshold"       as a      :: []                    ->
        panic "Command line argument \"%s\" expects a float." a;
    | "--threshold"       as a :: f :: args                  ->
        relevant_threshold := parse_float a f;
        parse_args files args
    | "--instr-threshold" as a      :: []                    ->
        panic "Command line argument \"%s\" expects an int." a;
    | "--instr-threshold" as a :: f :: args                  ->
        instr_threshold := parse_float a f;
        parse_args files args
    | "--csv"                       :: args                  ->
        output_format := CSV;
        parse_args files args
    | "--gitlab"                    :: args                  ->
        output_format := Gitlab;
        parse_args files args
    | "--diff-base-url" :: url      :: args                  ->
        diff_base_url := Some(url);
        parse_args files args
    | "--assume-missing-unchanged"  :: args                  ->
        missing_unchanged := true;
        parse_args files args
    | "--exclude" :: dir            :: args                  ->
        add_excluded dir;
        parse_args files args
    | arg                           :: _ when is_flag arg    ->
        panic "Invalid command line argument \"%s\"." arg;
    | file                          :: args                  ->
        if try Sys.is_directory file with Sys_error(_) -> false then
          panic "File expected, [%s] is a directory." file;
        if not (Sys.file_exists file) then
          panic "No such file or directory [%s]." file;
        parse_args (file :: files) args
    | []                                                     ->
        List.rev files
  in
  let files = parse_args [] args in
  match files with
  | file1 :: (_ :: _ as files) -> analyse file1 files
  | _                          ->
      let n = List.length files in
      panic "at least 2 file paths expected on the command line (%i given)." n

let _ =
  try main () with
  | Sys_error(msg) -> panic "%s" msg
  | e              -> panic "Uncaught exception: %s." (Printexc.to_string e)
