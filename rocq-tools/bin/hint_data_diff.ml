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

open Rocq_tools
open Rocq_tools.Extra

type data = Spandata.Data.t

let no_data : data =
  Spandata.Data.{count = 0; instr = 0}

type hint_data = {
  success : data;
  failure : data;
}

let make_hint_data : data option -> data option -> hint_data =
    fun success failure ->
  match (success, failure) with
  | (Some(success), Some(failure)) -> {success; failure}
  | (Some(success), None         ) -> {success; failure = no_data}
  | (None         , Some(failure)) -> {success = no_data; failure}
  | (None         , None         ) -> {success = no_data; failure = no_data}

module SMap = Map.Make(String)

type map = hint_data SMap.t

let read_data_file : string -> map = fun file ->
  let spandata =
    let spandata = Spandata.add_csv_file file Spandata.M.empty in
    let filter Spandata.Key.{span_path; span} =
      match span.Spandata.Span.status with
      | Some("hintOK" | "hintKO") -> Some(Spandata.Key.{span_path=[]; span})
      | _                         -> None
    in
    Spandata.aggregate_filter filter spandata
  in
  let (data_ok, data_ko) =
    let insert key data ((data_ok, data_ko) as acc) =
      let Spandata.Span.{name; status} = key.Spandata.Key.span in
      match status with
      | Some("hintOK") -> (SMap.add name data data_ok, data_ko)
      | Some("hintKO") -> (data_ok, SMap.add name data data_ko)
      | _              -> acc
    in
    Spandata.M.fold insert spandata (SMap.empty, SMap.empty)
  in
  SMap.merge (fun _ s f -> Some(make_hint_data s f)) data_ok data_ko

type combined = (hint_data option * hint_data option) SMap.t

(* Also filters unchanged data. *)
let combine_data : map -> map -> combined = fun old_map new_map ->
  let make _ old_hd new_hd =
    let same_counts old_hd new_hd =
      match (old_hd, new_hd) with
      | (Some(old_hd), Some(new_hd)) ->
          old_hd.success.count = new_hd.success.count &&
          old_hd.failure.count = new_hd.failure.count
      | (_           , _           ) ->
          false
    in
    if same_counts old_hd new_hd then None else Some(old_hd, new_hd)
  in
  SMap.merge make old_map new_map

let pp_markdown : Out_channel.t -> combined -> unit = fun oc combined ->
  let output_line name data =
    let percent_success_ratio data =
      let success_count = Float.of_int data.success.count in
      let total = Float.of_int (data.success.count + data.failure.count) in
      (100.0 *. success_count) /. total
    in
    let split_name name =
      let name = String.split_on_char '.' name in
      match List.rev name with
      | []         -> assert false
      | name :: [] -> (None, name)
      | name :: mp -> (Some (String.concat "." (List.rev mp)), name)
    in
    let (mod_path, name) = split_name name in
    let pp_mod_path oc mod_path =
      match mod_path with
      | None     -> ()
      | Some(mp) -> Printf.fprintf oc "%s.<br>" mp
    in
    match data with
    | (None          , None          ) ->
        assert false (* Unreachable. *)
    | (Some(old_data), None          ) ->
        let ratio = percent_success_ratio old_data in
        Printf.fprintf oc "| %i | %i | %0.2f%% | %a[-%s-] |\n"
          old_data.success.count old_data.failure.count ratio
          pp_mod_path mod_path name
    | (None          , Some(new_data)) ->
        let ratio = percent_success_ratio new_data in
        Printf.fprintf oc "| %i | %i | %0.2f%% | %a[+%s+] |\n"
          new_data.success.count new_data.failure.count ratio
          pp_mod_path mod_path name
    | (Some(old_data), Some(new_data)) ->
        let s_diff = new_data.success.count - old_data.success.count in
        let f_diff = new_data.failure.count - old_data.failure.count in
        let old_ratio = percent_success_ratio old_data in
        let new_ratio = percent_success_ratio new_data in
        let ratio_diff = new_ratio -. old_ratio in
        Printf.fprintf oc "| (%+i) %i | (%+i) %i | "
          s_diff new_data.success.count
          f_diff new_data.failure.count;
        let (l,r) =
          if new_ratio < old_ratio then ("[-", "-]") else
          if new_ratio > old_ratio then ("[+", "+]") else ("", "")
        in
        Printf.fprintf oc "(%s%+0.2f%%%s) %0.2f%% | %a%s |\n"
          l ratio_diff r new_ratio
          pp_mod_path mod_path name
  in
  Printf.fprintf oc "| (diff) #✓ | (diff) #✕ | (diff) ✓-ratio | Hint |\n";
  Printf.fprintf oc "|----------:|----------:|---------------:|------|\n";
  SMap.iter output_line combined

let pp_html : Out_channel.t -> combined -> unit = fun oc combined ->
  let line fmt = Printf.fprintf oc (fmt ^^ "\n") in
  let output_line (name, data) =
    let percent_success_ratio data =
      let success_count = Float.of_int data.success.count in
      let total = Float.of_int (data.success.count + data.failure.count) in
      (100.0 *. success_count) /. total
    in
    let split_name name =
      let name = String.split_on_char '.' name in
      match List.rev name with
      | []         -> assert false
      | name :: [] -> (None, name)
      | name :: mp -> (Some (String.concat "." (List.rev mp)), name)
    in
    let (mod_path, name) = split_name name in
    let pp_mod_path oc mod_path =
      match mod_path with
      | None     -> ()
      | Some(mp) -> Printf.fprintf oc "%s." mp
    in
    Printf.fprintf oc "    <tr";
    let m = 1_000_000 in
    begin
      match data with
      | (None          , None          ) ->
          assert false (* Unreachable. *)
      | (Some(old_data), None          ) ->
          let status = "removed" in
          Printf.fprintf oc " class=%S>" status;
          let ratio = percent_success_ratio old_data in
          Printf.fprintf oc "<td>%i</td>" old_data.success.count;
          Printf.fprintf oc "<td>%i</td>" old_data.failure.count;
          Printf.fprintf oc "<td>%0.2f%%</td>" ratio;
          Printf.fprintf oc "<td>%i</td>" (old_data.success.instr / m);
          Printf.fprintf oc "<td>%i</td>" (old_data.failure.instr / m);
          Printf.fprintf oc "<td>%i</td>"
            ((old_data.success.instr + old_data.failure.instr) / m);
          Printf.fprintf oc
            "<td><span title=\"%a%s\">%s (%s)</span></td>"
            pp_mod_path mod_path name name status
      | (None          , Some(new_data)) ->
          let status = "added" in
          Printf.fprintf oc " class=%S>" status;
          let ratio = percent_success_ratio new_data in
          Printf.fprintf oc "<td>%i</td>" new_data.success.count;
          Printf.fprintf oc "<td>%i</td>" new_data.failure.count;
          Printf.fprintf oc "<td>%0.2f%%</td>" ratio;
          Printf.fprintf oc "<td>%i</td>" (new_data.success.instr / m);
          Printf.fprintf oc "<td>%i</td>" (new_data.failure.instr / m);
          Printf.fprintf oc "<td>%i</td>"
            ((new_data.success.instr + new_data.failure.instr) / m);
          Printf.fprintf oc
            "<td><span title=\"%a%s\">%s (%s)</span></td>"
            pp_mod_path mod_path name name status
      | (Some(old_data), Some(new_data)) ->
          Printf.fprintf oc ">";
          let s_diff = new_data.success.count - old_data.success.count in
          let f_diff = new_data.failure.count - old_data.failure.count in
          let old_ratio = percent_success_ratio old_data in
          let new_ratio = percent_success_ratio new_data in
          let ratio_diff = new_ratio -. old_ratio in
          Printf.fprintf oc "<td>(%+i) %i</td>" s_diff new_data.success.count;
          Printf.fprintf oc "<td>(%+i) %i</td>" f_diff new_data.failure.count;
          let (l,r) =
            if new_ratio < old_ratio then
              ("<span class=\"neg\">", "</span>")
            else if new_ratio > old_ratio then
              ("<span class=\"pos\">", "</span>")
            else
              ("", "")
          in
          Printf.fprintf oc "<td>(%s%+0.2f%%%s) %0.2f%%</td>"
            l ratio_diff r new_ratio;
          let total_old = old_data.success.instr + old_data.failure.instr in
          let total_new = new_data.success.instr + new_data.failure.instr in
          let total_diff = total_new - total_old in
          let s_diff = new_data.success.instr - old_data.success.instr in
          let f_diff = new_data.failure.instr - old_data.failure.instr in
          Printf.fprintf oc "<td>(%+i) %i</td>"
            (s_diff / m) (new_data.success.instr / m);
          Printf.fprintf oc "<td>(%+i) %i</td>"
            (f_diff / m) (new_data.failure.instr / m);
          Printf.fprintf oc "<td>(%+i) %i</td>"
            (total_diff / m) (total_new / m);
          Printf.fprintf oc
            "<td><span title=\"%a%s\">%s</span></td>"
            pp_mod_path mod_path name name
    end;
    Printf.fprintf oc "</tr>\n"
  in
  line "<!DOCTYPE html>";
  line "<html lang=\"en\">";
  line "<head>";
  line "  <meta charset=\"utf-8\">";
  line "  <title>Hint Data Diff</title>";
  line "  <style>";
  line "    span.neg { color: red  ; }";
  line "    span.pos { color: green; }";
  line "    table, th, td {";
  line "      border:1px solid black;";
  line "      border-collapse: collapse;";
  line "    }";
  line "    tr.added   { background-color: #f2fff2; }";
  line "    tr.removed { background-color: #fff2f2; }";
  line "  </style>";
  line "</head>";
  line "<body>";
  line "  <table>";
  line "    <tr>";
  line "      <th>(diff) #✓</th>";
  line "      <th>(diff) #✕</th>";
  line "      <th>(diff) ✓-ratio</th>";
  line "      <th>(diff) ✓-Mi</th>";
  line "      <th>(diff) ✕-Mi</th>";
  line "      <th>(diff) Mi</th>";
  line "      <th>Hint</th>";
  line "    </tr>";
  let instr_weight data =
    match data with
    | (None      , None      ) -> 0
    | (Some(data), None      )
    | (_         , Some(data)) -> data.success.instr + data.failure.instr
  in
  let by_new_total_instr (_, data1) (_, data2) =
    Int.compare (instr_weight data2) (instr_weight data1)
  in
  let combined = SMap.bindings combined in
  let combined = List.sort by_new_total_instr combined in
  List.iter output_line combined;
  line "  </table>";
  line "</body>";
  line "</html>"

module Config = struct
  type mode = [ `HTML | `Markdown ]

  type t = {
    mode : mode;
  }

  let default : t = {
    mode = `Markdown;
  }
end

let output_data_diff : Config.mode -> combined -> unit = fun mode combined ->
  let pp = match mode with `Markdown -> pp_markdown | `HTML -> pp_html in
  Printf.printf "%a%!" pp combined

let hint_data_diff : Config.t -> string -> string -> unit =
    fun {mode} old_csv new_csv ->
  let old_htbl = read_data_file old_csv in
  let new_htbl = read_data_file new_csv in
  let combined = combine_data old_htbl new_htbl in
  output_data_diff mode combined

let usage : out_channel -> unit = fun oc ->
  let flags = String.concat " | " ["-h"; "--help"; "--html"; "--markdown"] in
  Printf.fprintf oc "Usage: %s [%s] OLD.csv NEW.csv\n%!" Sys.argv.(0) flags

let handle_flag : Config.t -> string -> Config.t = fun config flag ->
  match flag with
  | "-h" | "--help" -> usage stdout; exit 0
  | "--html"        -> {mode = `HTML}
  | "--markdown"    -> {mode = `Markdown}
  | _               -> usage stderr; panic "Unknown flag %S." flag

let _ =
  let (flags, files) =
    let is_flag arg = String.length arg > 0 && arg.[0] = '-' in
    List.partition is_flag (List.tl (Array.to_list Sys.argv))
  in
  let config = List.fold_left handle_flag Config.default flags in
  let (old_csv, new_csv) =
    match files with
    | [old_csv; new_csv] -> (old_csv, new_csv)
    | _                  -> usage stderr; panic "Two input files expected."
  in
  hint_data_diff config old_csv new_csv
