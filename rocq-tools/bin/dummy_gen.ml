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

let _ =
  let line fmt = Printf.printf (fmt ^^ "\n%!") in
  line "Require Import Stdlib.Strings.String.";
  line "Open Scope string.";
  line "";
  line "Definition files_md5_digests : list (string * string) :=";
  let pp_dep file =
    let digest = Digest.to_hex (Digest.file file) in
    line "  (%S, %S) ::" file digest
  in
  List.iter pp_dep (List.tl (Array.to_list Sys.argv));
  line "  nil."
