(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.parser.prelude.

Module Type PARSER_LANG.
  Parameter Inline parser_lang : lang.t.
End PARSER_LANG.
