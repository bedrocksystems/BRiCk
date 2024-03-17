(*
 * Copyright (c) 2023-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.cpp.mparser.prelude.
Require Import bedrock.lang.cpp.parser.type.

#[local] Definition parser_lang : lang.t := lang.temp.
Include ParserType.
