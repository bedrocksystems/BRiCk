(*
 * Copyright (C) BedRock Systems Inc. 2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export bedrock.upoly.base.	(* base.v *)

(** Types *)

Require bedrock.upoly.UTypes.	(* UTypes.v *)
Require bedrock.upoly.prod.	(* prod.v *)
Require bedrock.upoly.sum.	(* sum.v *)
Require bedrock.upoly.option.	(* option.v *)
Require bedrock.upoly.list.	(* list.v *)

(** Monads *)

Require bedrock.upoly.id.	(* id.v *)
Require bedrock.upoly.trace.	(* trace.v *)
Require bedrock.upoly.reader.	(* reader.v *)
Require bedrock.upoly.writer.	(* writer.v *)
Require bedrock.upoly.state.	(* state.v *)

(** Monad transformers *)

Require bedrock.upoly.optionT.	(* optionT.v *)
Require bedrock.upoly.listT.	(* listT.v *)
Require bedrock.upoly.traceT.	(* traceT.v *)
Require bedrock.upoly.readerT.	(* readerT.v *)
Require bedrock.upoly.writerT.	(* writerT.v *)
Require bedrock.upoly.stateT.	(* stateT.v *)

Require Export bedrock.upoly.effects.	(* effects.v *)
