(*
 * Copyright (C) BedRock Systems Inc. 2020-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import iris.proofmode.tactics.
Require Import bedrock.prelude.bytestring.
Require Export bedrock.prelude.tactics.base_dbs.
Require Ltac2.Ltac2.

(** NamedBinder is a wrapper around any type that can be used to record the name
    of a binder in a persistent way that is not affected by any computation.

    Existentials/universals of type [NamedBinder A str] are always
    eliminated/introduced directly as an assumption named [str] of type [A].
 *)
Definition NamedBinder (A:Type) (name : BS.t) := A.
#[global] Arguments NamedBinder : simpl never.
#[global] Hint Opaque NamedBinder : typeclass_instances br_opacity.

Module Binder.
  Import Ltac2.
  Import Ltac2.Printf.
  Import Ltac2.Constr.
  Import Ltac2.Constr.Unsafe.

  Ltac2 int_of_byte (b : constr) :=
    lazy_match! b with
    | Byte.x00 => 0
    | Byte.x01 => 1
    | Byte.x02 => 2
    | Byte.x03 => 3
    | Byte.x04 => 4
    | Byte.x05 => 5
    | Byte.x06 => 6
    | Byte.x07 => 7
    | Byte.x08 => 8
    | Byte.x09 => 9
    | Byte.x0a => 10
    | Byte.x0b => 11
    | Byte.x0c => 12
    | Byte.x0d => 13
    | Byte.x0e => 14
    | Byte.x0f => 15
    | Byte.x10 => 16
    | Byte.x11 => 17
    | Byte.x12 => 18
    | Byte.x13 => 19
    | Byte.x14 => 20
    | Byte.x15 => 21
    | Byte.x16 => 22
    | Byte.x17 => 23
    | Byte.x18 => 24
    | Byte.x19 => 25
    | Byte.x1a => 26
    | Byte.x1b => 27
    | Byte.x1c => 28
    | Byte.x1d => 29
    | Byte.x1e => 30
    | Byte.x1f => 31
    | Byte.x20 => 32
    | Byte.x21 => 33
    | Byte.x22 => 34
    | Byte.x23 => 35
    | Byte.x24 => 36
    | Byte.x25 => 37
    | Byte.x26 => 38
    | Byte.x27 => 39
    | Byte.x28 => 40
    | Byte.x29 => 41
    | Byte.x2a => 42
    | Byte.x2b => 43
    | Byte.x2c => 44
    | Byte.x2d => 45
    | Byte.x2e => 46
    | Byte.x2f => 47
    | Byte.x30 => 48
    | Byte.x31 => 49
    | Byte.x32 => 50
    | Byte.x33 => 51
    | Byte.x34 => 52
    | Byte.x35 => 53
    | Byte.x36 => 54
    | Byte.x37 => 55
    | Byte.x38 => 56
    | Byte.x39 => 57
    | Byte.x3a => 58
    | Byte.x3b => 59
    | Byte.x3c => 60
    | Byte.x3d => 61
    | Byte.x3e => 62
    | Byte.x3f => 63
    | Byte.x40 => 64
    | Byte.x41 => 65
    | Byte.x42 => 66
    | Byte.x43 => 67
    | Byte.x44 => 68
    | Byte.x45 => 69
    | Byte.x46 => 70
    | Byte.x47 => 71
    | Byte.x48 => 72
    | Byte.x49 => 73
    | Byte.x4a => 74
    | Byte.x4b => 75
    | Byte.x4c => 76
    | Byte.x4d => 77
    | Byte.x4e => 78
    | Byte.x4f => 79
    | Byte.x50 => 80
    | Byte.x51 => 81
    | Byte.x52 => 82
    | Byte.x53 => 83
    | Byte.x54 => 84
    | Byte.x55 => 85
    | Byte.x56 => 86
    | Byte.x57 => 87
    | Byte.x58 => 88
    | Byte.x59 => 89
    | Byte.x5a => 90
    | Byte.x5b => 91
    | Byte.x5c => 92
    | Byte.x5d => 93
    | Byte.x5e => 94
    | Byte.x5f => 95
    | Byte.x60 => 96
    | Byte.x61 => 97
    | Byte.x62 => 98
    | Byte.x63 => 99
    | Byte.x64 => 100
    | Byte.x65 => 101
    | Byte.x66 => 102
    | Byte.x67 => 103
    | Byte.x68 => 104
    | Byte.x69 => 105
    | Byte.x6a => 106
    | Byte.x6b => 107
    | Byte.x6c => 108
    | Byte.x6d => 109
    | Byte.x6e => 110
    | Byte.x6f => 111
    | Byte.x70 => 112
    | Byte.x71 => 113
    | Byte.x72 => 114
    | Byte.x73 => 115
    | Byte.x74 => 116
    | Byte.x75 => 117
    | Byte.x76 => 118
    | Byte.x77 => 119
    | Byte.x78 => 120
    | Byte.x79 => 121
    | Byte.x7a => 122
    | Byte.x7b => 123
    | Byte.x7c => 124
    | Byte.x7d => 125
    | Byte.x7e => 126
    | Byte.x7f => 127
    | Byte.x80 => 128
    | Byte.x81 => 129
    | Byte.x82 => 130
    | Byte.x83 => 131
    | Byte.x84 => 132
    | Byte.x85 => 133
    | Byte.x86 => 134
    | Byte.x87 => 135
    | Byte.x88 => 136
    | Byte.x89 => 137
    | Byte.x8a => 138
    | Byte.x8b => 139
    | Byte.x8c => 140
    | Byte.x8d => 141
    | Byte.x8e => 142
    | Byte.x8f => 143
    | Byte.x90 => 144
    | Byte.x91 => 145
    | Byte.x92 => 146
    | Byte.x93 => 147
    | Byte.x94 => 148
    | Byte.x95 => 149
    | Byte.x96 => 150
    | Byte.x97 => 151
    | Byte.x98 => 152
    | Byte.x99 => 153
    | Byte.x9a => 154
    | Byte.x9b => 155
    | Byte.x9c => 156
    | Byte.x9d => 157
    | Byte.x9e => 158
    | Byte.x9f => 159
    | Byte.xa0 => 160
    | Byte.xa1 => 161
    | Byte.xa2 => 162
    | Byte.xa3 => 163
    | Byte.xa4 => 164
    | Byte.xa5 => 165
    | Byte.xa6 => 166
    | Byte.xa7 => 167
    | Byte.xa8 => 168
    | Byte.xa9 => 169
    | Byte.xaa => 170
    | Byte.xab => 171
    | Byte.xac => 172
    | Byte.xad => 173
    | Byte.xae => 174
    | Byte.xaf => 175
    | Byte.xb0 => 176
    | Byte.xb1 => 177
    | Byte.xb2 => 178
    | Byte.xb3 => 179
    | Byte.xb4 => 180
    | Byte.xb5 => 181
    | Byte.xb6 => 182
    | Byte.xb7 => 183
    | Byte.xb8 => 184
    | Byte.xb9 => 185
    | Byte.xba => 186
    | Byte.xbb => 187
    | Byte.xbc => 188
    | Byte.xbd => 189
    | Byte.xbe => 190
    | Byte.xbf => 191
    | Byte.xc0 => 192
    | Byte.xc1 => 193
    | Byte.xc2 => 194
    | Byte.xc3 => 195
    | Byte.xc4 => 196
    | Byte.xc5 => 197
    | Byte.xc6 => 198
    | Byte.xc7 => 199
    | Byte.xc8 => 200
    | Byte.xc9 => 201
    | Byte.xca => 202
    | Byte.xcb => 203
    | Byte.xcc => 204
    | Byte.xcd => 205
    | Byte.xce => 206
    | Byte.xcf => 207
    | Byte.xd0 => 208
    | Byte.xd1 => 209
    | Byte.xd2 => 210
    | Byte.xd3 => 211
    | Byte.xd4 => 212
    | Byte.xd5 => 213
    | Byte.xd6 => 214
    | Byte.xd7 => 215
    | Byte.xd8 => 216
    | Byte.xd9 => 217
    | Byte.xda => 218
    | Byte.xdb => 219
    | Byte.xdc => 220
    | Byte.xdd => 221
    | Byte.xde => 222
    | Byte.xdf => 223
    | Byte.xe0 => 224
    | Byte.xe1 => 225
    | Byte.xe2 => 226
    | Byte.xe3 => 227
    | Byte.xe4 => 228
    | Byte.xe5 => 229
    | Byte.xe6 => 230
    | Byte.xe7 => 231
    | Byte.xe8 => 232
    | Byte.xe9 => 233
    | Byte.xea => 234
    | Byte.xeb => 235
    | Byte.xec => 236
    | Byte.xed => 237
    | Byte.xee => 238
    | Byte.xef => 239
    | Byte.xf0 => 240
    | Byte.xf1 => 241
    | Byte.xf2 => 242
    | Byte.xf3 => 243
    | Byte.xf4 => 244
    | Byte.xf5 => 245
    | Byte.xf6 => 246
    | Byte.xf7 => 247
    | Byte.xf8 => 248
    | Byte.xf9 => 249
    | Byte.xfa => 250
    | Byte.xfb => 251
    | Byte.xfc => 252
    | Byte.xfd => 253
    | Byte.xfe => 254
    | Byte.xff => 255
    | _ => Control.throw (Invalid_argument (Some (Message.of_constr b)))
    end.

  Ltac2 str_of_bs (bs : constr) : string :=
    let rec go bs acc :=
      lazy_match! bs with
      | BS.EmptyString => List.fold_left (fun (len, rev_acc) x => (Int.add len 1, x::rev_acc)) (0,[]) acc
      | BS.String ?b ?bs =>
        let char := Char.of_int (int_of_byte b) in
        go bs (char :: acc)
      end
    in
    let (len, chars) := go bs [] in
    let str := String.make len (Char.of_int 0) in
    List.iteri (fun i char => String.set str i char) chars;
    str.

  Ltac2 to_id_fun (bs : constr) : unit :=
    let str := str_of_bs bs in
    let id := Ident.of_string str in
    let binder := Constr.Binder.make id 'unit in
    let f := Constr.Unsafe.make (
        Constr.Unsafe.Lambda binder (Constr.Unsafe.make (Constr.Unsafe.Rel 1))
      )
    in
    refine f.

  Ltac id_of_bs := ltac2:(bs |- to_id_fun (Option.get (Ltac1.to_constr bs))).
End Binder.

(* [TCForceEq] disregards typeclass_instances opacity.  *)
Inductive TCForceEq {A : Type} (x : A) : A → Prop :=  TCForceEq_refl : TCForceEq x x.
Existing Class TCForceEq.
#[global] Hint Extern 100 (TCForceEq ?x _) => refine (TCForceEq_refl x) : typeclass_instances.

Class IdOfBS (name : BS.t) (ident : () -> ()) := ID_OF_BS {}.
#[global] Arguments IdOfBS name%_bs_scope _%_function_scope.
#[global] Hint Mode IdOfBS ! - : typeclass_instances.

#[global] Hint Extern 100 (IdOfBS ?name _) =>
  refine (@ID_OF_BS name ltac:(Binder.id_of_bs name)) : typeclass_instances.

#[global] Instance from_forall_named_binder {PROP:bi} {A} {name} {id}
  {Φ : NamedBinder A name -> PROP}
  {Φ' : A -> PROP} :
  IdOfBS name id ->
  TCForceEq Φ Φ' ->
  FromForall (∀ x : NamedBinder A name, Φ x) Φ' id | 0.
Proof. move => _ ->. by rewrite /FromForall. Qed.

#[global] Instance into_exist_named_binder {PROP:bi} {A} {name} {id}
  {Φ : NamedBinder A name -> PROP}
  {Φ' : A -> PROP} :
  IdOfBS name id ->
  TCForceEq Φ Φ' ->
  IntoExist (∃ x : NamedBinder A name, Φ x) Φ' id | 0.
Proof. move => _ ->. by rewrite /IntoExist. Qed.

Module Type Test.
  Tactic Notation "test" ident(name) := (assert (name = ()) by (destruct name; reflexivity)).

  Goal forall {PROP:bi}, ⊢@{PROP} ∀ x : NamedBinder unit "name"%bs, False.
  Proof.
    intros PROP.
    (* The name returned in [FromForall] is only honored if we explicitly introduce [(?)] *)
    assert_fails (iIntros; test name).
    assert_succeeds (iIntros (?); test name).
  Abort.

  Goal forall {PROP:bi}, (∃ x : NamedBinder unit "name"%bs, False) ⊢@{PROP} False.
  Proof.
    intros PROP.
    assert_succeeds (iIntros "[% ?]"; test name).
    assert_succeeds (iIntros "H"; iDestruct "H" as (?) "H"; test name).
  Abort.
End Test.
