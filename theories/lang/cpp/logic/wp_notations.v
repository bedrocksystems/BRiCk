(*
 * Copyright (c) 2019-2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Module Export cpp_region.
  Declare Custom Entry cpp_region.
  Declare Scope cppregion_scope.
  Delimit Scope cppregion_scope with cregion.

  Reserved Notation "'return' ty"
    (in custom cpp_region at level 0, ty constr,
     format "'[  ' return  ty ']'").
  Reserved Notation "[ 'this' := ptr ] ; 'return' ty"
    (in custom cpp_region at level 1, ptr constr, ty constr,
     format "'[' [ this  :=  ptr ] ']' ;  '/' '[  ' return  '/' ty ']'").
  Reserved Notation "v @ p ';' ρ "
    (in custom cpp_region at level 1, v constr, p constr, ρ custom cpp_region at level 1,
     format "'[' v  @  p ']' ;  '/' ρ").
End cpp_region.
