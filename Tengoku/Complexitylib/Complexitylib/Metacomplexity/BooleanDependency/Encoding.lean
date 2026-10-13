/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.BooleanDependency.Encoding.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.BooleanDependency.Encoding.Internal

/-!
# Canonical encoding of finite Boolean assignments and tables

This module exposes computable exact-length codecs for Boolean functions on
finite ordered domains, assignments on ordered finite coordinate sets, and
their full Boolean truth tables.
-/

public section

namespace Complexity

namespace BooleanDependency

/-- There are exactly `2^|S|` canonically ordered assignments to `S`.
@isnad1 id=eq.0h2v.s5.e533e35c9ddc from=translated src=- shape=25a363bd vocab=abf8c6ab
-/
theorem OrderedAssignment.card
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) :
    Fintype.card (OrderedAssignment coordinates) = 2 ^ coordinates.card :=
  OrderedAssignment.card_internal coordinates

/-- Ordered finite-function encodings contain exactly one bit per input.
@isnad1 id=eq.0h2v.s4.bb5e6f053909 from=translated src=- shape=441f2b31 vocab=e313e8b0
-/
@[simp] theorem length_encodeOrderedFunction
    {index : Type*} [Fintype index] [LinearOrder index]
    (function : index → Bool) :
    (encodeOrderedFunction function).length = Fintype.card index :=
  length_encodeOrderedFunction_internal function

/-- Exact round trip for Boolean functions on finite ordered domains.
@isnad1 id=eq.0h2v.s4.437df55eb502 from=translated src=- shape=e0bc9612 vocab=b17f347d
-/
@[simp] theorem decodeOrderedFunction?_encodeOrderedFunction
    {index : Type*} [Fintype index] [LinearOrder index]
    (function : index → Bool) :
    decodeOrderedFunction? (encodeOrderedFunction function) = some function :=
  decodeOrderedFunction?_encodeOrderedFunction_internal function

/-- Canonical ordered finite-function encoding is injective.
@isnad1 id=injectiv.0h1v.s4.86576ad2d490 from=translated src=- shape=4de69950 vocab=58c0f3be
-/
theorem encodeOrderedFunction_injective
    {index : Type*} [Fintype index] [LinearOrder index] :
    Function.Injective
      (encodeOrderedFunction : (index → Bool) → List Bool) :=
  encodeOrderedFunction_injective_internal

/-- Ordered finite-function decoding fails exactly on malformed lengths.
@isnad1 id=iff.0h2v.s5.2ee33539e305 from=translated src=- shape=8b025820 vocab=6050fd4b
-/
@[simp] theorem decodeOrderedFunction?_eq_none_iff
    {index : Type*} [Fintype index] [LinearOrder index]
    (bits : List Bool) :
    decodeOrderedFunction? (index := index) bits = none ↔
      bits.length ≠ Fintype.card index :=
  decodeOrderedFunction?_eq_none_iff_internal bits

/-- Assignment encodings contain exactly one bit per selected coordinate.
@isnad1 id=eq.0h3v.s5.19296b677a56 from=translated src=- shape=5ec7498b vocab=0115027c
-/
@[simp] theorem length_encodeAssignment
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (assignment : coordinates → Bool) :
    (encodeAssignment coordinates assignment).length = coordinates.card :=
  length_encodeAssignment_internal coordinates assignment

/-- Exact assignment-codec round trip.
@isnad1 id=eq.0h3v.s6.bad8ed214992 from=translated src=- shape=46137e38 vocab=96e141db
-/
@[simp] theorem decodeAssignment?_encodeAssignment
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (assignment : coordinates → Bool) :
    decodeAssignment? coordinates (encodeAssignment coordinates assignment) =
      some assignment :=
  decodeAssignment?_encodeAssignment_internal coordinates assignment

/-- Canonical assignment encoding is injective.
@isnad1 id=injectiv.0h2v.s5.b2c06a8e65b3 from=translated src=- shape=98d3d32f vocab=0a058cf2
-/
theorem encodeAssignment_injective
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) :
    Function.Injective (encodeAssignment coordinates) :=
  encodeAssignment_injective_internal coordinates

/-- Assignment decoding fails exactly on strings of the wrong length.
@isnad1 id=iff.0h3v.s6.f999f61e64c3 from=translated src=- shape=72fada68 vocab=c37a372c
-/
@[simp] theorem decodeAssignment?_eq_none_iff
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (bits : List Bool) :
    decodeAssignment? coordinates bits = none ↔
      bits.length ≠ coordinates.card :=
  decodeAssignment?_eq_none_iff_internal coordinates bits

/-- A full Boolean table has exactly `2^|S|` serialized entries.
@isnad1 id=eq.0h3v.s5.55fcec0e117b from=translated src=- shape=67eee381 vocab=4c8579f2
-/
@[simp] theorem length_encodeTable
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate)
    (table : (coordinates → Bool) → Bool) :
    (encodeTable coordinates table).length = 2 ^ coordinates.card :=
  length_encodeTable_internal coordinates table

/-- Exact dependency-table-codec round trip.
@isnad1 id=eq.0h3v.s6.205c8cf30fb5 from=translated src=- shape=6b22c196 vocab=0bb6e024
-/
@[simp] theorem decodeTable?_encodeTable
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate)
    (table : (coordinates → Bool) → Bool) :
    decodeTable? coordinates (encodeTable coordinates table) = some table :=
  decodeTable?_encodeTable_internal coordinates table

/-- Canonical dependency-table encoding is injective.
@isnad1 id=injectiv.0h2v.s5.8cd9170ccdbd from=translated src=- shape=a5f17723 vocab=eb76b672
-/
theorem encodeTable_injective
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) :
    Function.Injective (encodeTable coordinates) :=
  encodeTable_injective_internal coordinates

/-- Table decoding fails exactly on strings without one bit per assignment.
@isnad1 id=iff.0h3v.s6.56755b60d227 from=translated src=- shape=a32eb979 vocab=a3dba3e6
-/
@[simp] theorem decodeTable?_eq_none_iff
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (bits : List Bool) :
    decodeTable? coordinates bits = none ↔
      bits.length ≠ 2 ^ coordinates.card :=
  decodeTable?_eq_none_iff_internal coordinates bits

end BooleanDependency

end Complexity
