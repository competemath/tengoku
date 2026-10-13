/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.BooleanDependency.Encoding.Defs

/-!
# Canonical encoding of finite Boolean assignments and tables -- proof internals
-/

public section

namespace Complexity

namespace BooleanDependency

/--
@isnad1 id=eq.0h2v.s5.e533e35c9ddc from=translated src=- shape=25a363bd vocab=abf8c6ab
-/
theorem OrderedAssignment.card_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) :
    Fintype.card (OrderedAssignment coordinates) = 2 ^ coordinates.card := by
  simpa using Fintype.card_congr
    (OrderedAssignment.indexEquiv coordinates)

/--
@isnad1 id=eq.0h2v.s4.bb5e6f053909 from=translated src=- shape=441f2b31 vocab=e313e8b0
-/
theorem length_encodeOrderedFunction_internal
    {index : Type*} [Fintype index] [LinearOrder index]
    (function : index → Bool) :
    (encodeOrderedFunction function).length = Fintype.card index := by
  simp [encodeOrderedFunction]

/--
@isnad1 id=eq.0h2v.s4.437df55eb502 from=translated src=- shape=e0bc9612 vocab=b17f347d
-/
theorem decodeOrderedFunction?_encodeOrderedFunction_internal
    {index : Type*} [Fintype index] [LinearOrder index]
    (function : index → Bool) :
    decodeOrderedFunction? (encodeOrderedFunction function) = some function := by
  simp [decodeOrderedFunction?, encodeOrderedFunction]

/--
@isnad1 id=injectiv.0h1v.s4.86576ad2d490 from=translated src=- shape=4de69950 vocab=58c0f3be
-/
theorem encodeOrderedFunction_injective_internal
    {index : Type*} [Fintype index] [LinearOrder index] :
    Function.Injective (encodeOrderedFunction : (index → Bool) → List Bool) := by
  intro first second heq
  have hdecode := congrArg
    (decodeOrderedFunction? (index := index)) heq
  simpa only [decodeOrderedFunction?_encodeOrderedFunction_internal,
    Option.some.injEq] using hdecode

/--
@isnad1 id=iff.0h2v.s5.2ee33539e305 from=translated src=- shape=8b025820 vocab=6050fd4b
-/
theorem decodeOrderedFunction?_eq_none_iff_internal
    {index : Type*} [Fintype index] [LinearOrder index]
    (bits : List Bool) :
    decodeOrderedFunction? (index := index) bits = none ↔
      bits.length ≠ Fintype.card index := by
  simp [decodeOrderedFunction?]

/--
@isnad1 id=eq.0h3v.s5.19296b677a56 from=translated src=- shape=5ec7498b vocab=0115027c
-/
theorem length_encodeAssignment_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (assignment : coordinates → Bool) :
    (encodeAssignment coordinates assignment).length = coordinates.card := by
  simp [encodeAssignment]

/--
@isnad1 id=eq.0h3v.s6.bad8ed214992 from=translated src=- shape=46137e38 vocab=96e141db
-/
theorem decodeAssignment?_encodeAssignment_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (assignment : coordinates → Bool) :
    decodeAssignment? coordinates (encodeAssignment coordinates assignment) =
      some assignment := by
  simp [decodeAssignment?, encodeAssignment]

/--
@isnad1 id=injectiv.0h2v.s5.b2c06a8e65b3 from=translated src=- shape=98d3d32f vocab=0a058cf2
-/
theorem encodeAssignment_injective_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) :
    Function.Injective (encodeAssignment coordinates) := by
  intro first second heq
  have hdecode := congrArg (decodeAssignment? coordinates) heq
  simpa only [decodeAssignment?_encodeAssignment_internal,
    Option.some.injEq] using hdecode

/--
@isnad1 id=iff.0h3v.s6.f999f61e64c3 from=translated src=- shape=72fada68 vocab=c37a372c
-/
theorem decodeAssignment?_eq_none_iff_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (bits : List Bool) :
    decodeAssignment? coordinates bits = none ↔
      bits.length ≠ coordinates.card := by
  simp [decodeAssignment?]

/--
@isnad1 id=eq.0h3v.s5.55fcec0e117b from=translated src=- shape=67eee381 vocab=4c8579f2
-/
theorem length_encodeTable_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate)
    (table : (coordinates → Bool) → Bool) :
    (encodeTable coordinates table).length = 2 ^ coordinates.card := by
  simp [encodeTable]

/--
@isnad1 id=eq.0h3v.s6.205c8cf30fb5 from=translated src=- shape=6b22c196 vocab=0bb6e024
-/
theorem decodeTable?_encodeTable_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate)
    (table : (coordinates → Bool) → Bool) :
    decodeTable? coordinates (encodeTable coordinates table) = some table := by
  simp [decodeTable?, encodeTable]

/--
@isnad1 id=injectiv.0h2v.s5.8cd9170ccdbd from=translated src=- shape=a5f17723 vocab=eb76b672
-/
theorem encodeTable_injective_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) :
    Function.Injective (encodeTable coordinates) := by
  intro first second heq
  have hdecode := congrArg (decodeTable? coordinates) heq
  simpa only [decodeTable?_encodeTable_internal,
    Option.some.injEq] using hdecode

/--
@isnad1 id=iff.0h3v.s6.56755b60d227 from=translated src=- shape=a32eb979 vocab=a3dba3e6
-/
theorem decodeTable?_eq_none_iff_internal
    {coordinate : Type*} [LinearOrder coordinate]
    (coordinates : Finset coordinate) (bits : List Bool) :
    decodeTable? coordinates bits = none ↔
      bits.length ≠ 2 ^ coordinates.card := by
  simp [decodeTable?]

end BooleanDependency

end Complexity
