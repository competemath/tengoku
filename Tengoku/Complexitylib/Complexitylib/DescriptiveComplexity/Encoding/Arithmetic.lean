/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.Encoding.Arithmetic.Defs
import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.Encoding.Arithmetic.Internal

/-!
# Arithmetic access to the canonical structure encoding

Base-`card` tuple indices and prefix sums give exactly the bit positions defined
by the original site enumeration. The equalities include arbitrary relation
arities, nullary relations, and the one-hot blocks for distinguished constants.
Consequently the arithmetic addresses recover the encoded relation and constant
bits, without changing the wire format.
Fixed-width base expansion recovers the tuple coordinates; scanning the numeric
indices reproduces the encoder's tuple enumeration exactly.
-/

public section

namespace Complexity.DescriptiveComplexity

/-- Tuple packing is the usual little-endian positional numeral.
@isnad1 id=eq.0h3v.s5.0fefcf49a797 from=translated src=- shape=e6a2d7d5 vocab=d89bd532
-/
theorem tupleIndex_eq_sum (card : Nat) {k : Nat} (args : Fin k → Nat) :
    tupleIndex card args = ∑ i : Fin k, args i * card ^ i.val :=
  tupleIndex_eq_sum_internal card args

/-- Each extracted coordinate is a base-`card` digit, including at cardinality zero.
@isnad1 id=eq.0h4v.s5.d9be9fea06e4 from=translated src=- shape=0e88fbe5 vocab=04872815
-/
theorem tupleDigits_eq_div_pow (card k index : Nat) (i : Fin k) :
    tupleDigits card k index i = index / card ^ i.val % card :=
  tupleDigits_eq_div_pow_internal card k index i

/-- A tuple of valid coordinates has an index inside its relation truth table.
@isnad1 id=lt.0h3v.s5.4131f8ff9dd9 from=translated src=- shape=778d9573 vocab=a419774c
-/
theorem tupleIndex_lt {card k : Nat} (args : Fin k → Fin card) :
    tupleIndex card (fun i => (args i).val) < card ^ k := tupleIndex_lt_internal args

/-- The arithmetic index selects the tuple itself in the encoder's enumeration.
@isnad1 id=eq.0h3v.s6.eb23d2c87e5e from=translated src=- shape=3b96873d vocab=fdd369cb
-/
theorem getElem?_allTuples_index {card k : Nat} (args : Fin k → Fin card) :
    (allTuples card k)[tupleIndex card (fun i => (args i).val)]? = some args :=
  getElem?_allTuples_index_internal args

/-- Arithmetic tuple lookup recovers a bit from a relation's standalone truth table.
@isnad1 id=eq.0h4v.s5.a608f8df6297 from=translated src=- shape=eaf8cf4f vocab=343e5d9c
-/
theorem getElem?_encodeRelC_index {card k : Nat} (S : (Fin k → Fin card) → Bool)
    (args : Fin k → Fin card) :
    (encodeRelC S)[tupleIndex card (fun i => (args i).val)]? = some (S args) := by
  simp only [encodeRelC, List.getElem?_map, getElem?_allTuples_index, Option.map_some]

/-- Every extracted coordinate lies in a positive-cardinality universe.
@isnad1 id=lt.1h4v.s4.26e5cbacdf38 from=translated src=- shape=95719d25 vocab=4eed8b19
-/
theorem tupleDigits_lt {card : Nat} (hcard : 0 < card) (k index : Nat) (i : Fin k) :
    tupleDigits card k index i < card := tupleDigits_lt_internal hcard k index i

/-- Re-encoding the coordinates recovers every index inside the tuple table.
@isnad1 id=eq.2h3v.s5.f3aea9582d0a from=translated src=- shape=be560dc8 vocab=1f1f8cd7
-/
theorem tupleIndex_tupleDigits {card : Nat} (hcard : 0 < card) (k index : Nat)
    (hi : index < card ^ k) : tupleIndex card (tupleDigits card k index) = index :=
  tupleIndex_tupleDigits_internal hcard k index hi

/-- Enumerating tuples agrees with scanning their numeric indices in order.
@isnad1 id=eq.1h4v.s6.a53e1c1d6e62 from=translated src=- shape=597c7270 vocab=5d5c0960
-/
theorem map_allTuples_eq_range {α : Type} {card : Nat} (hcard : 0 < card)
    (k : Nat) (f : (Fin k → Nat) → α) :
    (allTuples card k).map (fun args => f (fun i => (args i).val)) =
      (List.range (card ^ k)).map (fun index => f (tupleDigits card k index)) :=
  map_allTuples_eq_range_internal hcard k f

end Complexity.DescriptiveComplexity
