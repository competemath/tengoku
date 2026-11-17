/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.DyadicZeroCount
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.CanonicalDivisor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dyadic zero-count bridge for the centered xi pullback

This file specializes the generic cumulative dyadic divisor-count theorem to
the exact occurrence-indexed canonical divisor of `EntireXiPullback`.
-/

namespace OverflowResidueRH

/-- The exact cumulative dyadic zero-count output needed for the canonical
multiplicity-bearing divisor of `EntireXiPullback`.-/
structure EntireXiPullbackDyadicCumulativeCountData : Type where
  lower : Nat
  C : Real
  C₀ : Real
  C_nonneg : 0 ≤ C
  C₀_nonneg : 0 ≤ C₀
  count_le : ∀ n : Nat, lower ≤ n →
    (hadamardZeroDyadicBallCard
        entireXiPullbackZeroOccurrenceLoc n : Real) ≤
      C * ((n + 1 : Nat) : Real) * (2 : Real) ^ n + C₀

/-- Expose canonical xi cumulative count data through the generic interface.-/
def EntireXiPullbackDyadicCumulativeCountData.toGeneric
    (H : EntireXiPullbackDyadicCumulativeCountData) :
    HadamardZeroDyadicCumulativeCountData
      entireXiPullbackZeroOccurrenceLoc where
  zero_ne := entireXiPullbackZeroOccurrenceLoc_ne_zero
  normProper := entireXiPullbackZeroOccurrenceNormProper
  lower := H.lower
  C := H.C
  C₀ := H.C₀
  C_nonneg := H.C_nonneg
  C₀_nonneg := H.C₀_nonneg
  count_le := H.count_le

/-- A cumulative dyadic `O(R log R)` count discharges the sole global
zero-distribution field of the canonical xi divisor.
@isnad1 id=entirexi.0h1v.s1.9b67c541cf03 from=translated src=- shape=1d48f1ac vocab=efc45546
-/
theorem EntireXiPullbackDyadicCumulativeCountData.toCanonicalZeroDistribution
    (H : EntireXiPullbackDyadicCumulativeCountData) :
    EntireXiPullbackCanonicalZeroDistribution :=
  ⟨H.toGeneric.invSq_summable⟩

end OverflowResidueRH
