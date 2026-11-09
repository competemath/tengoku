/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.HasseArf.LowerRamificationGroup
import Tengoku.Seed.Algebra.Order.Archimedean.Real.Basic
import Tengoku.Seed.Algebra.Order.Floor.Ring
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Real-index lower ramification groups

The ideal exponent at a real index `s` is `max(0, ceil(s + 1))`.
Consequently, indices at or below `-1` give the whole decomposition group,
and natural indices recover the usual `m^(n+1)` displacement condition.
-/

noncomputable section

namespace ClassFieldTheory

universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

private lemma smul_mem_maximalIdeal_pow_real
    (A : ValuationSubring L) (k : ℕ)
    (σ : A.decompositionSubgroup K) {x : A}
    (hx : x ∈ (IsLocalRing.maximalIdeal A) ^ k) :
    σ • x ∈ (IsLocalRing.maximalIdeal A) ^ k := by
  let e : A ≃+* A :=
    MulSemiringAction.toRingAut (A.decompositionSubgroup K) A σ
  have hx' : e x ∈ ((IsLocalRing.maximalIdeal A) ^ k).map e :=
    Ideal.mem_map_of_mem e hx
  rwa [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal] at hx'

/-- The real-index lower ramification group of a valuation subring. Its
elements act trivially modulo `m ^ max(0, ceil(s + 1))`.-/
def realLowerRamificationGroup (A : ValuationSubring L) (s : ℝ) :
    Subgroup (A.decompositionSubgroup K) where
  carrier := {σ | ∀ x : A,
    σ • x - x ∈
      (IsLocalRing.maximalIdeal A) ^ (Int.ceil (s + 1)).toNat}
  one_mem' := by simp
  mul_mem' := by
    intro σ τ hσ hτ x
    have hτ' := smul_mem_maximalIdeal_pow_real K A
      (Int.ceil (s + 1)).toNat σ (hτ x)
    have hsum :=
      (IsLocalRing.maximalIdeal A ^ (Int.ceil (s + 1)).toNat).add_mem
        hτ' (hσ x)
    simpa [mul_smul, smul_sub, sub_eq_add_neg, add_assoc] using hsum
  inv_mem' := by
    intro σ hσ x
    simpa [smul_smul] using
      (IsLocalRing.maximalIdeal A ^ (Int.ceil (s + 1)).toNat).neg_mem
        (hσ (σ⁻¹ • x))

end ClassFieldTheory
