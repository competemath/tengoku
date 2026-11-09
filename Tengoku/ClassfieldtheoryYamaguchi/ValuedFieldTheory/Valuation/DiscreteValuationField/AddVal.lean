/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.DiscreteValuationRing.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Normalized additive valuations on discrete valuation rings

This file supplies general-purpose facts about Mathlib's normalized additive
valuation on a discrete valuation ring which are independent of any chosen
valued-field presentation.
-/

noncomputable section

universe u

namespace IsDiscreteValuationRing

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Membership in a power of the maximal ideal is detected by the normalized
additive valuation.
@isnad1 id=iff.0h3v.s7.fd3765277aaa from=translated src=- shape=70241460 vocab=695db633
-/
theorem mem_maximalIdeal_pow_iff_addVal_ge (a : R) (n : ℕ) :
    a ∈ IsLocalRing.maximalIdeal R ^ n ↔ (n : ℕ∞) ≤ addVal R a := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, ← addVal_le_iff_dvd, hϖ.addVal_pow]

/-- A ring automorphism of a discrete valuation ring preserves its normalized
additive valuation.
@isnad1 id=eq.0h3v.s7.7bc89936f545 from=translated src=- shape=8207c7d4 vocab=760d00d5
-/
@[simp] theorem addVal_ringEquiv (e : R ≃+* R) (a : R) :
    addVal R (e a) = addVal R a := by
  by_cases ha : a = 0
  · subst a
    simp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, ha_decomp⟩ := eq_unit_mul_pow_irreducible ha hϖ
  have hmapϖ : Irreducible (e ϖ) := hϖ.map e
  have hmap_decomp :
      e a = (Units.map e.toMonoidHom u : R) * (e ϖ) ^ n := by
    rw [ha_decomp, map_mul, map_pow]
    rfl
  rw [addVal_def (e a) (Units.map e.toMonoidHom u) hmapϖ n hmap_decomp,
    addVal_def a u hϖ n ha_decomp]

end IsDiscreteValuationRing

end
