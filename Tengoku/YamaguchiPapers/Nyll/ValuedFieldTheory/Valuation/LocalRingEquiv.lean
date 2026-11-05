/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.NumberTheory.RamificationInertia.Ramification
import Tengoku.Seed.RingTheory.LocalRing.Basic
import Tengoku.Seed.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local-ring equivalences and maximal ideals

Equivalences of local rings preserve the maximal ideal and all of its powers.
The resulting membership criterion is useful when transporting principal-unit
filtrations between equivalent valuation rings.
-/

namespace ValuationTheory

/-- A local-ring equivalence maps the maximal ideal onto the maximal ideal.-/
theorem ringEquiv_map_maximalIdeal
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    Ideal.map e.toRingHom (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change e x ∈ IsLocalRing.maximalIdeal S
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro h
    have h' := h.map e.symm.toRingHom
    exact hx (by simpa using h')
  · intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    intro h
    exact hy (h.map e.toRingHom)

/-- For an injective local map of discrete valuation rings, the image of the
maximal ideal is the power prescribed by the ramification index.-/
theorem map_maximalIdeal_eq_pow_ramificationIdx
    {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hi : Function.Injective (algebraMap R S)) :
    Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S ^
        Ideal.ramificationIdx'
          (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) := by
  let q := IsLocalRing.maximalIdeal R
  let Q := IsLocalRing.maximalIdeal S
  have hq0 : q ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have hmap0 : Ideal.map (algebraMap R S) q ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hi).not.mpr hq0
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨n, hn⟩ :=
    IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmap0 hpi
  have hmapPow : Ideal.map (algebraMap R S) q = Q ^ n := by
    rw [hn, show Q = IsLocalRing.maximalIdeal S from rfl,
      hpi.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hnot : ¬ Ideal.map (algebraMap R S) q ≤ Q ^ (n + 1) := by
    rw [hmapPow]
    exact not_le_of_gt (Ideal.pow_succ_lt_pow
      (IsDiscreteValuationRing.not_a_field S) n)
  have he : Ideal.ramificationIdx' q Q = n :=
    Ideal.ramificationIdx'_spec (by rw [hmapPow]) hnot
  rw [he]
  exact hmapPow

end ValuationTheory
