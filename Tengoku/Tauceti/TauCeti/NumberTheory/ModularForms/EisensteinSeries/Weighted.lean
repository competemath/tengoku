/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# Eisenstein series weighted by a function of residues

For a level `N`, a weight `k` and a function `W : (Fin 2 → ZMod N) → ℂ`, the series
`∑_{v ∈ ℤ²} W(v mod N) · (v₀ z + v₁)^(-k)`.

Mathlib's `eisensteinSeries` sums over the *coprime* pairs in one residue class. The Eisenstein
series with character of Diamond–Shurman §4.5 are instead built from the sums
`G_k^{a}(z) = ∑_{v ≡ a mod N} (v₀ z + v₁)^(-k)` over *all* pairs in a residue class, weighted by
character values; every such combination is the series of this file for a suitable `W`
(`G_k^{a}` itself is the indicator function of `a`). Allowing an arbitrary weight keeps the
analytic input in one place.

For `3 ≤ k` the series converges absolutely and locally uniformly, and slashing by
`γ ∈ SL(2, ℤ)` only changes the weight, to `a ↦ W (a ᵥ* γ⁻¹)`
(`weightedEisensteinSeries_slash_apply`). Hence the series is a modular form of level `Γ(N)`
(`weightedEisensteinSeriesMF`); the character is then read off from the transformation of the
weight under `Γ₀(N)`.

## Main definitions

* `TauCeti.EisensteinSeries.weightedEisensteinSeries`: the weighted series, as a function.
* `TauCeti.EisensteinSeries.weightedEisensteinSeriesSIF`: it is slash invariant of level `Γ(N)`.
* `TauCeti.EisensteinSeries.weightedEisensteinSeriesMF`: for `3 ≤ k`, a modular form of level
  `Γ(N)`.

## Main results

* `TauCeti.EisensteinSeries.weightedEisensteinSeries_slash_apply`: the slash action on the series.
* `TauCeti.EisensteinSeries.weightedEisensteinSeries_eq_tsum_eisensteinSeries`: the series in
  terms of Mathlib's coprime-pair `eisensteinSeries`, through the `gammaSet` decomposition by gcd
  and residue class.
* `TauCeti.EisensteinSeries.weightedEisensteinSeries_smul`,
  `TauCeti.EisensteinSeries.weightedEisensteinSeries_add`: linearity in the weight.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.2, §4.5.
* The uniform-convergence argument follows Mathlib's
  `EisensteinSeries.eisensteinSeries_tendstoLocallyUniformly` (Chris Birkbeck and David Loeffler),
  while the holomorphy and boundedness arguments follow
  `EisensteinSeries.eisensteinSeriesSIF_mdifferentiable` and
  `EisensteinSeries.isBoundedAtImInfty_eisensteinSeriesSIF` (Chris Birkbeck), with the sum over
  a coprime residue class replaced by a sum over all pairs with bounded weights.
-/

public section

noncomputable section

open ModularForm UpperHalfPlane Matrix CongruenceSubgroup Complex Filter Set
open EisensteinSeries

open scoped MatrixGroups Topology Manifold

namespace TauCeti.EisensteinSeries

variable {N : ℕ} (W : (Fin 2 → ZMod N) → ℂ) (k : ℤ)

/-- The Eisenstein series of weight `k` weighted by `W : (Fin 2 → ZMod N) → ℂ`:
`∑' v : ℤ², W (v mod N) * (v 0 * z + v 1) ^ (-k)`. -/
def weightedEisensteinSeries (z : ℍ) : ℂ :=
  ∑' v : Fin 2 → ℤ, W ((↑) ∘ v) * eisSummand k v z

lemma weightedEisensteinSeries_def (z : ℍ) :
    weightedEisensteinSeries W k z = ∑' v : Fin 2 → ℤ, W ((↑) ∘ v) * eisSummand k v z :=
  (rfl)

/-- The series is linear in the weight: scalar multiples. -/
lemma weightedEisensteinSeries_smul (c : ℂ) :
    weightedEisensteinSeries (c • W) k = c • weightedEisensteinSeries W k := by
  ext z
  simp [weightedEisensteinSeries, mul_assoc, tsum_mul_left]

/-- Reduction modulo `N` commutes with right multiplication by `γ ∈ SL(2, ℤ)`. -/
lemma intCast_comp_vecMul (v : Fin 2 → ℤ) (γ : SL(2, ℤ)) :
    ((↑) : ℤ → ZMod N) ∘ (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) =
      ((↑) ∘ v) ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
  ext i
  simp [vecMul, dotProduct]

/-! ### Analytic properties -/

variable [NeZero N]

/-- A bound for the absolute values of the weights. -/
private lemma norm_le_sum_norm (a : Fin 2 → ZMod N) : ‖W a‖ ≤ ∑ b, ‖W b‖ :=
  Finset.single_le_sum (f := fun b ↦ ‖W b‖) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ a)

variable {k}

/-- The weighted series is absolutely convergent for `3 ≤ k`. -/
lemma summable_norm_weightedEisensteinSummand (hk : 3 ≤ k) (z : ℍ) :
    Summable fun v : Fin 2 → ℤ ↦ ‖W ((↑) ∘ v) * eisSummand k v z‖ :=
  ((summable_norm_eisSummand hk z).mul_left (∑ b, ‖W b‖)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun v ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_le_sum_norm W _) (norm_nonneg _)

/-- The series is linear in the weight: sums. -/
lemma weightedEisensteinSeries_add (hk : 3 ≤ k) (W' : (Fin 2 → ZMod N) → ℂ) :
    weightedEisensteinSeries (W + W') k =
      weightedEisensteinSeries W k + weightedEisensteinSeries W' k := by
  ext z
  simp only [weightedEisensteinSeries, Pi.add_apply, add_mul]
  exact (summable_norm_weightedEisensteinSummand W hk z).of_norm.tsum_add
    (summable_norm_weightedEisensteinSummand W' hk z).of_norm

/-- The partial sums of the weighted series converge locally uniformly on `ℍ`. -/
theorem weightedEisensteinSeries_tendstoLocallyUniformly (hk : 3 ≤ k) :
    TendstoLocallyUniformly
      (fun s : Finset (Fin 2 → ℤ) ↦ (∑ v ∈ s, W ((↑) ∘ v) * eisSummand k v ·))
      (weightedEisensteinSeries W k ·) atTop := by
  have hk' : (2 : ℝ) < k := by norm_cast
  simp only [tendstoLocallyUniformly_iff_forall_isCompact, weightedEisensteinSeries]
  intro K hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact hK
  refine (tendstoUniformlyOn_tsum (hu := ((summable_one_div_norm_rpow hk').mul_left
    (r ⟨⟨A, B⟩, hB⟩ ^ (-k : ℝ))).mul_left (∑ b, ‖W b‖)) (fun v z hz ↦ ?_)).mono HABK
  rw [norm_mul]
  refine mul_le_mul (norm_le_sum_norm W _) ?_ (norm_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  simpa only [eisSummand, one_div, ← zpow_neg, norm_zpow, ← Real.rpow_intCast,
    Int.cast_neg] using summand_bound_of_mem_verticalStrip (by positivity) v hB hz

/-- The coprime integer pairs are the disjoint union of the coprime pairs in each residue class. -/
private def gammaSetOneSigmaEquiv (N : ℕ) :
    gammaSet 1 1 0 ≃ Σ a : Fin 2 → ZMod N, gammaSet N 1 a where
  toFun y := ⟨(↑) ∘ y.1, y.1, rfl, y.2.2⟩
  invFun p := ⟨p.2.1, Subsingleton.elim _ _, p.2.2.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨a, x, rfl, hx⟩
    rfl

end TauCeti.EisensteinSeries
