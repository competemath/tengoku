/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku
import Tengoku.LanaTemperedFundamentalGroups.TemperedFundamentalGroups.Orbicurve.Exact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The coordinate ring of `E ∖ (E[ℓ] + M)` is a localization of `k[E]`

IUT's removed set `geomRemovedSet W ℓ M = E[ℓ] + M ⊆ E(k̄)` is symmetric and Galois stable
(`isGaloisStable_geomRemovedSet`), and finite when `M` is finite and `E[ℓ]` is finite over `k̄`
(`finite_geomRemovedSet`), e.g. for `ℓ ≥ 1` in characteristic `0`
(`finite_geomRemovedSet_of_charZero`) or for `char k ∤ 2ℓ`
(`finite_geomRemovedSet_of_not_dvd_charP`); finiteness of `E[ℓ]` is
`WeierstrassCurve.Affine.finite_torsion_of_charZero` resp.
`WeierstrassCurve.Affine.finite_torsion_of_not_dvd_charP` from `lana-agents/elliptic-curves`.
For `M ≤ E(k)[ℓ]` (as in IUT) it is `E(k̄)[ℓ]` (`geomRemovedSet_eq_torsion`).

In that case `E[ℓ] + M ∖ {0}` is the zero set of a function `Ψ(x)` of `x`, and the coordinate
ring `geomOrbicurveRing W ℓ M` of `E ∖ (E[ℓ] + M)` is the localization `k[E][Ψ(x)⁻¹]`
(`exists_isLocalization_geomOrbicurveRing`): its spectrum is the open subscheme
`D(Ψ(x)) = E ∖ (E[ℓ] + M)` of `E`.
-/

universe u

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace TemperedFundamentalGroups.Orbicurve

noncomputable section

variable {k : Type u} [Field k] [DecidableEq k] {W : WeierstrassCurve k} {ℓ : ℕ}
  {M : AddSubgroup W.toAffine.Point}

/-! ### Galois stability and finiteness of `E[ℓ] + M` -/

lemma map_mem_removedSetIn {K L : Type*} [Field K] [DecidableEq K] [Algebra k K] [Field L]
    [DecidableEq L] [Algebra k L] (φ : K →ₐ[k] L) {P : (W.toAffine⁄K).Point}
    (hP : P ∈ removedSetIn W K ℓ M) : Point.map φ P ∈ removedSetIn W L ℓ M := by
  obtain ⟨m, hm, h⟩ := hP
  refine ⟨m, hm, ?_⟩
  rw [← map_bc φ m, ← map_sub, ← map_nsmul, h, map_zero]

lemma isGaloisStable_geomRemovedSet : IsGaloisStable W (geomRemovedSet W ℓ M) :=
  fun _ _ hP => map_mem_removedSetIn _ hP

/-! ### Exactness -/

omit [DecidableEq k] in
lemma injective_algebraMap_polynomial :
    Function.Injective (algebraMap k[X] W.toAffine.CoordinateRing) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.of.injective_of_degree_ne_zero (by rw [W.toAffine.degree_polynomial]; decide)

variable [W.IsElliptic]

/-- **Exactness.** If `E[ℓ] + M ⊆ E(k̄)` is finite, then it is, away from `0`, the zero set of a
function `Ψ(x)` of `x`, and the coordinate ring of `E ∖ (E[ℓ] + M)` is the localization
`k[E][Ψ(x)⁻¹]`. -/
theorem exists_isLocalization_geomOrbicurveRing (hfin : (geomRemovedSet W ℓ M).Finite) :
    ∃ Ψ : k[X], Ψ ≠ 0 ∧
      zeroSet W (algebraMap k[X] W.toAffine.CoordinateRing Ψ) = geomRemovedSet W ℓ M \ {0} ∧
      IsLocalization.Away (algebraMap k[X] W.toAffine.CoordinateRing Ψ)
        (geomOrbicurveRing W ℓ M) := by
  obtain ⟨Ψ, hΨ, hz⟩ := exists_polynomial_zeroSet hfin (fun _ => neg_mem_removedSetIn)
    isGaloisStable_geomRemovedSet
  exact ⟨Ψ, hΨ, hz, isLocalization_away_ringAway
    ((_root_.map_ne_zero_iff _ injective_algebraMap_polynomial).mpr hΨ) hz⟩

end

end TemperedFundamentalGroups.Orbicurve
