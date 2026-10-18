/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.PowerSeriesBridge
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.MvPowerSeriesPderiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The outer-variable derivative on the double Laurent ring and its `pderivSnd` compatibility

Mathlib provides `LaurentSeries.derivative` (`= LaurentSeries.hasseDeriv 1`) as an `R`-linear map on
`R⸨X⸩ = HahnSeries ℤ R` with `(derivative R f).coeff n = (n + 1) • f.coeff (n + 1)`, but proves
**no** product rule for it.  This file supplies the missing calculus for the outer (`z₂`) grading of
the iterated Laurent ring `(R⸨X⸩)⸨X⸩ = HahnSeries ℤ (HahnSeries ℤ R)`, which is what the
invariant-differential invariance `(★)` of issue #315 needs on the explicit Laurent addition
formulas.

## Main results

* `LaurentSeries.coeff_derivative` : the coefficient formula `(derivative ℤ f).coeff n
  = (n + 1) • f.coeff (n + 1)` with `Ring.choose (n + 1) 1` simplified away.
* `LaurentSeries.derivative_mul` : the **product (Leibniz) rule**
  `derivative ℤ (f * g) = f * derivative ℤ g + derivative ℤ f * g` for `f g : R⸨X⸩`.
* `LaurentSeries.derivative_inverse` : the **quotient rule** for `Ring.inverse` of a unit `u`:
  `derivative ℤ (Ring.inverse u) = - Ring.inverse u * derivative ℤ u * Ring.inverse u`.
* `HahnSeries.embedDoubleLaurent_pderivSnd` (the headline compatibility): the writer
  `embedDoubleLaurent : MvPowerSeries (Fin 2) R → (R⸨X⸩)⸨X⸩` intertwines the `z₂`-partial derivative
  `MvPowerSeries.pderivSnd` with the outer Laurent derivative `LaurentSeries.derivative ℤ`:
  `embedDoubleLaurent (pderivSnd φ) = derivative ℤ (embedDoubleLaurent φ)`.

## ⚠️ One `@[simp]` attribute was removed here, and the lemma kept (`#1278`)

`derivative_C` carried `@[simp]`, and the default simp set **already proves it** — through
`HahnSeries.C_apply`, `derivative_apply`, `hasseDeriv_single`, `Ring.choose_one_right'` and
`map_zero`. Measured with Mathlib's `simpNF` environment linter, which had never been run on this
tree. The lemma is unchanged and still has four consumers outside this file; only the attribute
went.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4, Theorem 4.2; IV.5,
  Proposition 5.2.
-/

open scoped LaurentSeries

namespace LaurentSeries

variable {R : Type*} [CommRing R]

/-- The coefficient formula for the Laurent-series derivative, with the binomial coefficient
`Ring.choose (n + 1) 1` simplified to `n + 1`. -/
theorem coeff_derivative (f : R⸨X⸩) (n : ℤ) :
    (derivative ℤ f).coeff n = (n + 1) • f.coeff (n + 1) := by
  rw [derivative_apply, hasseDeriv_coeff, Ring.choose_one_right, Nat.cast_one]

/-- Reindexing helper for the Leibniz rule: the `n`-th coefficient of `f * g'` (where `g' =
derivative ℤ g`) as a sum over the `(n+1)`-antidiagonal of the supports of `f` and `g`, obtained by
shifting the outer index of the second factor by one. -/
private lemma coeff_mul_derivative_right (f g : R⸨X⸩) (n : ℤ) :
    (f * derivative ℤ g).coeff n
      = ∑ ij ∈ Finset.antidiagonal f.isPWO_support g.isPWO_support (n + 1),
          ij.2 • (f.coeff ij.1 * g.coeff ij.2) := by
  have hSg : ((fun k : ℤ => k - 1) '' g.support).IsPWO :=
    g.isPWO_support.image_of_monotone (fun _ _ h => sub_le_sub_right h 1)
  have hsub : (derivative ℤ g).support ⊆ (fun k : ℤ => k - 1) '' g.support := by
    intro j hj
    rw [HahnSeries.mem_support, coeff_derivative] at hj
    have hg : g.coeff (j + 1) ≠ 0 := fun h => hj (by rw [h, smul_zero])
    exact ⟨j + 1, by rwa [HahnSeries.mem_support], by ring⟩
  rw [HahnSeries.coeff_mul_right' hSg hsub]
  refine Finset.sum_nbij' (fun p => (p.1, p.2 + 1)) (fun p => (p.1, p.2 - 1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_antidiagonal, Set.mem_image] at hp ⊢
    obtain ⟨hp1, ⟨k, hk, hk2⟩, hp3⟩ := hp
    refine ⟨hp1, ?_, by omega⟩
    have : j + 1 = k := by omega
    rw [this]; exact hk
  · rintro ⟨i, j⟩ hq
    simp only [Finset.mem_antidiagonal, Set.mem_image] at hq ⊢
    obtain ⟨hq1, hq2, hq3⟩ := hq
    exact ⟨hq1, ⟨j, hq2, by omega⟩, by omega⟩
  · rintro ⟨i, j⟩ hp
    simp
  · rintro ⟨i, j⟩ hq
    simp
  · rintro ⟨i, j⟩ hp
    dsimp only
    rw [coeff_derivative, mul_smul_comm]

/-- Reindexing helper for the Leibniz rule: the `n`-th coefficient of `f' * g` (where `f' =
derivative ℤ f`) as a sum over the `(n+1)`-antidiagonal of the supports of `f` and `g`, obtained by
shifting the outer index of the first factor by one. -/
private lemma coeff_derivative_mul_left (f g : R⸨X⸩) (n : ℤ) :
    (derivative ℤ f * g).coeff n
      = ∑ ij ∈ Finset.antidiagonal f.isPWO_support g.isPWO_support (n + 1),
          ij.1 • (f.coeff ij.1 * g.coeff ij.2) := by
  have hSf : ((fun k : ℤ => k - 1) '' f.support).IsPWO :=
    f.isPWO_support.image_of_monotone (fun _ _ h => sub_le_sub_right h 1)
  have hsub : (derivative ℤ f).support ⊆ (fun k : ℤ => k - 1) '' f.support := by
    intro i hi
    rw [HahnSeries.mem_support, coeff_derivative] at hi
    have hf : f.coeff (i + 1) ≠ 0 := fun h => hi (by rw [h, smul_zero])
    exact ⟨i + 1, by rwa [HahnSeries.mem_support], by ring⟩
  rw [HahnSeries.coeff_mul_left' hSf hsub]
  refine Finset.sum_nbij' (fun p => (p.1 + 1, p.2)) (fun p => (p.1 - 1, p.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_antidiagonal, Set.mem_image] at hp ⊢
    obtain ⟨⟨k, hk, hk2⟩, hp2, hp3⟩ := hp
    refine ⟨?_, hp2, by omega⟩
    have : i + 1 = k := by omega
    rw [this]; exact hk
  · rintro ⟨i, j⟩ hq
    simp only [Finset.mem_antidiagonal, Set.mem_image] at hq ⊢
    obtain ⟨hq1, hq2, hq3⟩ := hq
    exact ⟨⟨i, hq1, by omega⟩, hq2, by omega⟩
  · rintro ⟨i, j⟩ hp
    simp
  · rintro ⟨i, j⟩ hq
    simp
  · rintro ⟨i, j⟩ hp
    dsimp only
    rw [coeff_derivative, smul_mul_assoc]

/-- **Product (Leibniz) rule** for the Laurent-series derivative. -/
theorem derivative_mul (f g : R⸨X⸩) :
    derivative ℤ (f * g) = f * derivative ℤ g + derivative ℤ f * g := by
  rw [← HahnSeries.coeff_inj]
  funext n
  rw [coeff_derivative, HahnSeries.coeff_mul, HahnSeries.coeff_add,
    coeff_mul_derivative_right, coeff_derivative_mul_left, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ij hij => ?_)
  rw [Finset.mem_antidiagonal] at hij
  rw [← hij.2.2, add_smul]
  exact add_comm _ _

/-- The derivative of a constant Laurent series `HahnSeries.C c` vanishes. -/
theorem derivative_C (c : R) : derivative ℤ (HahnSeries.C c : R⸨X⸩) = 0 := by
  rw [HahnSeries.C_apply, derivative_apply, hasseDeriv_single, Ring.choose_one_right,
    zero_smul, HahnSeries.single_eq_zero]

/-- **Quotient rule** for the `Ring.inverse` of a unit: differentiating `u⁻¹` from
`u * u⁻¹ = 1`. -/
theorem derivative_inverse {u : R⸨X⸩} (hu : IsUnit u) :
    derivative ℤ (Ring.inverse u) = - Ring.inverse u * derivative ℤ u * Ring.inverse u := by
  have huv : u * Ring.inverse u = 1 := Ring.mul_inverse_cancel u hu
  have d1 : derivative ℤ (1 : R⸨X⸩) = 0 := by
    have h1 : (1 : R⸨X⸩) = HahnSeries.C 1 := (map_one _).symm
    rw [h1, derivative_C]
  have h := congrArg (derivative ℤ) huv
  rw [derivative_mul, d1] at h
  linear_combination (Ring.inverse u) * h - (derivative ℤ (Ring.inverse u)) * huv

end LaurentSeries

namespace HahnSeries

variable {R : Type*} [CommRing R]

/-- The outer (`z₂`-grading) coefficient of `embedDoubleLaurent ψ`: it vanishes in negative outer
degree, and in nonnegative outer degree `N` is the inner Laurent series whose `z₁^m` coefficient is
`MvPowerSeries.coeff (single 0 m + single 1 N.natAbs) ψ`. -/
lemma coeff_embedDoubleLaurent (ψ : MvPowerSeries (Fin 2) R) (N : ℤ) :
    (embedDoubleLaurent ψ).coeff N
      = if N < 0 then 0 else
          ofPowerSeries ℤ R (PowerSeries.mk fun m =>
            MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 N.natAbs) ψ) := by
  unfold embedDoubleLaurent
  rw [PowerSeries.coeff_coe]
  split_ifs with h
  · rfl
  · rw [PowerSeries.coeff_mk]

end HahnSeries
