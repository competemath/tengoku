/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.Expansion
import Tengoku.Seed.RingTheory.MvPowerSeries.Rename
import Tengoku.Seed.RingTheory.MvPowerSeries.Equiv
import Tengoku.Seed.RingTheory.MvPowerSeries.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The first divided difference of a power series as a genuine bivariate power series

For a one-variable power series `f ∈ R⟦X⟧`, the *first divided difference*

`Δf(z₀, z₁) = (f(z₁) − f(z₀)) / (z₁ − z₀)`

is a genuine element of `R⟦z₀, z₁⟧ = MvPowerSeries (Fin 2) R`: the naive quotient by the
non-unit `z₁ − z₀` is regularised by the telescoping cancellation
`f(z₁) − f(z₀) = Σₙ cₙ (z₁ⁿ − z₀ⁿ) = (z₁ − z₀)·Σₙ cₙ (z₁ⁿ⁻¹ + ⋯ + z₀ⁿ⁻¹)`. Reading off the last
sum coefficientwise gives the explicit power series `Δf` with

`coeff (z₀^a z₁^b) (Δf) = f.coeff (a + b + 1)`,

and the defining regularity identity `(z₁ − z₀)·Δf = f(z₁) − f(z₀)` is then a finite check on each
bigraded coefficient (`dividedDiff_spec`).

This is the missing "`z₁ − z₀` divides `f(z₁) − f(z₀)`" fact underlying the genuine power-series
construction of the Weierstrass formal group law (Silverman AEC IV.1): the slope of the line through
the two formal points `(zᵢ, w(zᵢ))` is exactly `Δ(formalW)`, a genuine power series of positive
order, so no Laurent ring / pole cancellation is needed to form it.

## Main definitions and results

* `PowerSeries.dividedDiff f` : the divided difference `Δf ∈ MvPowerSeries (Fin 2) R`.
* `PowerSeries.coeff_dividedDiff` : its bigraded coefficients.
* `PowerSeries.dividedDiff_spec` : the regularity identity
  `(X 1 − X 0) · Δf = f.toMvPowerSeries 1 − f.toMvPowerSeries 0`.
* `PowerSeries.constantCoeff_dividedDiff`, `PowerSeries.le_order_dividedDiff` : basic API.
* `WeierstrassCurve.formalWDividedDiff*` : the slope series `Δ(formalW)` and its regularity identity
  and order bound (`2 ≤ order`), the input to the `(z, w)` construction of the formal group law.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open MvPowerSeries

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-! ### Coefficients of the one-variable embedding `f ↦ f(zᵢ)` -/

/-- The embedding `Unit ↪ σ` with constant value `i`. -/
private def punitEmb {σ : Type*} (i : σ) : Unit ↪ σ :=
  ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩

/-- The `single i k` coefficient of the one-variable embedding `f(zᵢ) = f.toMvPowerSeries i` is the
`k`-th coefficient of `f`. -/
theorem coeff_toMvPowerSeries_single {σ : Type*} (f : R⟦X⟧) (i : σ) (k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single i k) (f.toMvPowerSeries i) = coeff k f := by
  rw [PowerSeries.coeff_def (s := Finsupp.single () k) (by simp), PowerSeries.toMvPowerSeries_apply]
  have h := MvPowerSeries.coeff_embDomain_rename (R := R) (punitEmb i) f (Finsupp.single () k)
  rwa [Finsupp.embDomain_single] at h

/-- Off the axis `{single i k}`, the one-variable embedding `f(zᵢ)` has vanishing coefficients. -/
theorem coeff_toMvPowerSeries_of_ne {σ : Type*} (f : R⟦X⟧) (i : σ) {d : σ →₀ ℕ}
    (hd : d ≠ Finsupp.single i (d i)) : MvPowerSeries.coeff d (f.toMvPowerSeries i) = 0 := by
  rw [PowerSeries.toMvPowerSeries_apply]
  refine MvPowerSeries.coeff_rename_eq_zero (fun _ => i) f ?_
  rintro ⟨c, rfl⟩
  apply hd
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, c = Finsupp.single () m :=
    ⟨c (), Finsupp.ext fun x => by obtain rfl := Subsingleton.elim x (); simp⟩
  rw [Finsupp.mapDomain_single, Finsupp.single_eq_same]

/-! ### The divided difference -/

/-- The **first divided difference** `Δf = (f(z₁) − f(z₀)) / (z₁ − z₀)` of a one-variable power
series `f`, realised as a genuine bivariate power series: its `z₀^a z₁^b`-coefficient is
`f.coeff (a + b + 1)`. -/
noncomputable def dividedDiff (f : R⟦X⟧) : MvPowerSeries (Fin 2) R :=
  fun d => coeff (d 0 + d 1 + 1) f

@[simp]
theorem coeff_dividedDiff (f : R⟦X⟧) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (dividedDiff f) = coeff (d 0 + d 1 + 1) f := rfl

theorem constantCoeff_dividedDiff (f : R⟦X⟧) :
    MvPowerSeries.constantCoeff (dividedDiff f) = coeff 1 f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_dividedDiff]
  simp

/-- **Regularity of the divided difference.** The naive quotient is a genuine power series:
`(z₁ − z₀) · Δf = f(z₁) − f(z₀)`. -/
theorem dividedDiff_spec (f : R⟦X⟧) :
    (MvPowerSeries.X 1 - MvPowerSeries.X 0) * dividedDiff f
      = f.toMvPowerSeries 1 - f.toMvPowerSeries 0 := by
  classical
  ext d
  -- The two `X`-multiplications, via `coeff_monomial_mul`.
  have hX1 : MvPowerSeries.coeff d (MvPowerSeries.X (1 : Fin 2) * dividedDiff f)
      = if 1 ≤ d 1 then coeff (d 0 + d 1) f else 0 := by
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
    by_cases hb1 : 1 ≤ d 1
    · rw [ite_eq_left (Finsupp.single_le_iff.mpr hb1), ite_eq_left hb1, one_mul, coeff_dividedDiff]
      have h0 : (Finsupp.single (1 : Fin 2) 1) 0 = 0 := by simp
      have h1 : (Finsupp.single (1 : Fin 2) 1) 1 = 1 := by simp
      have key : ((d - Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ)) 0
          + ((d - Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ)) 1 + 1 = d 0 + d 1 := by
        rw [Finsupp.tsub_apply, Finsupp.tsub_apply, h0, h1, Nat.sub_zero]; omega
      rw [key]
    · rw [ite_eq_right (fun h => hb1 (Finsupp.single_le_iff.mp h)), ite_eq_right hb1]
  have hX0 : MvPowerSeries.coeff d (MvPowerSeries.X (0 : Fin 2) * dividedDiff f)
      = if 1 ≤ d 0 then coeff (d 0 + d 1) f else 0 := by
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
    by_cases ha1 : 1 ≤ d 0
    · rw [ite_eq_left (Finsupp.single_le_iff.mpr ha1), ite_eq_left ha1, one_mul, coeff_dividedDiff]
      have h0 : (Finsupp.single (0 : Fin 2) 1) 0 = 1 := by simp
      have h1 : (Finsupp.single (0 : Fin 2) 1) 1 = 0 := by simp
      have key : ((d - Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ)) 0
          + ((d - Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ)) 1 + 1 = d 0 + d 1 := by
        rw [Finsupp.tsub_apply, Finsupp.tsub_apply, h0, h1, Nat.sub_zero]; omega
      rw [key]
    · rw [ite_eq_right (fun h => ha1 (Finsupp.single_le_iff.mp h)), ite_eq_right ha1]
  -- The two embedding coefficients.
  have hE1 : MvPowerSeries.coeff d (f.toMvPowerSeries (1 : Fin 2))
      = if d 0 = 0 then coeff (d 1) f else 0 := by
    by_cases h0 : d 0 = 0
    · rw [ite_eq_left h0]
      have hds : d = Finsupp.single (1 : Fin 2) (d 1) := by
        ext s; fin_cases s <;> simp [h0]
      rw [hds, coeff_toMvPowerSeries_single, Finsupp.single_eq_same]
    · rw [ite_eq_right h0]
      apply coeff_toMvPowerSeries_of_ne
      intro hcon
      apply h0
      have := congrArg (fun g => g 0) hcon
      simpa [Finsupp.single_apply] using this
  have hE0 : MvPowerSeries.coeff d (f.toMvPowerSeries (0 : Fin 2))
      = if d 1 = 0 then coeff (d 0) f else 0 := by
    by_cases h0 : d 1 = 0
    · rw [ite_eq_left h0]
      have hds : d = Finsupp.single (0 : Fin 2) (d 0) := by
        ext s; fin_cases s <;> simp [h0]
      rw [hds, coeff_toMvPowerSeries_single, Finsupp.single_eq_same]
    · rw [ite_eq_right h0]
      apply coeff_toMvPowerSeries_of_ne
      intro hcon
      apply h0
      have := congrArg (fun g => g 1) hcon
      simpa [Finsupp.single_apply] using this
  -- Assemble.
  rw [sub_mul, map_sub, map_sub, hX1, hX0, hE1, hE0]
  rcases Nat.eq_zero_or_pos (d 0) with h0 | h0 <;> rcases Nat.eq_zero_or_pos (d 1) with h1 | h1
  · rw [ite_eq_right (by omega : ¬ 1 ≤ d 1), ite_eq_right (by omega : ¬ 1 ≤ d 0),
      ite_eq_left (by omega : d 0 = 0), ite_eq_left (by omega : d 1 = 0), h0, h1]; ring
  · rw [ite_eq_left (by omega : 1 ≤ d 1), ite_eq_right (by omega : ¬ 1 ≤ d 0),
      ite_eq_left (by omega : d 0 = 0), ite_eq_right (by omega : ¬ d 1 = 0), h0, Nat.zero_add]
  · rw [ite_eq_right (by omega : ¬ 1 ≤ d 1), ite_eq_left (by omega : 1 ≤ d 0),
      ite_eq_right (by omega : ¬ d 0 = 0), ite_eq_left (by omega : d 1 = 0), h1, Nat.add_zero]
  · rw [ite_eq_left (by omega : 1 ≤ d 1), ite_eq_left (by omega : 1 ≤ d 0),
      ite_eq_right (by omega : ¬ d 0 = 0), ite_eq_right (by omega : ¬ d 1 = 0)]; ring

/-- A lower bound on the order of the divided difference: if `f` has order `≥ n + 1` then `Δf` has
order `≥ n`. -/
theorem le_order_dividedDiff (f : R⟦X⟧) (n : ℕ) (hf : (n : ℕ∞) + 1 ≤ f.order) :
    (n : ℕ∞) ≤ (dividedDiff f).order := by
  apply MvPowerSeries.le_order
  intro d hd
  rw [coeff_dividedDiff]
  apply PowerSeries.coeff_of_lt_order
  have hdeg : d 0 + d 1 < n := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
    exact_mod_cast hd
  calc ((d 0 + d 1 + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast (by omega : d 0 + d 1 + 1 ≤ n)
    _ < (n : ℕ∞) + 1 := by exact_mod_cast (by omega : n < n + 1)
    _ ≤ f.order := hf

end PowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The **slope series** `λ = Δ(w) = (w(z₁) − w(z₀)) / (z₁ − z₀)` of the Weierstrass expansion, a
genuine element of `MvPowerSeries (Fin 2) R`. This is the slope of the line through the two formal
points `(zᵢ, w(zᵢ))` in the `(z, w)`-plane, the first ingredient of the genuine power-series
construction of the formal group law. -/
noncomputable def formalWDividedDiff : MvPowerSeries (Fin 2) R :=
  PowerSeries.dividedDiff W.formalW

/-- The slope series regularises the difference quotient of `w`:
`(z₁ − z₀) · λ = w(z₁) − w(z₀)`. -/
theorem formalWDividedDiff_spec :
    (MvPowerSeries.X 1 - MvPowerSeries.X 0) * W.formalWDividedDiff
      = W.formalW.toMvPowerSeries 1 - W.formalW.toMvPowerSeries 0 :=
  PowerSeries.dividedDiff_spec W.formalW

/-- The slope series has order at least `2` (since `w` has order at least `3`). In particular its
constant coefficient vanishes, so it is a legitimate substitutand/parameter. -/
theorem two_le_order_formalWDividedDiff : (2 : ℕ∞) ≤ W.formalWDividedDiff.order := by
  refine PowerSeries.le_order_dividedDiff W.formalW 2 ?_
  have h32 : ((2 : ℕ) : ℕ∞) + 1 = 3 := by norm_num
  rw [h32]
  exact W.order_formalW

end WeierstrassCurve
