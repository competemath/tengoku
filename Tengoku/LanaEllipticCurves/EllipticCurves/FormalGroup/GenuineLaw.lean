/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.DividedDifference
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.ExpansionSubst
import Tengoku.Seed.RingTheory.MvPowerSeries.Inverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Weierstrass formal group law as a genuine bivariate power series

Following Silverman AEC IV.1, this file constructs the Weierstrass formal group law *directly* as a
genuine element `W.formalGroupZW : MvPowerSeries (Fin 2) R`, using only pole-free `(z, w)`-plane
data, so that no Laurent ring and no pole cancellation is needed.

The construction is the classical chord process on the formal group, read in the `(z, w)`-plane:
* the **slope** `λ = W.formalWDividedDiff` of the line through the two formal points
  `(zᵢ, w(zᵢ))` is a genuine power series of order `≥ 2` (the divided difference, sibling A,
  `DividedDifference.lean`);
* the **intercept** `ν = w(z₁) − λ z₁` (`formalGroupNu`);
* substituting the line `w = λ z + ν` into the Weierstrass relation `w = wOp(w)` gives a cubic in
  `z` with leading coefficient `A = 1 + a₂λ + a₄λ² + a₆λ³` (a unit, `formalGroupLead`) and
  subleading coefficient `B = a₁λ + a₂ν + a₃λ² + 2a₄λν + 3a₆λ²ν` (order `≥ 2`, `formalGroupSub`);
  its two known roots are `z₁, z₂` (`formalCubicResidual_root_*`), so by Vieta the third root is
  `z₃' = −B·A⁻¹ − z₁ − z₂` (`formalThirdRoot`);
* finally the group sum's `z`-coordinate is the negation `i(z₃')` with
  `i(z) = −z / (1 − a₁z − a₃ w(z))`, giving the pole-free
  `formalGroupZW = −z₃' · (1 − a₁z₃' − a₃(λ z₃' + ν))⁻¹`.

The normalisation axioms `F(z₁, z₂) = z₁ + z₂ + ⋯` hold (`constantCoeff_formalGroupZW`,
`coeff_single_zero_formalGroupZW`, `coeff_single_one_formalGroupZW`), and `formalW.subst
formalGroupZW` is a fixed point of the substituted Weierstrass operator (the `w`-series of the sum,
`formalW_subst_formalGroupZW_fixed`). This is the object that #300 identifies with the Laurent
`F_E = W.formalGroupLaurent` (via the currying embedding), thereby concluding the inner
pole-freeness of `F_E`.

## Main definitions

* `WeierstrassCurve.formalGroupNu`, `formalGroupLead`, `formalGroupSub`, `formalThirdRoot`,
  `formalGroupDen` : the `(z, w)`-plane addition data.
* `WeierstrassCurve.formalGroupZW` : the genuine `MvPowerSeries (Fin 2) R` formal group law.

## Main results

* `WeierstrassCurve.constantCoeff_formalGroupZW`, `coeff_single_zero_formalGroupZW`,
  `coeff_single_one_formalGroupZW`, `one_le_order_formalGroupZW` : the normalisation axioms.
* `WeierstrassCurve.formalCubicResidual_root_zero` / `_one` : `z₁, z₂` solve the substituted cubic.
* `WeierstrassCurve.formalW_subst_formalGroupZW_fixed` : `formalW ∘ formalGroupZW` solves the
  Weierstrass relation (the `w`-series of the sum).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open MvPowerSeries

namespace WeierstrassCurve

section OrderLemmas

variable {R : Type*} [CommRing R] {σ : Type*}

/-- The order of a product is at least the order of its left factor. -/
private lemma le_order_mul_left {u v : MvPowerSeries σ R} {j : ℕ∞} (h : j ≤ u.order) :
    j ≤ (u * v).order :=
  le_trans h (le_trans le_self_add MvPowerSeries.le_order_mul)

/-- The order of a product is at least the order of its right factor. -/
private lemma le_order_mul_right {u v : MvPowerSeries σ R} {j : ℕ∞} (h : j ≤ v.order) :
    j ≤ (u * v).order :=
  le_trans h (le_trans le_add_self MvPowerSeries.le_order_mul)

/-- Order of a product from orders of both factors. -/
private lemma le_order_mul_add {u v : MvPowerSeries σ R} {a b : ℕ∞}
    (hu : a ≤ u.order) (hv : b ≤ v.order) : a + b ≤ (u * v).order :=
  le_trans (add_le_add hu hv) MvPowerSeries.le_order_mul

/-- Order of a sum from orders of both summands. -/
private lemma le_order_add {u v : MvPowerSeries σ R} {j : ℕ∞}
    (hu : j ≤ u.order) (hv : j ≤ v.order) : j ≤ (u + v).order :=
  le_trans (le_min hu hv) MvPowerSeries.min_order_le_add

/-- Order of a difference from orders of both terms. -/
private lemma le_order_sub {u v : MvPowerSeries σ R} {j : ℕ∞}
    (hu : j ≤ u.order) (hv : j ≤ v.order) : j ≤ (u - v).order := by
  rw [sub_eq_add_neg]
  exact le_order_add hu (by rw [MvPowerSeries.order_neg]; exact hv)

end OrderLemmas

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The line through the two formal points -/

/-- The **intercept** `ν = w(z₁) − λ z₁` of the line through the formal points
`(z₁, w(z₁))` and `(z₂, w(z₂))`, where `λ = W.formalWDividedDiff` is the slope. -/
noncomputable def formalGroupNu : MvPowerSeries (Fin 2) R :=
  W.formalW.toMvPowerSeries 0 - W.formalWDividedDiff * X 0

/-- `λ` has order `≥ 1`, hence vanishing constant coefficient. -/
private lemma one_le_order_formalWDividedDiff : (1 : ℕ∞) ≤ W.formalWDividedDiff.order :=
  le_trans (by exact_mod_cast one_le_two) W.two_le_order_formalWDividedDiff

private lemma constantCoeff_formalWDividedDiff :
    MvPowerSeries.constantCoeff W.formalWDividedDiff = 0 :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp W.one_le_order_formalWDividedDiff

/-- The embedding `w(z₀) = formalW.toMvPowerSeries 0` has order `≥ 2`. -/
private lemma two_le_order_toMvPowerSeries_formalW_zero :
    (2 : ℕ∞) ≤ (W.formalW.toMvPowerSeries (0 : Fin 2)).order := by
  apply MvPowerSeries.le_order
  intro d hd
  have hdeg : Finsupp.degree d = d 0 + d 1 := by rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  rw [hdeg] at hd
  have hsum : d 0 + d 1 < 2 := by exact_mod_cast hd
  by_cases hax : d = Finsupp.single 0 (d 0)
  · rw [hax, PowerSeries.coeff_toMvPowerSeries_single]
    apply PowerSeries.coeff_of_lt_order
    calc ((d 0 : ℕ) : ℕ∞) < 3 := by exact_mod_cast (by omega : d 0 < 3)
      _ ≤ W.formalW.order := W.order_formalW
  · exact PowerSeries.coeff_toMvPowerSeries_of_ne _ _ hax

/-- `ν` has order `≥ 2`. -/
private lemma two_le_order_formalGroupNu : (2 : ℕ∞) ≤ W.formalGroupNu.order := by
  rw [formalGroupNu]
  exact le_order_sub W.two_le_order_toMvPowerSeries_formalW_zero
    (le_order_mul_left W.two_le_order_formalWDividedDiff)

/-! ### The cubic coefficients and the Vieta third root -/

/-- The leading coefficient `A = 1 + a₂λ + a₄λ² + a₆λ³` of the substituted cubic (a unit). -/
noncomputable def formalGroupLead : MvPowerSeries (Fin 2) R :=
  1 + C W.a₂ * W.formalWDividedDiff + C W.a₄ * W.formalWDividedDiff ^ 2
    + C W.a₆ * W.formalWDividedDiff ^ 3

/-- The subleading coefficient `B = a₁λ + a₂ν + a₃λ² + 2a₄λν + 3a₆λ²ν` of the substituted cubic. -/
noncomputable def formalGroupSub : MvPowerSeries (Fin 2) R :=
  C W.a₁ * W.formalWDividedDiff + C W.a₂ * W.formalGroupNu + C W.a₃ * W.formalWDividedDiff ^ 2
    + 2 * C W.a₄ * W.formalWDividedDiff * W.formalGroupNu
    + 3 * C W.a₆ * W.formalWDividedDiff ^ 2 * W.formalGroupNu

/-- The leading coefficient of the cubic has constant coefficient `1`. -/
private lemma constantCoeff_formalGroupLead :
    MvPowerSeries.constantCoeff W.formalGroupLead = 1 := by
  rw [formalGroupLead]
  simp only [map_add, map_mul, map_pow, MvPowerSeries.constantCoeff_C, map_one,
    W.constantCoeff_formalWDividedDiff]
  ring

/-- The subleading coefficient of the cubic has order `≥ 2`. -/
private lemma two_le_order_formalGroupSub : (2 : ℕ∞) ≤ W.formalGroupSub.order := by
  rw [formalGroupSub]
  have hlam := W.two_le_order_formalWDividedDiff
  have hnu := W.two_le_order_formalGroupNu
  have hlam2 : (2 : ℕ∞) ≤ (W.formalWDividedDiff ^ 2).order := by
    rw [pow_two]; exact le_order_mul_left hlam
  refine le_order_add (le_order_add (le_order_add (le_order_add ?_ ?_) ?_) ?_) ?_
  · exact le_order_mul_right hlam
  · exact le_order_mul_right hnu
  · exact le_order_mul_right hlam2
  · exact le_order_mul_right hnu
  · exact le_order_mul_right hnu

/-- The **Vieta third root** `z₃' = −B·A⁻¹ − z₁ − z₂` of the substituted cubic: the third
intersection point of the chord with the curve. -/
noncomputable def formalThirdRoot : MvPowerSeries (Fin 2) R :=
  -(W.formalGroupSub * invOfUnit W.formalGroupLead 1) - X 0 - X 1

/-- The denominator `1 − a₁z₃' − a₃ w(z₃')` of the negation series (a unit). -/
noncomputable def formalGroupDen : MvPowerSeries (Fin 2) R :=
  1 - C W.a₁ * W.formalThirdRoot
    - C W.a₃ * (W.formalWDividedDiff * W.formalThirdRoot + W.formalGroupNu)

/-- The **Weierstrass formal group law** as a genuine bivariate power series
`MvPowerSeries (Fin 2) R`, built from the pole-free `(z, w)`-plane data:
`F(z₁, z₂) = i(z₃') = −z₃' / (1 − a₁z₃' − a₃ w(z₃'))`. (Silverman AEC IV.1, Theorem 1.1.) -/
noncomputable def formalGroupZW : MvPowerSeries (Fin 2) R :=
  (-W.formalThirdRoot) * invOfUnit W.formalGroupDen 1

/-! ### Normalisation axioms `F(z₁, z₂) = z₁ + z₂ + ⋯` -/

/-- The head-normalised remainder `F − z₁ − z₂` has order `≥ 2`. -/
private lemma two_le_order_formalGroupZW_sub :
    (2 : ℕ∞) ≤ (W.formalGroupZW - X 0 - X 1).order := by
  have key : W.formalGroupZW - X 0 - X 1
      = W.formalGroupSub * invOfUnit W.formalGroupLead 1 * invOfUnit W.formalGroupDen 1
        + (X 0 + X 1) * (invOfUnit W.formalGroupDen 1 - 1) := by
    rw [formalGroupZW, formalThirdRoot]; ring
  rw [key]
  refine le_order_add (le_order_mul_left (le_order_mul_left W.two_le_order_formalGroupSub)) ?_
  have hx : (1 : ℕ∞) ≤ (X (0 : Fin 2) + X 1 : MvPowerSeries (Fin 2) R).order :=
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (by
      simp [map_add, MvPowerSeries.constantCoeff_X])
  have hd : (1 : ℕ∞) ≤ (invOfUnit W.formalGroupDen 1 - 1).order :=
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (by
      rw [map_sub, MvPowerSeries.constantCoeff_invOfUnit, map_one, inv_one, Units.val_one,
        sub_self])
  have := le_order_mul_add hx hd
  rwa [show (1 : ℕ∞) + 1 = 2 by rfl] at this

/-- **Normalisation axiom (constant term).** `F` has zero constant term. -/
theorem constantCoeff_formalGroupZW :
    MvPowerSeries.constantCoeff W.formalGroupZW = 0 := by
  have hg : MvPowerSeries.constantCoeff (W.formalGroupZW - X 0 - X 1) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply MvPowerSeries.coeff_of_lt_order
    rw [map_zero]
    exact lt_of_lt_of_le (by norm_num) W.two_le_order_formalGroupZW_sub
  have hzw : W.formalGroupZW = X 0 + X 1 + (W.formalGroupZW - X 0 - X 1) := by ring
  rw [hzw]
  simp only [map_add, MvPowerSeries.constantCoeff_X, hg, add_zero]

private lemma single_zero_ne_single_one :
    (Finsupp.single (0 : Fin 2) 1) ≠ Finsupp.single 1 1 := by
  intro h
  have h0 := congrArg (fun f => f 0) h
  simp at h0

/-- **Normalisation axiom (`z₁`-linear term).** The coefficient of `z₁` in `F` is `1`. -/
theorem coeff_single_zero_formalGroupZW :
    MvPowerSeries.coeff (Finsupp.single 0 1) W.formalGroupZW = 1 := by
  have hg : MvPowerSeries.coeff (Finsupp.single 0 1) (W.formalGroupZW - X 0 - X 1) = 0 := by
    apply MvPowerSeries.coeff_of_lt_order
    rw [Finsupp.degree_single]
    exact lt_of_lt_of_le (by norm_num) W.two_le_order_formalGroupZW_sub
  have hzw : W.formalGroupZW = X 0 + X 1 + (W.formalGroupZW - X 0 - X 1) := by ring
  rw [hzw, map_add, map_add, hg, add_zero, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X,
    ite_eq_left rfl, ite_eq_right single_zero_ne_single_one, add_zero]

/-- **Normalisation axiom (`z₂`-linear term).** The coefficient of `z₂` in `F` is `1`. -/
theorem coeff_single_one_formalGroupZW :
    MvPowerSeries.coeff (Finsupp.single 1 1) W.formalGroupZW = 1 := by
  have hg : MvPowerSeries.coeff (Finsupp.single 1 1) (W.formalGroupZW - X 0 - X 1) = 0 := by
    apply MvPowerSeries.coeff_of_lt_order
    rw [Finsupp.degree_single]
    exact lt_of_lt_of_le (by norm_num) W.two_le_order_formalGroupZW_sub
  have hzw : W.formalGroupZW = X 0 + X 1 + (W.formalGroupZW - X 0 - X 1) := by ring
  rw [hzw, map_add, map_add, hg, add_zero, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X,
    ite_eq_right (Ne.symm single_zero_ne_single_one), ite_eq_left rfl, zero_add]

/-- `F` has order `≥ 1`. -/
theorem one_le_order_formalGroupZW : (1 : ℕ∞) ≤ W.formalGroupZW.order :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr W.constantCoeff_formalGroupZW

/-! ### Collinearity: `z₁, z₂` are roots of the substituted cubic -/

/-- The line value at `z₁` is `w(z₁)`. -/
private lemma line_zero :
    W.formalWDividedDiff * X 0 + W.formalGroupNu = W.formalW.subst (X (0 : Fin 2)) := by
  rw [formalGroupNu, PowerSeries.toMvPowerSeries_eq_subst]; ring

/-- The line value at `z₂` is `w(z₂)` (via divided-difference regularity). -/
private lemma line_one :
    W.formalWDividedDiff * X 1 + W.formalGroupNu = W.formalW.subst (X (1 : Fin 2)) := by
  have hspec := W.formalWDividedDiff_spec
  rw [PowerSeries.toMvPowerSeries_eq_subst, PowerSeries.toMvPowerSeries_eq_subst] at hspec
  rw [formalGroupNu, PowerSeries.toMvPowerSeries_eq_subst]
  linear_combination hspec

private lemma one_le_order_X (i : Fin 2) : (1 : ℕ∞) ≤ (X i : MvPowerSeries (Fin 2) R).order :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (MvPowerSeries.constantCoeff_X i)

/-- **Collinearity at `z₁`.** Substituting the line `w = λz + ν` into the Weierstrass relation, the
uniformiser `z₁` is a root of the resulting cubic (the chord meets the curve at `(z₁, w(z₁))`). -/
theorem formalCubicResidual_root_zero :
    (X (0 : Fin 2)) ^ 3
      + (C W.a₁ * X 0 + C W.a₂ * X 0 ^ 2) * (W.formalWDividedDiff * X 0 + W.formalGroupNu)
      + (C W.a₃ + C W.a₄ * X 0) * (W.formalWDividedDiff * X 0 + W.formalGroupNu) ^ 2
      + C W.a₆ * (W.formalWDividedDiff * X 0 + W.formalGroupNu) ^ 3
      - (W.formalWDividedDiff * X 0 + W.formalGroupNu) = 0 := by
  have hfix := W.formalW_subst_wOpSubst_fixed (t := (X (0 : Fin 2))) (one_le_order_X 0)
  simp only [wOpSubst] at hfix
  rw [W.line_zero]
  linear_combination -hfix

/-- **Collinearity at `z₂`.** Likewise `z₂` is a root of the substituted cubic. -/
theorem formalCubicResidual_root_one :
    (X (1 : Fin 2)) ^ 3
      + (C W.a₁ * X 1 + C W.a₂ * X 1 ^ 2) * (W.formalWDividedDiff * X 1 + W.formalGroupNu)
      + (C W.a₃ + C W.a₄ * X 1) * (W.formalWDividedDiff * X 1 + W.formalGroupNu) ^ 2
      + C W.a₆ * (W.formalWDividedDiff * X 1 + W.formalGroupNu) ^ 3
      - (W.formalWDividedDiff * X 1 + W.formalGroupNu) = 0 := by
  have hfix := W.formalW_subst_wOpSubst_fixed (t := (X (1 : Fin 2))) (one_le_order_X 1)
  simp only [wOpSubst] at hfix
  rw [W.line_one]
  linear_combination -hfix

/-! ### The `w`-series of the sum -/

/-- The `w`-series `formalW ∘ F` of the group sum solves the Weierstrass relation: it is the
positive-order fixed point of the substituted operator `wOpSubst F`. This feeds the identification
of `F` with the Laurent `F_E` in #300 (Silverman AEC IV.1, Theorem 1.1). -/
theorem formalW_subst_formalGroupZW_fixed :
    W.formalW.subst W.formalGroupZW
      = W.wOpSubst W.formalGroupZW (W.formalW.subst W.formalGroupZW) :=
  W.formalW_subst_wOpSubst_fixed W.one_le_order_formalGroupZW

end WeierstrassCurve
