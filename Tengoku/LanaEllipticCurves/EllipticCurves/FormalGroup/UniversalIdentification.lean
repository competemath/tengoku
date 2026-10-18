/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.ThirdRootMatching
import Tengoku.LanaEllipticCurves.EllipticCurves.UniversalCurve
import Tengoku.Seed.RingTheory.MvPolynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The universal-domain identification `embedDoubleLaurent formalGroupZW = formalGroupLaurent`

`EllipticCurves.FormalGroup.ThirdRootMatching` discharged the whole geometric half of the
identification, reducing it to a single **regularity** hypothesis on the coordinate differences:

`embedDoubleLaurent_formalGroupZW_of_regular` : given that `z_c - z₁` and `z_c - z₂` are regular
(left-cancellable) in `(R⸨X⸩)⸨X⸩`, the `(z, w)`- and Laurent formal group laws agree.

This file instantiates that reduction at the **universal curve** `WeierstrassCurve.univ` over
`S := MvPolynomial (Fin 5) ℤ` with `aᵢ = MvPolynomial.X i`, which is defined in
`EllipticCurves.UniversalCurve`.  Because `S` is a characteristic-`0`
integral domain, the double Laurent ring `(S⸨X⸩)⸨X⸩` is again an integral domain, so a nonzero
element is a non-zero-divisor.  The two regularity hypotheses then follow from the two nonvanishing
facts `z_c - z₁ ≠ 0` and `z_c - z₂ ≠ 0`.

Those two nonvanishing facts are extracted from the "unit-multiple" presentation
`(z_c - zᵢ)·(Y·yᵢ) = -ν·(x₃ - xᵢ)` (with `Y = secantY`, `yᵢ = biYᵢ`, `ν = formalNu` a unit); over
the domain `S` the difference `x₃ - xᵢ` is nonzero because its `(z₂, z₁)`-bidegree-`(1, -3)`
coefficient is `-2 ≠ 0` (Silverman AEC IV.1, the `-2` leading-slope finding).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open scoped LaurentSeries

namespace WeierstrassCurve

/-- The secant `y`-value times the coordinate-change third-point `z` is `-x₃`.  (Re-derivation of
the private `secantY_mul_coordChangeZ` from `isUnit_thirdSecantY`, for use over an arbitrary base.)
-/
private theorem secantY_mul_coordChangeZ' {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.secantY * W.coordChangeZ = -W.formalXThree := by
  have hY : W.secantY * Ring.inverse W.secantY = 1 :=
    Ring.mul_inverse_cancel _ W.isUnit_thirdSecantY
  rw [coordChangeZ]
  linear_combination (-W.formalXThree) * hY

/-- **Unit-multiple presentation of `z_c - z₁`.** `(z_c - z₁)·(Y·y₁) = -ν·(x₃ - x₁)`, where
`Y = secantY`, `y₁ = biY₁`, `ν = formalNu`.  Both `Y·y₁` and `ν` are units, so `z_c - z₁` is a
unit multiple of `x₃ - x₁`. -/
private theorem coordChangeZ_sub_biZ₁_mul {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    (W.coordChangeZ - W.biZ₁) * (W.secantY * W.biY₁)
      = -W.formalNu * (W.formalXThree - W.biX₁) := by
  have e1 := W.secantY_mul_coordChangeZ'
  have e2 := W.biZ₁_mul_biY₁
  have e3 := W.biY₁_eq
  have e4 : W.secantY = W.formalLambda * W.formalXThree + W.formalNu := rfl
  linear_combination W.biY₁ * e1 + (-W.secantY) * e2 + (-W.formalXThree) * e3 + W.biX₁ * e4

/-- **Unit-multiple presentation of `z_c - z₂`.** `(z_c - z₂)·(Y·y₂) = -ν·(x₃ - x₂)`. -/
private theorem coordChangeZ_sub_biZ₂_mul {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    (W.coordChangeZ - W.biZ₂) * (W.secantY * W.biY₂)
      = -W.formalNu * (W.formalXThree - W.biX₂) := by
  have e1 := W.secantY_mul_coordChangeZ'
  have e2 := W.biZ₂_mul_biY₂
  have e3 := W.biY₂_eq
  have e4 : W.secantY = W.formalLambda * W.formalXThree + W.formalNu := rfl
  linear_combination W.biY₂ * e1 + (-W.secantY) * e2 + (-W.formalXThree) * e3 + W.biX₂ * e4

end WeierstrassCurve

namespace WeierstrassCurve

/-- Over the universal (char-`0` domain) base, `x₃ - x₁ ≠ 0`: its bidegree-`(1, -3)` coefficient is
`-2 ≠ 0`. -/
theorem univ_formalXThree_sub_biX₁_ne_zero :
    univ.formalXThree - univ.biX₁ ≠ 0 := by
  intro h
  have hc : ((univ.formalXThree - univ.biX₁).coeff 1).coeff (-3)
      = (-2 : MvPolynomial (Fin 5) ℤ) := by
    rw [HahnSeries.coeff_sub, univ.coeff_biX₁_of_ne (by norm_num : (1 : ℤ) ≠ 0), sub_zero,
      univ.coeff_formalXThree_one_inner_neg_three]
  rw [h] at hc
  simp only [HahnSeries.coeff_zero] at hc
  exact (by norm_num : (-2 : MvPolynomial (Fin 5) ℤ) ≠ 0) hc.symm

/-- Over the universal (char-`0` domain) base, `x₃ - x₂ ≠ 0`. -/
theorem univ_formalXThree_sub_biX₂_ne_zero :
    univ.formalXThree - univ.biX₂ ≠ 0 := by
  intro h
  have hc : ((univ.formalXThree - univ.biX₂).coeff 1).coeff (-3)
      = (-2 : MvPolynomial (Fin 5) ℤ) := by
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_sub, univ.coeff_formalXThree_one_inner_neg_three,
      univ.coeff_biX₂, HahnSeries.C_apply,
      HahnSeries.coeff_single_of_ne (by norm_num : (-3 : ℤ) ≠ 0), sub_zero]
  rw [h] at hc
  simp only [HahnSeries.coeff_zero] at hc
  exact (by norm_num : (-2 : MvPolynomial (Fin 5) ℤ) ≠ 0) hc.symm

/-- Over the universal base, `z_c - z₁ ≠ 0`. -/
theorem univ_coordChangeZ_sub_biZ₁_ne_zero :
    univ.coordChangeZ - univ.biZ₁ ≠ 0 := by
  intro h
  have key := univ.coordChangeZ_sub_biZ₁_mul
  rw [h, zero_mul] at key
  have hprod : univ.formalNu * (univ.formalXThree - univ.biX₁) = 0 := by
    linear_combination key
  rcases mul_eq_zero.mp hprod with h1 | h2
  · exact univ.isUnit_formalNu.ne_zero h1
  · exact univ_formalXThree_sub_biX₁_ne_zero h2

/-- Over the universal base, `z_c - z₂ ≠ 0`. -/
theorem univ_coordChangeZ_sub_biZ₂_ne_zero :
    univ.coordChangeZ - univ.biZ₂ ≠ 0 := by
  intro h
  have key := univ.coordChangeZ_sub_biZ₂_mul
  rw [h, zero_mul] at key
  have hprod : univ.formalNu * (univ.formalXThree - univ.biX₂) = 0 := by
    linear_combination key
  rcases mul_eq_zero.mp hprod with h1 | h2
  · exact univ.isUnit_formalNu.ne_zero h1
  · exact univ_formalXThree_sub_biX₂_ne_zero h2

/-- **The universal-domain identification.** At the universal curve over
`S = MvPolynomial (Fin 5) ℤ`
the `(z, w)`- and Laurent formal group laws agree, unconditionally.  The two regularity hypotheses
of `embedDoubleLaurent_formalGroupZW_of_regular` follow from the nonvanishing of the coordinate
differences via `NoZeroDivisors` in the double Laurent domain. -/
theorem embedDoubleLaurent_formalGroupZW_univ :
    HahnSeries.embedDoubleLaurent univ.formalGroupZW = univ.formalGroupLaurent := by
  refine univ.embedDoubleLaurent_formalGroupZW_of_regular ?_ ?_
  · intro c hc
    exact (mul_eq_zero.mp hc).resolve_left univ_coordChangeZ_sub_biZ₁_ne_zero
  · intro c hc
    exact (mul_eq_zero.mp hc).resolve_left univ_coordChangeZ_sub_biZ₂_ne_zero

end WeierstrassCurve
