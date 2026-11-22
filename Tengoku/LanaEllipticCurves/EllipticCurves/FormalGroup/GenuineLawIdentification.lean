/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.GenuineLaw
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.EmbedDictionary
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.FormalGroupLaurent
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.Law

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Identification of the genuine `(z, w)` formal group law with the Laurent `F_E`

The genuine bivariate power series `W.formalGroupZW : MvPowerSeries (Fin 2) R` of
`EllipticCurves.FormalGroup.GenuineLaw` and the Laurent element
`W.formalGroupLaurent = -x₃ · y₃⁻¹ ∈ (R⸨X⸩)⸨X⸩` of `EllipticCurves.FormalGroup.FormalGroupLaurent`
are two constructions of the *same* Weierstrass formal group law, in the `(z, w)`-plane and the
`(x, y)`-plane respectively, related by the projective-linear change of coordinates
`z = -x/y`, `w = -1/y` (Silverman AEC IV.1). This file proves they agree under the faithful writer
`HahnSeries.embedDoubleLaurent`:

`embedDoubleLaurent W.formalGroupZW = W.formalGroupLaurent`,

and draws the two consequences that close the analytic core (#286):

* `coeff_formalGroupLaurent_inner_of_lt` : `F_E` is pole-free in the inner variable `z₁` — every
  outer coefficient is a genuine power series in `z₁`;
* `ofDoubleLaurent_formalGroupLaurent_eq` / `formalGroupSeries_eq_formalGroupZW` : the reader
  `ofDoubleLaurent` recovers `formalGroupZW`, so the extracted `W.formalGroupSeries` (Law.lean)
  coincides with the genuine `W.formalGroupZW`.

## Strategy

Write `φ := HahnSeries.embedDoubleLaurentRingHom` (a ring homomorphism). Pushing `φ` through the
`(z, w)` addition data with the generator dictionary
(`EllipticCurves.FormalGroup.EmbedDictionary`) gives the Laurent images of `ν, A, B, z₃', D`, and
the slope bridge `(z₂ - z₁)·λ_L = w₂ - w₁`. Because `y₃ = W.formalYThree` is a **unit**
(`isUnit_formalYThree`) and `F_E · y₃ = -x₃`, the whole identification reduces to the single
polynomial identity

`(★)  φ(z₃') · y₃ = x₃ · φ(D)`

after clearing the (unit) denominators, which is the change-of-coordinates core.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open MvPowerSeries
open scoped LaurentSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### Constant coefficients of the `(z, w)` addition data (unit witnesses) -/

private lemma cc_formalWDividedDiff :
    MvPowerSeries.constantCoeff W.formalWDividedDiff = 0 :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
    (le_trans (by exact_mod_cast one_le_two) W.two_le_order_formalWDividedDiff)

private lemma cc_toMvPowerSeries_formalW_zero :
    MvPowerSeries.constantCoeff (W.formalW.toMvPowerSeries (0 : Fin 2)) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      show (0 : Fin 2 →₀ ℕ) = Finsupp.single (0 : Fin 2) 0 by simp,
      PowerSeries.coeff_toMvPowerSeries_single]
  exact PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by norm_num) W.order_formalW)

private lemma cc_formalGroupNu : MvPowerSeries.constantCoeff W.formalGroupNu = 0 := by
  rw [formalGroupNu, map_sub, map_mul, W.cc_formalWDividedDiff, W.cc_toMvPowerSeries_formalW_zero]
  simp

private lemma cc_formalGroupLead : MvPowerSeries.constantCoeff W.formalGroupLead = 1 := by
  rw [formalGroupLead]
  simp only [map_add, map_mul, map_pow, MvPowerSeries.constantCoeff_C, map_one,
    W.cc_formalWDividedDiff]
  ring

private lemma cc_formalGroupSub : MvPowerSeries.constantCoeff W.formalGroupSub = 0 := by
  rw [formalGroupSub]
  simp [map_add, map_mul, map_pow, MvPowerSeries.constantCoeff_C, W.cc_formalWDividedDiff,
    W.cc_formalGroupNu]

private lemma cc_formalThirdRoot : MvPowerSeries.constantCoeff W.formalThirdRoot = 0 := by
  rw [formalThirdRoot]
  simp [map_sub, map_neg, map_mul, MvPowerSeries.constantCoeff_X, W.cc_formalGroupSub]

private lemma cc_formalGroupDen : MvPowerSeries.constantCoeff W.formalGroupDen = 1 := by
  rw [formalGroupDen]
  simp [map_sub, map_mul, map_add, map_one, MvPowerSeries.constantCoeff_C,
    W.cc_formalThirdRoot, W.cc_formalWDividedDiff, W.cc_formalGroupNu]

/-! ### The pushforward dictionary: `φ` applied to the `(z, w)` addition data -/

/-- `φ(ν) = w₁ - λ_L · z₁`.
@isnad1 id=eq.0h2v.s8.4fcb66103112 from=translated src=- shape=14d135d4 vocab=d52b7f88
-/
theorem embedDoubleLaurent_formalGroupNu :
    HahnSeries.embedDoubleLaurent W.formalGroupNu
      = W.biW₁ - HahnSeries.embedDoubleLaurent W.formalWDividedDiff * W.biZ₁ := by
  rw [← HahnSeries.embedDoubleLaurentRingHom_apply, formalGroupNu, map_sub, map_mul]
  simp only [HahnSeries.embedDoubleLaurentRingHom_apply, W.embedDoubleLaurent_biZ₁,
    W.embedDoubleLaurent_biW₁]

/-- The slope bridge: `(z₂ - z₁)·λ_L = w₂ - w₁` (the `φ`-image of `formalWDividedDiff_spec`).
@isnad1 id=eq.0h2v.s9.f2f5befe9d0a from=translated src=- shape=8e4745c8 vocab=3d7fe4a2
-/
theorem embedDoubleLaurent_formalWDividedDiff_spec :
    (W.biZ₂ - W.biZ₁) * HahnSeries.embedDoubleLaurent W.formalWDividedDiff = W.biW₂ - W.biW₁ := by
  have h := congrArg (HahnSeries.embedDoubleLaurentRingHom) W.formalWDividedDiff_spec
  simp only [map_sub, map_mul, HahnSeries.embedDoubleLaurentRingHom_apply,
    W.embedDoubleLaurent_biZ₁, W.embedDoubleLaurent_biZ₂, W.embedDoubleLaurent_biW₁,
    W.embedDoubleLaurent_biW₂] at h
  exact h

/-- `φ(A) = 1 + a₂ λ_L + a₄ λ_L² + a₆ λ_L³`.
@isnad1 id=eq.0h2v.s12.29779462b751 from=translated src=- shape=40e9bf3c vocab=7d89af69
-/
theorem embedDoubleLaurent_formalGroupLead :
    HahnSeries.embedDoubleLaurent W.formalGroupLead
      = 1 + HahnSeries.C (HahnSeries.C W.a₂) * HahnSeries.embedDoubleLaurent W.formalWDividedDiff
        + HahnSeries.C (HahnSeries.C W.a₄)
          * HahnSeries.embedDoubleLaurent W.formalWDividedDiff ^ 2
        + HahnSeries.C (HahnSeries.C W.a₆)
          * HahnSeries.embedDoubleLaurent W.formalWDividedDiff ^ 3 := by
  rw [← HahnSeries.embedDoubleLaurentRingHom_apply, formalGroupLead]
  simp only [map_add, map_mul, map_pow, map_one, HahnSeries.embedDoubleLaurentRingHom_apply,
    HahnSeries.embedDoubleLaurent_C]

/-- `φ(B) = a₁ λ_L + a₂ ν_L + a₃ λ_L² + 2 a₄ λ_L ν_L + 3 a₆ λ_L² ν_L`.
@isnad1 id=eq.0h2v.s13.b170ae8dd9c8 from=translated src=- shape=0a56fe47 vocab=0ae23f33
-/
theorem embedDoubleLaurent_formalGroupSub :
    HahnSeries.embedDoubleLaurent W.formalGroupSub
      = HahnSeries.C (HahnSeries.C W.a₁) * HahnSeries.embedDoubleLaurent W.formalWDividedDiff
        + HahnSeries.C (HahnSeries.C W.a₂) * HahnSeries.embedDoubleLaurent W.formalGroupNu
        + HahnSeries.C (HahnSeries.C W.a₃)
          * HahnSeries.embedDoubleLaurent W.formalWDividedDiff ^ 2
        + 2 * HahnSeries.C (HahnSeries.C W.a₄)
          * HahnSeries.embedDoubleLaurent W.formalWDividedDiff
          * HahnSeries.embedDoubleLaurent W.formalGroupNu
        + 3 * HahnSeries.C (HahnSeries.C W.a₆)
          * HahnSeries.embedDoubleLaurent W.formalWDividedDiff ^ 2
          * HahnSeries.embedDoubleLaurent W.formalGroupNu := by
  rw [← HahnSeries.embedDoubleLaurentRingHom_apply, formalGroupSub]
  simp only [map_add, map_mul, map_pow, map_ofNat, HahnSeries.embedDoubleLaurentRingHom_apply,
    HahnSeries.embedDoubleLaurent_C]

/-! ### Pushing `φ` through the inverses `invOfUnit A 1`, `invOfUnit D 1` -/

/-- `φ(invOfUnit A 1) = Ring.inverse (φ A)` (`A = formalGroupLead`, constant coefficient `1`).
@isnad1 id=eq.0h2v.s7.b067d0d08b59 from=translated src=- shape=b1b7bb7f vocab=fdf7b2b4
-/
theorem embedDoubleLaurent_invOfUnit_formalGroupLead :
    HahnSeries.embedDoubleLaurent (invOfUnit W.formalGroupLead 1)
      = Ring.inverse (HahnSeries.embedDoubleLaurent W.formalGroupLead) := by
  have hone : HahnSeries.embedDoubleLaurent W.formalGroupLead
      * HahnSeries.embedDoubleLaurent (invOfUnit W.formalGroupLead 1) = 1 := by
    rw [← HahnSeries.embedDoubleLaurentRingHom_apply, ← HahnSeries.embedDoubleLaurentRingHom_apply,
      ← map_mul, MvPowerSeries.mul_invOfUnit W.formalGroupLead 1
        (by rw [W.cc_formalGroupLead, Units.val_one]), map_one]
  have hu : IsUnit (HahnSeries.embedDoubleLaurent W.formalGroupLead) :=
    IsUnit.of_mul_eq_one _ hone
  calc HahnSeries.embedDoubleLaurent (invOfUnit W.formalGroupLead 1)
      = Ring.inverse (HahnSeries.embedDoubleLaurent W.formalGroupLead)
          * HahnSeries.embedDoubleLaurent W.formalGroupLead
          * HahnSeries.embedDoubleLaurent (invOfUnit W.formalGroupLead 1) := by
        rw [Ring.inverse_mul_cancel _ hu, one_mul]
    _ = Ring.inverse (HahnSeries.embedDoubleLaurent W.formalGroupLead)
          * (HahnSeries.embedDoubleLaurent W.formalGroupLead
            * HahnSeries.embedDoubleLaurent (invOfUnit W.formalGroupLead 1)) := by rw [mul_assoc]
    _ = Ring.inverse (HahnSeries.embedDoubleLaurent W.formalGroupLead) := by rw [hone, mul_one]

/-- `φ(invOfUnit D 1) = Ring.inverse (φ D)` (`D = formalGroupDen`, constant coefficient `1`).
@isnad1 id=eq.0h2v.s7.dd2d3b99183d from=translated src=- shape=b1b7bb7f vocab=dfff7113
-/
theorem embedDoubleLaurent_invOfUnit_formalGroupDen :
    HahnSeries.embedDoubleLaurent (invOfUnit W.formalGroupDen 1)
      = Ring.inverse (HahnSeries.embedDoubleLaurent W.formalGroupDen) := by
  have hone : HahnSeries.embedDoubleLaurent W.formalGroupDen
      * HahnSeries.embedDoubleLaurent (invOfUnit W.formalGroupDen 1) = 1 := by
    rw [← HahnSeries.embedDoubleLaurentRingHom_apply, ← HahnSeries.embedDoubleLaurentRingHom_apply,
      ← map_mul, MvPowerSeries.mul_invOfUnit W.formalGroupDen 1
        (by rw [W.cc_formalGroupDen, Units.val_one]), map_one]
  have hu : IsUnit (HahnSeries.embedDoubleLaurent W.formalGroupDen) :=
    IsUnit.of_mul_eq_one _ hone
  calc HahnSeries.embedDoubleLaurent (invOfUnit W.formalGroupDen 1)
      = Ring.inverse (HahnSeries.embedDoubleLaurent W.formalGroupDen)
          * HahnSeries.embedDoubleLaurent W.formalGroupDen
          * HahnSeries.embedDoubleLaurent (invOfUnit W.formalGroupDen 1) := by
        rw [Ring.inverse_mul_cancel _ hu, one_mul]
    _ = Ring.inverse (HahnSeries.embedDoubleLaurent W.formalGroupDen)
          * (HahnSeries.embedDoubleLaurent W.formalGroupDen
            * HahnSeries.embedDoubleLaurent (invOfUnit W.formalGroupDen 1)) := by rw [mul_assoc]
    _ = Ring.inverse (HahnSeries.embedDoubleLaurent W.formalGroupDen) := by rw [hone, mul_one]

/-- `φ(D)` is a unit of `(R⸨X⸩)⸨X⸩`.
@isnad1 id=isunit.0h2v.s6.e1a0dd1b79b3 from=translated src=- shape=b90ac62e vocab=3b1a0e38
-/
theorem isUnit_embedDoubleLaurent_formalGroupDen :
    IsUnit (HahnSeries.embedDoubleLaurent W.formalGroupDen) := by
  have hone : HahnSeries.embedDoubleLaurent W.formalGroupDen
      * HahnSeries.embedDoubleLaurent (invOfUnit W.formalGroupDen 1) = 1 := by
    rw [← HahnSeries.embedDoubleLaurentRingHom_apply, ← HahnSeries.embedDoubleLaurentRingHom_apply,
      ← map_mul, MvPowerSeries.mul_invOfUnit W.formalGroupDen 1
        (by rw [W.cc_formalGroupDen, Units.val_one]), map_one]
  exact IsUnit.of_mul_eq_one _ hone

/-- `φ(z₃') = -(φ(B) · Ring.inverse (φ A)) - z₁ - z₂`.
@isnad1 id=eq.0h2v.s9.c9c3e3d82ac7 from=translated src=- shape=f7f95874 vocab=7d7d0aa6
-/
theorem embedDoubleLaurent_formalThirdRoot :
    HahnSeries.embedDoubleLaurent W.formalThirdRoot
      = -(HahnSeries.embedDoubleLaurent W.formalGroupSub
          * Ring.inverse (HahnSeries.embedDoubleLaurent W.formalGroupLead))
        - W.biZ₁ - W.biZ₂ := by
  rw [← HahnSeries.embedDoubleLaurentRingHom_apply, formalThirdRoot, map_sub, map_sub, map_neg,
    map_mul]
  simp only [HahnSeries.embedDoubleLaurentRingHom_apply, W.embedDoubleLaurent_biZ₁,
    W.embedDoubleLaurent_biZ₂, W.embedDoubleLaurent_invOfUnit_formalGroupLead]

/-- `φ(D) = 1 - a₁ φ(z₃') - a₃ (λ_L φ(z₃') + ν_L)`.
@isnad1 id=eq.0h2v.s11.a7e034097bcd from=translated src=- shape=c51e5a78 vocab=839ee25d
-/
theorem embedDoubleLaurent_formalGroupDen :
    HahnSeries.embedDoubleLaurent W.formalGroupDen
      = 1 - HahnSeries.C (HahnSeries.C W.a₁) * HahnSeries.embedDoubleLaurent W.formalThirdRoot
        - HahnSeries.C (HahnSeries.C W.a₃)
          * (HahnSeries.embedDoubleLaurent W.formalWDividedDiff
              * HahnSeries.embedDoubleLaurent W.formalThirdRoot
            + HahnSeries.embedDoubleLaurent W.formalGroupNu) := by
  rw [← HahnSeries.embedDoubleLaurentRingHom_apply, formalGroupDen, map_sub, map_sub, map_mul,
    map_mul, map_add, map_mul, map_one]
  simp only [HahnSeries.embedDoubleLaurentRingHom_apply, HahnSeries.embedDoubleLaurent_C]

/-! ### The reduction of the identification to the single core identity `(★)` -/

/-- `φ(F) = -φ(z₃') · Ring.inverse (φ D)` — the `(z, w)` law written with a genuine inverse.
@isnad1 id=eq.0h2v.s8.50557ba355f9 from=translated src=- shape=b3c1b5fe vocab=b22f5f1c
-/
theorem embedDoubleLaurent_formalGroupZW_eq :
    HahnSeries.embedDoubleLaurent W.formalGroupZW
      = -(HahnSeries.embedDoubleLaurent W.formalThirdRoot)
        * Ring.inverse (HahnSeries.embedDoubleLaurent W.formalGroupDen) := by
  rw [← HahnSeries.embedDoubleLaurentRingHom_apply, formalGroupZW, map_mul, map_neg]
  simp only [HahnSeries.embedDoubleLaurentRingHom_apply,
    W.embedDoubleLaurent_invOfUnit_formalGroupDen]

/-- **Reduction to the core identity `(★)`.** Given `φ(z₃') · y₃ = x₃ · φ(D)`, the two formal group
law constructions agree: `embedDoubleLaurent W.formalGroupZW = W.formalGroupLaurent`. Both `y₃` and
`φ(D)` are units, so the two "fractions" `-φ(z₃')/φ(D)` and `-x₃/y₃` coincide.
@isnad1 id=eq.1h2v.s8.ca3173f2facf from=translated src=- shape=7de77a2c vocab=3fa42efc
-/
theorem embedDoubleLaurent_formalGroupZW_of_core
    (hcore : HahnSeries.embedDoubleLaurent W.formalThirdRoot * W.formalYThree
      = W.formalXThree * HahnSeries.embedDoubleLaurent W.formalGroupDen) :
    HahnSeries.embedDoubleLaurent W.formalGroupZW = W.formalGroupLaurent := by
  rw [W.embedDoubleLaurent_formalGroupZW_eq, formalGroupLaurent]
  set Z := HahnSeries.embedDoubleLaurent W.formalThirdRoot with hZ
  set D := HahnSeries.embedDoubleLaurent W.formalGroupDen with hD
  have hyc : W.formalYThree * Ring.inverse W.formalYThree = 1 := W.formalYThree_mul_inverse
  have hdc : D * Ring.inverse D = 1 :=
    Ring.mul_inverse_cancel _ W.isUnit_embedDoubleLaurent_formalGroupDen
  calc -Z * Ring.inverse D
      = -(Z * (W.formalYThree * Ring.inverse W.formalYThree)) * Ring.inverse D := by
        rw [hyc, mul_one]
    _ = -((Z * W.formalYThree) * Ring.inverse W.formalYThree) * Ring.inverse D := by ring
    _ = -((W.formalXThree * D) * Ring.inverse W.formalYThree) * Ring.inverse D := by rw [hcore]
    _ = -W.formalXThree * Ring.inverse W.formalYThree * (D * Ring.inverse D) := by ring
    _ = -W.formalXThree * Ring.inverse W.formalYThree := by rw [hdc, mul_one]

end WeierstrassCurve
