/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.GenuineLawIdentificationCore

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Base-change naturality of the genuine formal group law

For a ring homomorphism `f : R →+* S` and a Weierstrass curve `W : WeierstrassCurve R`, the genuine
`(z, w)` power-series formal group law commutes with base change:

`WeierstrassCurve.map_formalGroupZW` :
`MvPowerSeries.map f W.formalGroupZW = (W.map f).formalGroupZW`,

where `W.map f : WeierstrassCurve S` is the Mathlib base change of the curve (sends `aᵢ ↦ f W.aᵢ`)
and `MvPowerSeries.map f` is the coefficient-wise ring hom on `MvPowerSeries (Fin 2)`.

This is the base-change rung of the associativity programme (#263, route-2): associativity of
`formalGroupZW` is proved over the universal Weierstrass ring's fraction field (a `ℚ`-algebra) via
the formal logarithm, and then transferred to an arbitrary `CommRing R` along the base-change hom
`ℤ[a₁,…,a₆] → R`; that transfer consumes exactly this naturality lemma. It is independent of the
Laurent identification (#310/#314) and the invariant-differential crux `(★)`.

## Strategy

Push `MvPowerSeries.map f` down the construction tower
`formalW → λ, ν → A, B → z₃', D → F`. Every layer is a ring-hom image except `formalW` and the two
`invOfUnit` denominators:

* `map_formalW` : the Weierstrass expansion is natural because it is the *unique* order-`≥ 1` fixed
  point of `wOp` (`eq_formalW_of_wOp_fixed`, #294): `PowerSeries.map f W.formalW` is a fixed point
  of `(W.map f).wOp`, hence equals `(W.map f).formalW`.
* `map_invOfUnit` : `MvPowerSeries.map f` commutes with `invOfUnit _ 1` at constant coefficient `1`,
  by uniqueness of the inverse (mirrors `GenuineLawComm.rename_swap_invOfUnit`).
* everything else (`dividedDiff`, `toMvPowerSeries`, the Vieta polynomials) is pure functoriality.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

namespace WeierstrassCurve

open PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### Generic naturality: `map` through `dividedDiff`, `toMvPowerSeries` and `invOfUnit` -/

/-- `MvPowerSeries.map` commutes with the divided difference, coefficient by coefficient. -/
theorem map_dividedDiff (f : R →+* S) (g : R⟦X⟧) :
    MvPowerSeries.map f (PowerSeries.dividedDiff g)
      = PowerSeries.dividedDiff (PowerSeries.map f g) := by
  ext d
  rw [MvPowerSeries.coeff_map, PowerSeries.coeff_dividedDiff, PowerSeries.coeff_dividedDiff,
    PowerSeries.coeff_map]

/-- `MvPowerSeries.map` commutes with the one-variable embedding `g ↦ g(zᵢ)`. This is the
`map`/`rename` commutation, since `toMvPowerSeries i = rename (fun _ => i)` and
`PowerSeries.map = MvPowerSeries.map` on the one-variable ring. -/
theorem map_toMvPowerSeries (f : R →+* S) (g : R⟦X⟧) (i : Fin 2) :
    MvPowerSeries.map f (g.toMvPowerSeries i)
      = (PowerSeries.map f g).toMvPowerSeries i := by
  rw [PowerSeries.toMvPowerSeries_apply, PowerSeries.toMvPowerSeries_apply]
  exact (MvPowerSeries.rename_map (fun _ => i) f g).symm

/-- `MvPowerSeries.map f` commutes with `invOfUnit _ 1` when the constant coefficient is `1`
(mirrors `rename_swap_invOfUnit`, using that `map f` is a ring hom preserving the unit constant
coefficient). -/
theorem map_invOfUnit (f : R →+* S) (u : MvPowerSeries (Fin 2) R)
    (h : MvPowerSeries.constantCoeff u = 1) :
    MvPowerSeries.map f (MvPowerSeries.invOfUnit u 1)
      = MvPowerSeries.invOfUnit (MvPowerSeries.map f u) 1 := by
  set T := (MvPowerSeries.map f : MvPowerSeries (Fin 2) R →+* MvPowerSeries (Fin 2) S) with hT
  have hval : MvPowerSeries.constantCoeff u = ((1 : Rˣ) : R) := by rw [h, Units.val_one]
  have hsval : MvPowerSeries.constantCoeff (T u) = ((1 : Sˣ) : S) := by
    rw [hT, MvPowerSeries.constantCoeff_map, h, map_one, Units.val_one]
  have h1 : T u * T (MvPowerSeries.invOfUnit u 1) = 1 := by
    rw [hT, ← map_mul, MvPowerSeries.mul_invOfUnit u 1 hval, map_one]
  have h2 : MvPowerSeries.invOfUnit (T u) 1 * T u = 1 :=
    MvPowerSeries.invOfUnit_mul _ 1 hsval
  calc T (MvPowerSeries.invOfUnit u 1)
      = (MvPowerSeries.invOfUnit (T u) 1 * T u) * T (MvPowerSeries.invOfUnit u 1) := by
        rw [h2, one_mul]
    _ = MvPowerSeries.invOfUnit (T u) 1 * (T u * T (MvPowerSeries.invOfUnit u 1)) := by
        rw [mul_assoc]
    _ = MvPowerSeries.invOfUnit (T u) 1 := by rw [h1, mul_one]

variable (W : WeierstrassCurve R)

/-! ### Naturality of the Weierstrass expansion `w(z)` -/

/-- `PowerSeries.map f` commutes with the Weierstrass operator `wOp`. -/
theorem map_wOp (f : R →+* S) (v : R⟦X⟧) :
    PowerSeries.map f (W.wOp v) = (W.map f).wOp (PowerSeries.map f v) := by
  rw [wOp, wOp]
  simp only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X,
    map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]

/-- **Naturality of the Weierstrass expansion.** `PowerSeries.map f W.formalW = (W.map f).formalW`.
Proved via the uniqueness of `formalW` as the order-`≥ 1` fixed point of `wOp`. -/
theorem map_formalW (f : R →+* S) :
    PowerSeries.map f W.formalW = (W.map f).formalW := by
  have hcc : PowerSeries.constantCoeff W.formalW = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by norm_num) W.order_formalW)
  have horder : (1 : ℕ∞) ≤ (PowerSeries.map f W.formalW).order := by
    rw [PowerSeries.one_le_order_iff_constCoeff_eq_zero]
    change f (PowerSeries.constantCoeff W.formalW) = 0
    rw [hcc, map_zero]
  have hfix : PowerSeries.map f W.formalW = (W.map f).wOp (PowerSeries.map f W.formalW) := by
    conv_lhs => rw [W.formalW_eq]
    rw [W.map_wOp]
  exact (W.map f).eq_formalW_of_wOp_fixed horder hfix

/-! ### Naturality of the addition data -/

/-- Naturality of the slope `λ = Δ(w)`. -/
theorem map_formalWDividedDiff (f : R →+* S) :
    MvPowerSeries.map f W.formalWDividedDiff = (W.map f).formalWDividedDiff := by
  rw [formalWDividedDiff, formalWDividedDiff, map_dividedDiff, W.map_formalW]

/-- Naturality of the intercept `ν`. -/
theorem map_formalGroupNu (f : R →+* S) :
    MvPowerSeries.map f W.formalGroupNu = (W.map f).formalGroupNu := by
  rw [formalGroupNu, formalGroupNu, map_sub, map_mul, MvPowerSeries.map_X,
    W.map_formalWDividedDiff, map_toMvPowerSeries, W.map_formalW]

/-- Naturality of the cubic leading coefficient `A`. -/
theorem map_formalGroupLead (f : R →+* S) :
    MvPowerSeries.map f W.formalGroupLead = (W.map f).formalGroupLead := by
  rw [formalGroupLead, formalGroupLead]
  simp only [map_add, map_mul, map_pow, map_one, MvPowerSeries.map_C,
    W.map_formalWDividedDiff, map_a₂, map_a₄, map_a₆]

/-- Naturality of the cubic subleading coefficient `B`. -/
theorem map_formalGroupSub (f : R →+* S) :
    MvPowerSeries.map f W.formalGroupSub = (W.map f).formalGroupSub := by
  rw [formalGroupSub, formalGroupSub]
  simp only [map_add, map_mul, map_pow, map_ofNat, MvPowerSeries.map_C,
    W.map_formalWDividedDiff, W.map_formalGroupNu, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]

/-- Naturality of the Vieta third root `z₃'`. -/
theorem map_formalThirdRoot (f : R →+* S) :
    MvPowerSeries.map f W.formalThirdRoot = (W.map f).formalThirdRoot := by
  rw [formalThirdRoot, formalThirdRoot]
  simp only [map_sub, map_neg, map_mul, MvPowerSeries.map_X,
    map_invOfUnit f W.formalGroupLead W.constantCoeff_formalGroupLead,
    W.map_formalGroupSub, W.map_formalGroupLead]

/-! ### Constant coefficient of the negation denominator `D` (for `invOfUnit`) -/

private lemma cc_toMv_formalW_zero :
    MvPowerSeries.constantCoeff (W.formalW.toMvPowerSeries (0 : Fin 2)) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    show (0 : Fin 2 →₀ ℕ) = Finsupp.single (0 : Fin 2) 0 by simp,
    PowerSeries.coeff_toMvPowerSeries_single]
  exact PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by norm_num) W.order_formalW)

private lemma cc_formalGroupNu : MvPowerSeries.constantCoeff W.formalGroupNu = 0 := by
  rw [formalGroupNu, map_sub, map_mul, W.constantCoeff_formalWDividedDiff, W.cc_toMv_formalW_zero]
  simp

private lemma cc_formalGroupSub : MvPowerSeries.constantCoeff W.formalGroupSub = 0 := by
  rw [formalGroupSub]
  simp [map_add, map_mul, map_pow, MvPowerSeries.constantCoeff_C,
    W.constantCoeff_formalWDividedDiff, W.cc_formalGroupNu]

private lemma cc_formalThirdRoot : MvPowerSeries.constantCoeff W.formalThirdRoot = 0 := by
  rw [formalThirdRoot]
  simp [map_sub, map_neg, map_mul, MvPowerSeries.constantCoeff_X, W.cc_formalGroupSub]

/-- The negation denominator `D` has constant coefficient `1` (a unit). -/
theorem constantCoeff_formalGroupDen : MvPowerSeries.constantCoeff W.formalGroupDen = 1 := by
  rw [formalGroupDen]
  simp [map_sub, map_mul, map_add, map_one, MvPowerSeries.constantCoeff_C,
    W.cc_formalThirdRoot, W.constantCoeff_formalWDividedDiff, W.cc_formalGroupNu]

/-- Naturality of the negation denominator `D`. -/
theorem map_formalGroupDen (f : R →+* S) :
    MvPowerSeries.map f W.formalGroupDen = (W.map f).formalGroupDen := by
  rw [formalGroupDen, formalGroupDen]
  simp only [map_sub, map_mul, map_add, map_one, MvPowerSeries.map_C,
    W.map_formalThirdRoot, W.map_formalWDividedDiff, W.map_formalGroupNu, map_a₁, map_a₃]

/-! ### Base-change naturality of the formal group law -/

/-- **Base-change naturality of the genuine formal group law.**
`MvPowerSeries.map f W.formalGroupZW = (W.map f).formalGroupZW`. -/
theorem map_formalGroupZW (f : R →+* S) :
    MvPowerSeries.map f W.formalGroupZW = (W.map f).formalGroupZW := by
  rw [formalGroupZW, formalGroupZW, map_mul, map_neg,
    map_invOfUnit f W.formalGroupDen W.constantCoeff_formalGroupDen,
    W.map_formalThirdRoot, W.map_formalGroupDen]

end WeierstrassCurve
