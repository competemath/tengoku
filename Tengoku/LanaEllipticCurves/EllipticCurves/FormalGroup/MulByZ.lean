/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.MulByNPoint
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.PointGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The integer multiplication-by-`n` series and the `ℤ`-action on `FormalGroup.Point`

Let `F` be a one-dimensional formal group law over a commutative ring `R`.  The file
`EllipticCurves.FormalGroup.MulByN` builds the multiplication-by-`n` series `[n](z) = F.mulByN n`
for `n : ℕ`, and `EllipticCurves.FormalGroup.MulByNPoint` shows it computes the `ℕ`-action
`n • x` on Mathlib's group of points `F.Point σ`.  Meanwhile `EllipticCurves.FormalGroup.PointGroup`
equips `F.Point σ` with an `AddGroup` structure whose negation is substitution by the *formal
inverse* series `i(z) = F.formalInv`.

This file joins the two: it extends `[n]` to **all integers** by
`[-m](z) := i([m](z))` for `m ≥ 1`, giving `F.mulByZ : ℤ → PowerSeries R`, and proves the
integer version of the point bridge:

* `zsmul_val_eq_mulByZ_subst : (n • x).val = [n](x)` for every `n : ℤ` — the abstract series `[n]`
  substituted at a point `x` reproduces the concrete `zsmul` multiple `n • x`.

The negative case is `[-m] = i ∘ [m]`, matching `(-m) • x = -(m • x)` on points: the formal inverse
series realises negation, exactly as `neg_apply` does on `F.Point σ`.  Consequently torsion
questions `n • x = 0` (for `n : ℤ`) translate into vanishing of `[n]` evaluated at `x`.

No commutativity of `F` is needed: the `AddGroup` structure on `F.Point σ` (hence its `zsmul`) is
unconditional.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.2–IV.3.
-/

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R) {σ : Type*}

/-- The **integer multiplication-by-`n` series** `[n](z)` of the formal group `F`.  For `n ≥ 0` it
is the `ℕ`-series `F.mulByN n`; for `n = -(m+1) < 0` it is `i ∘ [m+1]`, the composite of the formal
inverse series with the positive series, realising `[-m] = -[m]`. -/
noncomputable def mulByZ (F : FormalGroup R) : ℤ → PowerSeries R
  | Int.ofNat n => F.mulByN n
  | Int.negSucc n => (F.formalInv).subst (F.mulByN (n + 1))

/--
@isnad1 id=eq.0h3v.s4.e129d294b8c1 from=translated src=- shape=b7f78dee vocab=2e399e01
-/
@[simp]
theorem mulByZ_ofNat (n : ℕ) : F.mulByZ (Int.ofNat n) = F.mulByN n := rfl

/--
@isnad1 id=eq.0h3v.s4.d43201d4a8cf from=translated src=- shape=307e489f vocab=378ca317
-/
@[simp]
theorem mulByZ_natCast (n : ℕ) : F.mulByZ (n : ℤ) = F.mulByN n := rfl

/--
@isnad1 id=eq.0h3v.s5.ca7f6cd9be8d from=translated src=- shape=34829f76 vocab=d36887a3
-/
theorem mulByZ_negSucc (n : ℕ) :
    F.mulByZ (Int.negSucc n) = (F.formalInv).subst (F.mulByN (n + 1)) := rfl

/-- The integer multiplication-by-`n` series is substitution-admissible.
@isnad1 id=hassubst.0h3v.s4.74f8fdaf9685 from=translated src=- shape=22a400fe vocab=6871cfc7
-/
theorem hasSubst_mulByZ (n : ℤ) : PowerSeries.HasSubst (F.mulByZ n) := by
  cases n with
  | ofNat n => exact F.hasSubst_mulByN n
  | negSucc n =>
    have h := (hasSubst_formalInv F).comp (F.hasSubst_mulByN (n + 1))
    rwa [PowerSeries.coe_substAlgHom (F.hasSubst_mulByN (n + 1))] at h

/-- `[n](z)` has zero constant coefficient, for every `n : ℤ`.
@isnad1 id=eq.0h3v.s6.16f9d39e475e from=translated src=- shape=d355250c vocab=73863692
-/
@[simp]
theorem constantCoeff_mulByZ (n : ℤ) : PowerSeries.constantCoeff (F.mulByZ n) = 0 := by
  cases n with
  | ofNat n => exact F.constantCoeff_mulByN n
  | negSucc n =>
    rw [mulByZ_negSucc]
    exact PowerSeries.constantCoeff_subst_eq_zero (F.constantCoeff_mulByN (n + 1))
      F.formalInv (constantCoeff_formalInv F)

/-- **The integer multiplication-by-`n` series computes the `ℤ`-action on points.**  For a point `x`
of the formal group, substituting `[n](z) = F.mulByZ n` at `x` reproduces the `zsmul` multiple
`n • x`, for every integer `n`.
@isnad1 id=eq.0h5v.s6.0e2cb53c33b7 from=translated src=- shape=db31aae0 vocab=0bce3bd8
-/
theorem zsmul_val_eq_mulByZ_subst (n : ℤ) (x : F.Point σ) :
    (n • x).val = (F.mulByZ n).subst x.val := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, natCast_zsmul]
    exact F.mulByN_subst_point n x
  | negSucc n =>
    rw [negSucc_zsmul, neg_apply, F.mulByN_subst_point (n + 1) x, mulByZ_negSucc]
    exact (PowerSeries.subst_comp_subst_apply (F.hasSubst_mulByN (n + 1)) x.prop _).symm

/-- A point is `n`-torsion (for `n : ℤ`) iff the series `[n](z)` vanishes at its coordinate.
@isnad1 id=iff.0h5v.s7.1266466085c8 from=translated src=- shape=2943d353 vocab=0bce3bd8
-/
theorem zsmul_eq_zero_iff_mulByZ_subst (n : ℤ) (x : F.Point σ) :
    n • x = 0 ↔ (F.mulByZ n).subst x.val = 0 := by
  rw [← F.zsmul_val_eq_mulByZ_subst n x]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact Subtype.ext h

end FormalGroup
