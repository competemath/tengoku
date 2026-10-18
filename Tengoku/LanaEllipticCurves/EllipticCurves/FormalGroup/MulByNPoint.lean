/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.MulByNLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The multiplication-by-`n` series computes the `ℕ`-action on `FormalGroup.Point`

Let `F` be a one-dimensional formal group law over a commutative ring `R`.  Mathlib equips the type
of points `F.Point σ = {f : MvPowerSeries σ R // PowerSeries.HasSubst f}` with an `AddMonoid`
structure whose scalar action `n • x` is built from the recursive `nsmulRec`.  On the other hand,
`EllipticCurves.FormalGroup.MulByN` builds the *multiplication-by-`n` series*
`[n](z) = F.mulByN n`.  This file proves that the two agree:

* `mulByN_subst_point : (n • x).val = [n](x)` — substituting the abstract series `[n](z)` at a point
  `x` reproduces the concrete scalar multiple `n • x`.

So `F.mulByN` genuinely *is* "multiplication by `n`" on points, and torsion questions `n • x = 0`
translate into vanishing of `[n]` evaluated at `x`.

The proof is a short induction: the load-bearing step is `fgAdd_subst_mv`, the generalisation of
`FormalGroup.fgAdd_subst` (from `MulByNLaws`) allowing the substituent to be an arbitrary
`MvPowerSeries σ R` (a point coordinate) rather than a one-variable series.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.2–IV.3.
-/

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R) {σ : Type*}

/-- **Substitution distributes over formal-group addition, into an arbitrary coordinate ring.**
For `a`, `b` of zero constant coefficient and `c : MvPowerSeries σ R` substitution-admissible,
`(a ⊕ b) ∘ c = F(a ∘ c, b ∘ c)`.  This is `FormalGroup.fgAdd_subst` with the target of the
substitution generalised from `PowerSeries R` to `MvPowerSeries σ R`, which is exactly what is
needed to substitute at a point coordinate `x.val`. -/
theorem fgAdd_subst_mv {a b : PowerSeries R} (c : MvPowerSeries σ R)
    (ha : PowerSeries.constantCoeff a = 0) (hb : PowerSeries.constantCoeff b = 0)
    (hc : PowerSeries.HasSubst c) :
    (F.fgAdd a b).subst c = F.toPowerSeries.subst ![a.subst c, b.subst c] := by
  unfold fgAdd
  rw [PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (hasSubst_cons ha hb) hc.const]
  congr 1
  funext s
  fin_cases s <;> simp [PowerSeries.subst_def]

/-- **The multiplication-by-`n` series computes the `ℕ`-action on points.**  For a point `x` of the
formal group, substituting `[n](z) = F.mulByN n` at `x` reproduces the `n`-fold sum `n • x`. -/
theorem mulByN_subst_point (n : ℕ) (x : F.Point σ) :
    ((n : ℕ) • x).val = (F.mulByN n).subst x.val := by
  induction n with
  | zero =>
    rw [zero_nsmul, mulByN_zero, ← PowerSeries.coe_substAlgHom x.prop, map_zero]
    rfl
  | succ n ih =>
    rw [succ_nsmul, add_apply, ih, mulByN_succ,
      F.fgAdd_subst_mv x.val (F.constantCoeff_mulByN n) PowerSeries.constantCoeff_X x.prop,
      PowerSeries.subst_X x.prop]

/-- A point is `n`-torsion iff the series `[n](z)` vanishes at its coordinate. -/
theorem nsmul_eq_zero_iff_mulByN_subst (n : ℕ) (x : F.Point σ) :
    (n : ℕ) • x = 0 ↔ (F.mulByN n).subst x.val = 0 := by
  rw [← F.mulByN_subst_point n x]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact Subtype.ext h

end FormalGroup
