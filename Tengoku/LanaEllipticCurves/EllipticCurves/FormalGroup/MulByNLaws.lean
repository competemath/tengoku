/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.MulByN

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Additivity and composition laws of the multiplication-by-`n` series

Let `F` be a one-dimensional formal group law over a commutative ring `R`, with group operation
`z₁ ⊕ z₂ = F(z₁, z₂)`.  Building on the multiplication-by-`n` series `[n](z) = F.mulByN n`
constructed in `EllipticCurves.FormalGroup.MulByN`, this file proves the two structural laws that
make `n ↦ [n]` a genuine action of `ℕ` on the formal group:

* **Additivity** `mulByN_fgAdd : [m+n](z) = F([m](z), [n](z))` — so `[·]` is a formal-group
  homomorphism `(ℕ, +) → (Point, ⊕)`;
* **Composition / multiplicativity** `mulByN_subst_mulByN : [m] ∘ [n] = [mn]` (as substitution of
  power series) — so `[·]` respects multiplication.

Both are pure, abstract `FormalGroup` power-series identities, proved by induction entirely at the
`PowerSeries` level.  The load-bearing lemma is `fgAdd_subst`: substitution distributes over the
formal-group addition, which follows from associativity of substitution (`subst_comp_subst`).

These are the algebraic identities behind `[m] : Ê(𝔪) → Ê(𝔪)` being a group endomorphism and its
compatibility with the `[·]`-action, and behind the extension of `[m]` to integer `m` via the
additive inverse series.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.2–IV.3.
-/

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

/-- **Substitution distributes over formal-group addition.**  For `a`, `b` of zero constant
coefficient and `c` substitution-admissible, `(a ⊕ b) ∘ c = (a ∘ c) ⊕ (b ∘ c)`, i.e.
`F(a, b) ∘ c = F(a ∘ c, b ∘ c)`.  This is associativity of substitution
(`MvPowerSeries.subst_comp_subst_apply`) applied to the bivariate law `F`. -/
theorem fgAdd_subst {a b c : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0)
    (hb : PowerSeries.constantCoeff b = 0) (hc : PowerSeries.HasSubst c) :
    (F.fgAdd a b).subst c = F.fgAdd (a.subst c) (b.subst c) := by
  unfold fgAdd
  rw [PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (hasSubst_cons ha hb) hc.const]
  congr 1
  funext s
  fin_cases s <;> simp [PowerSeries.subst_def]

/-- **Additivity of the multiplication-by-`n` series.**  `[m+n](z) = F([m](z), [n](z))`, so
`n ↦ [n]` is a homomorphism from `(ℕ, +)` to the formal-group operation `⊕`. -/
theorem mulByN_fgAdd (m n : ℕ) :
    F.mulByN (m + n) = F.fgAdd (F.mulByN m) (F.mulByN n) := by
  induction n with
  | zero =>
    rw [Nat.add_zero, mulByN_zero]
    exact (F.add_zero (hasSubst_mulByN F m)).symm
  | succ k ih =>
    have hmk : m + (k + 1) = (m + k) + 1 := by ring
    rw [hmk, mulByN_succ, ih, mulByN_succ]
    exact F.assoc' (hasSubst_mulByN F m) (hasSubst_mulByN F k) PowerSeries.HasSubst.X'

/-- **Composition / multiplicativity of the multiplication-by-`n` series.**  `[m] ∘ [n] = [mn]`
(substitution of power series), so `n ↦ [n]` respects multiplication. -/
theorem mulByN_subst_mulByN (m n : ℕ) :
    (F.mulByN m).subst (F.mulByN n) = F.mulByN (m * n) := by
  induction m with
  | zero =>
    simp only [mulByN_zero, Nat.zero_mul]
    rw [← PowerSeries.coe_substAlgHom (hasSubst_mulByN F n), map_zero]
  | succ k ih =>
    rw [mulByN_succ, F.fgAdd_subst (F.constantCoeff_mulByN k) PowerSeries.constantCoeff_X
      (hasSubst_mulByN F n), ih, PowerSeries.subst_X (hasSubst_mulByN F n), ← F.mulByN_fgAdd]
    congr 1
    ring

end FormalGroup
