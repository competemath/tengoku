/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Geometry.Points
import Tengoku.Seed.FieldTheory.Perfect

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integral Frobenius powers

The integral Frobenius powers `n ↦ Frob^n` of a perfect field of exponential characteristic `q`
(`frobeniusZPow`), and their basic calculus.

* Natural powers raise to `q^n` (`frobeniusZPow_natCast_apply`).
* Quotients of powers are powers (`frobeniusZPow_sub`, `frobeniusZPow_sub_apply_of_pow_eq`).
* In characteristic zero every power is the identity (`frobeniusZPow_eq_one_of_eq_one`).
* They act trivially on the point geometry (`point_frobeniusZPow`).
* The natural two-sided twist relation `a' = a^{q^s} ∨ a = a'^{q^s}` is the integral one
  (`exists_frobeniusZPow_iff`).

The Frobenius kernel theorem (`AclGeom.Reconstruct.Kernel`), the existing perfection action
(`AclGeom.Perfection.Lattice`) and the conditional Frobenius-link correctness
(`AclGeom.Interpretation.FrobEqCorrect`) use this definition. Separation of exponents on
transcendental elements stays in the kernel, which needs `AclGeom.Transfer.Descent`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.

**Status:** Frobenius calculus and trivial point action for the kernel theorem (#9, U1), and
the natural/integral twist comparison for the Frobenius link (#23).
-/

namespace AclGeom

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section FrobeniusPowers

variable (K) (q : ℕ) [ExpChar K q] [PerfectRing K q]

/-- The integral Frobenius powers `n ↦ Frob^n` of a perfect field of
exponential characteristic `q`, as a group power of `frobeniusEquiv` in the
automorphism group.  In characteristic zero (`q = 1`) every power is the
identity.-/
def frobeniusZPow (n : ℤ) : RingAut K :=
  (frobeniusEquiv K q : RingAut K) ^ n

variable {K}

/-- Natural Frobenius powers raise to the corresponding power of `q`.
@isnad1 id=eq.0h4v.s7.80fdccd85520 from=translated src=- shape=1dbf21cc vocab=f93664a0
-/
theorem frobeniusZPow_natCast_apply (n : ℕ) (x : K) :
    frobeniusZPow K q n x = x ^ q ^ n := by
  rw [frobeniusZPow, zpow_natCast]
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RingAut.mul_apply, ih, frobeniusEquiv_apply, frobenius_def,
      ← pow_mul, pow_succ']

/-- The quotient of two Frobenius powers, as an automorphism.
@isnad1 id=eq.0h4v.s8.f4139629410b from=translated src=- shape=b5085174 vocab=e11eb7c6
-/
theorem frobeniusZPow_sub (m n : ℤ) :
    frobeniusZPow K q (m - n) = (frobeniusZPow K q n)⁻¹ * frobeniusZPow K q m := by
  rw [frobeniusZPow, frobeniusZPow, frobeniusZPow, ← zpow_neg, ← zpow_add,
    neg_add_eq_sub]

/-- If `y^(q^v) = x^(q^u)` then `y` is the `(u - v)`-th Frobenius power of
`x`.
@isnad1 id=eq.1h6v.s7.1de151acd181 from=translated src=- shape=dde08f25 vocab=2b2dc460
-/
theorem frobeniusZPow_sub_apply_of_pow_eq {u v : ℕ} {x y : K}
    (h : y ^ q ^ v = x ^ q ^ u) :
    frobeniusZPow K q ((u : ℤ) - v) x = y := by
  have hv : frobeniusZPow K q v y = frobeniusZPow K q u x := by
    rw [frobeniusZPow_natCast_apply, frobeniusZPow_natCast_apply, h]
  rw [frobeniusZPow_sub, RingAut.mul_apply, ← hv]
  exact (frobeniusZPow K q v).symm_apply_apply y

/-- In exponential characteristic one (characteristic zero) every integral Frobenius power is
the identity (blueprint validation item TEST-1).
@isnad1 id=eq.1h3v.s7.d5f11efbd861 from=translated src=- shape=5284e762 vocab=1b6ffaf7
-/
theorem frobeniusZPow_eq_one_of_eq_one (hq : q = 1) (n : ℤ) : frobeniusZPow K q n = 1 := by
  subst hq
  have h1 : (frobeniusEquiv K 1 : RingAut K) = 1 := by
    ext z
    simp [frobeniusEquiv_apply, frobenius_def]
  rw [frobeniusZPow, h1, one_zpow]

end FrobeniusPowers

end

end AclGeom
