/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.DivisionBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# degree bounds for the error factors

This file supplies the degree estimates for the polynomials `f_n` appearing in
the coefficientwise Hensel iteration.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- if `deg f ≤ d`, `deg g ≤ m`, and `deg h ≤ d-m`, then
`deg(f-gh)≤d`.-/
theorem henselFactorization_error_natDegree_le
    {R : Type*} [CommRing R] {f g h : R[X]} {d m : ℕ}
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ m)
    (hh : h.natDegree ≤ d - m) (hmd : m ≤ d) :
    (f - g * h).natDegree ≤ d := by
  have hmul : (g * h).natDegree ≤ d := by
    have hmul' : (g * h).natDegree ≤ m + (d - m) :=
      Polynomial.natDegree_mul_le_of_le hg hh
    have hsum : m + (d - m) = d := by
      rw [Nat.add_comm, Nat.sub_add_cancel hmd]
    simpa [hsum] using hmul'
  have hsub := Polynomial.natDegree_sub_le_of_le hf hmul
  simpa using hsub

/-- if `P=C(a)Q` with `a≠0`, then a degree bound on `P`
is a degree bound on `Q`.-/
theorem henselFactorization_factor_natDegree_le_of_constant_mul_eq
    {R : Type*} [CommRing R] [NoZeroDivisors R] {a : R} (ha : a ≠ 0)
    {P Q : R[X]} {d : ℕ}
    (hP : P.natDegree ≤ d) (hfactor : P = Polynomial.C a * Q) :
    Q.natDegree ≤ d := by
  have hCQ : (Polynomial.C a * Q).natDegree ≤ d := by
    simpa [hfactor] using hP
  simpa [Polynomial.natDegree_C_mul (p := Q) (a0 := ha)] using hCQ

/-- degree bound for the next error factor `f_n` from the
current factorization error.-/
theorem henselFactorization_error_factor_natDegree_le
    {R : Type*} [CommRing R] [NoZeroDivisors R] {π : R} {n : ℕ}
    (hπn : π ^ n ≠ 0)
    {f g h fn : R[X]} {d m : ℕ}
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ m)
    (hh : h.natDegree ≤ d - m) (hmd : m ≤ d)
    (hfactor : f - g * h = Polynomial.C (π ^ n) * fn) :
    fn.natDegree ≤ d :=
  henselFactorization_factor_natDegree_le_of_constant_mul_eq
    (a := π ^ n) hπn
    (P := f - g * h) (Q := fn)
    (henselFactorization_error_natDegree_le hf hg hh hmd)
    hfactor

end Valuations
end AlgebraicNumberTheory

end
