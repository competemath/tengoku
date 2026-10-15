/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import Tengoku.LeanPool.LeanPool.PentagonalNumberTheoremAnalytic.QSeries.FPS

/-!
# FPS Euler Second Identity

We prove the Euler second identity purely algebraically in the formal power series ring:
  `qPochhammerInf(-a) = Σ_{n≥0} X^{C(n,2)} · aⁿ · (qPochhammer(X, n))⁻¹`

The proof uses the finite q-binomial theorem (which holds in any commutative ring)
and takes the limit in the pi topology. The key step is showing that the
Gaussian binomial coefficient `qBinom(N, k, X)` converges to `(qPochhammer(X, k))⁻¹`
as N → ∞.
-/

@[expose] public section

noncomputable section

open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset

namespace QSeries.FormalPowerSeries

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- The constant term of `qPochhammer X n` is 1.
@isnad1 id=eq.0h2v.s6.2e833671165d from=translated src=- shape=9f35bdc9 vocab=2b396573
-/
theorem constantCoeff_qPochhammer_X (n : ℕ) :
    constantCoeff (qPochhammer (X : R⟦X⟧) n) = 1 := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih =>
    rw [qPochhammer_succ]
    simp [map_mul, map_sub, ih]

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- `qPochhammer X n` is a unit in `R⟦X⟧` (its constant term is 1).
@isnad1 id=isunit.0h2v.s5.79aedc73c8bd from=translated src=- shape=e81faeda vocab=2ec834d7
-/
theorem isUnit_qPochhammer_X (n : ℕ) : IsUnit (qPochhammer (X : R⟦X⟧) n) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_qPochhammer_X]
  exact isUnit_one

/-- `qPochhammerInf a = qPochhammer a n · qPochhammerInf (a · X^n)`.
@isnad1 id=eq.0h3v.s6.ba09feced9b2 from=translated src=- shape=361c7b20 vocab=21d21004
-/
theorem qPochhammerInf_eq_qPochhammer_mul (a : R⟦X⟧) (n : ℕ) :
    qPochhammerInf a = qPochhammer a n * qPochhammerInf (a * X ^ n) := by
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih =>
    rw [ih, qPochhammer_succ, mul_assoc]
    congr 1
    rw [qPochhammerInf_eq_one_sub_mul]
    ring_nf

/-- `qPochhammerInf X = qPochhammer X n · qPochhammerInf (X * X^n)`.
@isnad1 id=eq.0h2v.s6.cfca69dbc389 from=translated src=- shape=4b74fa49 vocab=21d21004
-/
theorem qPochhammerInf_X_eq_qPochhammer_mul (n : ℕ) :
    qPochhammerInf (X : R⟦X⟧) = qPochhammer X n * qPochhammerInf (X * X ^ n) :=
  qPochhammerInf_eq_qPochhammer_mul X n

end QSeries.FormalPowerSeries

end
