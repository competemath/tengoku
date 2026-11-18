import Tengoku.Seed.RingTheory.PowerSeries.Derivative
import Tengoku.Seed.RingTheory.PowerSeries.Inverse
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin
import Tengoku.Seed.Algebra.BigOperators.NatAntidiagonal
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms coeff_entry` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms coeff_derivative` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms entry_derivative` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms coeff_mul_range_left` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms coeff_mul_range_right` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms coeff_rank_derivative` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms equation_of_coefficients` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms isUnit_of_constant_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_inverse_of_constant_one` (it only prints; the queue checks the axioms of every declaration). -/

/-! Noncommutative matrix power series for the formal gauge equation.
The derivative is defined by its actual coefficients and is identified with
mathlib's scalar formal derivative in every matrix entry. Invertibility comes
from the unit constant coefficient, with explicit two-sided formal inverses. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace WasowPowerSeries
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extract one scalar power series from a matrix-coefficient power series.-/
def entry (F : PowerSeries (Matrix ι ι ℂ)) (i j : ι) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => (PowerSeries.coeff n F) i j)

/-- The coefficientwise formal derivative in the noncommutative matrix ring.-/
def derivative (F : PowerSeries (Matrix ι ι ℂ)) : PowerSeries (Matrix ι ι ℂ) :=
  PowerSeries.mk (fun n => ((n+1 : ℕ) : ℂ) • PowerSeries.coeff (n+1) F)

/--
@isnad1 id=eq.0h5v.s8.ba38066dd947 from=translated src=- shape=47d141f6 vocab=4ef2d1d7
-/
@[simp] theorem coeff_entry (F : PowerSeries (Matrix ι ι ℂ)) (i j : ι) (n : ℕ) :
    PowerSeries.coeff n (entry F i j) = (PowerSeries.coeff n F) i j :=
  PowerSeries.coeff_mk _ _

/--
@isnad1 id=eq.0h3v.s9.7b94b132f58b from=translated src=- shape=2101c035 vocab=57357ffa
-/
@[simp] theorem coeff_derivative (F : PowerSeries (Matrix ι ι ℂ)) (n : ℕ) :
    PowerSeries.coeff n (derivative F) = ((n+1 : ℕ) : ℂ) • PowerSeries.coeff (n+1) F :=
  PowerSeries.coeff_mk _ _

/-- The new matrix derivative is exactly the established scalar derivative in
all entries; it is not a hypothesis about formal differentiation.
@isnad1 id=eq.0h4v.s7.e70086b8563e from=translated src=- shape=42ea2108 vocab=bd1baa2d
-/
theorem entry_derivative (F : PowerSeries (Matrix ι ι ℂ)) (i j : ι) :
    entry (derivative F) i j = PowerSeries.derivative ℂ (entry F i j) := by
  apply PowerSeries.ext
  intro n
  simp [PowerSeries.coeff_derivative, Matrix.smul_apply, mul_comm]

/--
@isnad1 id=eq.0h4v.s8.b8f865697a56 from=translated src=- shape=0cd570a2 vocab=2383e521
-/
theorem coeff_mul_range_left {R : Type*} [Semiring R]
    (F G : PowerSeries R) (k : ℕ) :
    PowerSeries.coeff k (F*G) = ∑ i ∈ Finset.range (k+1),
      PowerSeries.coeff i F * PowerSeries.coeff (k-i) G := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _

/--
@isnad1 id=eq.0h4v.s8.206368126555 from=translated src=- shape=0d06232b vocab=2383e521
-/
theorem coeff_mul_range_right {R : Type*} [Semiring R]
    (F G : PowerSeries R) (k : ℕ) :
    PowerSeries.coeff k (F*G) = ∑ i ∈ Finset.range (k+1),
      PowerSeries.coeff (k-i) F * PowerSeries.coeff i G := by
  rw [PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _

/-- The rank convention is `q = q_book + 1`. Changing from `z` to `t = 1/z`
turns Wasow's equation into `AP-PB = -t^(q+1) P_t'`.
@isnad1 id=eq.0h4v.s9.ee802ebff804 from=translated src=- shape=30f40c1a vocab=15918d74
-/
theorem coeff_rank_derivative (F : PowerSeries (Matrix ι ι ℂ)) (q k : ℕ) :
    PowerSeries.coeff k (-((PowerSeries.X : PowerSeries (Matrix ι ι ℂ)) ^ (q+1) * derivative F)) =
      -(if q < k then ((k-q : ℕ) : ℂ) • PowerSeries.coeff (k-q) F else 0) := by
  rw [map_neg, PowerSeries.coeff_X_pow_mul']
  by_cases h : q < k
  · rw [ite_eq_left (by omega), ite_eq_left h, coeff_derivative]
    have heq : k - (q+1) + 1 = k-q := by omega
    rw [heq]
  · rw [ite_eq_right (by omega), ite_eq_right h]

/-- Coefficient identities imply the actual noncommutative formal equation.
@isnad1 id=eq.1h5v.s9.8135fa30db49 from=translated src=- shape=f0009626 vocab=e62dca05
-/
theorem equation_of_coefficients (A P B : ℕ → Matrix ι ι ℂ) (q : ℕ)
    (h : ∀ k, (∑ i ∈ Finset.range (k+1), (A (k-i) * P i - P i * B (k-i))) =
      -(if q < k then ((k-q : ℕ) : ℂ) • P (k-q) else 0)) :
    PowerSeries.mk A * PowerSeries.mk P - PowerSeries.mk P * PowerSeries.mk B =
      -((PowerSeries.X : PowerSeries (Matrix ι ι ℂ)) ^ (q+1) * derivative (PowerSeries.mk P)) := by
  apply PowerSeries.ext
  intro k
  rw [map_sub, coeff_mul_range_right, coeff_mul_range_left, coeff_rank_derivative]
  simpa only [PowerSeries.coeff_mk, ← Finset.sum_sub_distrib] using h k

/-- A matrix series with identity constant term is a genuine unit.
@isnad1 id=isunit.1h2v.s6.499525178643 from=translated src=- shape=c050aa54 vocab=673434a8
-/
theorem isUnit_of_constant_one (P : ℕ → Matrix ι ι ℂ) (hP : P 0 = 1) :
    IsUnit (PowerSeries.mk P) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hP]
  exact isUnit_one

/-- An explicit inverse series has both inverse identities.
@isnad1 id=ex.1h2v.s7.7be47826bdf4 from=translated src=- shape=76403a30 vocab=c97d3c00
-/
theorem exists_inverse_of_constant_one (P : ℕ → Matrix ι ι ℂ) (hP : P 0 = 1) :
    ∃ S : PowerSeries (Matrix ι ι ℂ),
      S * PowerSeries.mk P = 1 ∧ PowerSeries.mk P * S = 1 := by
  refine ⟨PowerSeries.invOfUnit (PowerSeries.mk P) 1, ?_, ?_⟩
  · apply PowerSeries.invOfUnit_mul
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hP]
    rfl
  · apply PowerSeries.mul_invOfUnit
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hP]
    rfl

end WasowPowerSeries
