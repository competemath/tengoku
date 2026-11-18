import Tengoku.XzMathieuSu2Counterexamples.XZMathieuSU2Counterexamples.XZWitness
import Tengoku.Seed.RingTheory.PowerSeries.Basic
import Tengoku.Seed.Data.Nat.Choose.Sum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open Polynomial
namespace XZMathieuSU2Counterexamples

/--
@isnad1 id=eq.1h1v.s6.e74395cd25f3 from=translated src=- shape=0e15ca0c vocab=f4f8f162
-/
theorem alternating_row (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n+1), (-1 : ℂ)^k * n.choose k) = 0 := by
  exact_mod_cast Int.alternating_sum_range_choose_of_ne (n := n) (by omega)

/--
@isnad1 id=eq.1h1v.s6.9078781f0607 from=translated src=- shape=0f38e996 vocab=625adcbd
-/
theorem alternating_partial_row (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range n, (-1 : ℂ)^k * n.choose k) = (-1 : ℂ)^(n-1) := by
  obtain ⟨m,rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
  have h := Int.alternating_sum_range_choose_eq_choose (n := m) (m := m)
  simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.add_sub_cancel] at h ⊢
  exact_mod_cast h

/-- Coefficientwise moment generating series; its degree-zero moment is included.-/
def momentSeries : PowerSeries ℂ := PowerSeries.mk (fun n => integral (basic^n))

/--
@isnad1 id=eq.0h0v.s3.5abf0f44341f from=translated src=- shape=2d527563 vocab=6041af59
-/
theorem momentSeries_eq_one : momentSeries = 1 := by
  ext n
  simp only [momentSeries, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  cases n with
  | zero => simp [integral]
  | succ n => simp [basic_pure (n+1) (by omega)]

/-- The exact radicand simplification in Remark 2.3.
@isnad1 id=eq.0h2v.s7.640f1d9c33c0 from=translated src=- shape=261c42ae vocab=a4e5d5bd
-/
theorem generating_radicand (x t : ℂ) :
    (1-t*(1-2*x))^2 + 4*t^2*x*(1-x) = (1-t)^2 + 4*t*x := by ring

/-- The cancellation identity displayed in Section 5.
@isnad1 id=and.1h1v.s8.5b341352867f from=translated src=- shape=2e6aa1cc vocab=fd81bb84
-/
theorem cancellation_mechanism (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n+1), (-1 : ℂ)^k * n.choose k) = 0 ∧
    (∑ k ∈ Finset.range n, (-1 : ℂ)^k * n.choose k) = (-1 : ℂ)^(n-1) ∧
    integral (basic^n) = 0 ∧ integral (LaurentPolynomial.T (-1) * basic^n) ≠ 0 :=
  ⟨alternating_row n hn, alternating_partial_row n hn, basic_pure n hn, basic_marked_ne_zero n hn⟩

end XZMathieuSU2Counterexamples
