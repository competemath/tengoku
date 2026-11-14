import Tengoku
import Tengoku.Twinprime.TwinPrime.Basic
import Tengoku.Twinprime.TwinPrime.Conditional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The twin prime constant and the Hardy–Littlewood conjecture

* `twinPrimeConstant` : `C₂ = ∏_{p > 2} (1 - 1/(p-1)²) ≈ 0.6601618158…`, defined as a convergent
  infinite product (`multipliable_twinConstantFactor`), with `0 < C₂ ≤ 1`.
* `HardyLittlewoodConjecture` : `π₂(x) ∼ 2 C₂ x / (log x)²` (open).
* `twinPrimeConjecture_of_hardyLittlewoodConjecture` : it implies the twin prime conjecture.

Numerically (see `data/twin_counts_1e13.tsv`) the ratio `π₂(x) / (2 C₂ ∫_2^x dt/(log t)²)`
equals `1.000004` at `x = 10^13`.
-/

noncomputable section

open Real Filter Topology

namespace TwinPrime

/-- The local factor `1 - 1/(p-1)²` at odd primes `p`, and `1` elsewhere.-/
def twinConstantFactor (p : ℕ) : ℝ :=
  if p.Prime ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

theorem twinConstantFactor_pos (p : ℕ) : 0 < twinConstantFactor p := by
  unfold twinConstantFactor
  split_ifs with h
  · have hp : (3 : ℝ) ≤ p := by exact_mod_cast h.2
    have h4 : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) h4
    linarith
  · exact one_pos

theorem twinConstantFactor_le_one (p : ℕ) : twinConstantFactor p ≤ 1 := by
  unfold twinConstantFactor
  split_ifs
  · have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith
  · exact le_rfl

/-- `twinConstantFactor p = 1 + twinConstantDefect p`.-/
def twinConstantDefect (p : ℕ) : ℝ := twinConstantFactor p - 1

theorem twinConstantFactor_eq (p : ℕ) : twinConstantFactor p = 1 + twinConstantDefect p := by
  unfold twinConstantDefect; ring

theorem summable_twinConstantDefect : Summable twinConstantDefect := by
  have hg : Summable (fun p : ℕ => 4 / ((p : ℝ) ^ 2)) := by
    have := (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
    have h4 := this.mul_left 4
    refine h4.congr fun p => ?_
    ring
  refine Summable.of_norm_bounded hg fun p => ?_
  unfold twinConstantDefect twinConstantFactor
  split_ifs with h
  · have hp : (3 : ℝ) ≤ p := by exact_mod_cast h.2
    rw [show (1 - 1 / ((p : ℝ) - 1) ^ 2 - 1) = -(1 / ((p : ℝ) - 1) ^ 2) by ring, norm_neg,
      Real.norm_of_nonneg (by positivity)]
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith
  · simp only [sub_self, norm_zero]
    positivity

theorem summable_log_twinConstantFactor :
    Summable (fun p : ℕ => Real.log (twinConstantFactor p)) := by
  have := Real.summable_log_one_add_of_summable summable_twinConstantDefect
  refine this.congr fun p => ?_
  rw [twinConstantFactor_eq]

theorem multipliable_twinConstantFactor : Multipliable twinConstantFactor :=
  Real.multipliable_of_summable_log twinConstantFactor_pos summable_log_twinConstantFactor

/-- **The twin prime constant** `C₂ = ∏_{p > 2} (1 - 1/(p-1)²) ≈ 0.6601618158…`.-/
def twinPrimeConstant : ℝ := ∏' p : ℕ, twinConstantFactor p

theorem twinPrimeConstant_eq_exp :
    twinPrimeConstant = Real.exp (∑' p : ℕ, Real.log (twinConstantFactor p)) := by
  unfold twinPrimeConstant
  rw [Real.rexp_tsum_eq_tprod twinConstantFactor_pos summable_log_twinConstantFactor]

theorem twinPrimeConstant_pos : 0 < twinPrimeConstant := by
  rw [twinPrimeConstant_eq_exp]
  exact Real.exp_pos _

theorem twinPrimeConstant_le_one : twinPrimeConstant ≤ 1 := by
  rw [twinPrimeConstant_eq_exp, Real.exp_le_one_iff]
  apply tsum_nonpos
  intro p
  exact Real.log_nonpos (twinConstantFactor_pos p).le (twinConstantFactor_le_one p)

/-- **The Hardy–Littlewood twin prime conjecture**: `π₂(x) ∼ 2 C₂ x / (log x)²`.  Open.-/
def HardyLittlewoodConjecture : Prop := HardyLittlewoodAsymptotic (2 * twinPrimeConstant)

/-- The Hardy–Littlewood conjecture implies the twin prime conjecture.-/
theorem twinPrimeConjecture_of_hardyLittlewoodConjecture (h : HardyLittlewoodConjecture) :
    TwinPrimeConjecture :=
  twinPrimeConjecture_of_hardyLittlewood (by have := twinPrimeConstant_pos; linarith) h

end TwinPrime
