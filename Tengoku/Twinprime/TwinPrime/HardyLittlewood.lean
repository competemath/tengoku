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

/--
@isnad1 id=lt.0h1v.s3.680e0d23cc82 from=translated src=- shape=b9369acb vocab=e26a6823
-/
theorem twinConstantFactor_pos (p : ℕ) : 0 < twinConstantFactor p := by
  unfold twinConstantFactor
  split_ifs with h
  · have hp : (3 : ℝ) ≤ p := by exact_mod_cast h.2
    have h4 : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) h4
    linarith
  · exact one_pos

/--
@isnad1 id=le.0h1v.s3.d9c03b48f94d from=translated src=- shape=a311c14d vocab=26916029
-/
theorem twinConstantFactor_le_one (p : ℕ) : twinConstantFactor p ≤ 1 := by
  unfold twinConstantFactor
  split_ifs
  · have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith
  · exact le_rfl

/-- `twinConstantFactor p = 1 + twinConstantDefect p`.-/
def twinConstantDefect (p : ℕ) : ℝ := twinConstantFactor p - 1

/--
@isnad1 id=eq.0h1v.s4.548166a8a8ec from=translated src=- shape=9fc36aa0 vocab=6d08a4bf
-/
theorem twinConstantFactor_eq (p : ℕ) : twinConstantFactor p = 1 + twinConstantDefect p := by
  unfold twinConstantDefect; ring

/--
@isnad1 id=summable.0h0v.s3.cb2366780c1c from=translated src=- shape=ef4b497d vocab=b826dfda
-/
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

/--
@isnad1 id=summable.0h0v.s4.b59acc01d096 from=translated src=- shape=11722f18 vocab=fd4b413e
-/
theorem summable_log_twinConstantFactor :
    Summable (fun p : ℕ => Real.log (twinConstantFactor p)) := by
  have := Real.summable_log_one_add_of_summable summable_twinConstantDefect
  refine this.congr fun p => ?_
  rw [twinConstantFactor_eq]

/--
@isnad1 id=multipli.0h0v.s3.b146eaac4de3 from=translated src=- shape=ef4b497d vocab=2d7b758a
-/
theorem multipliable_twinConstantFactor : Multipliable twinConstantFactor :=
  Real.multipliable_of_summable_log twinConstantFactor_pos summable_log_twinConstantFactor

/-- **The twin prime constant** `C₂ = ∏_{p > 2} (1 - 1/(p-1)²) ≈ 0.6601618158…`.-/
def twinPrimeConstant : ℝ := ∏' p : ℕ, twinConstantFactor p

/--
@isnad1 id=eq.0h0v.s4.9ef71c74b20f from=translated src=- shape=ef9065e5 vocab=1cd1a7b7
-/
theorem twinPrimeConstant_eq_exp :
    twinPrimeConstant = Real.exp (∑' p : ℕ, Real.log (twinConstantFactor p)) := by
  unfold twinPrimeConstant
  rw [Real.rexp_tsum_eq_tprod twinConstantFactor_pos summable_log_twinConstantFactor]

/--
@isnad1 id=lt.0h0v.s3.1e3446d12500 from=translated src=- shape=ff3a10fc vocab=08223b2f
-/
theorem twinPrimeConstant_pos : 0 < twinPrimeConstant := by
  rw [twinPrimeConstant_eq_exp]
  exact Real.exp_pos _

/--
@isnad1 id=le.0h0v.s3.921da216349a from=translated src=- shape=ffdda526 vocab=eb9b5e9a
-/
theorem twinPrimeConstant_le_one : twinPrimeConstant ≤ 1 := by
  rw [twinPrimeConstant_eq_exp, Real.exp_le_one_iff]
  apply tsum_nonpos
  intro p
  exact Real.log_nonpos (twinConstantFactor_pos p).le (twinConstantFactor_le_one p)

/-- **The Hardy–Littlewood twin prime conjecture**: `π₂(x) ∼ 2 C₂ x / (log x)²`.  Open.-/
def HardyLittlewoodConjecture : Prop := HardyLittlewoodAsymptotic (2 * twinPrimeConstant)

/-- The Hardy–Littlewood conjecture implies the twin prime conjecture.
@isnad1 id=twinprim.1h0v.s1.0012417c48c1 from=translated src=- shape=1d48f1ac vocab=0977cb67
-/
theorem twinPrimeConjecture_of_hardyLittlewoodConjecture (h : HardyLittlewoodConjecture) :
    TwinPrimeConjecture :=
  twinPrimeConjecture_of_hardyLittlewood (by have := twinPrimeConstant_pos; linarith) h

end TwinPrime
