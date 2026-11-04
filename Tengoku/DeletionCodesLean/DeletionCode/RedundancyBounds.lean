import Tengoku.DeletionCodesLean.DeletionCode.PaperParameters
import Tengoku.DeletionCodesLean.DeletionCode.WitnessCost

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms code_nonempty` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms redundancy_le_log_labels` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms logb_labelCount` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms paper_redundancy_bound` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Translate the actual finite-code cardinality bound into the manuscript's
redundancy bound. Positivity of the code size follows from that bound rather
than being assumed. The explicit label count gives the stated log-log term.
-/
namespace DeletionCode.RedundancyBounds

open HeaderRecovery

noncomputable def redundancy (n : ℕ) (C : Finset (Bits n)) : ℝ :=
  (n : ℝ) - Real.logb 2 (C.card : ℝ)

/--
@isnad1 id=lt.1h3v.s6.2bacef248e48 from=translated src=- shape=4f5b6588 vocab=a9fe6ab4
-/
theorem card_positive (n Q : ℕ) (C : Finset (Bits n))
    (hcard : 2 ^ n ≤ 8 * Q * C.card) : 0 < C.card := by
  have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  by_contra h
  have hz : C.card = 0 := by omega
  rw [hz, mul_zero] at hcard
  omega

/--
@isnad1 id=nonempty.1h3v.s5.6efe6b5e192c from=translated src=- shape=f4710149 vocab=85757424
-/
theorem code_nonempty (n Q : ℕ) (C : Finset (Bits n))
    (hcard : 2 ^ n ≤ 8 * Q * C.card) : C.Nonempty :=
  Finset.card_pos.mp (card_positive n Q C hcard)

/--
@isnad1 id=eq.0h0v.s4.cc7c5c1bf0e4 from=translated src=- shape=7226d0ee vocab=601a38d2
-/
theorem logb_eight : Real.logb 2 (8 : ℝ) = 3 := by
  calc
    Real.logb 2 (8 : ℝ) = Real.logb 2 ((2 : ℝ) ^ (3 : ℕ)) := by norm_num
    _ = 3 := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      norm_num

/-- The finite counting estimate gives redundancy at most log₂ Q + 3.
@isnad1 id=le.2h3v.s6.af5c1b34d56a from=translated src=- shape=8b6be69c vocab=72696df8
-/
theorem redundancy_le_log_labels (n Q : ℕ) (C : Finset (Bits n))
    (hQ : 1 ≤ Q) (hcard : 2 ^ n ≤ 8 * Q * C.card) :
    redundancy n C ≤ Real.logb 2 (Q : ℝ) + 3 := by
  have hc : (0 : ℝ) < C.card := by exact_mod_cast card_positive n Q C hcard
  have hq : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hreal : (2 : ℝ) ^ n ≤ 8 * (Q : ℝ) * (C.card : ℝ) := by exact_mod_cast hcard
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num : (0 : ℝ) < 2) n) hreal
  rw [Real.logb_mul (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hq)) (ne_of_gt hc),
    Real.logb_mul (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hq)] at hlog
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one, logb_eight] at hlog
  unfold redundancy
  linarith

/-- The paper's concrete integer label count, with its derived exponent b_t.-/
def labelCount (t n : ℕ) : ℕ :=
  8 * n ^ (2 * t - 1) * (PaperParameters.L n) ^ (WitnessCost.exponent t)

/--
@isnad1 id=lt.1h2v.s4.22073462ed7a from=translated src=- shape=676e8bff vocab=9d157cad
-/
theorem labelCount_positive (t n : ℕ) (hn : 1 ≤ n) : 0 < labelCount t n := by
  have hL : 0 < PaperParameters.L n := by have := PaperParameters.nine_le_L n; omega
  unfold labelCount
  exact mul_pos (mul_pos (by decide : 0 < 8) (pow_pos (by omega) _)) (pow_pos hL _)

/--
@isnad1 id=eq.1h2v.s6.9a5dd268f182 from=translated src=- shape=660ae21e vocab=726ffb41
-/
theorem logb_labelCount (t n : ℕ) (hn : 1 ≤ n) :
    Real.logb 2 (labelCount t n : ℝ) =
      3 + ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
        (WitnessCost.exponent t : ℝ) * Real.logb 2 (PaperParameters.L n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLpos : (0 : ℝ) < PaperParameters.L n := by
    exact_mod_cast (show 0 < PaperParameters.L n by have := PaperParameters.nine_le_L n; omega)
  have hnzero : (n : ℝ) ^ (2 * t - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hnpos)
  have hLzero : (PaperParameters.L n : ℝ) ^ (WitnessCost.exponent t) ≠ 0 :=
    pow_ne_zero _ (ne_of_gt hLpos)
  simp only [labelCount, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  rw [Real.logb_mul (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) hnzero) hLzero,
    Real.logb_mul (by norm_num : (8 : ℝ) ≠ 0) hnzero,
    logb_eight, Real.logb_pow, Real.logb_pow]

/-- Explicit redundancy bound for the actual parameter choice. Its only code
hypothesis is the established finite cardinality inequality.
@isnad1 id=le.2h3v.s7.31a0b572db9a from=translated src=- shape=6a08e64b vocab=00784832
-/
theorem paper_redundancy_bound (t n : ℕ) (C : Finset (Bits n)) (hn : 4 ≤ n)
    (hcard : 2 ^ n ≤ 8 * labelCount t n * C.card) :
    redundancy n C ≤
      ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
        ((6 * WitnessCost.exponent t + 6 : ℕ) : ℝ) *
          Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  have hn' : 1 ≤ n := by omega
  have hbase := redundancy_le_log_labels n (labelCount t n) C
    (labelCount_positive t n hn') hcard
  rw [logb_labelCount t n hn'] at hbase
  have hwindow := mul_le_mul_of_nonneg_left
    (PaperParameters.logb_L_le_six_logb_logb n hn)
    (Nat.cast_nonneg (WitnessCost.exponent t) : (0 : ℝ) ≤ (WitnessCost.exponent t : ℝ))
  have hloglog := PaperParameters.one_le_logb_logb n hn
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

end DeletionCode.RedundancyBounds
