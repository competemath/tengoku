import Tengoku.DeletionCodesLean.DeletionCode.FinitePairUnion
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms short_records_bound` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms combined_records_bound` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Explicit constants for counting short and nonseparated alignment records.
Four edit tags over-encode the orientation and inserted bit. This changes
only the constant depending on t, not the essential power n^(2*t-1).
-/
namespace DeletionCode.ExceptionalCountArithmetic

open scoped BigOperators

/-- A deliberately generous constant, depending only on the edit radius.-/
def exceptionalConstant (t : ℕ) : ℕ :=
  (t + 8 * (2 * t) * (2 * t + 2)) * 4 ^ (2 * t)

/--
@isnad1 id=lt.1h1v.s4.f49f2ed54d65 from=translated src=- shape=a8dc2df9 vocab=1746f67f
-/
theorem exceptionalConstant_pos {t : ℕ} (ht : 1 ≤ t) :
    0 < exceptionalConstant t := by
  unfold exceptionalConstant
  apply Nat.mul_pos
  · omega
  · positivity

/-- All smaller balanced edit counts contribute a lower power of n. Including
the unused zero-edit record is harmless and simplifies the upper bound.
@isnad1 id=le.1h2v.s7.2d9106610540 from=translated src=- shape=ce2803d7 vocab=e6f1a7a1
-/
theorem short_records_bound (n t : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ Finset.range t, n ^ (2 * d) * 4 ^ (2 * d)) ≤
      t * 4 ^ (2 * t) * n ^ (2 * t - 1) := by
  calc
    _ ≤ ∑ _d ∈ Finset.range t, 4 ^ (2 * t) * n ^ (2 * t - 1) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdt : d < t := Finset.mem_range.mp hd
      have he : 2 * d ≤ 2 * t - 1 := by omega
      have hn' : n ^ (2 * d) ≤ n ^ (2 * t - 1) := pow_le_pow_right₀ hn he
      have hfour : (4 : ℕ) ^ (2 * d) ≤ 4 ^ (2 * t) :=
        pow_le_pow_right₀ (by decide) (by omega)
      calc
        _ ≤ n ^ (2 * t - 1) * 4 ^ (2 * t) := Nat.mul_le_mul hn' hfour
        _ = _ := Nat.mul_comm _ _
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

/-- The close-anchor saving and the short-trace bound combine into one
constant times L*n^(2*t-1).
@isnad1 id=le.2h3v.s8.e7d085e0ed1e from=translated src=- shape=12a8a736 vocab=43d19d56
-/
theorem combined_records_bound (n t L : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    (∑ d ∈ Finset.range t, n ^ (2 * d) * 4 ^ (2 * d)) +
        (2 * t) * (2 * t + 2) * (2 * (4 * L)) * n ^ (2 * t - 1) * 4 ^ (2 * t) ≤
      exceptionalConstant t * L * n ^ (2 * t - 1) := by
  have hs := short_records_bound n t hn
  have hsL : t * 4 ^ (2 * t) * n ^ (2 * t - 1) ≤
      t * 4 ^ (2 * t) * n ^ (2 * t - 1) * L :=
    Nat.le_mul_of_pos_right _ hL
  calc
    _ ≤ t * 4 ^ (2 * t) * n ^ (2 * t - 1) * L +
        (2 * t) * (2 * t + 2) * (2 * (4 * L)) * n ^ (2 * t - 1) * 4 ^ (2 * t) :=
      Nat.add_le_add_right (hs.trans hsL) _
    _ = _ := by unfold exceptionalConstant; ring

end DeletionCode.ExceptionalCountArithmetic
