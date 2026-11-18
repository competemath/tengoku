import Tengoku.TusnadyLean.Oscillation.AveragedComparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Summing the actual row gains gives the full oscillation drift. -/
namespace Oscillation
noncomputable section
open Finset
set_option maxHeartbeats 1000000

lemma gridMax_numerator_split_old {n : ℕ} (K V b m : ℕ) (hm : 0 < m)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) :
    (∑ c : Fin K, ∑ w : Fin (V * b), gridMax hm (blockValues χ p Y c.val w.val)) =
      ∑ c : Fin K, ∑ v : Fin V, ∑ l : Fin b,
        gridMax hm (blockValues χ p Y c.val (v.val * b + l.val)) := by
  apply sum_congr rfl
  intro c _
  simpa only [Nat.mul_comm] using
    (sum_fin_mul (K := V) (b := b) (fun w => gridMax hm (blockValues χ p Y c.val w)))

lemma gridMax_numerator_split_new {n : ℕ} (K V b m : ℕ) (hm : 0 < m)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) :
    (∑ w : Fin (K * b), ∑ v : Fin V, gridMax hm (blockValues χ p Y w.val v.val)) =
      ∑ c : Fin K, ∑ v : Fin V, ∑ k : Fin b,
        gridMax hm (blockValues χ p Y (b * c.val + k.val) v.val) := by
  rw [sum_fin_mul (fun w => ∑ v : Fin V, gridMax hm (blockValues χ p Y w v.val))]
  apply sum_congr rfl
  intro c _
  exact sum_comm

end
end Oscillation
