import Tengoku.TusnadyLean.Oscillation.BucketGeometry
import Tengoku.TusnadyLean.Oscillation.Tail

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Oscillation
open scoped BigOperators
open MeasureTheory Riesz Riesz.PointSets Riesz.Occupancy
noncomputable section

lemma interiorMass_nonneg' {n : ℕ} (K V b m : ℕ) (p Y : Fin n → ℕ) :
    0 ≤ interiorMass K V b m p Y := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

lemma interiorMass_le_count_root {n : ℕ} (K V b m : ℕ) (p Y : Fin n → ℕ) :
    interiorMass K V b m p Y ≤ (K*V:ℕ) * Real.sqrt n := by
  unfold interiorMass
  calc
    _ ≤ ∑ _c : Fin K, ∑ _v : Fin V, Real.sqrt n := by
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro v _
      apply Real.sqrt_le_sqrt
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset
        (fun i : Fin n => p i = c.val ∧ v.val*(b*m)+m ≤ Y i ∧
          Y i < v.val*(b*m)+(b-1)*m) Finset.univ)).trans_eq (Finset.card_fin n)
    _ = _ := by simp; ring

end
end Oscillation
