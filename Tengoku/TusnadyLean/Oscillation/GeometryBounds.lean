import Tengoku.TusnadyLean.Oscillation.RowComparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Oscillation
noncomputable section
open Finset MeasureTheory

/--
@isnad1 id=le.0h7v.s5.71ce1c5e1656 from=translated src=- shape=98028130 vocab=ca66a2e1
-/
lemma interiorCount_le {n : ℕ} (b m : ℕ) (p Y : Fin n → ℕ) (c v : ℕ) :
    interiorCount b m p Y c v ≤ n := by
  unfold interiorCount interiorIndices
  exact (card_filter_le _ _).trans_eq (by simp)

/--
@isnad1 id=le.0h7v.s5.a92a5722a10d from=translated src=- shape=871ef69a vocab=e88c2d28
-/
lemma interiorMass_nonneg {n : ℕ} (K V b m : ℕ) (p Y : Fin n → ℕ) :
    0 ≤ interiorMass K V b m p Y := by
  unfold interiorMass
  exact sum_nonneg fun c _ => sum_nonneg fun v _ => Real.sqrt_nonneg _

/--
@isnad1 id=le.0h7v.s5.7abbcb9fa162 from=translated src=- shape=38738d29 vocab=a3423512
-/
lemma interiorMass_le_sqrt {n : ℕ} (K V b m : ℕ) (p Y : Fin n → ℕ) :
    interiorMass K V b m p Y ≤ (K * V : ℕ) * Real.sqrt n := by
  unfold interiorMass
  calc
    _ ≤ ∑ _c : Fin K, ∑ _v : Fin V, Real.sqrt n := by
      apply sum_le_sum
      intro c _
      apply sum_le_sum
      intro v _
      apply Real.sqrt_le_sqrt
      exact_mod_cast interiorCount_le b m p Y c.val v.val
    _ = _ := by simp; ring

/--
@isnad1 id=le.1h7v.s6.d7809aea2b3a from=translated src=- shape=50de1e36 vocab=c944aa9b
-/
lemma interiorMass_le_linear {n : ℕ} (hn : 1 ≤ n) (K V b m : ℕ) (p Y : Fin n → ℕ) :
    interiorMass K V b m p Y ≤ (K * V : ℕ) * (n : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact (interiorMass_le_sqrt K V b m p Y).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr hn')) (by positivity))

/--
@isnad1 id=le.1h6v.s5.fdbfdcf7c21d from=translated src=- shape=881cf7d3 vocab=813c743a
-/
lemma endpointValue_abs_le_card {n : ℕ} (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| ≤ 1)
    (p Y : Fin n → ℕ) (c y : ℕ) : |endpointValue χ p Y c y| ≤ n := by
  unfold endpointValue
  calc
    _ ≤ ∑ i, |χ i * (if Y i < y then 1 else 0) * endpointWeight (p i) c| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply sum_le_sum
      intro i _
      rw [abs_mul, abs_mul, abs_of_nonneg (endpointWeight_nonneg (p i) c)]
      split_ifs
      · norm_num only [abs_one, mul_one]
        exact (mul_le_mul_of_nonneg_right (hχ i) (endpointWeight_nonneg (p i) c)).trans
          (by simpa using endpointWeight_le_one (p i) c)
      · norm_num
    _ = _ := by simp

/--
@isnad1 id=le.4h7v.s6.fc3624cc480c from=translated src=- shape=04ebc652 vocab=449b4314
-/
lemma gridPotential_le_two_card {n K V m : ℕ} (hK : 0 < K) (hV : 0 < V)
    (hm : 0 < m) (χ : Fin n → ℝ) (hχ : ∀ i, |χ i| ≤ 1)
    (p Y : Fin n → ℕ) : gridPotential K V m hm χ p Y ≤ 2 * n := by
  apply gridPotential_le_of_values hK hV hm χ p Y n
  intro c v t
  exact endpointValue_abs_le_card χ hχ p Y c.val _

/--
@isnad1 id=measurab.0h5v.s6.385a1bfae03a from=translated src=- shape=1667d91e vocab=05441b37
-/
lemma interiorMass_measurable {n : ℕ} (K V b m : ℕ) :
    Measurable (fun pY : (Fin n → ℕ) × (Fin n → ℕ) =>
      interiorMass K V b m pY.1 pY.2) := measurable_of_countable _

/--
@isnad1 id=measurab.1h5v.s6.f183ba70bb88 from=translated src=- shape=e0ecc534 vocab=1a3fdefe
-/
lemma gridPotential_measurable {n : ℕ} (K V m : ℕ) (hm : 0 < m) (χ : Fin n → ℝ) :
    Measurable (fun pY : (Fin n → ℕ) × (Fin n → ℕ) =>
      gridPotential K V m hm χ pY.1 pY.2) := measurable_of_countable _

end
end Oscillation
