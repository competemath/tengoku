import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.SmoothRows

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
variable {H : Type uH} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

theorem half_sum_lipschitz {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {f g : H → ℝ} (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g) :
    LipschitzWith 1 (fun p => (f p+g p)/2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hf' := hf.dist_le_mul p q
  have hg' := hg.dist_le_mul p q
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at *
  have he : (f p+g p)/2-(f q+g q)/2 = ((f p-f q)+(g p-g q))/2 := by ring
  rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have := abs_add_le (f p-f q) (g p-g q)
  linarith

theorem half_sub_lipschitz {f g : H → ℝ} (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g) :
    LipschitzWith 1 (fun p => (f p-g p)/2) := by
  simpa only [sub_eq_add_neg,Pi.neg_apply] using half_sum_lipschitz hf hg.neg

theorem dyadicMean_lipschitz (u : ℕ → Smooth H) (hu : ∀ i, LipschitzWith 1 (u i).val) (n k : ℕ) :
    LipschitzWith 1 (dyadicMean u n k).val := by
  induction n generalizing k with
  | zero => exact hu k
  | succ n ih =>
    convert half_sum_lipschitz (ih k) (ih (k+2^n)) using 1
    ext p
    change (1/2:ℝ)*((dyadicMean u n k).val p+(dyadicMean u n (k+2^n)).val p) = _
    ring

theorem dyadicMean_zero_value {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (u : ℕ → Smooth H) (hu : ∀ i, (u i).val 0 = 0) (n k : ℕ) :
    (dyadicMean u n k).val 0 = 0 := by
  have he := map_dyadicMean (Smooth.eval (0:H)) u n k
  change (dyadicMean u n k).val 0 = dyadicMean (fun i => (u i).val 0) n k at he
  rw [he]
  exact le_antisymm (dyadicMean_le _ _ _ (fun i _ _ => (hu i).le))
    (le_dyadicMean _ _ _ (fun i _ _ => (hu i).ge))

def halfBlock (u : ℕ → Smooth H) (n k : ℕ) : Smooth H :=
  (1/2:ℝ) • (dyadicMean u n k-dyadicMean u n (k+2^n))

theorem halfBlock_lipschitz (u : ℕ → Smooth H) (hu : ∀ i, LipschitzWith 1 (u i).val) (n k : ℕ) :
    LipschitzWith 1 (halfBlock u n k).val := by
  convert half_sub_lipschitz (dyadicMean_lipschitz u hu n k) (dyadicMean_lipschitz u hu n (k+2^n)) using 1
  ext p
  change (1/2:ℝ)*((dyadicMean u n k).val p-(dyadicMean u n (k+2^n)).val p) = _
  ring

theorem halfBlock_zero_value (u : ℕ → Smooth H) (hu : ∀ i, (u i).val 0 = 0) (n k : ℕ) :
    (halfBlock u n k).val 0 = 0 := by
  change (1/2:ℝ)*((dyadicMean u n k).val 0-(dyadicMean u n (k+2^n)).val 0) = 0
  rw [dyadicMean_zero_value u hu,dyadicMean_zero_value u hu,sub_self,mul_zero]

theorem augmentedEnergy_smul (a : MolecularData H) (S : Finset H) (D c : ℝ) (f : Smooth H) :
    augmentedEnergy a S D (c • f) = c^2*augmentedEnergy a S D f := by
  simp only [augmentedEnergy,gradEnergy_smul,mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  change (D*(c*f.val p))^2 = c^2*(D*f.val p)^2
  ring

end LipschitzCounterexample.CompactWSC
end

end OAI
