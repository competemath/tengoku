import Tengoku.OpenaiMath.OAI.Analysis.BackwardIntertwiners.WeightSeparation

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

abbrev Fiber := lp (fun _ : ℤ => ℂ) 2

def coordinateTail (h : ℤ) : Submodule ℂ Fiber where
  carrier := {v | ∀ j : ℤ, j < h → v j = 0}
  zero_mem' := by simp
  add_mem' := by intro v z hv hz j hj; simp [hv j hj, hz j hj]
  smul_mem' := by intro a v hv j hj; simp [hv j hj]

lemma fiber_exists_coordinate {v : Fiber} (hv : v ≠ 0) : ∃ j : ℤ, v j ≠ 0 := by
  by_contra! h
  apply hv
  ext j
  exact h j

lemma weighted_shift_pow {w : ℤ → ℝ} (hw : ∀ j, 0 < w j)
    {T : Fiber →L[ℂ] Fiber}
    (hT : ∀ v j, T v j = (w j / w (j-1) : ℂ) * v (j-1))
    (n : ℕ) (v : Fiber) (j : ℤ) :
    (T^n) v j = (w j / w (j-(n:ℤ)) : ℂ) * v (j-(n:ℤ)) := by
  have hwC (k : ℤ) : (w k:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hw k))
  induction n generalizing j with
  | zero => simp [hwC]
  | succ n ih =>
    rw [pow_succ']
    change T ((T^n) v) j = _
    rw [hT, ih]
    have hi : j-1-(n:ℤ) = j-((n+1:ℕ):ℤ) := by omega
    rw [hi]
    field_simp [hwC]

lemma SupportSeparation.strict_order {w : ℤ → ℝ} (hsep : SupportSeparation w)
    {b c : ℤ → ℂ} (hbn : ∃ j, b j ≠ 0) (hcn : ∃ j, c j ≠ 0)
    {B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hb : ∀ j, ‖b j‖ ≤ B*w j) (hc : ∀ j, ‖c j‖*w j ≤ C)
    (hz : ∀ r : ℕ, (∑' j : ℤ, b j * c (j-r)) = 0)
    {i j : ℤ} (hbi : b i ≠ 0) (hcj : c j ≠ 0) : i < j := by
  obtain ⟨t, h, hbt, hch, hbmax, hcmin, hth⟩ :=
    hsep.of_bounded hbn hcn hB hC hb hc (fun r _ => hz r)
  have hit : i ≤ t := by by_contra! hh; exact hbi (hbmax i hh)
  have hhj : h ≤ j := by by_contra! hh; exact hcj (hcmin j hh)
  have hstrict : t < h := by
    by_contra! hht
    have he : t = h := le_antisymm hth hht
    have hsingle : (∑' k : ℤ, b k*c k) = b t*c h := by
      rw [tsum_eq_single t, he]
      intro k hk
      by_cases hkt : t < k
      · simp [hbmax k hkt]
      · rw [hcmin k (by omega), mul_zero]
    have hzero := hz 0
    simp only [Nat.cast_zero, sub_zero] at hzero
    rw [hsingle] at hzero
    exact (mul_ne_zero hbt hch) hzero
  omega

end
end BackwardIntertwiners

end OAI
