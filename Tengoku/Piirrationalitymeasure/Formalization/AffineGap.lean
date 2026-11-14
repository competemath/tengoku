import Tengoku.Piirrationalitymeasure.Formalization.FloorGerm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Positive affine gaps dominate a quadratic sampling distance near zero. -/

namespace PiIrrationality

open Filter Set
open scoped Topology

theorem affine_gt_sq_eventually_of_pos {a b : ℝ}
    (hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < a + s * b) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, s ^ 2 < a + s * b := by
  have hlim : Tendsto (fun s : ℝ => a + s * b) (𝓝[>] 0) (𝓝 a) := by
    have hc : ContinuousAt (fun s : ℝ => a + s * b) 0 := by fun_prop
    simpa only [zero_mul, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have ha : 0 ≤ a := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (hpos.mono fun _ hs => hs.le)
  rcases ha.eq_or_lt with ha | ha
  · subst a
    have hspos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
    obtain ⟨s, hs, hsb⟩ := (hspos.and hpos).exists
    have hb : 0 < b := pos_of_mul_pos_right (by simpa only [zero_add] using hsb) hs.le
    have hneg : quadraticPerturbationNegative (-b) 1 := Or.inl (neg_neg_of_pos hb)
    filter_upwards [quadratic_perturbation_eventually_neg hneg] with t ht
    nlinarith only [ht]
  · have hc : ContinuousAt (fun s : ℝ => a + s * b - s ^ 2) 0 := by fun_prop
    have he := hc.eventually_const_lt (by simpa using ha : 0 < a + 0 * b - 0 ^ 2)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with s hs
    linarith only [hs]

end PiIrrationality
