import Tengoku.OpenaiMath.OAI.InformationTheory.BooleanNoise.InverseScalars
import Tengoku.OpenaiMath.OAI.InformationTheory.BooleanNoise.EndpointLimits
import Tengoku.OpenaiMath.OAI.InformationTheory.BooleanNoise.ArtanhBounds

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem psi_pos_of_pos {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) : 0 < psi u := by
  simpa only [psi_zero] using
    strictMonoOn_psi (show (0 : ℝ) ∈ Icc 0 1 by norm_num) ⟨hu.le, hu1⟩ hu

theorem rDeriv_psi {u : ℝ} (hu : u ∈ Ioo 0 1) :
    rDeriv (psi u) = 1 + u / ((1 - u ^ 2) * Real.artanh u) := by
  simp only [rDeriv, ite_eq_right (not_le.mpr (psi_pos_of_pos hu.1 hu.2.le)),
    psiInv_psi ⟨hu.1.le, hu.2.le⟩]

theorem rSecondDeriv_psi {u : ℝ} (hu : u ∈ Ioo 0 1) :
    rSecondDeriv (psi u) = ((1 + u ^ 2) * Real.artanh u - u) /
      ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3) := by
  simp only [rSecondDeriv, ite_eq_right (not_le.mpr (psi_pos_of_pos hu.1 hu.2.le)),
    psiInv_psi ⟨hu.1.le, hu.2.le⟩]

theorem continuousOn_rGap : ContinuousOn rGap (Ico 0 ell) :=
  continuousOn_r.sub (continuous_const.mul continuous_id).continuousOn

theorem hasDerivAt_rGap {s : ℝ} (hs : s ∈ Ioo 0 ell) :
    HasDerivAt rGap (rDeriv s - 2) s := by
  convert! (hasDerivAt_r hs).sub ((hasDerivAt_id s).const_mul 2) using 1
  simp

theorem L_ell_sub {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) :
    L (ell - s) = r s - 2 * s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [L]
  · have hx : 0 < ell - s ∧ ell - s < ell := by constructor <;> linarith
    simp only [L, ite_eq_left hx, rGap, sub_sub_cancel]

theorem L_entropy {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    L (entropy u) = r (psi u) - 2 * psi u :=
  L_ell_sub (psi_nonneg u) (psi_lt_ell hu)

theorem LDeriv_entropy {u : ℝ} (hu : u ∈ Ioo 0 1) :
    LDeriv (entropy u) = 2 - rDeriv (psi u) := by
  have hp := psi_pos_of_pos hu.1 hu.2.le
  have hpl := psi_lt_ell (show u ∈ Ioo (-1) 1 by constructor <;> linarith [hu.1, hu.2])
  have hx : 0 < entropy u ∧ entropy u < ell := by unfold entropy; constructor <;> linarith
  rw [LDeriv, ite_eq_left hx]
  simp only [entropy, sub_sub_cancel]

theorem rDeriv_ge_two {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) : 2 ≤ rDeriv s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  · have hu := psiInv_mem_Ioo ⟨hs, hsell⟩
    have hq : 0 < 1 - (psiInv s) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1 + psiInv s by linarith [hu.1])]
    have ht := Real.artanh_pos hu
    have hb := one_sub_sq_mul_artanh_le_self ⟨hu.1.le, hu.2⟩
    have hd : 1 ≤ psiInv s / ((1 - (psiInv s) ^ 2) * Real.artanh (psiInv s)) :=
      (le_div_iff₀ (mul_pos hq ht)).mpr (by simpa using hb)
    simp only [rDeriv, ite_eq_right (not_le.mpr hs)]
    linarith

theorem monotoneOn_rGap : MonotoneOn rGap (Ico 0 ell) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun s => rDeriv s - 2)
    (convex_Ico 0 ell) continuousOn_rGap ?_ ?_
  · intro s hs
    exact (hasDerivAt_rGap (by simpa using hs)).hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Ioo 0 ell := by simpa using hs
    exact sub_nonneg.mpr (rDeriv_ge_two hs'.1.le hs'.2)

theorem rGap_nonneg {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) : 0 ≤ rGap s := by
  simpa only [rGap_zero] using monotoneOn_rGap ⟨le_rfl, ell_pos⟩ ⟨hs, hsell⟩ hs

theorem tendsto_psiInv_zero_right : Tendsto psiInv (𝓝[>] 0) (𝓝[>] 0) := by
  have hc : Tendsto psiInv (𝓝[≥] 0) (𝓝 0) := by
    simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE ell_pos, psiInv_zero] using
      continuousOn_psiInv 0 ⟨le_rfl, ell_pos.le⟩
  refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self), ?_⟩
  filter_upwards [Ioo_mem_nhdsGT ell_pos] with s hs
  exact (psiInv_mem_Ioo hs).1

theorem tendsto_rDeriv_zero_right : Tendsto rDeriv (𝓝[>] 0) (𝓝 2) := by
  apply (tendsto_entropy_inverse_derivative_zero_right.comp tendsto_psiInv_zero_right).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_apply, rDeriv, ite_eq_right (not_le.mpr (show 0 < s from hs))]

theorem tendsto_rSecondDeriv_zero_right : Tendsto rSecondDeriv (𝓝[>] 0) (𝓝 (4 / 3 : ℝ)) := by
  apply (tendsto_entropy_inverse_second_derivative_zero_right.comp tendsto_psiInv_zero_right).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_apply, rSecondDeriv, ite_eq_right (not_le.mpr (show 0 < s from hs))]

end LeanBlast.CourtadeKumar

end

end OAI
