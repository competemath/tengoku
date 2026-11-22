import Tengoku.Leancert.LeanCert.Analysis.DBN.HeatFlow
import Tengoku.Seed.Analysis.Normed.Group.FunctionSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Continuity of the actual kernel and integrability of its even extension. -/
namespace LeanCert.Analysis.DBN
open Set Filter MeasureTheory
open scoped Topology

/--
@isnad1 id=continuo.0h0v.s3.85be1e23a07b from=translated src=- shape=e3d48bcb vocab=ec2c9cee
-/
theorem continuous_Phi : Continuous Phi := by
  rw [continuous_iff_continuousAt]
  intro x
  let A := kernelScale (x-1)
  have hA : 0 < A := kernelScale_pos _
  have hs : Summable (fun n : ℕ => 22*Real.exp (x+1) * Real.exp (-A*(n : ℝ))) :=
    (Real.summable_exp_nat_mul_of_ge (neg_neg_of_pos hA) (fun n => le_refl (n : ℝ))).mul_left _
  have hc : ContinuousOn Phi (Icc (x-1) (x+1)) := by
    apply continuousOn_tsum (fun n => (show Continuous (fun u => kernelTerm u n) by
      unfold kernelTerm; fun_prop).continuousOn) hs
    intro n u hu
    apply (kernelTerm_bound u n).trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu.2) (by norm_num)
    · apply Real.exp_le_exp.mpr
      have hscale : A ≤ kernelScale u := by
        unfold A kernelScale
        gcongr
        exact hu.1
      have hn : (n : ℝ) ≤ ((n : ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      nlinarith [mul_le_mul_of_nonneg_left hn hA.le,
        mul_nonneg (sub_nonneg.mpr hscale) (sq_nonneg ((n : ℝ)+1))]
    · positivity
    · positivity
  exact (hc x (by constructor <;> linarith)).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

/-- The even extension is used only as a real integration kernel. -/
noncomputable def evenPhi (u : ℝ) : ℝ := Phi |u|

/--
@isnad1 id=continuo.0h0v.s3.9794ba0d59b2 from=translated src=- shape=e3d48bcb vocab=f5c7294f
-/
theorem continuous_evenPhi : Continuous evenPhi := continuous_Phi.comp continuous_abs

/--
@isnad1 id=lt.0h1v.s3.54a186ec2c89 from=translated src=- shape=8a62b088 vocab=8490a070
-/
theorem evenPhi_pos (u : ℝ) : 0 < evenPhi u := Phi_pos (abs_nonneg u)

/--
@isnad1 id=le.0h1v.s5.bfce4ad935b0 from=translated src=- shape=bc7d4a86 vocab=9c31c043
-/
theorem evenPhi_bound (u : ℝ) :
    ‖evenPhi u‖ ≤ (44*Real.exp 1) * Real.exp (-u^2) := by
  have h := Phi_bound_nonneg (abs_nonneg u)
  apply h.trans
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 4*|u| by positivity)
  have hk := kernelScale_ge_exp (u := |u|)
  nlinarith [sq_abs u, abs_nonneg u, sq_nonneg u]

/--
@isnad1 id=integrab.0h0v.s4.a0eacdc1457e from=translated src=- shape=e14394ff vocab=ec5aa457
-/
theorem integrable_evenPhi : Integrable evenPhi := by
  apply ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
    (44*Real.exp 1)).mono' continuous_evenPhi.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun u => by simpa using evenPhi_bound u)

end LeanCert.Analysis.DBN
