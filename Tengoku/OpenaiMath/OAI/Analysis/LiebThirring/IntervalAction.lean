import Tengoku.OpenaiMath.OAI.Analysis.LiebThirring.ConnectingPath

namespace OAI

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
open Set Metric
open scoped NNReal
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof MatrixFlow MeasureTheory Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

def actionDensity (σ : ℝ) (k a v : Fin N → ℝ) : ℝ :=
  (∑ i, v i^2) + (∑ i, k i^2*a i^2) - (∑ i, a i^2) ^ (1+1/σ)

lemma actionDensity_continuous {σ : ℝ} (hσ : 0 < σ) (k : Fin N → ℝ) :
    Continuous (fun z : (Fin N → ℝ) × (Fin N → ℝ) ↦ actionDensity σ k z.1 z.2) := by
  unfold actionDensity
  apply Continuous.sub
  · fun_prop
  · exact (by fun_prop : Continuous (fun z : (Fin N → ℝ) × (Fin N → ℝ) ↦ ∑ i, z.1 i^2)).rpow_const
      (fun _ ↦ Or.inr (by positivity))

lemma penalized_action_integral {σ δ ε l r η : ℝ}
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ) (hε : 0 < ε) (hlr : l ≤ r)
    (k : Fin N → ℝ) (a v : ℝ → Fin N → ℝ)
    (ha : ContinuousOn a (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (had : ∀ t ∈ Ioo l r, ∀ i, HasDerivAt (fun t ↦ a t i) (v t i) t)
    (hal : a l = 0) (har : a r = 0) (X : ℝ → Sym N)
    (hXi : X l = symDiag k) (hXf : X r = -symDiag k)
    (hXd : ∀ t ∈ Icc l r, HasDerivWithinAt X
      (ε⁻¹ • (sourceField σ δ hσ₁ hδ k (X t) - symOuter (a t))) (Icc l r) t)
    (hp : ∀ t ∈ Icc l r, actionDefect σ k (X t,a t) - constraintDefect σ δ k (X t,a t)/ε ≤ η) :
    fieldPrimitive σ δ k (-diagonal k) - fieldPrimitive σ δ k (diagonal k) ≤
      (∫ t in l..r, actionDensity σ k (a t) (v t)) + (r-l)*η := by
  have hX := HasDerivWithinAt.continuousOn hXd
  have hXval := continuous_subtype_val.comp_continuousOn hX
  let G := fun t ↦ fieldPrimitive σ δ k (X t) + ∑ i, a t i * ((X t).val *ᵥ a t) i
  let G' := fun t ↦ 2*(∑ i, v t i * ((X t).val *ᵥ a t) i) - constraintDefect σ δ k (X t,a t)/ε
  have hJ : Continuous (fun A : Sym N ↦ fieldPrimitive σ δ k A) :=
    continuous_iff_continuousAt.mpr (fun A ↦ (fieldPrimitive_hasFDerivAt hσ₁ hδ k A).continuousAt)
  have hMV : ContinuousOn (fun t ↦ (X t).val *ᵥ a t) (Icc l r) :=
    (show Continuous (fun z : Matrix (Fin N) (Fin N) ℝ × (Fin N → ℝ) ↦ z.1 *ᵥ z.2)
      by fun_prop).comp_continuousOn (hXval.prodMk ha)
  have hdot : Continuous (fun z : (Fin N → ℝ) × (Fin N → ℝ) ↦ ∑ i, z.1 i * z.2 i) := by
    fun_prop
  have hG : ContinuousOn G (Icc l r) :=
    (hJ.comp_continuousOn hX).add (hdot.comp_continuousOn (ha.prodMk hMV))
  have hG' : ContinuousOn G' (Icc l r) :=
    ((hdot.comp_continuousOn (hv.prodMk hMV)).const_mul 2).sub
      (((constraintDefect_continuous hσ₁ hδ k).comp_continuousOn (hX.prodMk ha)).div_const ε)
  have hd (t : ℝ) (ht : t ∈ Ioo l r) : HasDerivAt G (G' t) t := by
    apply action_ode_identity hσ₁ hδ hε k (had t ht)
      ((hXd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    change ε • (ε⁻¹ • (matrixField σ δ k (X t).val - vecMulVec (a t) (a t))) = _
    rw [smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr hG hd
    (hG'.intervalIntegrable_of_Icc (μ := volume) hlr)
  have hlim : G r - G l = fieldPrimitive σ δ k (-diagonal k) - fieldPrimitive σ δ k (diagonal k) := by
    simp only [G,har,hal,hXi,hXf,Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero]
    rfl
  rw [hlim] at hi
  have hec := (actionDensity_continuous hσ₀ k).comp_continuousOn (ha.prodMk hv)
  have hbound := intervalIntegral.integral_mono_on hlr
    (hG'.intervalIntegrable_of_Icc (μ := volume) hlr)
    ((hec.add (continuousOn_const (c := η))).intervalIntegrable_of_Icc (μ := volume) hlr)
    (fun t ht ↦ (action_penalty_pointwise k (X t) (a t) (v t)).trans
      (add_le_add (le_refl (actionDensity σ k (a t) (v t))) (hp t ht)))
  change (∫ t in l..r, G' t) ≤ (∫ t in l..r, actionDensity σ k (a t) (v t) + η) at hbound
  change ContinuousOn (fun t ↦ actionDensity σ k (a t) (v t)) (Icc l r) at hec
  rw [hi,intervalIntegral.integral_add (hec.intervalIntegrable_of_Icc (μ := volume) hlr)
    (intervalIntegrable_const),intervalIntegral.integral_const,smul_eq_mul] at hbound
  exact hbound

end SharpLiebThirring.ActionProof
namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof MatrixFlow MeasureTheory Set Filter ContinuationGap
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

lemma compact_amplitudes {l r R : ℝ} {u : ℝ → Fin N → ℝ}
    (hu : ContinuousOn u (Icc l r)) :
    IsCompact ((fun z : LowerSpace N × ℝ ↦ z.1.val *ᵥ u z.2) ''
      ({C : LowerSpace N | ∀ i j, |C.val i j| ≤ R} ×ˢ Icc l r)) := by
  apply ((compact_lower_box R).prod isCompact_Icc).image_of_continuousOn
  have hu' : ContinuousOn (fun z : LowerSpace N × ℝ ↦ u z.2)
      ({C : LowerSpace N | ∀ i j, |C.val i j| ≤ R} ×ˢ Icc l r) :=
    hu.comp continuousOn_snd (fun _ hz ↦ hz.2)
  have hC : Continuous (fun z : LowerSpace N × ℝ ↦ z.1.val) := continuous_subtype_val.comp continuous_fst
  exact (show Continuous (fun z : Matrix (Fin N) (Fin N) ℝ × (Fin N → ℝ) ↦ z.1 *ᵥ z.2)
    by fun_prop).comp_continuousOn (hC.continuousOn.prodMk hu')

end SharpLiebThirring.ActionProof

end

end

end

end

end

end

end

end OAI
