import Tengoku.OpenaiMath.OAI.Analysis.TracialSplitting.FaithfulRepresentations

namespace OAI

universe uH uI

section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

namespace NuclearTrace

open Pureness UnitalTomsWinter

open scoped TensorProduct ComplexOrder

section SpatialHypertrace

variable {A H : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (f : A →ₚ[ℂ] ℂ) (ht : ∀ a b, f (a*b) = f (b*a))

end SpatialHypertrace

end NuclearTrace

noncomputable section

namespace NuclearTrace

open scoped InnerProductSpace ComplexOrder

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma operator_le_of_unit_quadratic {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    {c : ℝ} (h : ∀ ξ : H, ‖ξ‖ ≤ 1 → (⟪ξ, T ξ⟫_ℂ).re ≤ c) :
    T ≤ c • (1 : H →L[ℂ] H) := by
  have hc : 0 ≤ c := by simpa using h 0 (by simp)
  apply sub_nonneg.mp
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨((IsSelfAdjoint.all c).smul (IsSelfAdjoint.one (H →L[ℂ] H))).sub hT, ?_⟩
  intro ξ
  by_cases hz : ξ = 0
  · subst ξ; change 0 ≤ (⟪(c • (1 : H →L[ℂ] H)-T) (0 : H),0⟫_ℂ).re; simp
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hz
  have hu : ‖(‖ξ‖⁻¹ : ℝ) • ξ‖ ≤ 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_cancel₀ hn.ne']
  have hb := h ((‖ξ‖⁻¹ : ℝ) • ξ) hu
  have he : (⟪(‖ξ‖⁻¹ : ℝ) • ξ, T ((‖ξ‖⁻¹ : ℝ) • ξ)⟫_ℂ).re =
      ‖ξ‖⁻¹ * ‖ξ‖⁻¹ * (⟪ξ,T ξ⟫_ℂ).re := by
    simp only [T.map_smul_of_tower,inner_smul_left_eq_smul,inner_smul_right_eq_smul,
      Complex.smul_re,smul_eq_mul]
    ring
  rw [he] at hb
  have hb' : (⟪ξ,T ξ⟫_ℂ).re ≤ c * ‖ξ‖^2 := by
    have hmul := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖ξ‖)
    field_simp at hmul
    nlinarith
  change 0 ≤ (⟪(c • (1 : H →L[ℂ] H)-T) ξ,ξ⟫_ℂ).re
  simp only [sub_apply,smul_apply,
    one_apply_eq_self,inner_sub_left,inner_smul_left_eq_smul,
    Complex.sub_re,Complex.smul_re,smul_eq_mul,inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_pow, Complex.ofReal_re]
  rw [show (⟪T ξ,ξ⟫_ℂ).re = (⟪ξ,T ξ⟫_ℂ).re from @inner_re_symm ℂ H _ _ _ (T ξ) ξ]
  linarith

variable {I : Type uI} [Fintype I]

def vectorTest (T : I → H →L[ℂ] H) (ξ : H) : I → ℝ :=
  fun i => (⟪ξ,T i ξ⟫_ℂ).re

def stateTest (T : I → H →L[ℂ] H) (σ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) : I → ℝ :=
  fun i => (σ (T i)).re

lemma real_pi_linear_expansion [DecidableEq I] (f : (I → ℝ) →L[ℝ] ℝ) (v : I → ℝ) :
    f v = ∑ i, f (Pi.single i 1) * v i := by
  classical
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show Pi.single i (v i) = v i • Pi.single i (1 : ℝ) by
    simpa only [smul_eq_mul,mul_one] using Pi.single_smul' i (v i) (1 : ℝ)]
  rw [map_smul,smul_eq_mul,mul_comm]

lemma stateTest_mem_closure (T : I → H →L[ℂ] H) (hT : ∀ i, IsSelfAdjoint (T i))
    (σ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) (hσ : σ 1 = 1) :
    stateTest T σ ∈ closure (convexHull ℝ (vectorTest T '' Metric.closedBall 0 1)) := by
  classical
  by_contra hn
  obtain ⟨f,c,hf,hc⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (vectorTest T '' Metric.closedBall 0 1)).closure
      isClosed_closure hn
  let S : H →L[ℂ] H := ∑ i, f (Pi.single i 1) • T i
  have hS : IsSelfAdjoint S := isSelfAdjoint_sum _ fun i _ => (IsSelfAdjoint.all _).smul (hT i)
  have he (ξ : H) : f (vectorTest T ξ) = (⟪ξ,S ξ⟫_ℂ).re := by
    rw [real_pi_linear_expansion]
    simp only [S,sum_apply,inner_sum,Complex.re_sum,
      smul_apply,inner_smul_right_eq_smul,Complex.smul_re,smul_eq_mul,vectorTest]
  have hle : S ≤ c • (1 : H →L[ℂ] H) := operator_le_of_unit_quadratic hS (by
    intro ξ hξ
    rw [← he]
    exact (hf _ (subset_closure (subset_convexHull ℝ _
      ⟨ξ,by simpa using hξ,rfl⟩))).le)
  have hb := (σ.monotone hle).1
  have hs : f (stateTest T σ) = (σ S).re := by
    rw [real_pi_linear_expansion]
    simp only [S,map_sum,Complex.re_sum,σ.map_smul_of_tower,Complex.smul_re,
      smul_eq_mul,stateTest]
  change (σ S).re ≤ (σ (c • 1)).re at hb
  rw [σ.map_smul_of_tower,hσ,Complex.smul_re,Complex.one_re,smul_eq_mul,mul_one] at hb
  exact (not_le_of_gt hc) (hs ▸ hb)

theorem finite_vector_state_approximation (T : I → H →L[ℂ] H)
    (hT : ∀ i, IsSelfAdjoint (T i))
    (σ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) (hσ : σ 1 = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (ξ : Fin n → H),
      (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧ (∀ j, ‖ξ j‖ ≤ 1) ∧
      ∀ i, |(σ (T i)).re - ∑ j, w j * (⟪ξ j,T i (ξ j)⟫_ℂ).re| < ε := by
  classical
  obtain ⟨z,hz,hzε⟩ := Metric.mem_closure_iff.mp (stateTest_mem_closure T hT σ hσ) ε hε
  obtain ⟨J,_,w,v,hw,hw1,hv,hsum⟩ := mem_convexHull_iff_exists_fintype.mp hz
  choose ξ hξ hvξ using hv
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J,w ∘ e,ξ ∘ e,fun j => hw (e j),(e.sum_comp w).trans hw1,
    fun j => by simpa using hξ (e j),?_⟩
  intro i
  have hle := (norm_le_pi_norm (stateTest T σ-z) i).trans_lt (by
    simpa only [dist_eq_norm] using hzε)
  have he : (∑ j : Fin (Fintype.card J), w (e j) * (⟪ξ (e j),T i (ξ (e j))⟫_ℂ).re) = z i := by
    rw [e.sum_comp (fun j => w j * (⟪ξ j,T i (ξ j)⟫_ℂ).re)]
    have hv' := congrFun hsum i
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,← hvξ,vectorTest] using hv'
  simpa only [Function.comp_apply,he,Real.norm_eq_abs,Pi.sub_apply,stateTest] using hle

end NuclearTrace

noncomputable section

namespace NuclearTrace

open scoped TensorProduct ComplexOrder InnerProductSpace

section CyclicExtension

variable {A B N H : Type} [CStarAlgebra A] [CStarAlgebra B]

variable [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end CyclicExtension

end NuclearTrace

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end OAI
