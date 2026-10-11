import Tengoku.OpenaiMath.OAI.Analysis.Steinitz.Adaptive

namespace OAI

/-! Filtered-body energy and the predictor slab budget. -/

section

open Matrix GaussianTail MeasureTheory ProbabilityTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Pointwise NNReal
namespace GaussianEvents
variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype I]
noncomputable def openConstraints (A : I → E →L[ℝ] F) (R : I → ℝ) : Set E :=
  {x | ∀ i,‖A i x‖ < R i}
lemma openConstraints_open (A : I → E →L[ℝ] F) (R : I → ℝ) : IsOpen (openConstraints A R) := by
  simp only [openConstraints,Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (A i).continuous.norm continuous_const
omit [Fintype I] in
lemma openConstraints_convex (A : I → E →L[ℝ] F) (R : I → ℝ) : Convex ℝ (openConstraints A R) := by
  have he : openConstraints A R = ⋂ i,(A i) ⁻¹' Metric.ball 0 (R i) := by
    ext x; simp [openConstraints,Metric.mem_ball,dist_zero_right]
  rw [he]
  exact convex_iInter fun i => (convex_ball (0:F) (R i)).linear_preimage (A i).toLinearMap
omit [Fintype I] in
lemma openConstraints_symmetric (A : I → E →L[ℝ] F) (R : I → ℝ) :
    ∀ x∈openConstraints A R,-x∈openConstraints A R := by
  intro x hx i
  simpa only [map_neg,norm_neg] using hx i
omit [Fintype I] in
lemma openConstraints_zero (A : I → E →L[ℝ] F) {R : I → ℝ} (hR : ∀ i,0<R i) :
    (0:E)∈openConstraints A R := by intro i; simpa only [map_zero,norm_zero] using hR i
end GaussianEvents

namespace EuclideanSteinitz.Filter
open GaussianAR GaussianEvents Coefficient
variable {ι κ T J : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Fintype T] [Fintype J] [Nonempty ι] [Nonempty κ]

noncomputable def bodyRate : ℝ := 2*stateRate+1
lemma bodyRate_nonneg : 0≤bodyRate := by unfold bodyRate; linarith [stateRate_nonneg]
noncomputable def applicationDomain (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) : Set (EuclideanSpace ℝ κ) :=
  openConstraints (fun t => matrixMap (Rt t)) (fun _ => 2*stateRadius*Real.sqrt (Fintype.card ι)) ∩
  Metric.ball 0 (2*stateRadius*Real.sqrt (Fintype.card κ)) ∩
  openConstraints (fun j => matrixMap (H j)) (fun _ => 2*slabRadius)

omit [DecidableEq ι] [Nonempty ι] [Nonempty κ] in
lemma applicationDomain_open (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) :
    IsOpen (applicationDomain Rt H) :=
  ((openConstraints_open _ _).inter Metric.isOpen_ball).inter (openConstraints_open _ _)
omit [DecidableEq ι] [Nonempty ι] [Nonempty κ] [Fintype T] [Fintype J] in
lemma applicationDomain_convex (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) :
    Convex ℝ (applicationDomain Rt H) :=
  ((openConstraints_convex _ _).inter (convex_ball _ _)).inter (openConstraints_convex _ _)
omit [DecidableEq ι] [Fintype T] [Fintype J] [Nonempty ι] [Nonempty κ] in
lemma applicationDomain_bounded (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) :
    Bornology.IsBounded (applicationDomain Rt H) :=
  (Metric.isBounded_ball (x := (0:EuclideanSpace ℝ κ)) (r := _)).subset (fun _ hx => hx.1.2)
omit [DecidableEq ι] [Nonempty ι] [Nonempty κ] [Fintype T] [Fintype J] in
lemma applicationDomain_symmetric (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) :
    ∀ x∈applicationDomain Rt H,-x∈applicationDomain Rt H := by
  intro x hx
  refine ⟨⟨openConstraints_symmetric _ _ x hx.1.1,?_⟩,openConstraints_symmetric _ _ x hx.2⟩
  simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hx.1.2
omit [DecidableEq ι] [Fintype T] [Fintype J] in
lemma applicationDomain_zero (Rt : T → Matrix ι κ ℝ) (H : J → Matrix Unit κ ℝ) :
    (0:EuclideanSpace ℝ κ)∈applicationDomain Rt H := by
  have hι : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hκ : (0:ℝ)<Fintype.card κ := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨⟨openConstraints_zero _ (fun _ => mul_pos (mul_pos (by norm_num) stateRadius_pos) (Real.sqrt_pos.mpr hι)),?_⟩,openConstraints_zero _ (fun _ => mul_pos (by norm_num) slabRadius_pos)⟩
  simp only [Metric.mem_ball,dist_self]
  exact mul_pos (mul_pos (by norm_num) stateRadius_pos) (Real.sqrt_pos.mpr hκ)

omit [Nonempty κ] in
lemma slabs_rate (H : J → Matrix Unit κ ℝ) (hH : ∀ i,∑ j, (H j () i)^2 ≤ 1)
    {q : κ → ℝ} (hq : ∀ i,0≤q i) :
    (∑ j,weightedSq (H j) (diagonal q)) ≤ ∑ i,q i := by
  simp only [weighted_diagonal_eq,Fintype.sum_unique]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.mul_sum]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hH i) (hq i)

noncomputable def bodyScale : ℝ := 1000*(2*bodyRate+1)
lemma bodyScale_pos : 0 < bodyScale := by unfold bodyScale; linarith [bodyRate_nonneg]
lemma bodyScale_ge_one : 1 ≤ bodyScale := by unfold bodyScale; linarith [bodyRate_nonneg]
lemma bodyScale_bound : (2*bodyRate+1)/bodyScale^2 ≤ 1/10000 := by
  apply (div_le_iff₀ (sq_pos_of_pos bodyScale_pos)).mpr
  unfold bodyScale
  nlinarith [bodyRate_nonneg,sq_nonneg bodyRate]

end EuclideanSteinitz.Filter

end

end OAI
