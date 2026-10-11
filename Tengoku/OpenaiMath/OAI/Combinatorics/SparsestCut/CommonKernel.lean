import Tengoku.OpenaiMath.OAI.Combinatorics.SparsestCut.KernelApprox

namespace OAI

universe u1 u2 u3

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CommonKernel
open MeasureTheory Set
open scoped RealInnerProductSpace BigOperators Matrix

variable {ι : Type u1} [Fintype ι]

lemma integral_posSemidef (K : ℝ → Matrix ι ι ℝ) {a b : ℝ} (hab : a ≤ b)
    (hK : ∀ t ∈ Icc a b, (K t).PosSemidef)
    (hi : ∀ i j, IntervalIntegrable (fun t => K t i j) volume a b) :
    Matrix.PosSemidef (fun i j => ∫ t in a..b, K t i j) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    apply intervalIntegral.integral_congr
    intro t ht
    simpa using (hK t (by simpa [uIcc_of_le hab] using ht)).isHermitian.apply i j
  · intro c
    have h : 0 ≤ ∫ t in a..b, star c ⬝ᵥ (K t *ᵥ c) :=
      intervalIntegral.integral_nonneg hab (fun t ht => (hK t ht).dotProduct_mulVec_nonneg c)
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial] at h ⊢
    have hrow (i : ι) : IntervalIntegrable (fun t => ∑ j, K t i j*c j) volume a b := by
      convert IntervalIntegrable.sum Finset.univ (fun j _ => (hi i j).mul_const (c j)) using 1
      first
        | (all_goals grind; done)
        | (all_goals simp_all; done)
        | (all_goals aesop; done)
        | (all_goals omega; done)
        | (all_goals norm_num; done)
        | (all_goals positivity; done)
        | (all_goals linarith; done)
        | (all_goals decide; done)
        | (all_goals tauto; done)
    rw [intervalIntegral.integral_finsetSum (fun i _ => (hrow i).const_mul (c i))] at h
    simp_rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun j _ => (hi _ j).mul_const (c j)),
      intervalIntegral.integral_mul_const] at h
    exact h

def circle (t q : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![Real.cos t-q*Real.sin t, Real.sin t+q*Real.cos t]

lemma circle_inner (t v q p : ℝ) :
    inner ℝ (circle t q) (circle v p) =
      (1+q*p)*Real.cos (v-t)+(q-p)*Real.sin (v-t) := by
  simp [circle, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub, Real.sin_sub]

  ring

lemma circle_self (t q : ℝ) : ‖circle t q‖^2 = 1+q^2 := by
  rw [← real_inner_self_eq_norm_sq, circle_inner]
  simp [pow_two]

variable {E : Type u2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {κ : Type u3} [Fintype κ]

def gram (g : κ → E) (θ : ι → E) (α : ι → κ → ℝ) (M ε a b : ℝ) : Matrix ι ι ℝ :=
  fun v w => M*(∫ σ in a..b, Real.exp (-‖θ v-θ w‖^2/(2*σ^2))) +
    ε*∑ k, ∫ σ in a..b,
      inner ℝ (circle (inner ℝ (g k) (θ v)/σ) (α v k))
        (circle (inner ℝ (g k) (θ w)/σ) (α w k)) / σ

omit [Fintype ι] [InnerProductSpace ℝ E] in
lemma gaussian_integrable (θ : ι → E) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (v w : ι) :
    IntervalIntegrable (fun σ => Real.exp (-‖θ v-θ w‖^2/(2*σ^2))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply Real.continuous_exp.comp_continuousOn
  apply continuousOn_const.div (by fun_prop)
  intro σ hσ
  have hp : 0 < σ := ha.trans_le hσ.1
  positivity

omit [Fintype ι] [Fintype κ] in
lemma circle_integrable (g : κ → E) (θ : ι → E) (α : ι → κ → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (v w : ι) (k : κ) :
    IntervalIntegrable (fun σ => inner ℝ (circle (inner ℝ (g k) (θ v)/σ) (α v k))
      (circle (inner ℝ (g k) (θ w)/σ) (α w k))/σ) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  have hne : ∀ σ ∈ Icc a b, σ ≠ 0 := fun σ hσ => (ha.trans_le hσ.1).ne'
  have h1 : ContinuousOn (fun σ : ℝ => inner ℝ (g k) (θ v)/σ) (Icc a b) :=
    continuousOn_const.div continuousOn_id hne
  have h2 : ContinuousOn (fun σ : ℝ => inner ℝ (g k) (θ w)/σ) (Icc a b) :=
    continuousOn_const.div continuousOn_id hne
  simp only [circle_inner]
  exact (((continuousOn_const.mul (Real.continuous_cos.comp_continuousOn (h2.sub h1))).add
    (continuousOn_const.mul (Real.continuous_sin.comp_continuousOn (h2.sub h1)))).div continuousOn_id hne)

end UniformSparsestCut.CommonKernel

end

end OAI
