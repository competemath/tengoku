import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.Eigenmeasure

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass

def positiveFunctionalCLM.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (Λ : C(X,ℝ) →ₗ[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) : C(X,ℝ) →L[ℝ] ℝ :=
  Λ.mkContinuous (Λ 1) (positive_functional_bound Λ hp)

def intervalFunctional.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A : ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (Λ : C(X,ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (a b : ℝ) (hab : a ≤ b) : C(X,ℝ) →L[ℝ] ℝ :=
  positiveFunctionalCLM
    { toFun := fun f => ∫ t in a..b, Λ (A t f)
      map_add' := by
        intro f g
        simp only [map_add]
        exact intervalIntegral.integral_add ((Λ.continuous.comp (hc f)).intervalIntegrable a b)
          ((Λ.continuous.comp (hc g)).intervalIntegrable a b)
      map_smul' := by
        intro c f
        simp only [map_smul,smul_eq_mul]
        exact intervalIntegral.integral_const_mul c _ }
    (by
      intro f hf
      exact intervalIntegral.integral_nonneg hab (fun t _ => hΛ _ (hp t f hf)))

def probabilityFunctional.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X) : C(X,ℝ) →L[ℝ] ℝ :=
  positiveFunctionalCLM
    { toFun := fun f => ∫ x, f x ∂(μ : Measure X)
      map_add' := fun f g => integral_add (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => integral_smul c f }
    (fun _ hf => integral_nonneg hf)

lemma periodic_dyadic_integral (F : ℝ → ℝ) (hc : Continuous F) (hp : Function.Periodic F 2) :
    (∫ x in (0 : ℝ)..2, (F (-1/2+x/2)+F (1/2+x/2))) = 2*∫ x in (0 : ℝ)..2, F x := by
  have hm : (∫ x in (0 : ℝ)..2, F (-1/2+x/2)) = 2*∫ x in (-1/2 : ℝ)..(1/2), F x := by
    have hh := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 2) F
      (by norm_num : (1/2 : ℝ) ≠ 0) (-1/2)
    convert hh using 1 <;> (try { congr 1; funext x; congr 1; ring }); norm_num
  have hp' : (∫ x in (0 : ℝ)..2, F (1/2+x/2)) = 2*∫ x in (1/2 : ℝ)..(3/2), F x := by
    have hh := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 2) F
      (by norm_num : (1/2 : ℝ) ≠ 0) (1/2)
    convert hh using 1 <;> (try { congr 1; funext x; congr 1; ring }); norm_num
  have hi : (∫ x in (-1/2 : ℝ)..(3/2), F x) = ∫ x in (0 : ℝ)..2, F x := by
    convert hp.intervalIntegral_add_eq (-1/2) 0 using 1 <;> norm_num
  have hcm : Continuous (fun x : ℝ => F (-1/2+x/2)) := hc.comp (continuous_const.add (continuous_id.div_const 2))
  have hcp : Continuous (fun x : ℝ => F (1/2+x/2)) := hc.comp (continuous_const.add (continuous_id.div_const 2))
  rw [intervalIntegral.integral_add (hcm.intervalIntegrable _ _) (hcp.intervalIntegrable _ _),hm,hp',← mul_add,
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),hi]

end Brennan

end

end OAI
