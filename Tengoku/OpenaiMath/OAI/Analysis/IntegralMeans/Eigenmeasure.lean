import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.TransferOperator

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

lemma log_norm_pow_subadditive.{u_1} {A : Type u_1} [NormedRing A] (a : A)
    (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) : Subadditive (fun n => Real.log ‖a^n‖) := by
  intro m n
  change Real.log ‖a^(m+n)‖ ≤ _
  rw [pow_add]
  calc
    Real.log ‖a^m*a^n‖ ≤ Real.log (‖a^m‖*‖a^n‖) :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one (by simpa [pow_add] using h (m+n))) (norm_mul_le _ _)
    _ = Real.log ‖a^m‖ + Real.log ‖a^n‖ := Real.log_mul (by linarith [h m]) (by linarith [h n])

def growthLog.{u_1} {A : Type u_1} [NormedRing A] (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) : ℝ :=
  (log_norm_pow_subadditive a h).lim

def growthRate.{u_1} {A : Type u_1} [NormedRing A] (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) : ℝ :=
  Real.exp (growthLog a h)

def positiveResolvent.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (τ : ℝ) : C(X,ℝ) →L[ℝ] C(X,ℝ) :=
  ∑' n : ℕ, (τ⁻¹)^n • L^n

lemma positive_functional_bound.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (Λ : C(X,ℝ) →ₗ[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (f : C(X,ℝ)) :
    ‖Λ f‖ ≤ Λ 1 * ‖f‖ := by
  have hlo : (-‖f‖) • (1 : C(X,ℝ)) ≤ f := by
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).1
  have hhi : f ≤ ‖f‖ • (1 : C(X,ℝ)) := by
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).2
  have h1 := hp (f-(-‖f‖) • 1) (sub_nonneg.mpr hlo)
  have h2 := hp (‖f‖ • 1-f) (sub_nonneg.mpr hhi)
  simp only [map_sub,map_smul,smul_eq_mul,neg_mul] at h1 h2
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith

end Brennan

end

end OAI
