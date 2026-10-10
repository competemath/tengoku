import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.DomainCalculus

namespace OAI

universe u_245 u_246

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
def kernel : AnalyticBidiskKernel := actualExteriorKernel D.exterior.radius_gt
  D.exterior.leading_ne D.exterior.analytic_regular D.exterior.injective
  D.exterior.noncritical D.support_circle
lemma outside_imp (t : ℂ) (ht : D.exterior.radius⁻¹ < ‖t‖) (hz : D.G t ∈ D.domain) :
    t ∈ ball (0:ℂ) 1 := (D.exterior.interior_iff t ht).mp hz
lemma inner_maps : MapsTo D.G ({t | D.exterior.radius⁻¹ < ‖t‖} ∩ ball 0 1) (closure D.domain) := by
  intro t ht
  exact subset_closure ((D.exterior.interior_iff t ht.1).mpr ht.2)
variable {n : Type u_245} {m : Type u_246} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
def trace (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    C(UnitAddCircle,Matrix m m ℂ) :=
  ⟨fun t => v (D.G t.toCircle), (hv.comp D.G_analytic (fun _ ht => (D.G_boundary ht).1)).continuousOn.comp_continuous
    (continuous_subtype_val.comp AddCircle.continuous_toCircle) (fun t => t.toCircle.property)⟩

def resolventField (A : Matrix n n ℂ) (t : UnitAddCircle) : Matrix n n ℂ :=
  ((t.toCircle : ℂ)*deriv D.G (t.toCircle : ℂ)) •
    (D.G t.toCircle • (1:Matrix n n ℂ)-A)⁻¹
lemma curve_continuous : Continuous (fun t : UnitAddCircle => D.G t.toCircle) :=
  D.G_analytic.continuousOn.comp_continuous
    (continuous_subtype_val.comp AddCircle.continuous_toCircle) (fun t => t.toCircle.property)
lemma normal_continuous : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)*deriv D.G t.toCircle) :=
  (continuous_subtype_val.comp AddCircle.continuous_toCircle).mul
    (D.G_analytic.deriv.continuousOn.comp_continuous
      (continuous_subtype_val.comp AddCircle.continuous_toCircle) (fun t => t.toCircle.property))
lemma resolvent_continuous (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain) :
    Continuous (D.resolventField A) :=
  D.normal_continuous.smul (matrix_resolvent_continuous A D.curve_continuous
    (fun t hz => D.G_ne_interior (hA hz) (by simp [Circle.norm_coe]) rfl))
lemma fourier_resolvent_eval (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    (ij : m × m) (k : ℤ) {v : ℂ → Matrix m m ℂ}
    (he : ∀ z ∈ D.domain, ∀ i j, v z i j =
      ∫ t : UnitAddCircle, ((t.toCircle : ℂ)*deriv D.G (t.toCircle : ℂ)) *
        matrixFourierTrace ij k t i j / (D.G t.toCircle-z) ∂AddCircle.haarAddCircle) :
    completeAnalyticEval A v = ∫ t : UnitAddCircle,
      D.resolventField A t ⊗ₖ matrixFourierTrace ij k t ∂AddCircle.haarAddCircle := by
  unfold resolventField
  rw [← complete_cauchy_integral_evaluation (μ := AddCircle.haarAddCircle) A D.curve_continuous D.normal_continuous
    (matrixFourierTrace ij k).continuous D.isOpen hA
    (fun z hz t => D.G_ne_interior hz (by simp [Circle.norm_coe]))]
  apply completeAnalyticEval_eqOn A D.isOpen hA
  intro z hz
  ext i j
  exact he z hz i j
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
