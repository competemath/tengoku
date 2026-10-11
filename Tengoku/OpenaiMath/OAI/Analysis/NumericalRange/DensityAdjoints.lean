import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.BoundaryCalculus

namespace OAI

universe u_247 u_248

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {n : Type u_247} {m : Type u_248} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
lemma hsTrace_mean_coefficient (u : C(UnitAddCircle,Matrix m m ℂ)) (ij : m × m) :
    fourierCoeff (l2Coordinate ij (hsTraceLp u)) 0 =
      (∫ t, u t ∂AddCircle.haarAddCircle) ij.1 ij.2 := by
  have hi := u.continuous.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle)
    (HasCompactSupport.of_compactSpace _)
  rw [matrix_integral_entry hi]
  simp only [fourierCoeff,neg_zero,fourier_zero,one_smul]
  apply integral_congr_ae
  filter_upwards [l2Coordinate_ae ij (hsTraceLp u),hsTraceLp_ae u] with t hc hu
  rw [hc,hu]
  rfl
lemma left_adjoint_of_ae {F : UnitAddCircle → Matrix m m ℂ}
    (L : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m))
    (hL : ∀ u, L u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (F t*fromHS (u t)))
    {p r : MatrixCircleL2 (m := m)}
    (hp : p =ᵐ[AddCircle.haarAddCircle] fun t => toHS ((F t)ᴴ*fromHS (r t))) :
    p = L.adjoint r := by
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hp,hL u] with t hp hl
  rw [hp,hl]
  change inner ℂ (hsLeft (F t)ᴴ (r t)) (u t) = inner ℂ (r t) (hsLeft (F t) (u t))
  rw [← hsLeft_adjoint,ContinuousLinearMap.adjoint_inner_left]
lemma right_adjoint_of_ae {F : UnitAddCircle → Matrix m m ℂ}
    (R : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m))
    (hR : ∀ u, R u =ᵐ[AddCircle.haarAddCircle] fun t => toHS (fromHS (u t)*F t))
    {q r : MatrixCircleL2 (m := m)}
    (hq : q =ᵐ[AddCircle.haarAddCircle] fun t => toHS (fromHS (r t)*(F t)ᴴ)) :
    q = R.adjoint r := by
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hq,hR u] with t hq hr
  rw [hq,hr]
  change inner ℂ (hsRight (F t)ᴴ (r t)) (u t) = inner ℂ (r t) (hsRight (F t) (u t))
  rw [← hsRight_adjoint,ContinuousLinearMap.adjoint_inner_left]
end CompleteCrouzeix

end

end

end OAI
