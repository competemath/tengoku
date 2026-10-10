import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.DensityIdentification

namespace OAI

noncomputable section

universe u_253 u_254

namespace CompleteCrouzeix
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace AdmissibleDomain

section
variable (D : AdmissibleDomain)
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {n : Type u_253} {m : Type u_254} [Fintype n] [DecidableEq n] [Nonempty n] [Fintype m] [DecidableEq m]
lemma coordinate_analytic_spectrum (D : AdmissibleDomain)
    {n : Type u_253} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain) :
    ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ D.interior.toDisk z :=
  fun z hz => D.interior.analytic_to z (D.interior.closure_subset (subset_closure (hA hz)))
end
variable (D : AdmissibleDomain) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
lemma resolventField_posSemidef (hW : numericalRange A ⊆ D.domain) (t : UnitAddCircle) :
    (D.resolventField A t+(D.resolventField A t)ᴴ).PosSemidef := by
  apply supporting_resolvent_posSemidef
  · intro hz
    exact D.G_ne_interior (hW hz) (Circle.norm_coe t.toCircle).ge rfl
  · intro w hw
    exact D.support _ t.toCircle.2 w (subset_closure (hW hw))
end AdmissibleDomain
end CompleteCrouzeix

end

end OAI
