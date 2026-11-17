import Tengoku.PaperCLean.PaperCPrel8.InformationSaddleScales

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The literal first-order information budget of section 6.2 -/
namespace PaperC.Prel8.InformationSaddleLimit
open Filter Topology
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales
open PaperC.Prel8.InformationSaddleBudget PaperC.Prel8.InformationSaddleScales
noncomputable section

/-- Elementary positive-root identity used only after constructing the actual saddle.-/
theorem budget_quadratic_formula {x j : ℝ} (hx : 0 ≤ x) (hj : 0 ≤ j) :
    (x-j)/2=(Real.sqrt (j^2+4*(x^2+j*x))-3*j)/4 := by
  have he : j^2+4*(x^2+j*x)=(2*x+j)^2 := by ring
  rw [he,Real.sqrt_sq (by positivity : 0 ≤ 2*x+j)]
  ring

end
end PaperC.Prel8.InformationSaddleLimit
