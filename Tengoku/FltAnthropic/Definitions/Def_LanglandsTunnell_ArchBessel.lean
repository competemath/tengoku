import Tengoku.Seed.Analysis.MellinTransform

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.ArchBessel

open MeasureTheory Set

def besselKernel (ν : ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))

/--
@isnad1 id=eq.0h2v.s6.fdba87afb6e3 from=translated src=- shape=b9f7c823 vocab=f253a60d
-/
theorem besselKernel_def (ν : ℂ) (x : ℝ) :
    besselKernel ν x = ∫ t in Ioi (0 : ℝ), (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1)) :=
  rfl

end LanglandsTunnell.ArchBessel

end
