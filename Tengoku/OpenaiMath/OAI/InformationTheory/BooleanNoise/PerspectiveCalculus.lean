import Tengoku.OpenaiMath.OAI.InformationTheory.BooleanNoise.ConcavityAcrossJoin
import Tengoku

namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

def logCorrectedPerspective (f : ℝ → ℝ) (x C v : ℝ) : ℝ :=
  v * f (x / v) - C * v * Real.log v

def logCorrectedPerspectiveDeriv (f f' : ℝ → ℝ) (x C v : ℝ) : ℝ :=
  f (x / v) - (x / v) * f' (x / v) - C * (Real.log v + 1)

def logCorrectedPerspectiveSecondDeriv (f'' : ℝ → ℝ) (x C v : ℝ) : ℝ :=
  ((x / v) ^ 2 * f'' (x / v) - C) / v

theorem continuousOn_logCorrectedPerspectiveDeriv (f f' : ℝ → ℝ) (x C : ℝ)
    (hx : 0 < x) (hf : ∀ y, 0 < y → HasDerivAt f (f' y) y)
    (hf' : ContinuousOn f' (Ioi 0)) :
    ContinuousOn (logCorrectedPerspectiveDeriv f f' x C) (Ioi 0) := by
  have hi : ContinuousOn (fun v : ℝ => x / v) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun _ hv => ne_of_gt hv)
  have hmap : MapsTo (fun v : ℝ => x / v) (Ioi 0) (Ioi 0) :=
    fun _ hv => div_pos hx hv
  have hcf : ContinuousOn f (Ioi 0) :=
    fun y hy => (hf y hy).continuousAt.continuousWithinAt
  have hl : ContinuousOn Real.log (Ioi 0) :=
    continuousOn_id.log (fun _ hv => ne_of_gt hv)
  exact ((hcf.comp hi hmap).sub (hi.mul (hf'.comp hi hmap))).sub
    (continuousOn_const.mul (hl.add continuousOn_const))

end LeanBlast.CourtadeKumar

end

end OAI
