/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.AngularParameters
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.NodeSensitivity
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.GapSigns

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual interpolation derivatives in the open angular chart

The anchored angle is fixed at zero; the remaining angles are literal free
coordinates. The embedding of parameter directions inserts a zero in that
first slot, and the derivative sum contains exactly the moving nodes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ContDiff

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

def angularParameterEmbedding : (Fin d → ℝ) →L[ℝ] (Fin (d + 1) → ℝ) :=
  ContinuousLinearMap.pi (Fin.cases 0 (fun j => ContinuousLinearMap.proj j))

/--
@isnad1 id=eq.0h2v.s8.dfdc358ddfb7 from=translated src=- shape=af4824aa vocab=b128f9b7
-/
lemma angularParameterEmbedding_apply (v : Fin d → ℝ) :
    angularParameterEmbedding v = angularParameterAngles v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [angularParameterEmbedding, angularParameterAngles]

/--
@isnad1 id=hasfderi.0h2v.s7.9e389ccd9528 from=translated src=- shape=3868e385 vocab=32baa8ae
-/
lemma hasFDerivAt_angularParameterAngles (u : Fin d → ℝ) :
    HasFDerivAt angularParameterAngles angularParameterEmbedding u := by
  have heq : (angularParameterEmbedding : (Fin d → ℝ) → Fin (d + 1) → ℝ) =
      angularParameterAngles := funext angularParameterEmbedding_apply
  rw [← heq]
  exact angularParameterEmbedding.hasFDerivAt

/--
@isnad1 id=contdiff.0h2v.s7.e7deb24d999b from=translated src=- shape=03d3037c vocab=0246e1bd
-/
lemma contDiff_angularParameterAngles (m : ℕ∞ω) :
    ContDiff ℝ m (angularParameterAngles : (Fin d → ℝ) → Fin (d + 1) → ℝ) := by
  have heq : (angularParameterEmbedding : (Fin d → ℝ) → Fin (d + 1) → ℝ) =
      angularParameterAngles := funext angularParameterEmbedding_apply
  rw [← heq]
  exact angularParameterEmbedding.contDiff

def angularInterpolantParameterDerivative (u : Fin d → ℝ) (c : Fin (d + 1) → ℝ)
    (t : ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  (sineInterpolantParameterDerivative (angularParameterAngles u) c t).comp
    angularParameterEmbedding

/--
@isnad1 id=eq.0h5v.s8.3fed6a9d41f2 from=translated src=- shape=29604ae8 vocab=c3accde9
-/
lemma angularInterpolantParameterDerivative_apply (u v : Fin d → ℝ)
    (c : Fin (d + 1) → ℝ) (t : ℝ) :
    angularInterpolantParameterDerivative u c t v =
      ∑ j : Fin d, v j *
        (-deriv (sineInterpolant (angularParameterAngles u) c) (u j) *
          sineCardinal (angularParameterAngles u) j.succ t) := by
  rw [angularInterpolantParameterDerivative, ContinuousLinearMap.comp_apply,
    angularParameterEmbedding_apply, sineInterpolantParameterDerivative_apply,
    Fin.sum_univ_succ]
  simp only [angularParameterAngles_zero, angularParameterAngles_succ, zero_mul, zero_add]

/--
@isnad1 id=hasfderi.1h4v.s7.3151ecc89f07 from=translated src=- shape=7d2ca668 vocab=c27d0648
-/
lemma hasFDerivAt_angularInterpolant_parameters (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (c : Fin (d + 1) → ℝ) (t : ℝ) :
    HasFDerivAt (fun v : Fin d → ℝ => sineInterpolant (angularParameterAngles v) c t)
      (angularInterpolantParameterDerivative u c t) u := by
  have hθ := (cyclicAnglesOfParameters u hu).phaseNodes_injective
  exact (hasFDerivAt_sineInterpolant_parameters (angularParameterAngles u) c t hθ
    (angularParameterAngle_mem_Ico u hu)).comp u (hasFDerivAt_angularParameterAngles u)

/--
@isnad1 id=contdiff.1h5v.s7.9a621313b73d from=translated src=- shape=321b1dbf vocab=b178abc9
-/
lemma contDiffAt_angularInterpolant_joint (m : ℕ∞ω) (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (c : Fin (d + 1) → ℝ) (t : ℝ) :
    ContDiffAt ℝ m (fun x : (Fin d → ℝ) × ℝ =>
      sineInterpolant (angularParameterAngles x.1) c x.2) (u, t) := by
  have hθ := (cyclicAnglesOfParameters u hu).phaseNodes_injective
  have hmap : ContDiffAt ℝ m (fun x : (Fin d → ℝ) × ℝ =>
      (angularParameterAngles x.1, x.2)) (u, t) :=
    (((contDiff_angularParameterAngles m).contDiffAt.comp (u, t) contDiffAt_fst).prodMk
      contDiffAt_snd)
  have hcomp := (contDiffAt_sineInterpolant_joint m (angularParameterAngles u) t c hθ).comp
    (u, t) hmap
  exact hcomp

end

end UnitCircleInterpolation
