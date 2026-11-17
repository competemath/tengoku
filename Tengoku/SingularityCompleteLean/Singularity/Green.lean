import Tengoku.SingularityCompleteLean.Singularity.Operators
import Tengoku.Seed.Analysis.Normed.Algebra.Spectrum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Green resolvent from an operator spectral gap

The spectral gap is an explicit hypothesis. This file does not prove the
nonamenability criterion that supplies it for the random walk.
-/

noncomputable section

namespace Singularity

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The bounded resolvent. Its identification with the path-counting Green kernel
is proved for the right Markov operator in `WalkKernel.lean`.-/
def green (P : E →L[ℂ] E) : E →L[ℂ] E := Ring.inverse (1 - P)

/-- A spectral radius below one places `1` in the resolvent set.
@isnad1 id=isunit.1h2v.s9.9b8e3ad898e7 from=translated src=- shape=260682fa vocab=65f63ede
-/
theorem one_sub_isUnit (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1) :
    IsUnit (1 - P) := by
  have hres : (1 : ℂ) ∈ resolventSet ℂ P :=
    spectrum.mem_resolventSet_of_spectralRadius_lt (by simpa using hgap)
  simpa only [map_one] using spectrum.mem_resolventSet_iff.mp hres

/--
@isnad1 id=eq.1h3v.s9.6edaf17f31fb from=translated src=- shape=156edd39 vocab=d71e1024
-/
theorem green_right_inverse (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1)
    (v : E) : green P v - P (green P v) = v := by
  have h := congrArg (fun T : E →L[ℂ] E => T v)
    (Ring.mul_inverse_cancel (1 - P) (one_sub_isUnit P hgap))
  exact h

/--
@isnad1 id=eq.1h3v.s9.6307aa272b5f from=translated src=- shape=271a0d71 vocab=d71e1024
-/
theorem green_left_inverse (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1)
    (v : E) : green P (v - P v) = v := by
  have h := congrArg (fun T : E →L[ℂ] E => T v)
    (Ring.inverse_mul_cancel (1 - P) (one_sub_isUnit P hgap))
  exact h

/-- Coercivity of the Green resolvent under exactly the two operator
hypotheses used in the argument.
@isnad1 id=coercive.2h2v.s8.3286492ae4cb from=translated src=- shape=c94cbcf0 vocab=955af52a
-/
theorem green_coercive_of_gap (P : E →L[ℂ] E)
    (hcontract : ∀ v, ‖P v‖ ≤ ‖v‖) (hgap : spectralRadius ℂ P < 1) :
    Coercive (green P) (1 / 2) :=
  green_coercive P (green P) hcontract (green_right_inverse P hgap)

variable [CompleteSpace E]

/-- The compressed Green operator as a bounded linear equivalence.-/
def compressedGreenEquiv (P : E →L[ℂ] E) (i : F →ₗᵢ[ℂ] E)
    (hcontract : ∀ v, ‖P v‖ ≤ ‖v‖) (hgap : spectralRadius ℂ P < 1) :
    F ≃L[ℂ] F :=
  (compression_coercive i (green_coercive_of_gap P hcontract hgap)).equiv (by norm_num)

end Singularity
