import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_RightConvolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply

open NumberField
open MeasureTheory AutomorphicForm

/--
@isnad1 id=eq.0h5v.s10.cfcfbd149802 from=translated src=- shape=acda62d4 vocab=5f07505e
-/
theorem solution
    (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (g t : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K φ f (g * t) = rightConv K φ (fun y => f (t⁻¹ * y)) g := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  show (∫ x, φ (g * t * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))
      = ∫ x, φ (g * x) * f (t⁻¹ * x) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  have h := integral_mul_left_eq_self (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
    (fun x => φ (g * x) * f (t⁻¹ * x)) t
  simp only [inv_mul_cancel_left] at h
  simpa only [mul_assoc] using h
