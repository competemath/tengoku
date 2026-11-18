import Tengoku.Seed.Analysis.Distribution.SchwartzSpace.Basic
import Tengoku.Seed.Analysis.Fourier.FourierTransform
import Tengoku.FltAnthropic.P2M.Sol.S_VectorFourier_ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_VectorFourier_ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory
open scoped FourierTransform

theorem VectorFourier.ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (_hB : B.Nondegenerate)
    (f : V → ℂ) (_hf : Integrable f μ)
    (_h : ∀ w : V, VectorFourier.fourierIntegral 𝐞 μ B f w = 0) :
    f =ᵐ[μ] 0 := by exact @_root_.P2MW.S_VectorFourier_ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero.solution V _ _ _ _ _ μ _ B _hB f _hf _h
