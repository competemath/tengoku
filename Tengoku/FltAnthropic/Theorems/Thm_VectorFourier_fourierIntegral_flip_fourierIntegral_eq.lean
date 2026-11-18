import Tengoku.Seed.Analysis.Distribution.SchwartzSpace.Basic
import Tengoku.Seed.Analysis.Fourier.FourierTransform
import Tengoku.Seed.Algebra.Module.ZLattice.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_VectorFourier_fourierIntegral_flip_fourierIntegral_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_VectorFourier_fourierIntegral_flip_fourierIntegral_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped FourierTransform SchwartzMap
theorem VectorFourier.fourierIntegral_flip_fourierIntegral_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ V)
    (f : 𝓢(V, ℂ)) (x : V) :
    VectorFourier.fourierIntegral 𝐞 μ B.flip (VectorFourier.fourierIntegral 𝐞 μ B f) x
      = ((μ.real (ZSpan.fundamentalDomain b)) ^ 2 / |(Matrix.of fun i j => B (b i) (b j)).det| : ℝ)
        * f (-x) := by exact @_root_.P2MW.S_VectorFourier_fourierIntegral_flip_fourierIntegral_eq.solution V _ _ _ _ _ μ _ B hB ι _ _ b f x
