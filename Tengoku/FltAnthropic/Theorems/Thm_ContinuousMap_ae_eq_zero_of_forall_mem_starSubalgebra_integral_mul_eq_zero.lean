import Tengoku.Seed.Topology.ContinuousMap.StoneWeierstrass
import Tengoku.Seed.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Tengoku.Seed.MeasureTheory.Function.L2Space
import Tengoku.Seed.Analysis.RCLike.Lemmas
import Tengoku.FltAnthropic.P2M.Sol.S_ContinuousMap_ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ContinuousMap_ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

theorem ContinuousMap.ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (A : StarSubalgebra ℂ C(X, ℂ)) (hA : A.SeparatesPoints)
    (β : C(X, ℂ))
    (h : ∀ f ∈ A, ∫ x, f x * β x ∂μ = 0) :
    (β : X → ℂ) =ᵐ[μ] 0 := by exact @_root_.P2MW.S_ContinuousMap_ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero.solution X _ _ _ _ _ μ _ A hA β h
