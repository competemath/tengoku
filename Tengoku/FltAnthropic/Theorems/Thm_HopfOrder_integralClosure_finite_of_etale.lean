import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfOrder_integralClosure_finite_of_etale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfOrder_integralClosure_finite_of_etale.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v w
theorem HopfOrder.integralClosure_finite_of_etale
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type w} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    [Algebra.Etale K A] : Module.Finite R ↥(integralClosure R A) := by exact @_root_.P2MW.S_HopfOrder_integralClosure_finite_of_etale.solution R _ _ _ _ K _ _ _ A _ _ _ _ _
