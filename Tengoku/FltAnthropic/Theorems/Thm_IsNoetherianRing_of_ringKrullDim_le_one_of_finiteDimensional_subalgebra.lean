import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v w

theorem IsNoetherianRing.of_ringKrullDim_le_one_of_finiteDimensional_subalgebra
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] (hR : ringKrullDim R ≤ 1)
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type w) [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] [FiniteDimensional K L]
    (B : Subalgebra R L) :
    IsNoetherianRing ↥B ∧ ringKrullDim ↥B ≤ 1 := by exact @_root_.P2MW.S_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra.solution R _ _ _ hR K _ _ _ L _ _ _ _ _ B
