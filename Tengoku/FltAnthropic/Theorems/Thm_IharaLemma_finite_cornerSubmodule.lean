import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting
import Tengoku.Seed.RingTheory.Finiteness.Cardinality
import Tengoku.FltAnthropic.P2M.Sol.S_IharaLemma_finite_cornerSubmodule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IharaLemma_finite_cornerSubmodule.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem IharaLemma.finite_cornerSubmodule {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B]
    [Algebra 𝒪 B] {V : Type} [AddCommGroup V] [Module B V] [Module 𝒪 V] [IsScalarTower 𝒪 B V]
    (e : B) [Module.Finite 𝒪 V] :
    Module.Finite 𝒪 ↥(IharaLemma.cornerSubmodule (M := V) e) := by exact @_root_.P2MW.S_IharaLemma_finite_cornerSubmodule.solution 𝒪 _ B _ _ V _ _ _ _ e _
