import Tengoku.Seed.RepresentationTheory.Irreducible
import Tengoku.FltAnthropic.P2M.Sol.S_Representation_span_range_eq_top_of_isIrreducible

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Representation_span_range_eq_top_of_isIrreducible.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open Module LinearMap
theorem Representation.span_range_eq_top_of_isIrreducible
    {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible] :
    Submodule.span k (Set.range ⇑ρ) = ⊤ := by exact @_root_.P2MW.S_Representation_span_range_eq_top_of_isIrreducible.solution k G V _ _ _ _ _ _ ρ _
