import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsAdicComplete_of_module_finite_free_span_natCast

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsAdicComplete_of_module_finite_free_span_natCast.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

theorem IsAdicComplete.of_module_finite_free_span_natCast
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (R : Type v) [CommRing R] [Algebra 𝓞 R] [Module.Finite 𝓞 R] [Module.Free 𝓞 R] :
    IsAdicComplete (Ideal.span {(p : R)}) R := by exact @_root_.P2MW.S_IsAdicComplete_of_module_finite_free_span_natCast.solution 𝓞 _ p _ R _ _ _ _
