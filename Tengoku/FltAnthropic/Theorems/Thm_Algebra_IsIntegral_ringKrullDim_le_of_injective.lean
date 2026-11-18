import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_IsIntegral_ringKrullDim_le_of_injective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_IsIntegral_ringKrullDim_le_of_injective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=le.1h2v.s6.b44ee6c1ba20 from=translated src=- shape=e3a90ee3 vocab=1a19cc10
-/
theorem Algebra.IsIntegral.ringKrullDim_le_of_injective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R ≤ ringKrullDim S := by exact @_root_.P2MW.S_Algebra_IsIntegral_ringKrullDim_le_of_injective.solution R S _ _ _ _ hinj
