import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

/--
@isnad1 id=ex.2h3v.s8.954d56c84875 from=translated src=- shape=a654afbd vocab=8eec4a4e
-/
theorem Module.exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
    (h𝔭ic : IsIntegrallyClosed (Localization.AtPrime 𝔭)) (h𝔭dim : ringKrullDim (Localization.AtPrime 𝔭) ≤ 1)
    (B : Type u) [AddCommGroup B] [Module A B] [Module.Finite A B] [NoZeroSMulDivisors A B] :
    ∃ f : A, f ∉ 𝔭 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) B) := by exact @_root_.P2MW.S_Module_exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one.solution A _ _ _ 𝔭 _ h𝔭ic h𝔭dim B _ _ _ _
