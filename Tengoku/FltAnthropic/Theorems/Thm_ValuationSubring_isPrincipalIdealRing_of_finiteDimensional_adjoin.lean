import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=isprinci.2h4v.s8.1f8082a0ddff from=translated src=- shape=879b8bc1 vocab=70340834
-/
theorem ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (O : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ O) (hO : O ≠ ⊤) :
    IsPrincipalIdealRing O := by exact @_root_.P2MW.S_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin.solution K F _ _ _ x _ O hK hO
