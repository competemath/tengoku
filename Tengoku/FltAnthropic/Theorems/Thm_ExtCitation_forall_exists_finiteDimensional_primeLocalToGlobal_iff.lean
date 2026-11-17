import Tengoku.FltAnthropic.Definitions.Def_ExtEndgame_ProductionDatum
import Tengoku.FltAnthropic.P2M.Sol.S_ExtCitation_forall_exists_finiteDimensional_primeLocalToGlobal_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ExtCitation_forall_exists_finiteDimensional_primeLocalToGlobal_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open CategoryTheory ExtCitation
/--
@isnad1 id=iff.0h3v.s13.dd5f1d461bd9 from=translated src=- shape=8674436f vocab=0403df3e
-/
theorem ExtCitation.forall_exists_finiteDimensional_primeLocalToGlobal_iff
    (q : Nat.Primes) [Fact (q : ℕ).Prime]
    {k : Type} [CommRing k] (M : Rep k (primeLocalGaloisGroup q)) :
    (∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m) ↔
      ∀ m : M, ∃ K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)), FiniteDimensional ℚ_[(q : ℕ)] K ∧
        ∀ s : primeLocalGaloisGroup q, s ∈ K.fixingSubgroup → M.ρ s m = m := by exact @_root_.P2MW.S_ExtCitation_forall_exists_finiteDimensional_primeLocalToGlobal_iff.solution q _ k _ M
