import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ValuationSubring_CompletionRatClosure
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_valuationSubring_ratClosure_and_irreducible_natCast_and_finite_quotient_of_liesOverPrime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_isDiscreteValuationRing_valuationSubring_ratClosure_and_irreducible_natCast_and_finite_quotient_of_liesOverPrime.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open ValuationSubring

/--
@isnad1 id=and.1h2v.s18.8810864910b5 from=translated src=- shape=ba0cd517 vocab=05cd1f8a
-/
theorem ValuationSubring.isDiscreteValuationRing_valuationSubring_ratClosure_and_irreducible_natCast_and_finite_quotient_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    (⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)) ∈ (Valued.v.comap (ratClosure A).subtype).valuationSubring ∧
    IsDiscreteValuationRing ↥(Valued.v.comap (ratClosure A).subtype).valuationSubring ∧
    (∀ h : (⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)) ∈ (Valued.v.comap (ratClosure A).subtype).valuationSubring,
      Irreducible (⟨(⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)), h⟩ : ↥(Valued.v.comap (ratClosure A).subtype).valuationSubring) ∧
      Finite (↥(Valued.v.comap (ratClosure A).subtype).valuationSubring ⧸ Ideal.span {(⟨(⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)), h⟩ : ↥(Valued.v.comap (ratClosure A).subtype).valuationSubring)}) ∧
      Nat.card (↥(Valued.v.comap (ratClosure A).subtype).valuationSubring ⧸ Ideal.span {(⟨(⟨(r : A.valuation.Completion), natCast_mem_ratClosure A r⟩ : ↥(ratClosure A)), h⟩ : ↥(Valued.v.comap (ratClosure A).subtype).valuationSubring)}) = r) := by exact @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_valuationSubring_ratClosure_and_irreducible_natCast_and_finite_quotient_of_liesOverPrime.solution r _ A hA
