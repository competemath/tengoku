import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ValuationSubring_CompletionRatClosure
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IsDedekindDomain NumberField ValuationSubring

/--
@isnad1 id=ex.2h3v.s17.e27010434e7d from=translated src=- shape=7f640a36 vocab=7ba1d3a7
-/
theorem ValuationSubring.exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ e : v.adicCompletion ℚ ≃+* ↥(ratClosure A),
      (∀ q : ℚ, ((e (algebraMap ℚ (v.adicCompletion ℚ) q) : ↥(ratClosure A)) : A.valuation.Completion) =
        ((q : AlgebraicClosure ℚ) : A.valuation.Completion)) ∧
      (∀ x : v.adicCompletion ℚ,
        x ∈ v.adicCompletionIntegers ℚ ↔ e x ∈ (Valued.v.comap (ratClosure A).subtype).valuationSubring) ∧
      Continuous e ∧ Continuous e.symm := by exact @_root_.P2MW.S_ValuationSubring_exists_ringEquiv_adicCompletion_ratClosure_of_liesOverPrime.solution r _ A hA v hv
