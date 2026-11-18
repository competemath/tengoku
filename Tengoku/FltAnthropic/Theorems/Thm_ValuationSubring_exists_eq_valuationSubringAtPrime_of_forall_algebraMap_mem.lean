import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.2h3v.s8.f4fb827e8181 from=translated src=- shape=e505169e vocab=172371ba
-/
theorem ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (V : ValuationSubring K) (hRV : ∀ r : R, algebraMap R K r ∈ V) (hV : V ≠ ⊤) :
    ∃ v : IsDedekindDomain.HeightOneSpectrum R, V = v.valuationSubringAtPrime K ∧
      ∀ r : R, r ∈ v.asIdeal ↔ algebraMap R K r ∈ V.nonunits := by exact @_root_.P2MW.S_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem.solution R K _ _ _ _ _ V hRV hV
