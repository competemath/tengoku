import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open IsLocalRing
/--
@isnad1 id=eq.2h2v.s7.cf6cfcd8d902 from=translated src=- shape=e213f437 vocab=7421f17c
-/
theorem IsLocalRing.ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by exact @_root_.P2MW.S_IsLocalRing_ringKrullDim_quotient_span_singleton_add_one_of_forall_minimalPrimes_notMem.solution R _ _ _ x hx hxmin
