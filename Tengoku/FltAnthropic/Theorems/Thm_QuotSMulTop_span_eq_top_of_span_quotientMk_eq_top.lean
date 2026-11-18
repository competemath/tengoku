import Tengoku.Seed.RingTheory.LocalRing.Module
import Tengoku.Seed.LinearAlgebra.Dimension.StrongRankCondition
import Tengoku.Seed.RingTheory.Regular.IsSMulRegular
import Tengoku.Seed.RingTheory.Regular.RegularSequence
import Tengoku.FltAnthropic.P2M.Sol.S_QuotSMulTop_span_eq_top_of_span_quotientMk_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_QuotSMulTop_span_eq_top_of_span_quotientMk_eq_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped Pointwise
theorem QuotSMulTop.span_eq_top_of_span_quotientMk_eq_top {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) {ι : Type*} (m : ι → M) (hspan : Submodule.span (R ⧸ Ideal.span {x}) (Set.range fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) = ⊤) :
    Submodule.span R (Set.range m) = ⊤ := by exact @_root_.P2MW.S_QuotSMulTop_span_eq_top_of_span_quotientMk_eq_top.solution R _ M _ _ _ _ x hx ι m hspan
