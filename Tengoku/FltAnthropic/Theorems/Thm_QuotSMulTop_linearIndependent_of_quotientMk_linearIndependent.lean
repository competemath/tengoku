import Tengoku.Seed.RingTheory.LocalRing.Module
import Tengoku.Seed.LinearAlgebra.Dimension.StrongRankCondition
import Tengoku.Seed.RingTheory.Regular.IsSMulRegular
import Tengoku.Seed.RingTheory.Regular.RegularSequence
import Tengoku.FltAnthropic.P2M.Sol.S_QuotSMulTop_linearIndependent_of_quotientMk_linearIndependent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_QuotSMulTop_linearIndependent_of_quotientMk_linearIndependent.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped Pointwise
/--
@isnad1 id=linearin.3h5v.s10.44eef595c360 from=translated src=- shape=61f1aab6 vocab=f2faa9e7
-/
theorem QuotSMulTop.linearIndependent_of_quotientMk_linearIndependent {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [IsNoetherianRing R] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) {ι : Type*} [Fintype ι] (m : ι → M) (hli : LinearIndependent (R ⧸ Ideal.span {x}) (fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M))) :
    LinearIndependent R m := by exact @_root_.P2MW.S_QuotSMulTop_linearIndependent_of_quotientMk_linearIndependent.solution R _ M _ _ _ _ x hx hreg ι _ m hli
