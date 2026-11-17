import Tengoku.FltAnthropic.Definitions.Def_CohCarrier_HeckeData
import Tengoku.Seed.RingTheory.AdicCompletion.Basic
import Tengoku.Seed.RingTheory.Noetherian.Defs
import Tengoku.Seed.RingTheory.Finiteness.Defs
import Tengoku.Seed.LinearAlgebra.FreeModule.Basic
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Defs
import Tengoku.FltAnthropic.P2M.Sol.S_CohCarrier_HeckeData_finite_ML_and_free_ML

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CohCarrier_HeckeData_finite_ML_and_free_ML.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-instance] IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing
attribute [-simp] IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply

set_option autoImplicit false

theorem CohCarrier.HeckeData.finite_ML_and_free_ML {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (D : CohCarrier.HeckeData 𝒪 V k) :
    Module.Finite 𝒪 D.ML ∧ (Module.Free 𝒪 V → Module.Free 𝒪 D.ML) := by exact @_root_.P2MW.S_CohCarrier_HeckeData_finite_ML_and_free_ML.solution 𝒪 _ _ _ _ V _ _ _ k _ _ hk D
