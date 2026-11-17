import Tengoku.FltAnthropic.Definitions.Def_CohCarrier_HeckeData
import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting
import Tengoku.FltAnthropic.Theorems.Thm_IharaLemma_nonempty_idempotentSplitting_of_finite
import Tengoku.Seed.RingTheory.Noetherian.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CohCarrier_HeckeData_nonempty_idempotentSplitting_opSubalgebra.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CohCarrier_HeckeData_nonempty_idempotentSplitting_opSubalgebra

set_option autoImplicit false

open scoped IsMulCommutative

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type} [Field k] [Algebra 𝒪 k] (D : CohCarrier.HeckeData 𝒪 V k) :
    Nonempty (IharaLemma.IdempotentSplitting ↥D.opSubalgebra) :=
  haveI : Module.Finite 𝒪 ↥D.opSubalgebra :=
    Module.Finite.of_injective D.opSubalgebra.val.toLinearMap fun _ _ h => Subtype.ext h
  IharaLemma.nonempty_idempotentSplitting_of_finite 𝒪 ↥D.opSubalgebra
