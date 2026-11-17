import Tengoku.Seed.RingTheory.Etale.Field
import Tengoku.Seed.FieldTheory.Perfect
import Tengoku.Seed.RingTheory.HopfAlgebra.Basic
import Tengoku.FltAnthropic.Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_algebra_etale_of_module_finite_of_charZero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_algebra_etale_of_module_finite_of_charZero

set_option maxHeartbeats 3200000

attribute [local instance] Ideal.Quotient.field

/--
@isnad1 id=etale.0h2v.s7.c7a48a87e1ec from=translated src=- shape=44d74c9d vocab=1d4ab7c7
-/
theorem solution
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] :
    Algebra.Etale K A := by

  haveI : Algebra.FiniteType K A := inferInstance

  haveI : IsReduced A := HopfAlgebra.isReduced_of_finiteType_of_charZero K A

  haveI : IsArtinianRing A := .of_finite K A
  haveI : Finite (MaximalSpectrum A) := inferInstance

  have hI (I : MaximalSpectrum A) : Algebra.FormallyEtale K (A ⧸ I.asIdeal) := by
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    haveI : Module.Finite K (A ⧸ I.asIdeal) := Module.Finite.quotient K _
    haveI : Algebra.IsAlgebraic K (A ⧸ I.asIdeal) := Algebra.IsIntegral.isAlgebraic
    haveI : Algebra.IsSeparable K (A ⧸ I.asIdeal) := inferInstance
    exact Algebra.FormallyEtale.of_isSeparable K (A ⧸ I.asIdeal)
  refine ⟨?_, ?_⟩
  ·
    exact Algebra.FormallyEtale.of_equiv
      ((IsArtinianRing.equivPi A).restrictScalars K).symm
  ·
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
