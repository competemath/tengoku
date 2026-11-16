import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_Etale_of_formallyUnramified_residueField_baseChange.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_Etale_of_formallyUnramified_residueField_baseChange
open scoped TensorProduct

/--
@isnad1 id=etale.1h2v.s8.7a2f7c5c4449 from=translated src=- shape=ebab5dda vocab=7634a95e
-/
theorem solution (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S]
    (h : Algebra.FormallyUnramified (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S)) :
    Algebra.Etale R S := by
  haveI := Algebra.FormallyUnramified.of_residueField_baseChange_of_finite R S h
  haveI : Module.Free R S := Module.free_of_flat_of_isLocalRing
  haveI : Module.FinitePresentation R S := Module.finitePresentation_of_projective R S
  haveI : Algebra.FinitePresentation R S := inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat
