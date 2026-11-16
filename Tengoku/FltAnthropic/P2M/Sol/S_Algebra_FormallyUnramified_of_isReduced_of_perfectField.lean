import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_FormallyUnramified_of_isReduced_of_perfectField.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_FormallyUnramified_of_isReduced_of_perfectField

namespace B7

/--
@isnad1 id=formally.0h2v.s6.e004f77110f2 from=translated src=- shape=fa9ae7f2 vocab=86b44ac9
-/
theorem formallyUnramified_of_isReduced (K B : Type*) [Field K]
    [PerfectField K] [CommRing B] [Algebra K B] [Module.Finite K B] [IsReduced B] :
    Algebra.FormallyUnramified K B := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite K B
  haveI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _

  haveI : ∀ I : MaximalSpectrum B, Algebra.FormallyUnramified K (B ⧸ I.asIdeal) := by
    intro I
    letI : Field (B ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Module.Finite K (B ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
        (Ideal.Quotient.mkₐ_surjective K I.asIdeal)
    haveI : Algebra.IsAlgebraic K (B ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite K _
    haveI : Algebra.IsSeparable K (B ⧸ I.asIdeal) := Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact Algebra.FormallyUnramified.of_isSeparable K (B ⧸ I.asIdeal)
  haveI : Algebra.FormallyUnramified K ((I : MaximalSpectrum B) → B ⧸ I.asIdeal) :=
    (Algebra.FormallyUnramified.pi_iff (fun I : MaximalSpectrum B => B ⧸ I.asIdeal)).mpr
      (fun I => inferInstance)

  let e : B ≃ₐ[K] ((I : MaximalSpectrum B) → B ⧸ I.asIdeal) :=
    AlgEquiv.ofRingEquiv (f := IsArtinianRing.equivPi B) (fun r => by
      ext I
      rfl)
  exact Algebra.FormallyUnramified.of_equiv e.symm
end B7

/--
@isnad1 id=formally.0h2v.s6.e004f77110f2 from=translated src=- shape=fa9ae7f2 vocab=86b44ac9
-/
theorem solution (K B : Type*) [Field K] [PerfectField K] [CommRing B] [Algebra K B] [Module.Finite K B] [IsReduced B] : Algebra.FormallyUnramified K B :=
  B7.formallyUnramified_of_isReduced K B
