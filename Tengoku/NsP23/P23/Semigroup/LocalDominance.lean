import Tengoku.NsP23.P23.Presentation.LocalDominance
import Tengoku.NsP23.P23.Semigroup.ChosenBaseCanonicalQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Semigroup
noncomputable section
open P23.OneTie P23.Artin P23.Presentation

/-- An actual budget-one normalization, with its own dependent root indices.-/
structure BudgetOneDominantCanonicalRoot (D : FourGeneratedNumericalSemigroup) (i : Fin 4) where
  budgetOne : D.fourBaseBudget i=1
  normalization : BudgetOneOneTieNormalization D i
  root : ↥normalization.roots
  dominant : IsDominantRoot normalization.roots root
  typeTwoOrThree : normalization.roots.card=2 ∨ normalization.roots.card=3
  typeEqSemigroup : normalization.roots.card=D.semigroupType
  kernelMuEqRho : idealGeneratorMu (finitePresentationIdeal (k:=ℚ) normalization.roots)=D.semigroupRho

/--
@isnad1 id=nonempty.4h2v.s6.cbb65f8f39f3 from=translated src=- shape=cbd11343 vocab=67be7a3a
-/
theorem budgetOneDominantCanonicalRoot (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hB : D.fourBaseBudget i=1) (ht : D.semigroupType=2 ∨ D.semigroupType=3)
    (hn : SemigroupNearlyGorenstein D) (hr : D.semigroupType+4≤D.semigroupRho) :
    Nonempty (BudgetOneDominantCanonicalRoot D i) := by
  obtain ⟨B⟩ := budgetOneOneTieNormalization D i hB
  have he : B.roots.card=D.semigroupType :=
    (quotientType_eq_rootCard (k:=ℚ) B.roots B.roots_nonempty
      B.coordinates.liveDomain B.roots_live B.roots_antichain).symm.trans
      (B.canonicalOneTieType_eq_chosenBaseType.trans (chosenBaseType_eq_semigroupType D i))
  have hc : B.roots.card=2 ∨ B.roots.card=3 := by rwa [he]
  have hng := B.canonicalOneTie_ng_iff.mp
    (semigroupNearlyGorenstein_to_chosenBaseNearlyGorenstein D i hn)
  have hm : B.roots.card+4 ≤ idealGeneratorMu (finitePresentationIdeal (k:=ℚ) B.roots) := by
    rwa [he,B.canonicalKernelMu_eq_rho]
  obtain ⟨s,hs,hd⟩ := oneTie_ng_kernel_mu_ge_type_plus_four_has_dominant
    B.roots B.roots_nonempty B.coordinates.liveDomain B.roots_live B.roots_antichain hc hng hm
  exact ⟨⟨hB,B,⟨s,hs⟩,hd,hc,he,B.canonicalKernelMu_eq_rho⟩⟩

end
end P23.Semigroup
