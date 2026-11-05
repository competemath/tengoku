import Tengoku.NsP23.P23.Semigroup.ChosenBaseRelationSpace
import Tengoku.NsP23.P23.Semigroup.ChosenBaseTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Universal polynomial-ideal minimality for every genuine chosen base.
No normalization or H-L5 conclusion belongs to this interface. -/
namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup P23.Presentation
variable {k : Type*} [Field k]
variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem chosenBaseDefiningIdeal_generator_card_lower_bound (G : Finset (TailPoly k))
    (hG : Ideal.span (↑G : Set (TailPoly k)) = chosenBaseDefiningIdeal D i) :
    D.semigroupRho ≤ G.card := by
  have h := finrank_le_of_span_eq_top (chosenBaseGeneratorClasses_span_eq_top D i G hG)
  rw [chosenBaseRelationSpace_finrank] at h
  simpa using h

theorem specializedConnectorFinset_card_eq_rho :
    (specializedConnectorFinset (k := k) D i).card = D.semigroupRho :=
  Nat.le_antisymm (specializedConnectorFinset_card_le_rho D i)
    (chosenBaseDefiningIdeal_generator_card_lower_bound D i _ (specializedConnectorFinset_span_eq D i))

theorem specializedConnectorPolynomial_injective :
    Function.Injective (D.specializedConnectorPolynomial (k := k) i) := by
  intro g h he
  by_contra hn
  have hc := congrArg (chosenBaseConnectorCoeff (k := k) D i g) he
  rw [chosenBaseConnectorCoeff_specializedConnector,
    chosenBaseConnectorCoeff_specializedConnector] at hc
  simp only [ite_eq_left rfl, ite_eq_right hn] at hc
  exact one_ne_zero hc

theorem chosenBaseDefiningIdeal_minimalGeneratorCard :
    HasMinimalGeneratorCard (chosenBaseDefiningIdeal (k := k) D i) D.semigroupRho :=
  ⟨⟨specializedConnectorFinset D i, specializedConnectorFinset_span_eq D i,
    specializedConnectorFinset_card_eq_rho D i⟩,
    chosenBaseDefiningIdeal_generator_card_lower_bound D i⟩

abbrev chosenBaseMu := idealGeneratorMu (chosenBaseDefiningIdeal (k := k) D i)

theorem chosenBaseDefiningIdeal_mu_eq_rho :
    idealGeneratorMu (chosenBaseDefiningIdeal (k := k) D i) = D.semigroupRho := by
  have hmin := chosenBaseDefiningIdeal_minimalGeneratorCard (k := k) D i
  rcases hmin.1 with ⟨G₀, hG₀, hcard₀⟩
  have hex : ∃ n : ℕ, ∃ G : Finset (TailPoly k),
      Ideal.span (↑G : Set (TailPoly k)) = chosenBaseDefiningIdeal D i ∧ G.card = n :=
    ⟨D.semigroupRho, G₀, hG₀, hcard₀⟩
  rw [idealGeneratorMu, dite_eq_left hex]
  apply Nat.le_antisymm
  · exact Nat.find_min' hex ⟨G₀, hG₀, hcard₀⟩
  · rcases Nat.find_spec hex with ⟨G,hG,hcard⟩
    rw [← hcard]
    exact hmin.2 G hG

theorem chosenBase_mu_eq_rho_Q :
    idealGeneratorMu (chosenBaseDefiningIdeal (k := ℚ) D i) = D.semigroupRho :=
  chosenBaseDefiningIdeal_mu_eq_rho D i

/-- The chosen-base arbitrary-polynomial interpretation; not the optional toric mu claim.-/
def SemigroupRhoAsChosenBaseIdealMu : Prop :=
  ∀ i : Fin 4, HasMinimalGeneratorCard (chosenBaseDefiningIdeal (k := k) D i) D.semigroupRho ∧
    idealGeneratorMu (chosenBaseDefiningIdeal (k := k) D i) = D.semigroupRho

theorem semigroupRhoAsChosenBaseIdealMu : SemigroupRhoAsChosenBaseIdealMu (k := k) D :=
  fun i => ⟨chosenBaseDefiningIdeal_minimalGeneratorCard D i, chosenBaseDefiningIdeal_mu_eq_rho D i⟩

def MinimalMonomialChosenBasePresentation : Prop :=
  ∃ G : Finset (TailPoly k), Ideal.span (↑G : Set (TailPoly k)) = chosenBaseDefiningIdeal D i ∧
    G.card = D.semigroupRho ∧
    (∀ p ∈ G, ∃ u : Fin 3 →₀ ℕ, p = MvPolynomial.monomial u 1 ∧ p ≠ 0) ∧
    HasMinimalGeneratorCard (chosenBaseDefiningIdeal (k := k) D i) D.semigroupRho

theorem chosenBase_minimalMonomialPresentation_of_budget_zero
    (hB : D.fourBaseBudget i = 0) : MinimalMonomialChosenBasePresentation (k := k) D i := by
  let G := (specializedConnectorFinset (k := k) D i).image Neg.neg
  have hspan : Ideal.span (↑G : Set (TailPoly k)) = chosenBaseDefiningIdeal D i := by
    rw [← specializedConnectorFinset_span_eq (k := k) D i]
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      exact neg_mem (Ideal.subset_span hq)
    · apply Ideal.span_le.mpr
      intro p hp
      have hneg : -p ∈ Ideal.span (↑G : Set (TailPoly k)) :=
        Ideal.subset_span (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
      simpa using neg_mem hneg
  refine ⟨G,hspan,?_,?_,chosenBaseDefiningIdeal_minimalGeneratorCard D i⟩
  · rw [Finset.card_image_of_injective _ neg_injective, specializedConnectorFinset_card_eq_rho]
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hq
    have hg := D.specializedConnector_isMonomial_of_base_mem_support (k := k) i g
      (D.all_connectors_external_of_budget_zero i hB g)
    exact ⟨D.connectorRightTail i g, by simp [hg.1], neg_ne_zero.mpr hg.2⟩

/-- A monomial cannot have the two distinct nonzero endpoint coefficients of a live binomial,
including in characteristic two.-/
theorem neg_monomial_not_live (w : Fin 3 →₀ ℕ) :
    ¬D.LiveTailBinomial (k := k) i (-MvPolynomial.monomial w 1) := by
  rintro ⟨u,v,he,_,_,_,huv,_⟩
  have hcu := congrArg (MvPolynomial.coeff u) he
  have hw : w = u := by
    by_contra hwu
    have : (0 : k) = 1 := by simpa [MvPolynomial.coeff_monomial, hwu, Ne.symm hwu, huv, Ne.symm huv] using hcu
    exact zero_ne_one this
  subst w
  have hcv := congrArg (MvPolynomial.coeff v) he
  have : (0 : k) = -1 := by simpa [MvPolynomial.coeff_monomial, huv, Ne.symm huv] using hcv
  exact neg_ne_zero.mpr one_ne_zero this.symm

def MinimalOneLiveBinomialChosenBasePresentation : Prop :=
  ∃ (G : Finset (TailPoly k)) (g : D.BaseAdaptedGlobalConnector i),
    Ideal.span (↑G : Set (TailPoly k)) = chosenBaseDefiningIdeal D i ∧ G.card = D.semigroupRho ∧
    D.specializedConnectorPolynomial (k := k) i g ∈ G ∧
    D.LiveTailBinomial (k := k) i (D.specializedConnectorPolynomial i g) ∧
    (∀ p ∈ G, D.LiveTailBinomial (k := k) i p ↔ p = D.specializedConnectorPolynomial i g) ∧
    (∀ p ∈ G, p ≠ D.specializedConnectorPolynomial i g →
      ∃ w, p = -MvPolynomial.monomial w 1 ∧ p ≠ 0) ∧
    (G.erase (D.specializedConnectorPolynomial i g)).card = D.semigroupRho - 1 ∧
    ((D.connectorLeftTail i g).support.card = 1 ∨ (D.connectorRightTail i g).support.card = 1) ∧
    HasMinimalGeneratorCard (chosenBaseDefiningIdeal (k := k) D i) D.semigroupRho

theorem chosenBase_minimal_one_live_binomial_of_budget_one
    (hB : D.fourBaseBudget i = 1) : MinimalOneLiveBinomialChosenBasePresentation (k := k) D i := by
  obtain ⟨g,hg,huniq⟩ := D.existsUnique_internal_connector_of_budget_one i hB
  have hlive := D.specializedConnector_isLiveBinomial_of_base_not_mem_support (k := k) i g hg
  have hmem : D.specializedConnectorPolynomial (k := k) i g ∈ specializedConnectorFinset D i :=
    Finset.mem_image.mpr ⟨g,Finset.mem_univ _,rfl⟩
  have external : ∀ h : D.BaseAdaptedGlobalConnector i, h ≠ g →
      D.specializedConnectorPolynomial (k := k) i h = -MvPolynomial.monomial (D.connectorRightTail i h) 1 ∧
      D.specializedConnectorPolynomial (k := k) i h ≠ 0 := by
    intro h hne
    apply D.specializedConnector_isMonomial_of_base_mem_support
    by_contra hi
    exact hne (huniq h hi)
  refine ⟨specializedConnectorFinset D i,g,specializedConnectorFinset_span_eq D i,
    specializedConnectorFinset_card_eq_rho D i,hmem,hlive,?_,?_,?_,
    D.internal_connector_pure_side i g hg,chosenBaseDefiningIdeal_minimalGeneratorCard D i⟩
  · intro p hp
    obtain ⟨h,_,rfl⟩ := Finset.mem_image.mp hp
    constructor
    · intro hh
      by_cases he : h = g
      · rw [he]
      · rw [(external h he).1] at hh
        exact False.elim (neg_monomial_not_live D i _ hh)
    · intro he
      rw [he]
      exact hlive
  · intro p hp hne
    obtain ⟨h,_,rfl⟩ := Finset.mem_image.mp hp
    have he : h ≠ g := fun he => hne (congrArg (D.specializedConnectorPolynomial i) he)
    exact ⟨_,external h he⟩
  · rw [Finset.card_erase_of_mem hmem, specializedConnectorFinset_card_eq_rho]

theorem semigroup_type_three_ng_chosenBase_fullBridge
    (htype : D.semigroupType = 3) (hNG : SemigroupNearlyGorenstein D) :
    chosenBaseType (k := ℚ) D i = 3 ∧ ChosenBaseNearlyGorenstein (k := ℚ) D i ∧
      idealGeneratorMu (chosenBaseDefiningIdeal (k := ℚ) D i) = D.semigroupRho := by
  obtain ⟨ht,hn⟩ := semigroup_type_three_ng_gives_chosenBase_type_three_ng (k := ℚ) D i htype hNG
  exact ⟨ht,hn,chosenBase_mu_eq_rho_Q D i⟩

structure ChosenBaseMinimalityBridge : Prop where
  exactSubmodule : ∀ f : chosenBaseDefiningIdeal (k := k) D i,
    f ∈ chosenBaseRelationSubmodule D i ↔ f.1 ∈ polyVariableIdeal * chosenBaseDefiningIdeal D i
  basis : ∀ g, chosenBaseRelationBasis (k := k) D i g = displayedChosenBaseRelation D i g
  dimension : Module.finrank k (ChosenBaseRelationSpace k D i) = D.semigroupRho
  arbitraryLower : ∀ G : Finset (TailPoly k), Ideal.span (↑G : Set (TailPoly k)) =
    chosenBaseDefiningIdeal D i → D.semigroupRho ≤ G.card
  exactCard : (specializedConnectorFinset (k := k) D i).card = D.semigroupRho
  minimal : HasMinimalGeneratorCard (chosenBaseDefiningIdeal (k := k) D i) D.semigroupRho
  numeric : idealGeneratorMu (chosenBaseDefiningIdeal (k := k) D i) = D.semigroupRho
  allBaseSemantic : SemigroupRhoAsChosenBaseIdealMu (k := k) D
  budgetZero : D.fourBaseBudget i = 0 → MinimalMonomialChosenBasePresentation (k := k) D i
  budgetOne : D.fourBaseBudget i = 1 → MinimalOneLiveBinomialChosenBasePresentation (k := k) D i

theorem chosenBaseMinimalityBridge : ChosenBaseMinimalityBridge (k := k) D i where
  exactSubmodule := mem_chosenBaseRelationSubmodule_iff D i
  basis := chosenBaseRelationBasis_apply D i
  dimension := chosenBaseRelationSpace_finrank D i
  arbitraryLower := chosenBaseDefiningIdeal_generator_card_lower_bound D i
  exactCard := specializedConnectorFinset_card_eq_rho D i
  minimal := chosenBaseDefiningIdeal_minimalGeneratorCard D i
  numeric := chosenBaseDefiningIdeal_mu_eq_rho D i
  allBaseSemantic := semigroupRhoAsChosenBaseIdealMu D
  budgetZero := chosenBase_minimalMonomialPresentation_of_budget_zero D i
  budgetOne := chosenBase_minimal_one_live_binomial_of_budget_one D i

end
end P23.Semigroup
