import Tengoku.NsP23.P23.Semigroup.GlobalToricPresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact global numerical-semigroup presentation size

`semigroupRho` is defined by minimization over finite genuine same-fiber
presentations.  Its Betti-sum formula is proved afterwards.
-/

namespace P23.Semigroup

open scoped BigOperators

noncomputable section

open FourGeneratedNumericalSemigroup

namespace FourGeneratedNumericalSemigroup

variable (D : FourGeneratedNumericalSemigroup)

private theorem relationsAtDegree_pairwiseDisjoint
    (R : Finset (SemigroupPresentationRelation D)) :
    ((Finset.univ : Finset D.BettiDegreeIndex) : Set D.BettiDegreeIndex).PairwiseDisjoint
      (fun d => D.relationsAtDegree R d.1) := by
  classical
  intro d _ e _ hde
  change Disjoint (D.relationsAtDegree R d.1)
    (D.relationsAtDegree R e.1)
  rw [Finset.disjoint_left]
  intro r hrd hre
  have hd := (D.mem_relationsAtDegree.mp hrd).2
  have he := (D.mem_relationsAtDegree.mp hre).2
  apply hde
  apply Subtype.ext
  exact hd.symm.trans he

private theorem sum_relationsAtDegree_card_le
    (R : Finset (SemigroupPresentationRelation D)) :
    (∑ d : D.BettiDegreeIndex, (D.relationsAtDegree R d.1).card) ≤ R.card := by
  classical
  let U := (Finset.univ : Finset D.BettiDegreeIndex).biUnion
    (fun d => D.relationsAtDegree R d.1)
  have hU : U ⊆ R := by
    intro r hr
    rcases Finset.mem_biUnion.mp hr with ⟨d, -, hdr⟩
    exact (D.mem_relationsAtDegree.mp hdr).1
  have hcard := Finset.card_biUnion (D.relationsAtDegree_pairwiseDisjoint R)
  change U.card = _ at hcard
  calc
    (∑ d : D.BettiDegreeIndex, (D.relationsAtDegree R d.1).card) =
        U.card := hcard.symm
    _ ≤ R.card := Finset.card_le_card hU

/-- Universal lower bound for every finite genuine semigroup presentation.
@isnad1 id=le.1h2v.s5.12441d4c41bc from=translated src=- shape=9f3ed6cc vocab=9def19bc
-/
theorem globalPresentation_card_lower_bound
    (R : Finset (SemigroupPresentationRelation D))
    (hR : D.IsSemigroupPresentation (k := ℚ) R) :
    (∑ d : D.BettiDegreeIndex, D.bettiContribution d.1) ≤ R.card := by
  calc
    (∑ d : D.BettiDegreeIndex, D.bettiContribution d.1) ≤
        ∑ d : D.BettiDegreeIndex, (D.relationsAtDegree R d.1).card := by
      apply Finset.sum_le_sum
      intro d _
      exact D.globalPresentation_degree_card_lower_bound R hR d.2
    _ ≤ R.card := D.sum_relationsAtDegree_card_le R

/-- A cardinal is attained by a finite genuine same-fiber presentation.-/
def HasSemigroupPresentationCard (n : ℕ) : Prop :=
  ∃ R : Finset (SemigroupPresentationRelation D),
    D.IsSemigroupPresentation (k := ℚ) R ∧ R.card = n

/--
@isnad1 id=ex.0h1v.s3.683e3c936713 from=translated src=- shape=4e3b816f vocab=60abf918
-/
theorem exists_semigroupPresentationCard :
    ∃ n, D.HasSemigroupPresentationCard n := by
  obtain ⟨R, hR⟩ := D.exists_finite_semigroupPresentation
  exact ⟨R.card, R, hR, rfl⟩

/-- Least cardinality of a finite genuine factorization-relation
presentation.  This definition does not mention Betti degrees.-/
noncomputable def semigroupRho (D : FourGeneratedNumericalSemigroup) : ℕ := by
  classical
  exact Nat.find D.exists_semigroupPresentationCard

/--
@isnad1 id=hassemig.0h1v.s2.436229dd01f4 from=translated src=- shape=9d44d080 vocab=85c7becf
-/
theorem semigroupRho_spec : D.HasSemigroupPresentationCard D.semigroupRho :=
  by
    classical
    exact Nat.find_spec D.exists_semigroupPresentationCard

/--
@isnad1 id=le.1h2v.s4.bbda85669696 from=translated src=- shape=2f03d7dc vocab=c8b8428d
-/
theorem semigroupRho_le_of_presentation
    (R : Finset (SemigroupPresentationRelation D))
    (hR : D.IsSemigroupPresentation (k := ℚ) R) :
    D.semigroupRho ≤ R.card := by
  classical
  exact Nat.find_min' D.exists_semigroupPresentationCard ⟨R, hR, rfl⟩

/-- Exact global Betti-sum formula for the genuine minimal presentation
cardinality.
@isnad1 id=eq.0h1v.s4.c4abe0677dbb from=translated src=- shape=9ae97a7d vocab=24e17ff3
-/
theorem semigroupRho_eq_sum_bettiContribution :
    D.semigroupRho =
      ∑ d : D.BettiDegreeIndex, D.bettiContribution d.1 := by
  apply le_antisymm
  · rw [← D.globalConnectorFinset_card]
    exact D.semigroupRho_le_of_presentation D.globalConnectorFinset
      D.globalConnectorFinset_isPresentation
  · obtain ⟨R, hR, hcard⟩ := D.semigroupRho_spec
    rw [← hcard]
    exact D.globalPresentation_card_lower_bound R hR

abbrev rho : ℕ := D.semigroupRho

/--
@isnad1 id=eq.0h1v.s3.170aaf33bc11 from=translated src=- shape=dea8492f vocab=575be5ad
-/
theorem globalConnectorFinset_card_eq_rho :
    D.globalConnectorFinset.card = D.semigroupRho := by
  rw [D.globalConnectorFinset_card, D.semigroupRho_eq_sum_bettiContribution]

private def budgetDegreeToBetti : D.BudgetDegree → D.BettiDegreeIndex :=
  fun d => ⟨d.1, d.2.1⟩

private theorem budgetDegreeToBetti_injective :
    Function.Injective D.budgetDegreeToBetti := by
  intro d e h
  apply Subtype.ext
  exact congrArg (fun z : D.BettiDegreeIndex => z.1) h

/-- The contribution visible after omitting one generator is bounded by the
global presentation size.
@isnad1 id=le.0h2v.s4.c377b73e594d from=translated src=- shape=c72097d8 vocab=e47ef38c
-/
theorem fourBaseBudget_le_rho (i : Fin 4) :
    D.fourBaseBudget i ≤ D.semigroupRho := by
  rw [D.semigroupRho_eq_sum_bettiContribution]
  calc
    D.fourBaseBudget i ≤
        ∑ d : D.BudgetDegree, D.bettiContribution d.1 := by
      unfold fourBaseBudget
      apply Finset.sum_le_sum
      intro d _
      split <;> omega
    _ = ((Finset.univ : Finset D.BudgetDegree).image
          D.budgetDegreeToBetti).sum (fun e => D.bettiContribution e.1) := by
      symm
      rw [Finset.sum_image]
      · rfl
      · intro a _ b _ hab
        exact D.budgetDegreeToBetti_injective hab
    _ ≤ ∑ d : D.BettiDegreeIndex, D.bettiContribution d.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _
      · intro _ _ _
        exact Nat.zero_le _

/--
@isnad1 id=le.0h1v.s5.23d611c22707 from=translated src=- shape=a351062a vocab=e295fe19
-/
theorem fourBaseBudget_sum_le_four_global :
    (∑ i : Fin 4, D.fourBaseBudget i) ≤ 4 :=
  D.fourBaseBudget_sum_le_four

/-- Scope-explicit Run25 import boundary.-/
structure GlobalToricPresentationBridge : Prop where
  connectorGeneration : ∀ (k : Type*) [Field k],
    D.toricIdeal (k := k) =
      Ideal.span (Set.range (D.globalConnectorBinomial (k := k)))
  finitePresentation : ∃ R : Finset (SemigroupPresentationRelation D),
    D.IsSemigroupPresentation (k := ℚ) R
  finiteBetti : Finite D.BettiDegreeIndex
  connectorPresentation : ∀ (k : Type*) [Field k],
    D.IsSemigroupPresentation (k := k) D.globalConnectorFinset
  connectorCard : D.globalConnectorFinset.card =
    ∑ d : D.BettiDegreeIndex, D.bettiContribution d.1
  universalLower : ∀ R : Finset (SemigroupPresentationRelation D),
    D.IsSemigroupPresentation (k := ℚ) R →
      (∑ d : D.BettiDegreeIndex, D.bettiContribution d.1) ≤ R.card
  rhoFormula : D.semigroupRho =
    ∑ d : D.BettiDegreeIndex, D.bettiContribution d.1
  budgetCompatibility : ∀ i, D.fourBaseBudget i ≤ D.semigroupRho

/--
@isnad1 id=globalto.0h1v.s2.25f98f313883 from=translated src=- shape=5c11bb93 vocab=0d123774
-/
theorem globalToricPresentationBridge : D.GlobalToricPresentationBridge where
  connectorGeneration := fun k _ =>
    D.toricIdeal_eq_span_globalConnectorBinomials (k := k)
  finitePresentation := D.exists_finite_semigroupPresentation
  finiteBetti := D.finite_bettiDegrees
  connectorPresentation := fun k _ =>
    D.globalConnectorFinset_isPresentation (k := k)
  connectorCard := D.globalConnectorFinset_card
  universalLower := fun R hR => D.globalPresentation_card_lower_bound R hR
  rhoFormula := D.semigroupRho_eq_sum_bettiContribution
  budgetCompatibility := fun i => D.fourBaseBudget_le_rho i

end FourGeneratedNumericalSemigroup

end

end P23.Semigroup
