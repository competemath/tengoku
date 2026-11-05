import Tengoku.NsP23.P23.Semigroup.BettiFibers
import Tengoku.Seed.Tactic.IntervalCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The combinatorial four-base Betti budget

All statements in this module count factorization components and supports.
They do not assert toric-ideal or polynomial-presentation minimality.
-/

namespace P23.Semigroup

open scoped BigOperators

noncomputable section

namespace FourGeneratedNumericalSemigroup

variable (D : FourGeneratedNumericalSemigroup)

/--
@isnad1 id=le.0h2v.s3.3cd62aac8a22 from=translated src=- shape=4f17ad3b vocab=a78b9280
-/
theorem supportCard_le_four (d : ℕ) : D.supportCard d ≤ 4 := by
  unfold supportCard
  have hsub : D.combinedSupport d ⊆ Finset.univ := fun _ _ => Finset.mem_univ _
  simpa using Finset.card_le_card hsub

/--
@isnad1 id=eq.0h2v.s5.45d8ef29d437 from=translated src=- shape=9a600aa3 vocab=25713a29
-/
theorem supportCard_eq_componentSupport_sum (d : ℕ) :
    D.supportCard d = ∑ C : D.BettiComponent d, (D.componentSupport C).card := by
  classical
  have hp : (↑(Finset.univ : Finset (D.BettiComponent d)) : Set (D.BettiComponent d)).PairwiseDisjoint
      D.componentSupport := by
    simpa using D.componentSupport_pairwiseDisjoint d
  have h := Finset.card_biUnion (s := (Finset.univ : Finset (D.BettiComponent d)))
    (t := D.componentSupport) hp
  rw [D.biUnion_componentSupport] at h
  simpa [supportCard] using h

/--
@isnad1 id=le.1h2v.s4.ae0cbdeafc2f from=translated src=- shape=739b1af0 vocab=eeaecb24
-/
theorem componentCount_le_supportCard_of_isBetti {d : ℕ}
    (hd : D.IsBettiDegree d) : D.componentCount d ≤ D.supportCard d := by
  classical
  rw [D.supportCard_eq_componentSupport_sum]
  unfold componentCount
  have hsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset (D.BettiComponent d)))
    (f := fun _ => 1) (g := fun C => (D.componentSupport C).card)
    (fun C _ => Finset.card_pos.mpr (D.componentSupport_nonempty_of_isBetti hd C))
  simpa using hsum

/--
@isnad1 id=le.1h2v.s5.b1589f795bd7 from=translated src=- shape=1d976795 vocab=b700ecdf
-/
theorem twice_componentCount_le_supportCard_add_singletons {d : ℕ}
    (hd : D.IsBettiDegree d) :
    2 * D.componentCount d ≤ D.supportCard d + D.singletonComponentCount d := by
  classical
  have hpoint : ∀ C : D.BettiComponent d,
      2 ≤ (D.componentSupport C).card +
        (if D.IsSingletonSupportComponent C then 1 else 0) := by
    intro C
    have hpos : 0 < (D.componentSupport C).card :=
      Finset.card_pos.mpr (D.componentSupport_nonempty_of_isBetti hd C)
    by_cases hcard : (D.componentSupport C).card = 1
    · simp [IsSingletonSupportComponent, hcard]
    · have hge : 2 ≤ (D.componentSupport C).card := by omega
      simp [IsSingletonSupportComponent, hcard, hge]
  have hsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset (D.BettiComponent d))) (fun C _ => hpoint C)
  rw [Finset.sum_add_distrib] at hsum
  have hsupport := D.supportCard_eq_componentSupport_sum d
  have hsingle :
      (∑ C : D.BettiComponent d, if D.IsSingletonSupportComponent C then 1 else 0) =
        D.singletonComponentCount d := by
    unfold singletonComponentCount
    simpa using (Finset.sum_boole
      (fun C : D.BettiComponent d => D.IsSingletonSupportComponent C) Finset.univ)
  rw [← hsupport, hsingle] at hsum
  simpa [componentCount, Nat.mul_comm] using hsum

/-- The local four-variable support inequality from the human Betti budget.
@isnad1 id=le.1h2v.s5.2a2958e9443e from=translated src=- shape=ca1f63ac vocab=2da8cc52
-/
theorem localSupportInequality {d : ℕ} (hd : D.IsBettiDegree d) :
    (4 - D.supportCard d) * (D.componentCount d - 1) ≤
      D.singletonComponentCount d := by
  have hc2 : 2 ≤ D.componentCount d := hd
  have hcv := D.componentCount_le_supportCard_of_isBetti hd
  have hv4 := D.supportCard_le_four d
  have htwice := D.twice_componentCount_le_supportCard_add_singletons hd
  interval_cases hv : D.supportCard d <;> omega

/-- The purely combinatorial contribution `c_d - 1`.-/
def bettiContribution (d : ℕ) : ℕ := D.componentCount d - 1

/--
@isnad1 id=lt.1h2v.s4.c94b07ccbfae from=translated src=- shape=7ac36ccc vocab=24700445
-/
theorem bettiContribution_pos {d : ℕ} (hd : D.IsBettiDegree d) :
    0 < D.bettiContribution d := by
  unfold bettiContribution IsBettiDegree at *
  omega

/--
@isnad1 id=lt.2h2v.s4.be76cdb9a3bf from=translated src=- shape=8ebac54c vocab=99634dd4
-/
theorem singletonComponentCount_pos_of_budget {d : ℕ}
    (hd : D.IsBettiDegree d) (hv : D.supportCard d < 4) :
    0 < D.singletonComponentCount d := by
  have hlocal := D.localSupportInequality hd
  have hc : 0 < D.componentCount d - 1 := by
    unfold IsBettiDegree at hd
    omega
  have hmissing : 0 < 4 - D.supportCard d := by omega
  have hprod : 0 < (4 - D.supportCard d) * (D.componentCount d - 1) :=
    Nat.mul_pos hmissing hc
  omega

/--
@isnad1 id=ex.2h2v.s5.059854d32e09 from=translated src=- shape=3d4e348f vocab=deac8578
-/
theorem exists_singleton_component_of_budget {d : ℕ}
    (hd : D.IsBettiDegree d) (hv : D.supportCard d < 4) :
    ∃ C : D.BettiComponent d, D.IsSingletonSupportComponent C := by
  classical
  have hpos := D.singletonComponentCount_pos_of_budget hd hv
  unfold singletonComponentCount at hpos
  obtain ⟨C, hC⟩ := Finset.card_pos.mp hpos
  exact ⟨C, (Finset.mem_filter.mp hC).2⟩

/-- Only disconnected degrees omitting at least one of four variables can
contribute to a four-base internal combinatorial budget.-/
def BudgetDegree :=
  {d : ℕ // D.IsBettiDegree d ∧ D.supportCard d < 4}

def budgetDegreeSingletonComponent (d : D.BudgetDegree) : D.BettiComponent d.1 :=
  Classical.choose (D.exists_singleton_component_of_budget d.2.1 d.2.2)

/--
@isnad1 id=issingle.0h2v.s4.e44bbbbd11b2 from=translated src=- shape=ea13f59f vocab=646dd422
-/
theorem budgetDegreeSingletonComponent_isSingleton (d : D.BudgetDegree) :
    D.IsSingletonSupportComponent (D.budgetDegreeSingletonComponent d) :=
  Classical.choose_spec (D.exists_singleton_component_of_budget d.2.1 d.2.2)

def budgetDegreeOccurrence (d : D.BudgetDegree) : D.SingletonBettiOccurrence where
  degree := d.1
  isBetti := d.2.1
  component := D.budgetDegreeSingletonComponent d
  singleton := D.budgetDegreeSingletonComponent_isSingleton d

/--
@isnad1 id=injectiv.0h1v.s3.7f1f0d468b8f from=translated src=- shape=ca92e646 vocab=631fe1c3
-/
theorem budgetDegreeOccurrence_injective :
    Function.Injective D.budgetDegreeOccurrence := by
  intro d e h
  apply Subtype.ext
  exact congrArg SingletonBettiOccurrence.degree h

/--
@isnad1 id=finite.0h1v.s2.c6c79a65127e from=translated src=- shape=76a08d12 vocab=3021654c
-/
noncomputable instance budgetDegreeFinite : Finite (D.BudgetDegree) :=
  Finite.of_injective D.budgetDegreeOccurrence D.budgetDegreeOccurrence_injective

noncomputable instance budgetDegreeFintype : Fintype (D.BudgetDegree) :=
  Fintype.ofFinite _

/-- Singleton components occurring over budget degrees.-/
abbrev BudgetSingletonOccurrence :=
  Sigma fun d : D.BudgetDegree =>
    {C : D.BettiComponent d.1 // D.IsSingletonSupportComponent C}

def budgetSingletonToOccurrence (o : D.BudgetSingletonOccurrence) :
    D.SingletonBettiOccurrence where
  degree := o.1.1
  isBetti := o.1.2.1
  component := o.2.1
  singleton := o.2.2

/--
@isnad1 id=injectiv.0h1v.s3.fc9ff9ebea2a from=translated src=- shape=ca92e646 vocab=c9aaee0a
-/
theorem budgetSingletonToOccurrence_injective :
    Function.Injective D.budgetSingletonToOccurrence := by
  rintro ⟨d, C⟩ ⟨e, E⟩ h
  have hde : d = e := Subtype.ext (congrArg SingletonBettiOccurrence.degree h)
  subst e
  have hkey := congrArg
    (fun o : D.SingletonBettiOccurrence =>
      (⟨o.degree, o.component⟩ : Sigma fun n : ℕ => D.BettiComponent n)) h
  have hCE : C.1 = E.1 := by
    simpa [budgetSingletonToOccurrence] using hkey
  have hCE' : C = E := Subtype.ext hCE
  rw [hCE']

noncomputable instance budgetSingletonFiberFintype (d : D.BudgetDegree) :
    Fintype {C : D.BettiComponent d.1 // D.IsSingletonSupportComponent C} :=
  Fintype.ofFinite _

/--
@isnad1 id=eq.0h1v.s6.3f0db9b9cff7 from=translated src=- shape=1224692c vocab=c47f7934
-/
theorem budgetSingletonOccurrence_card_eq_sum :
    Fintype.card (D.BudgetSingletonOccurrence) =
      ∑ d : D.BudgetDegree, D.singletonComponentCount d.1 := by
  classical
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro d _
  unfold singletonComponentCount
  exact Fintype.card_subtype (fun C : D.BettiComponent d.1 =>
    D.IsSingletonSupportComponent C)

/--
@isnad1 id=le.0h1v.s5.7c74a2d8cc22 from=translated src=- shape=b67d16a0 vocab=5543db21
-/
theorem budget_singleton_sum_le_four :
    (∑ d : D.BudgetDegree, D.singletonComponentCount d.1) ≤ 4 := by
  rw [← D.budgetSingletonOccurrence_card_eq_sum]
  exact (Fintype.card_le_of_injective D.budgetSingletonToOccurrence
    D.budgetSingletonToOccurrence_injective).trans
      D.singletonBettiOccurrence_card_le_four

/-- The combinatorial internal budget associated with omitting base `i`.-/
def fourBaseBudget (i : Fin 4) : ℕ :=
  ∑ d : D.BudgetDegree,
    if i ∉ D.combinedSupport d.1 then D.bettiContribution d.1 else 0

/--
@isnad1 id=ex.2h3v.s8.99652f65826a from=translated src=- shape=2ab0a48d vocab=4efd12fb
-/
theorem fourBaseBudget_includes {i : Fin 4} {d : ℕ}
    (hd : D.IsBettiDegree d) (hi : i ∉ D.combinedSupport d) :
    ∃ q : D.BudgetDegree, q.1 = d ∧
      (if i ∉ D.combinedSupport q.1 then D.bettiContribution q.1 else 0) =
        D.bettiContribution d := by
  have hcard : D.supportCard d < 4 := by
    unfold supportCard
    have hproper : D.combinedSupport d ⊂ (Finset.univ : Finset (Fin 4)) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨fun _ _ => Finset.mem_univ _, ?_⟩
      intro heq
      apply hi
      rw [heq]
      exact Finset.mem_univ _
    simpa using Finset.card_lt_card hproper
  let q : D.BudgetDegree := ⟨d, hd, hcard⟩
  exact ⟨q, rfl, by simp [q, hi]⟩

/--
@isnad1 id=eq.0h2v.s7.1235c5b08c7e from=translated src=- shape=6f08cea4 vocab=5a172246
-/
theorem omittedVariableCount (d : ℕ) :
    (Finset.univ.filter fun i : Fin 4 => i ∉ D.combinedSupport d).card =
      4 - D.supportCard d := by
  classical
  rw [Finset.filter_not]
  have hfilter : (Finset.univ.filter fun i : Fin 4 => i ∈ D.combinedSupport d) =
      D.combinedSupport d := by ext i; simp
  rw [hfilter, Finset.card_sdiff]
  simp [supportCard]

/--
@isnad1 id=eq.0h2v.s7.bd64024462df from=translated src=- shape=ea5d7f32 vocab=5afd89e2
-/
theorem sum_omitted_contribution (d : ℕ) :
    (∑ i : Fin 4, if i ∉ D.combinedSupport d then D.bettiContribution d else 0) =
      (4 - D.supportCard d) * D.bettiContribution d := by
  classical
  calc
    (∑ i : Fin 4, if i ∉ D.combinedSupport d then D.bettiContribution d else 0) =
        ∑ i ∈ (Finset.univ.filter fun i : Fin 4 => i ∉ D.combinedSupport d),
          D.bettiContribution d := by
      exact (Finset.sum_filter
        (fun i : Fin 4 => i ∉ D.combinedSupport d)
        (fun _ => D.bettiContribution d)).symm
    _ = (Finset.univ.filter fun i : Fin 4 => i ∉ D.combinedSupport d).card *
          D.bettiContribution d := by
      exact Finset.sum_const_nat (fun _ _ => rfl)
    _ = (4 - D.supportCard d) * D.bettiContribution d := by
      rw [D.omittedVariableCount]

/-- Finite double counting of omitted variables and component contributions.
@isnad1 id=eq.0h1v.s6.c15bbc8a2cf5 from=translated src=- shape=49264af0 vocab=9db9e514
-/
theorem fourBaseBudget_doubleCount :
    (∑ i : Fin 4, D.fourBaseBudget i) =
      ∑ d : D.BudgetDegree,
        (4 - D.supportCard d.1) * D.bettiContribution d.1 := by
  classical
  unfold fourBaseBudget
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  exact D.sum_omitted_contribution d.1

/-- The exact combinatorial four-base budget.
@isnad1 id=le.0h1v.s5.23d611c22707 from=translated src=- shape=a351062a vocab=e295fe19
-/
theorem fourBaseBudget_sum_le_four :
    (∑ i : Fin 4, D.fourBaseBudget i) ≤ 4 := by
  rw [D.fourBaseBudget_doubleCount]
  calc
    (∑ d : D.BudgetDegree,
        (4 - D.supportCard d.1) * D.bettiContribution d.1) ≤
        ∑ d : D.BudgetDegree, D.singletonComponentCount d.1 := by
      apply Finset.sum_le_sum
      intro d _
      exact D.localSupportInequality d.2.1
    _ ≤ 4 := D.budget_singleton_sum_le_four

/--
@isnad1 id=le.0h2v.s4.45a99d7cf7bf from=translated src=- shape=360a1ae1 vocab=5b01faee
-/
theorem fourBaseBudget_le_four (i : Fin 4) : D.fourBaseBudget i ≤ 4 := by
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
    D.fourBaseBudget_sum_le_four

section Connectors

/-- A selected root component in a Betti fiber.-/
def rootComponent {d : ℕ} (hd : D.IsBettiDegree d) : D.BettiComponent d := by
  classical
  apply Classical.choice
  apply Fintype.card_pos_iff.mp
  change 2 ≤ Fintype.card (D.BettiComponent d) at hd
  omega

/-- One star connector for every non-root component.-/
abbrev ComponentConnector {d : ℕ} (hd : D.IsBettiDegree d) :=
  {C : D.BettiComponent d // C ≠ D.rootComponent hd}

noncomputable instance componentConnectorFintype {d : ℕ} (hd : D.IsBettiDegree d) :
    Fintype (D.ComponentConnector hd) := Fintype.ofFinite _

def componentRepresentative {d : ℕ} (C : D.BettiComponent d) :
    D.FactorizationAt d :=
  Classical.choose (SimpleGraph.ConnectedComponent.nonempty_supp C)

/--
@isnad1 id=eq.0h3v.s4.682d0a399a3b from=translated src=- shape=0221f8a5 vocab=3566ad19
-/
theorem componentRepresentative_component {d : ℕ} (C : D.BettiComponent d) :
    D.componentOf (D.componentRepresentative C) = C :=
  (SimpleGraph.ConnectedComponent.mem_supp_iff C _).mp
    (Classical.choose_spec (SimpleGraph.ConnectedComponent.nonempty_supp C))

/-- The representative relation joining the root to a non-root component.-/
def connectorEndpoints {d : ℕ} (hd : D.IsBettiDegree d)
    (e : D.ComponentConnector hd) : D.FactorizationAt d × D.FactorizationAt d :=
  (D.componentRepresentative (D.rootComponent hd), D.componentRepresentative e.1)

/--
@isnad1 id=and.1h3v.s6.94b2d43f3588 from=translated src=- shape=079f24f3 vocab=63bd69c1
-/
theorem connectorEndpoints_components {d : ℕ} (hd : D.IsBettiDegree d)
    (e : D.ComponentConnector hd) :
    D.componentOf (D.connectorEndpoints hd e).1 = D.rootComponent hd ∧
      D.componentOf (D.connectorEndpoints hd e).2 = e.1 := by
  exact ⟨D.componentRepresentative_component _, D.componentRepresentative_component _⟩

/--
@isnad1 id=eq.1h2v.s5.e91bbbf3a3a3 from=translated src=- shape=7ad6a044 vocab=b27d73fb
-/
theorem connectorCount {d : ℕ} (hd : D.IsBettiDegree d) :
    Fintype.card (D.ComponentConnector hd) = D.componentCount d - 1 := by
  classical
  unfold ComponentConnector componentCount
  simpa using Fintype.card_subtype_compl
    (fun C : D.BettiComponent d => C = D.rootComponent hd)

/-- The component-level star graph obtained by adjoining the connector family.-/
def componentConnectorGraph {d : ℕ} (hd : D.IsBettiDegree d) :
    SimpleGraph (D.BettiComponent d) :=
  SimpleGraph.fromRel fun C E => C = D.rootComponent hd ∧ E ≠ D.rootComponent hd

/--
@isnad1 id=iff.1h4v.s6.3a6683802288 from=translated src=- shape=52851e09 vocab=93bc34d6
-/
theorem componentConnectorGraph_adj {d : ℕ} (hd : D.IsBettiDegree d)
    (C E : D.BettiComponent d) :
    (D.componentConnectorGraph hd).Adj C E ↔
      C ≠ E ∧ ((C = D.rootComponent hd ∧ E ≠ D.rootComponent hd) ∨
        (E = D.rootComponent hd ∧ C ≠ D.rootComponent hd)) := by
  rfl

/--
@isnad1 id=connecte.1h2v.s4.2d1912e959b3 from=translated src=- shape=26d66f16 vocab=43aa8a43
-/
theorem componentConnectorGraph_connected {d : ℕ} (hd : D.IsBettiDegree d) :
    (D.componentConnectorGraph hd).Connected := by
  classical
  have hnonempty : Nonempty (D.BettiComponent d) :=
    ⟨D.rootComponent hd⟩
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, hnonempty⟩
  intro C E
  have toRoot (A : D.BettiComponent d) :
      (D.componentConnectorGraph hd).Reachable A (D.rootComponent hd) := by
    by_cases hA : A = D.rootComponent hd
    · subst A
      exact SimpleGraph.Reachable.refl (G := D.componentConnectorGraph hd) _
    · exact ((D.componentConnectorGraph_adj hd A (D.rootComponent hd)).2
        ⟨hA, Or.inr ⟨rfl, hA⟩⟩).reachable
  exact (toRoot C).trans (toRoot E).symm

end Connectors

/-- Scope-explicit stable package for Run 23.-/
structure FourBaseBettiCombinatorics : Prop where
  componentSupportDisjoint : ∀ d (C E : D.BettiComponent d), C ≠ E →
    Disjoint (D.componentSupport C) (D.componentSupport E)
  localInequality : ∀ d, D.IsBettiDegree d →
    (4 - D.supportCard d) * (D.componentCount d - 1) ≤ D.singletonComponentCount d
  singletonDegreeUnique : ∀ j d₁ d₂, D.IsBettiDegree d₁ → D.IsBettiDegree d₂ →
    D.HasSingletonComponentAt j d₁ → D.HasSingletonComponentAt j d₂ → d₁ = d₂
  singletonOccurrenceBound : Fintype.card (D.SingletonBettiOccurrence) ≤ 4
  fourBaseBudgetBound : (∑ i : Fin 4, D.fourBaseBudget i) ≤ 4

/--
@isnad1 id=fourbase.0h1v.s2.966b93a1be6b from=translated src=- shape=5c11bb93 vocab=fe38d212
-/
theorem fourBaseBettiCombinatorics : D.FourBaseBettiCombinatorics where
  componentSupportDisjoint := fun _ _ _ h => D.componentSupport_disjoint h
  localInequality := fun _ h => D.localSupportInequality h
  singletonDegreeUnique := fun _ _ _ h₁ h₂ hs₁ hs₂ =>
    D.singletonComponent_degree_unique h₁ h₂ hs₁ hs₂
  singletonOccurrenceBound := D.singletonBettiOccurrence_card_le_four
  fourBaseBudgetBound := D.fourBaseBudget_sum_le_four

end FourGeneratedNumericalSemigroup

end

end P23.Semigroup
