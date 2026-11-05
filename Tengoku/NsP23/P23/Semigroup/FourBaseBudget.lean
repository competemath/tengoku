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

theorem supportCard_le_four (d : ℕ) : D.supportCard d ≤ 4 := by
  unfold supportCard
  have hsub : D.combinedSupport d ⊆ Finset.univ := fun _ _ => Finset.mem_univ _
  simpa using Finset.card_le_card hsub

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

/-- The local four-variable support inequality from the human Betti budget.-/
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

theorem bettiContribution_pos {d : ℕ} (hd : D.IsBettiDegree d) :
    0 < D.bettiContribution d := by
  unfold bettiContribution IsBettiDegree at *
  omega

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

theorem budgetDegreeSingletonComponent_isSingleton (d : D.BudgetDegree) :
    D.IsSingletonSupportComponent (D.budgetDegreeSingletonComponent d) :=
  Classical.choose_spec (D.exists_singleton_component_of_budget d.2.1 d.2.2)

def budgetDegreeOccurrence (d : D.BudgetDegree) : D.SingletonBettiOccurrence where
  degree := d.1
  isBetti := d.2.1
  component := D.budgetDegreeSingletonComponent d
  singleton := D.budgetDegreeSingletonComponent_isSingleton d

theorem budgetDegreeOccurrence_injective :
    Function.Injective D.budgetDegreeOccurrence := by
  intro d e h
  apply Subtype.ext
  exact congrArg SingletonBettiOccurrence.degree h

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

theorem omittedVariableCount (d : ℕ) :
    (Finset.univ.filter fun i : Fin 4 => i ∉ D.combinedSupport d).card =
      4 - D.supportCard d := by
  classical
  rw [Finset.filter_not]
  have hfilter : (Finset.univ.filter fun i : Fin 4 => i ∈ D.combinedSupport d) =
      D.combinedSupport d := by ext i; simp
  rw [hfilter, Finset.card_sdiff]
  simp [supportCard]

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

/-- Finite double counting of omitted variables and component contributions.-/
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

/-- The exact combinatorial four-base budget.-/
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

theorem componentRepresentative_component {d : ℕ} (C : D.BettiComponent d) :
    D.componentOf (D.componentRepresentative C) = C :=
  (SimpleGraph.ConnectedComponent.mem_supp_iff C _).mp
    (Classical.choose_spec (SimpleGraph.ConnectedComponent.nonempty_supp C))

/-- The representative relation joining the root to a non-root component.-/
def connectorEndpoints {d : ℕ} (hd : D.IsBettiDegree d)
    (e : D.ComponentConnector hd) : D.FactorizationAt d × D.FactorizationAt d :=
  (D.componentRepresentative (D.rootComponent hd), D.componentRepresentative e.1)

theorem connectorEndpoints_components {d : ℕ} (hd : D.IsBettiDegree d)
    (e : D.ComponentConnector hd) :
    D.componentOf (D.connectorEndpoints hd e).1 = D.rootComponent hd ∧
      D.componentOf (D.connectorEndpoints hd e).2 = e.1 := by
  exact ⟨D.componentRepresentative_component _, D.componentRepresentative_component _⟩

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

theorem componentConnectorGraph_adj {d : ℕ} (hd : D.IsBettiDegree d)
    (C E : D.BettiComponent d) :
    (D.componentConnectorGraph hd).Adj C E ↔
      C ≠ E ∧ ((C = D.rootComponent hd ∧ E ≠ D.rootComponent hd) ∨
        (E = D.rootComponent hd ∧ C ≠ D.rootComponent hd)) := by
  rfl

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
