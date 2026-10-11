import Tengoku.OpenaiMath.OAI.Probability.CriticalZ3.TrialCounts

namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem measurableSet_shell_blocked (C : Box) (o : G.Node) (L : ℕ) :
    MeasurableSet {ω | 0 < (G.entrants m C ω o).card ∧
      (G.entrants m C ω o).card < L ∧ G.Blocked m C ω o} := by
  let J := G.outsideBits m C
  let ξ (a : J → Bool) := ProductCylinder.extend J a
  let A (a : J → Bool) : Set m.Config := if 0 < (G.entrants m C (ξ a) o).card ∧
      (G.entrants m C (ξ a) o).card < L then allValue (G.entryBits m C (ξ a) o) false else ∅
  have h := measurableSet_select J A (fun a => by
    dsimp only [A]; split_ifs
    · exact measurableSet_allValue _ _
    · exact MeasurableSet.empty)
  have he : {ω | ω ∈ A (J.restrict ω)} = {ω | 0 < (G.entrants m C ω o).card ∧
      (G.entrants m C ω o).card < L ∧ G.Blocked m C ω o} := by
    ext ω
    have hY := ProductCylinder.determinedBy_eq_extend (G.entrants_determined m C o) ω
    have hK := ProductCylinder.determinedBy_eq_extend (G.entryBits_determined m C o) ω
    change G.entrants m C ω o = G.entrants m C (ξ (J.restrict ω)) o at hY
    change G.entryBits m C ω o = G.entryBits m C (ξ (J.restrict ω)) o at hK
    simp only [A,←hY,←hK,Set.mem_ofPred_eq,Blocked,allValue]
    split_ifs with hh
    · tauto
    · simp only [Set.mem_empty_iff_false]; tauto
  rwa [he] at h

end CriticalZ3.LatticeGraph

namespace FiniteAssociation
open Classical
variable {E : Type}

theorem indicator_monotone {P : (E → Bool) → Prop} (hP : Monotone P) :
    Monotone (fun ω => if P ω then (1 : ℝ) else 0) := by
  intro ω ω' h
  by_cases h' : P ω
  · simp [h',hP h h']
  · simp only [h',ite_false]
    split_ifs <;> norm_num

theorem prob_and_increasing [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    {P Q : (E → Bool) → Prop} (hP : Monotone P) (hQ : Monotone Q) :
    prob p P * prob p Q ≤ prob p (fun ω => P ω ∧ Q ω) := by
  have h := increasing p _ _ (indicator_monotone hP) (indicator_monotone hQ)
  change mean p _ * mean p _ ≤ mean p _
  convert h using 1
  congr 1
  funext ω
  by_cases h₁ : P ω <;> by_cases h₂ : Q ω <;> simp [h₁,h₂]
end FiniteAssociation

namespace ProductCylinder
open MeasureTheory ProbabilityTheory Classical
variable {E : Type}

theorem probability_congr_parameters (J : Finset E)
    (p q : E → Set.Icc (0 : ℝ) 1) (hpq : ∀ e ∈ J, p e = q e)
    (A : Set (E → Bool)) (hA : DeterminedBy (F := Prop) J (fun ω => ω ∈ A)) :
    (law p).real A = (law q).real A := by
  simp only [Measure.real_def,probability_determined J _ A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h))]
  congr 2
  unfold finiteLaw
  congr 1
  funext e
  rw [hpq e e.2]

theorem determinedBy_mono {J K : Finset E} (hJK : J ⊆ K) {F : Type}
    {f : (E → Bool) → F} (hf : DeterminedBy J f) : DeterminedBy K f :=
  fun ω ω' h => hf ω ω' (fun e he => h e (hJK he))

theorem increasing_and (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A B : Set (E → Bool))
    (hA : DeterminedBy (F := Prop) J (fun ω => ω ∈ A))
    (hB : DeterminedBy (F := Prop) J (fun ω => ω ∈ B))
    (hmA : Monotone (fun ω => ω ∈ A)) (hmB : Monotone (fun ω => ω ∈ B)) :
    (law p).real A*(law p).real B ≤ (law p).real (A ∩ B) := by
  have he (C : Set (E → Bool)) (hC : DeterminedBy (F := Prop) J (fun ω => ω ∈ C)) :
      (law p).real C = FiniteAssociation.prob (fun e : J => p e) (fun ξ => extend J ξ ∈ C) := by
    rw [FiniteAssociation.prob_eq_real,Measure.real_def,Measure.real_def,
      probability_determined J p C (fun ω ω' h => eq_iff_iff.mp (hC ω ω' h))]
    rfl
  have hAB : DeterminedBy (F := Prop) J (fun ω => ω ∈ A ∩ B) := by
    intro ω ω' h
    simp only [Set.mem_inter_iff,hA ω ω' h,hB ω ω' h]
  rw [he A hA,he B hB,he (A ∩ B) hAB]
  exact FiniteAssociation.prob_and_increasing _ (hmA.comp (extend_mono J)) (hmB.comp (extend_mono J))

/-- The open-seed Harris estimate, with a separate increasing connecting event. -/
theorem seed_failure_bound (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (O A C : Set (E → Bool))
    (hO : DeterminedBy (F := Prop) J (fun ω => ω ∈ O))
    (hA : DeterminedBy (F := Prop) J (fun ω => ω ∈ A))
    (hmO : Monotone (fun ω => ω ∈ O)) (hmA : Monotone (fun ω => ω ∈ A))
    (hsub : O ∩ A ⊆ C) {γ : ℝ} (hprob : 1-γ ≤ (law p).real A) :
    (law p).real (O ∩ Cᶜ) ≤ (law p).real O*γ := by
  have hm := measurableSet_determined J A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h))
  have ha := increasing_and J p O A hO hA hmO hmA
  have hadd := measureReal_inter_add_sdiff (μ := law p) (s := O) hm
  have hsub' : O ∩ Cᶜ ⊆ O \ A := by
    intro ω hω
    exact ⟨hω.1,fun h => hω.2 (hsub ⟨hω.1,h⟩)⟩
  have hle := measureReal_mono (μ := law p) hsub'
  have h0 : 0 ≤ (law p).real O := measureReal_nonneg
  nlinarith
end ProductCylinder

namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E : Type}

theorem allValue_true_monotone (J : Finset E) : Monotone (fun ω => ω ∈ allValue J true) := by
  intro ω ω' h hh e he
  have hi := h e
  rw [hh e he] at hi
  exact le_antisymm le_top hi

theorem measurableSet_conditional_test (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (C : Set (E → Bool)) (a : ℝ) :
    MeasurableSet {ω | conditionalProbability p J C ω ≤ a} := by
  refine ProductCylinder.measurableSet_determined J _ ?_
  intro ω ω' h
  simp only [Set.mem_ofPred_eq,conditionalProbability_determined p J C ω ω' h]
end InfiniteConditioning

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem conn_mono {ω ω' : m.Config} (h : ω ≤ ω') {x y : G.Node}
    (hc : G.Conn m ω x y) : G.Conn m ω' x y := by
  have hopen {e : m.Bit} (he : ω e = true) : ω' e = true := by
    have hi := h e
    rw [he] at hi
    exact le_antisymm le_top hi
  obtain ⟨hx,hc⟩ := (G.conn_iff m ω x y).mp hc
  refine (G.conn_iff m ω' x y).mpr ⟨?_,?_⟩
  · cases m
    · trivial
    · exact hopen hx
  · apply Relation.ReflTransGen.mono (r := G.Adj m ω) (p := G.Adj m ω') ?_ x y hc
    intro a b hab
    cases m
    · obtain ⟨e,he,hi,ho⟩ := hab
      exact ⟨e,he,hi,hopen ho⟩
    · exact ⟨hab.1,hopen hab.2.1,hopen hab.2.2⟩

theorem meets_mono (o : G.Node) (T : Set Vertex) : Monotone (fun ω => G.Meets m ω o T) := by
  intro ω ω' h ⟨y,hy,hc⟩
  exact ⟨y,hy,G.conn_mono m h hc⟩

noncomputable def goodRelays (p : m.Bit → Set.Icc (0 : ℝ) 1) (J : Finset m.Bit)
    (T : Set Vertex) (τ : ℝ) (ω : m.Config) : Set Vertex :=
  {v | ∃ a : G.Node, a.1 = v ∧ 1-τ < conditionalProbability p J {ω | G.Meets m ω a T} ω}

theorem goodRelays_determined (p : m.Bit → Set.Icc (0 : ℝ) 1) (J : Finset m.Bit)
    (T : Set Vertex) (τ : ℝ) : ProductCylinder.DeterminedBy J (G.goodRelays m p J T τ) := by
  intro ω ω' h
  ext v
  simp only [goodRelays,Set.mem_ofPred_eq,conditionalProbability_determined p J _ ω ω' h]

end CriticalZ3.LatticeGraph

end OAI
