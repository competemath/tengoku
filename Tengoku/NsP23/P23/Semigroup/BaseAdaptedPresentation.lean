import Tengoku.NsP23.P23.Semigroup.ChosenBaseSpecialization
import Tengoku.NsP23.P23.Semigroup.Rho

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Base-adapted stars and genuine chosen-base generation, without minimality. -/
namespace P23.Semigroup
noncomputable section
open scoped BigOperators
open FourGeneratedNumericalSemigroup
variable {k : Type*} [Field k]
namespace FourGeneratedNumericalSemigroup
variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem existsUnique_baseSupportComponent {d : ℕ} (hi : i ∈ D.combinedSupport d) :
    ∃! C : D.BettiComponent d, i ∈ D.componentSupport C := by
  obtain ⟨u, hui⟩ := D.mem_combinedSupport_iff.mp hi
  refine ⟨D.componentOf u, D.mem_componentSupport_iff.mpr ⟨u, rfl, hui⟩, ?_⟩
  intro C hC
  by_contra hne
  exact Finset.disjoint_left.mp (D.componentSupport_disjoint hne) hC
    (D.mem_componentSupport_iff.mpr ⟨u, rfl, hui⟩)

def baseSupportComponent {d : ℕ} (_hd : D.IsBettiDegree d)
    (hi : i ∈ D.combinedSupport d) : D.BettiComponent d :=
  (D.existsUnique_baseSupportComponent i hi).choose

theorem baseSupportComponent_mem {d : ℕ} (hd : D.IsBettiDegree d)
    (hi : i ∈ D.combinedSupport d) : i ∈ D.componentSupport (D.baseSupportComponent i hd hi) :=
  (D.existsUnique_baseSupportComponent i hi).choose_spec.1

def baseUsingFactorization {d : ℕ} (hd : D.IsBettiDegree d)
    (hi : i ∈ D.combinedSupport d) : D.FactorizationAt d :=
  (D.mem_componentSupport_iff.mp (D.baseSupportComponent_mem i hd hi)).choose

theorem baseUsingFactorization_component {d : ℕ} (hd : D.IsBettiDegree d)
    (hi : i ∈ D.combinedSupport d) :
    D.componentOf (D.baseUsingFactorization i hd hi) = D.baseSupportComponent i hd hi :=
  (D.mem_componentSupport_iff.mp (D.baseSupportComponent_mem i hd hi)).choose_spec.1

theorem baseUsingFactorization_pos {d : ℕ} (hd : D.IsBettiDegree d)
    (hi : i ∈ D.combinedSupport d) : 0 < (D.baseUsingFactorization i hd hi).1 i :=
  (D.mem_componentSupport_iff.mp (D.baseSupportComponent_mem i hd hi)).choose_spec.2

theorem factorization_base_zero_of_other_component {d : ℕ}
    (hd : D.IsBettiDegree d) (hi : i ∈ D.combinedSupport d)
    (u : D.FactorizationAt d) (hu : D.componentOf u ≠ D.baseSupportComponent i hd hi) :
    u.1 i = 0 := by
  by_contra h
  exact Finset.disjoint_left.mp (D.componentSupport_disjoint hu)
    (D.mem_componentSupport_iff.mpr ⟨u, rfl, Nat.pos_of_ne_zero h⟩)
    (D.baseSupportComponent_mem i hd hi)

theorem factorization_base_zero_of_internal {d : ℕ}
    (hi : i ∉ D.combinedSupport d) (u : D.FactorizationAt d) : u.1 i = 0 := by
  by_contra h
  exact hi (D.mem_combinedSupport_iff.mpr ⟨u, Nat.pos_of_ne_zero h⟩)

def baseAdaptedRootComponent {d : ℕ} (hd : D.IsBettiDegree d) : D.BettiComponent d :=
  if hi : i ∈ D.combinedSupport d then D.baseSupportComponent i hd hi else D.rootComponent hd

def baseAdaptedRootFactorization {d : ℕ} (hd : D.IsBettiDegree d) : D.FactorizationAt d :=
  if hi : i ∈ D.combinedSupport d then D.baseUsingFactorization i hd hi
    else D.componentRepresentative (D.rootComponent hd)

@[simp] theorem baseAdaptedRootFactorization_component {d : ℕ} (hd : D.IsBettiDegree d) :
    D.componentOf (D.baseAdaptedRootFactorization i hd) = D.baseAdaptedRootComponent i hd := by
  unfold baseAdaptedRootFactorization baseAdaptedRootComponent
  split <;> simp [D.baseUsingFactorization_component, D.componentRepresentative_component]

theorem baseAdaptedRootFactorization_pos {d : ℕ} (hd : D.IsBettiDegree d)
    (hi : i ∈ D.combinedSupport d) : 0 < (D.baseAdaptedRootFactorization i hd).1 i := by
  simpa only [baseAdaptedRootFactorization, dite_eq_left hi] using D.baseUsingFactorization_pos i hd hi

abbrev BaseAdaptedConnector {d : ℕ} (hd : D.IsBettiDegree d) :=
  {C : D.BettiComponent d // C ≠ D.baseAdaptedRootComponent i hd}

def baseAdaptedConnectorEndpoints {d : ℕ} (hd : D.IsBettiDegree d)
    (g : D.BaseAdaptedConnector i hd) : D.FactorizationAt d × D.FactorizationAt d :=
  (D.baseAdaptedRootFactorization i hd, D.componentRepresentative g.1)

theorem baseAdaptedConnectorEndpoints_components {d : ℕ} (hd : D.IsBettiDegree d)
    (g : D.BaseAdaptedConnector i hd) :
    D.componentOf (D.baseAdaptedConnectorEndpoints i hd g).1 = D.baseAdaptedRootComponent i hd ∧
    D.componentOf (D.baseAdaptedConnectorEndpoints i hd g).2 = g.1 :=
  ⟨D.baseAdaptedRootFactorization_component i hd, D.componentRepresentative_component g.1⟩

def baseAdaptedConnectorRelation {d : ℕ} (hd : D.IsBettiDegree d)
    (g : D.BaseAdaptedConnector i hd) : SemigroupPresentationRelation D :=
  ⟨d, (D.baseAdaptedConnectorEndpoints i hd g).1, (D.baseAdaptedConnectorEndpoints i hd g).2⟩

def baseAdaptedConnectorBinomial {d : ℕ} (hd : D.IsBettiDegree d)
    (g : D.BaseAdaptedConnector i hd) : FourPoly k :=
  D.presentationRelationBinomial (D.baseAdaptedConnectorRelation i hd g)

theorem baseAdaptedConnector_card {d : ℕ} (hd : D.IsBettiDegree d) :
    Fintype.card (D.BaseAdaptedConnector i hd) = D.bettiContribution d := by
  classical
  simpa [bettiContribution, componentCount] using
    Fintype.card_subtype_compl (fun C : D.BettiComponent d => C = D.baseAdaptedRootComponent i hd)

abbrev BaseAdaptedGlobalConnector := Σ d : D.BettiDegreeIndex, D.BaseAdaptedConnector i d.2

def baseAdaptedGlobalConnectorRelation (g : D.BaseAdaptedGlobalConnector i) :=
  D.baseAdaptedConnectorRelation i g.1.2 g.2

def baseAdaptedGlobalConnectorBinomial (g : D.BaseAdaptedGlobalConnector i) : FourPoly k :=
  D.baseAdaptedConnectorBinomial i g.1.2 g.2

private def adaptedRepresentative {d : ℕ} (hd : D.IsBettiDegree d)
    (C : D.BettiComponent d) : D.FactorizationAt d :=
  if C = D.baseAdaptedRootComponent i hd then D.baseAdaptedRootFactorization i hd
  else D.componentRepresentative C

private theorem adaptedRepresentative_component {d : ℕ} (hd : D.IsBettiDegree d)
    (C : D.BettiComponent d) : D.componentOf (D.adaptedRepresentative i hd C) = C := by
  classical
  unfold adaptedRepresentative
  split <;> simp_all [D.componentRepresentative_component]

private theorem adaptedPair_mem_span {d : ℕ} (hd : D.IsBettiDegree d)
    (C E : D.BettiComponent d) :
    D.fiberBinomial (k := k) (D.adaptedRepresentative i hd C) (D.adaptedRepresentative i hd E) ∈
      Ideal.span (Set.range (D.baseAdaptedGlobalConnectorBinomial (k := k) i)) := by
  classical
  let J := Ideal.span (Set.range (D.baseAdaptedGlobalConnectorBinomial (k := k) i))
  have hstar : ∀ C : D.BettiComponent d,
      D.fiberBinomial (k := k) (D.baseAdaptedRootFactorization i hd)
        (D.adaptedRepresentative i hd C) ∈ J := by
    intro C
    by_cases hC : C = D.baseAdaptedRootComponent i hd
    · simp [adaptedRepresentative, hC, fiberBinomial]
    · have hgen : D.baseAdaptedGlobalConnectorBinomial (k := k) i
          ⟨⟨d, hd⟩, ⟨C, hC⟩⟩ ∈ J := Ideal.subset_span ⟨_, rfl⟩
      simpa [baseAdaptedGlobalConnectorBinomial, baseAdaptedConnectorBinomial,
        baseAdaptedConnectorRelation, baseAdaptedConnectorEndpoints, presentationRelationBinomial,
        adaptedRepresentative, hC] using hgen
  have h := J.sub_mem (hstar E) (hstar C)
  have heq :
      D.fiberBinomial (k := k) (D.baseAdaptedRootFactorization i hd) (D.adaptedRepresentative i hd E) -
        D.fiberBinomial (k := k) (D.baseAdaptedRootFactorization i hd) (D.adaptedRepresentative i hd C) =
      D.fiberBinomial (k := k) (D.adaptedRepresentative i hd C) (D.adaptedRepresentative i hd E) := by
    unfold fiberBinomial
    abel
  rw [heq] at h
  exact h

theorem fiberBinomial_mem_span_baseAdaptedGlobalConnectorBinomials {d : ℕ}
    (u v : D.FactorizationAt d) : D.fiberBinomial (k := k) u v ∈
      Ideal.span (Set.range (D.baseAdaptedGlobalConnectorBinomial (k := k) i)) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      have hlower : D.lowerToricIdeal (k := k) d ≤
          Ideal.span (Set.range (D.baseAdaptedGlobalConnectorBinomial (k := k) i)) := by
        rw [lowerToricIdeal, Ideal.span_le]
        rintro p ⟨e, he, u, v, rfl⟩
        exact ih e he u v
      by_cases hcomp : D.componentOf u = D.componentOf v
      · exact hlower (D.fiberBinomial_mem_lower_of_sameComponent hcomp)
      · have hd : D.IsBettiDegree d := by
          have hc := Fintype.one_lt_card_iff.mpr ⟨D.componentOf u, D.componentOf v, hcomp⟩
          unfold IsBettiDegree componentCount
          omega
        let ru := D.adaptedRepresentative i hd (D.componentOf u)
        let rv := D.adaptedRepresentative i hd (D.componentOf v)
        have hu : D.fiberBinomial (k := k) u ru ∈ _ :=
          hlower (D.fiberBinomial_mem_lower_of_sameComponent
            (D.adaptedRepresentative_component i hd (D.componentOf u)).symm)
        have hv : D.fiberBinomial (k := k) rv v ∈ _ :=
          hlower (D.fiberBinomial_mem_lower_of_sameComponent
            (D.adaptedRepresentative_component i hd (D.componentOf v)))
        have hm := D.adaptedPair_mem_span (k := k) i hd (D.componentOf u) (D.componentOf v)
        have hsum := Ideal.add_mem _ (Ideal.add_mem _ hu hm) hv
        simpa [ru, rv, fiberBinomial] using hsum

theorem toricIdeal_eq_span_baseAdaptedGlobalConnectorBinomials : D.toricIdeal (k := k) =
    Ideal.span (Set.range (D.baseAdaptedGlobalConnectorBinomial (k := k) i)) := by
  apply le_antisymm
  · rw [D.toricIdeal_eq_span_fiberBinomials, Ideal.span_le]
    rintro p ⟨d, u, v, rfl⟩
    exact D.fiberBinomial_mem_span_baseAdaptedGlobalConnectorBinomials i u v
  · rw [Ideal.span_le]
    rintro p ⟨g, rfl⟩
    exact D.fiberBinomial_mem_toricIdeal _ _

theorem baseAdaptedGlobalConnectorRelation_injective :
    Function.Injective (D.baseAdaptedGlobalConnectorRelation i) := by
  rintro ⟨d, C⟩ ⟨e, E⟩ h
  have hde : d = e := Subtype.ext (congrArg (fun r => r.degree) h)
  subst e
  have hr : (D.componentRepresentative C.1).1 = (D.componentRepresentative E.1).1 :=
    congrArg (fun r => r.right.1) h
  have hCE : C = E := Subtype.ext (by
    have hc := congrArg D.componentOf (Subtype.ext hr)
    simpa [D.componentRepresentative_component] using hc)
  subst E
  rfl

def baseAdaptedConnectorRelationFinset : Finset (SemigroupPresentationRelation D) :=
  Finset.univ.image (D.baseAdaptedGlobalConnectorRelation i)

theorem baseAdaptedConnectorRelationFinset_card :
    (D.baseAdaptedConnectorRelationFinset i).card =
      ∑ d : D.BettiDegreeIndex, D.bettiContribution d.1 := by
  rw [baseAdaptedConnectorRelationFinset,
    Finset.card_image_of_injective _ (D.baseAdaptedGlobalConnectorRelation_injective i)]
  change Fintype.card (D.BaseAdaptedGlobalConnector i) = _
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun d _ => D.baseAdaptedConnector_card i d.2)

theorem baseAdaptedConnectorRelationFinset_card_eq_rho :
    (D.baseAdaptedConnectorRelationFinset i).card = D.semigroupRho := by
  rw [D.baseAdaptedConnectorRelationFinset_card, D.semigroupRho_eq_sum_bettiContribution]

theorem baseAdaptedConnectorRelationFinset_isPresentation :
    D.IsSemigroupPresentation (k := k) (D.baseAdaptedConnectorRelationFinset i) := by
  unfold IsSemigroupPresentation presentationIdeal baseAdaptedConnectorRelationFinset
  rw [D.toricIdeal_eq_span_baseAdaptedGlobalConnectorBinomials i]
  congr 1
  ext p
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨D.baseAdaptedGlobalConnectorRelation i g, Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩, rfl⟩

def specializedConnectorPolynomial (g : D.BaseAdaptedGlobalConnector i) : TailPoly k :=
  baseSpecialization D i (D.baseAdaptedGlobalConnectorBinomial i g)

def connectorLeftTail (g : D.BaseAdaptedGlobalConnector i) : Fin 3 →₀ ℕ :=
  restrictToTails D i (D.baseAdaptedRootFactorization i g.1.2).1

def connectorRightTail (g : D.BaseAdaptedGlobalConnector i) : Fin 3 →₀ ℕ :=
  restrictToTails D i (D.componentRepresentative g.2.1).1

theorem connector_target_base_zero (g : D.BaseAdaptedGlobalConnector i) :
    (D.componentRepresentative g.2.1).1 i = 0 := by
  by_cases hi : i ∈ D.combinedSupport g.1.1
  · apply D.factorization_base_zero_of_other_component i g.1.2 hi
    rw [D.componentRepresentative_component]
    simpa only [baseAdaptedRootComponent, dite_eq_left hi] using g.2.2
  · exact D.factorization_base_zero_of_internal i hi _

theorem specializedConnectorPolynomial_external (g : D.BaseAdaptedGlobalConnector i)
    (hi : i ∈ D.combinedSupport g.1.1) :
    D.specializedConnectorPolynomial (k := k) i g =
      -MvPolynomial.monomial (D.connectorRightTail i g) 1 := by
  unfold specializedConnectorPolynomial baseAdaptedGlobalConnectorBinomial
    baseAdaptedConnectorBinomial presentationRelationBinomial baseAdaptedConnectorRelation
    baseAdaptedConnectorEndpoints fiberBinomial fiberMonomial
  rw [map_sub, baseSpecialization_monomial_of_base_pos D i _ _
    (D.baseAdaptedRootFactorization_pos i g.1.2 hi),
    baseSpecialization_monomial_of_base_zero D i _ _ (D.connector_target_base_zero i g)]
  exact zero_sub _

theorem specializedConnector_isMonomial_of_base_mem_support
    (g : D.BaseAdaptedGlobalConnector i) (hi : i ∈ D.combinedSupport g.1.1) :
    D.specializedConnectorPolynomial (k := k) i g =
      -MvPolynomial.monomial (D.connectorRightTail i g) 1 ∧
      D.specializedConnectorPolynomial (k := k) i g ≠ 0 := by
  refine ⟨D.specializedConnectorPolynomial_external i g hi, ?_⟩
  rw [D.specializedConnectorPolynomial_external i g hi, neg_ne_zero]
  simp

theorem specializedConnectorPolynomial_internal (g : D.BaseAdaptedGlobalConnector i)
    (hi : i ∉ D.combinedSupport g.1.1) :
    D.specializedConnectorPolynomial (k := k) i g =
      MvPolynomial.monomial (D.connectorLeftTail i g) 1 -
        MvPolynomial.monomial (D.connectorRightTail i g) 1 := by
  unfold specializedConnectorPolynomial baseAdaptedGlobalConnectorBinomial
    baseAdaptedConnectorBinomial presentationRelationBinomial baseAdaptedConnectorRelation
    baseAdaptedConnectorEndpoints fiberBinomial fiberMonomial
  rw [map_sub, baseSpecialization_monomial_of_base_zero D i _ _
    (D.factorization_base_zero_of_internal i hi _),
    baseSpecialization_monomial_of_base_zero D i _ _ (D.connector_target_base_zero i g)]
  rfl

theorem connector_tail_supports_disjoint (g : D.BaseAdaptedGlobalConnector i) :
    Disjoint (D.connectorLeftTail i g).support (D.connectorRightTail i g).support := by
  rw [Finset.disjoint_left]
  intro j hjl hjr
  have hl : 0 < (D.baseAdaptedRootFactorization i g.1.2).1 (D.tailIndex i j) := by
    simpa only [connectorLeftTail, restrictToTails_apply, Finsupp.mem_support_iff,
      Nat.pos_iff_ne_zero] using hjl
  have hr : 0 < (D.componentRepresentative g.2.1).1 (D.tailIndex i j) := by
    simpa only [connectorRightTail, restrictToTails_apply, Finsupp.mem_support_iff,
      Nat.pos_iff_ne_zero] using hjr
  exact Finset.disjoint_left.mp (D.componentSupport_disjoint g.2.2)
    (D.mem_componentSupport_iff.mpr ⟨_, D.componentRepresentative_component _, hr⟩)
    (D.mem_componentSupport_iff.mpr ⟨_, D.baseAdaptedRootFactorization_component i _, hl⟩)

theorem factorization_ne_zero_of_isBetti {d : ℕ} (hd : D.IsBettiDegree d)
    (u : D.FactorizationAt d) : u.1 ≠ 0 := by
  intro hu
  have hd0 : d = 0 := by simpa [hu] using (D.factorizationAt_degree u).symm
  obtain ⟨j, hj⟩ := D.componentSupport_nonempty_of_isBetti hd (D.componentOf u)
  obtain ⟨v, _, hvj⟩ := D.mem_componentSupport_iff.mp hj
  have hv := D.factorization_eq_zero_of_degree_eq_zero hd0 v
  simp [hv] at hvj

theorem restricted_factorization_support_nonempty {d : ℕ} (hd : D.IsBettiDegree d)
    (u : D.FactorizationAt d) (hu : u.1 i = 0) : (restrictToTails D i u.1).support.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  have hzero := Finsupp.support_eq_empty.mp he
  have hr := tailEmbedding_restrictToTails D i u.1 hu
  rw [hzero] at hr
  rw [tailEmbeddingExponent_eq_mapDomain D i] at hr
  apply D.factorization_ne_zero_of_isBetti hd u
  simpa using hr.symm

theorem internal_connector_tail_supports_nonempty (g : D.BaseAdaptedGlobalConnector i)
    (hi : i ∉ D.combinedSupport g.1.1) :
    (D.connectorLeftTail i g).support.Nonempty ∧ (D.connectorRightTail i g).support.Nonempty :=
  ⟨D.restricted_factorization_support_nonempty i g.1.2 _
      (D.factorization_base_zero_of_internal i hi _),
    D.restricted_factorization_support_nonempty i g.1.2 _ (D.connector_target_base_zero i g)⟩

theorem internal_connector_tail_ne (g : D.BaseAdaptedGlobalConnector i)
    (hi : i ∉ D.combinedSupport g.1.1) : D.connectorLeftTail i g ≠ D.connectorRightTail i g := by
  intro h
  obtain ⟨j, hj⟩ := (D.internal_connector_tail_supports_nonempty i g hi).1
  exact Finset.disjoint_left.mp (D.connector_tail_supports_disjoint i g) hj (h ▸ hj)

def bettiDegreeGamma (d : D.BettiDegreeIndex) : D.Gamma :=
  ⟨d.1, (D.mem_Gamma_iff _).mpr
    ⟨(D.componentRepresentative (D.rootComponent d.2)).1, D.factorizationAt_degree _⟩⟩

theorem internalDegree_isApery (d : D.BettiDegreeIndex) (hi : i ∉ D.combinedSupport d.1) :
    D.IsApery i (D.bettiDegreeGamma d) := by
  rintro ⟨h, he⟩
  obtain ⟨v, hv⟩ := (D.mem_Gamma_iff h.1).mp h.2
  let w := Finsupp.single i 1 + v
  have hw : D.weightedDegree w = d.1 := by
    have hh := congrArg Subtype.val he
    change d.1 = D.n i + h.1 at hh
    change D.weightedDegree (Finsupp.single i 1 + v) = d.1
    have hadd : D.weightedDegree (Finsupp.single i 1 + v) =
        D.weightedDegree (Finsupp.single i 1) + D.weightedDegree v :=
      weightedDegreeOf_add D.n _ _
    rw [hadd, D.weightedDegree_single, one_mul, hv]
    exact hh.symm
  let u : D.FactorizationAt d.1 := ⟨w, D.mem_factorizations.mpr hw⟩
  apply hi
  apply D.mem_combinedSupport_iff.mpr
  refine ⟨u, ?_⟩
  simp [u, w]

theorem internal_term_image (d : D.BettiDegreeIndex) (hi : i ∉ D.combinedSupport d.1)
    (u : D.FactorizationAt d.1) :
    chosenBaseEquivApery (k := k) D i
      (tailPolyToChosenBase D i (MvPolynomial.monomial (restrictToTails D i u.1) 1)) =
      AperyArtin.A (D.bettiDegreeGamma d) (D.internalDegree_isApery i d hi) := by
  rw [tailPolyToChosenBase_monomial, one_smul]
  have he : tailDegreeGamma D i (restrictToTails D i u.1) = D.bettiDegreeGamma d := by
    apply Subtype.ext
    exact (restrictToTails_degree D i u.1 (D.factorization_base_zero_of_internal i hi u)).trans
      (D.factorizationAt_degree u)
  rw [he]
  simp [truncatedAperyMonomial, D.internalDegree_isApery i d hi]

theorem internal_connector_images_live (g : D.BaseAdaptedGlobalConnector i)
    (hi : i ∉ D.combinedSupport g.1.1) :
    tailPolyToChosenBase (k := k) D i (MvPolynomial.monomial (D.connectorLeftTail i g) 1) =
      tailPolyToChosenBase D i (MvPolynomial.monomial (D.connectorRightTail i g) 1) ∧
    tailPolyToChosenBase (k := k) D i (MvPolynomial.monomial (D.connectorLeftTail i g) 1) ≠ 0 := by
  have hl := D.internal_term_image (k := k) i g.1 hi (D.baseAdaptedRootFactorization i g.1.2)
  have hr := D.internal_term_image (k := k) i g.1 hi (D.componentRepresentative g.2.1)
  refine ⟨(chosenBaseEquivApery D i).injective (hl.trans hr.symm), ?_⟩
  intro hz
  change tailPolyToChosenBase (k := k) D i
    (MvPolynomial.monomial (restrictToTails D i (D.baseAdaptedRootFactorization i g.1.2).1) 1) = 0 at hz
  have hA : AperyArtin.A (k := k) (D.bettiDegreeGamma g.1)
      (D.internalDegree_isApery i g.1 hi) = 0 := by rw [← hl, hz]; exact map_zero _
  have hc := congrArg (fun x : AperyArtin k D i =>
    x.coeff ⟨D.bettiDegreeGamma g.1, D.internalDegree_isApery i g.1 hi⟩) hA
  simpa using hc

def LiveTailBinomial (p : TailPoly k) : Prop :=
  ∃ u v : Fin 3 →₀ ℕ, p = MvPolynomial.monomial u 1 - MvPolynomial.monomial v 1 ∧
    u.support.Nonempty ∧ v.support.Nonempty ∧ Disjoint u.support v.support ∧ u ≠ v ∧ p ≠ 0 ∧
    tailPolyToChosenBase (k := k) D i (MvPolynomial.monomial u 1) =
      tailPolyToChosenBase (k := k) D i (MvPolynomial.monomial v 1) ∧
    tailPolyToChosenBase (k := k) D i (MvPolynomial.monomial u 1) ≠ 0

theorem specializedConnector_isLiveBinomial_of_base_not_mem_support
    (g : D.BaseAdaptedGlobalConnector i) (hi : i ∉ D.combinedSupport g.1.1) :
    D.LiveTailBinomial (k := k) i (D.specializedConnectorPolynomial i g) := by
  have hsup := D.internal_connector_tail_supports_nonempty i g hi
  have himg := D.internal_connector_images_live (k := k) i g hi
  refine ⟨_, _, D.specializedConnectorPolynomial_internal i g hi, hsup.1, hsup.2,
    D.connector_tail_supports_disjoint i g, D.internal_connector_tail_ne i g hi, ?_, himg⟩
  rw [D.specializedConnectorPolynomial_internal i g hi, sub_ne_zero]
  exact fun h => D.internal_connector_tail_ne i g hi (MvPolynomial.monomial_left_injective one_ne_zero h)

theorem chosenBaseDefiningIdeal_eq_span_specializedConnectors :
    chosenBaseDefiningIdeal (k := k) D i =
      Ideal.span (Set.range (D.specializedConnectorPolynomial (k := k) i)) := by
  rw [← map_toricIdeal_eq_chosenBaseDefiningIdeal D i,
    D.toricIdeal_eq_span_baseAdaptedGlobalConnectorBinomials i, Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨D.baseAdaptedGlobalConnectorBinomial i g, ⟨g, rfl⟩, rfl⟩

theorem disjoint_three_supports_one_singleton (u v : Fin 3 →₀ ℕ)
    (hu : u.support.Nonempty) (hv : v.support.Nonempty) (h : Disjoint u.support v.support) :
    u.support.card = 1 ∨ v.support.card = 1 := by
  have hc : (u.support ∪ v.support).card ≤ 3 := by
    simpa using Finset.card_le_card (Finset.subset_univ (u.support ∪ v.support))
  rw [Finset.card_union_of_disjoint h] at hc
  have hcu := Finset.card_pos.mpr hu
  have hcv := Finset.card_pos.mpr hv
  omega

theorem internal_connector_pure_side (g : D.BaseAdaptedGlobalConnector i)
    (hi : i ∉ D.combinedSupport g.1.1) :
    (D.connectorLeftTail i g).support.card = 1 ∨ (D.connectorRightTail i g).support.card = 1 :=
  disjoint_three_supports_one_singleton _ _
    (D.internal_connector_tail_supports_nonempty i g hi).1
    (D.internal_connector_tail_supports_nonempty i g hi).2 (D.connector_tail_supports_disjoint i g)

def IsInternalBaseConnector (g : D.BaseAdaptedGlobalConnector i) : Prop :=
  i ∉ D.combinedSupport g.1.1

def internalBaseConnectorFinset : Finset (D.BaseAdaptedGlobalConnector i) :=
  Finset.univ.filter (D.IsInternalBaseConnector i)

def externalBaseConnectorFinset : Finset (D.BaseAdaptedGlobalConnector i) :=
  Finset.univ.filter (fun g => ¬D.IsInternalBaseConnector i g)

private def internalBettiBudgetEquiv :
    {d : D.BettiDegreeIndex // i ∉ D.combinedSupport d.1} ≃
      {d : D.BudgetDegree // i ∉ D.combinedSupport d.1} where
  toFun d := by
    have hc : D.supportCard d.1.1 < 4 := by
      obtain ⟨q, hq, _⟩ := D.fourBaseBudget_includes d.1.2 d.2
      rw [← hq]
      exact q.2.2
    exact ⟨⟨d.1.1, d.1.2, hc⟩, d.2⟩
  invFun d := ⟨⟨d.1.1, d.1.2.1⟩, d.2⟩
  left_inv d := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv d := by apply Subtype.ext; apply Subtype.ext; rfl

theorem internalBaseConnectorFinset_card :
    (D.internalBaseConnectorFinset i).card = D.fourBaseBudget i := by
  classical
  calc
    (D.internalBaseConnectorFinset i).card =
        Fintype.card {g : D.BaseAdaptedGlobalConnector i // D.IsInternalBaseConnector i g} :=
      (Fintype.card_subtype (D.IsInternalBaseConnector i)).symm
    _ = Fintype.card (Σ d : {d : D.BettiDegreeIndex // i ∉ D.combinedSupport d.1},
        D.BaseAdaptedConnector i d.1.2) :=
      Fintype.card_congr (Equiv.subtypeSigmaEquiv
        (fun d : D.BettiDegreeIndex => D.BaseAdaptedConnector i d.2)
        (fun d : D.BettiDegreeIndex => i ∉ D.combinedSupport d.1))
    _ = ∑ d : {d : D.BettiDegreeIndex // i ∉ D.combinedSupport d.1},
        D.bettiContribution d.1.1 := by
      rw [Fintype.card_sigma]
      exact Finset.sum_congr rfl (fun d _ => D.baseAdaptedConnector_card i d.1.2)
    _ = ∑ d : {d : D.BudgetDegree // i ∉ D.combinedSupport d.1},
        D.bettiContribution d.1.1 :=
      Fintype.sum_equiv (D.internalBettiBudgetEquiv i) _ _ (fun _ => rfl)
    _ = D.fourBaseBudget i := by
      unfold fourBaseBudget
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype
        (Finset.univ.filter (fun d : D.BudgetDegree => i ∉ D.combinedSupport d.1))
        (by intro d; simp) (fun d : D.BudgetDegree => D.bettiContribution d.1)).symm

theorem baseAdaptedGlobalConnector_card_eq_rho :
    Fintype.card (D.BaseAdaptedGlobalConnector i) = D.semigroupRho := by
  rw [D.semigroupRho_eq_sum_bettiContribution, Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun d _ => D.baseAdaptedConnector_card i d.2)

theorem externalBaseConnectorFinset_card :
    (D.externalBaseConnectorFinset i).card = D.semigroupRho - D.fourBaseBudget i := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (D.BaseAdaptedGlobalConnector i))) (D.IsInternalBaseConnector i)
  change (D.internalBaseConnectorFinset i).card + (D.externalBaseConnectorFinset i).card =
    Fintype.card (D.BaseAdaptedGlobalConnector i) at h
  rw [D.internalBaseConnectorFinset_card, D.baseAdaptedGlobalConnector_card_eq_rho] at h
  omega

def chosenBaseReducedRelationFamily : Finset (D.BaseAdaptedGlobalConnector i) := Finset.univ

theorem chosenBaseReducedRelationFamily_generates :
    chosenBaseDefiningIdeal (k := k) D i = Ideal.span
      {p | ∃ g ∈ D.chosenBaseReducedRelationFamily i, p = D.specializedConnectorPolynomial (k := k) i g} := by
  rw [D.chosenBaseDefiningIdeal_eq_span_specializedConnectors i]
  congr 1
  ext p
  simp [chosenBaseReducedRelationFamily, Set.mem_range, eq_comm]

def IsMonomialChosenBaseIdeal : Prop :=
  ∃ M : Finset (Fin 3 →₀ ℕ), chosenBaseDefiningIdeal (k := k) D i =
    Ideal.span ((fun u => MvPolynomial.monomial u (1 : k)) '' (M : Set (Fin 3 →₀ ℕ)))

theorem all_connectors_external_of_budget_zero (hB : D.fourBaseBudget i = 0)
    (g : D.BaseAdaptedGlobalConnector i) : i ∈ D.combinedSupport g.1.1 := by
  by_contra hi
  have hempty : D.internalBaseConnectorFinset i = ∅ :=
    Finset.card_eq_zero.mp ((D.internalBaseConnectorFinset_card i).trans hB)
  have hg : g ∈ D.internalBaseConnectorFinset i := by simp [internalBaseConnectorFinset, IsInternalBaseConnector, hi]
  rw [hempty] at hg
  exact Finset.notMem_empty g hg

theorem chosenBaseIdeal_monomial_of_budget_eq_zero (hB : D.fourBaseBudget i = 0) :
    D.IsMonomialChosenBaseIdeal (k := k) i := by
  let M := (Finset.univ : Finset (D.BaseAdaptedGlobalConnector i)).image (D.connectorRightTail i)
  refine ⟨M, ?_⟩
  rw [D.chosenBaseDefiningIdeal_eq_span_specializedConnectors i]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro p ⟨g, rfl⟩
    rw [D.specializedConnectorPolynomial_external i g (D.all_connectors_external_of_budget_zero i hB g)]
    apply neg_mem
    apply Ideal.subset_span
    refine ⟨D.connectorRightTail i g, ?_, rfl⟩
    exact Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩
  · rw [Ideal.span_le]
    rintro p ⟨u, hu, rfl⟩
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hu
    have hg : D.specializedConnectorPolynomial (k := k) i g ∈
        Ideal.span (Set.range (D.specializedConnectorPolynomial (k := k) i)) :=
      Ideal.subset_span ⟨g, rfl⟩
    rw [D.specializedConnectorPolynomial_external i g (D.all_connectors_external_of_budget_zero i hB g)] at hg
    simpa using neg_mem hg

theorem existsUnique_internal_connector_of_budget_one (hB : D.fourBaseBudget i = 1) :
    ∃! g : D.BaseAdaptedGlobalConnector i, D.IsInternalBaseConnector i g := by
  have hcard := (D.internalBaseConnectorFinset_card i).trans hB
  obtain ⟨g, hg, huniq⟩ := Finset.card_eq_one_iff_existsUnique.mp hcard
  refine ⟨g, ?_, ?_⟩
  · simpa [internalBaseConnectorFinset] using hg
  · intro h hh
    apply huniq
    simpa [internalBaseConnectorFinset] using hh

def externalSpecializedConnectorSet : Set (TailPoly k) :=
  {p | ∃ g : D.BaseAdaptedGlobalConnector i,
    ¬D.IsInternalBaseConnector i g ∧ p = D.specializedConnectorPolynomial (k := k) i g}

def OneLiveBinomialGeneration : Prop :=
  ∃ g : D.BaseAdaptedGlobalConnector i, D.IsInternalBaseConnector i g ∧
    (∀ h : D.BaseAdaptedGlobalConnector i, D.IsInternalBaseConnector i h → h = g) ∧
    chosenBaseDefiningIdeal (k := k) D i = Ideal.span
      ({D.specializedConnectorPolynomial (k := k) i g} ∪ D.externalSpecializedConnectorSet (k := k) i) ∧
    D.LiveTailBinomial (k := k) i (D.specializedConnectorPolynomial (k := k) i g) ∧
    ((D.connectorLeftTail i g).support.card = 1 ∨ (D.connectorRightTail i g).support.card = 1) ∧
    (∀ h : D.BaseAdaptedGlobalConnector i, h ≠ g →
      D.specializedConnectorPolynomial (k := k) i h = -MvPolynomial.monomial (D.connectorRightTail i h) 1 ∧
        D.specializedConnectorPolynomial (k := k) i h ≠ 0)

theorem chosenBaseIdeal_one_live_binomial_generation_of_budget_eq_one
    (hB : D.fourBaseBudget i = 1) : D.OneLiveBinomialGeneration (k := k) i := by
  obtain ⟨g, hg, huniq⟩ := D.existsUnique_internal_connector_of_budget_one i hB
  refine ⟨g, hg, huniq, ?_, D.specializedConnector_isLiveBinomial_of_base_not_mem_support i g hg,
    D.internal_connector_pure_side i g hg, ?_⟩
  · rw [D.chosenBaseDefiningIdeal_eq_span_specializedConnectors i]
    congr 1
    ext p
    constructor
    · rintro ⟨h, rfl⟩
      by_cases hh : D.IsInternalBaseConnector i h
      · exact Or.inl (by rw [huniq h hh]; exact Set.mem_singleton _)
      · exact Or.inr ⟨h, hh, rfl⟩
    · rintro (hp | ⟨h, hh, rfl⟩)
      · exact ⟨g, (Set.mem_singleton_iff.mp hp).symm⟩
      · exact ⟨h, rfl⟩
  · intro h hne
    have hh : i ∈ D.combinedSupport h.1.1 := by
      by_contra hi
      exact hne (huniq h hi)
    exact D.specializedConnector_isMonomial_of_base_mem_support i h hh

/-- Stable generation-only boundary; no ideal-generator minimality field.-/
structure ChosenBaseReduction : Prop where
  commuting : fourPolyToChosenBase (k := k) D i =
    (tailPolyToChosenBase D i).comp (baseSpecialization D i)
  exactImage : Ideal.map (baseSpecialization (k := k) D i).toRingHom D.toricIdeal = chosenBaseDefiningIdeal D i
  toricGeneration : D.toricIdeal (k := k) =
    Ideal.span (Set.range (D.baseAdaptedGlobalConnectorBinomial (k := k) i))
  taggedCard : (D.baseAdaptedConnectorRelationFinset i).card = D.semigroupRho
  externalShape : ∀ g : D.BaseAdaptedGlobalConnector i, i ∈ D.combinedSupport g.1.1 →
    D.specializedConnectorPolynomial (k := k) i g = -MvPolynomial.monomial (D.connectorRightTail i g) 1 ∧
      D.specializedConnectorPolynomial (k := k) i g ≠ 0
  internalShape : ∀ g : D.BaseAdaptedGlobalConnector i, D.IsInternalBaseConnector i g →
    D.LiveTailBinomial (k := k) i (D.specializedConnectorPolynomial (k := k) i g)
  chosenGeneration : chosenBaseDefiningIdeal (k := k) D i =
    Ideal.span (Set.range (D.specializedConnectorPolynomial (k := k) i))
  internalCard : (D.internalBaseConnectorFinset i).card = D.fourBaseBudget i
  externalCard : (D.externalBaseConnectorFinset i).card = D.semigroupRho - D.fourBaseBudget i
  zeroBudget : D.fourBaseBudget i = 0 → D.IsMonomialChosenBaseIdeal (k := k) i
  oneBudget : D.fourBaseBudget i = 1 → D.OneLiveBinomialGeneration (k := k) i

theorem chosenBaseReduction : D.ChosenBaseReduction (k := k) i where
  commuting := fourPolyToChosenBase_eq D i
  exactImage := map_toricIdeal_eq_chosenBaseDefiningIdeal D i
  toricGeneration := D.toricIdeal_eq_span_baseAdaptedGlobalConnectorBinomials i
  taggedCard := D.baseAdaptedConnectorRelationFinset_card_eq_rho i
  externalShape := D.specializedConnector_isMonomial_of_base_mem_support i
  internalShape := D.specializedConnector_isLiveBinomial_of_base_not_mem_support i
  chosenGeneration := D.chosenBaseDefiningIdeal_eq_span_specializedConnectors i
  internalCard := D.internalBaseConnectorFinset_card i
  externalCard := D.externalBaseConnectorFinset_card i
  zeroBudget := D.chosenBaseIdeal_monomial_of_budget_eq_zero i
  oneBudget := D.chosenBaseIdeal_one_live_binomial_generation_of_budget_eq_one i

end FourGeneratedNumericalSemigroup
end
end P23.Semigroup
