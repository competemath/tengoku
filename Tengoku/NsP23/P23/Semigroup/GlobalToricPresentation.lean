import Tengoku.NsP23.P23.Semigroup.BettiLowerDegree
import Tengoku.Seed.RingTheory.Polynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Global toric presentations for four-generated numerical semigroups

This file globalizes the exact degree-local relation spaces.  Presentations
are finite families of genuine same-fiber factorization relations.
-/

namespace P23.Semigroup

open scoped BigOperators

noncomputable section

open FourGeneratedNumericalSemigroup

/-- A genuine homogeneous factorization relation.-/
structure SemigroupPresentationRelation
    (D : FourGeneratedNumericalSemigroup) where
  degree : ℕ
  left : D.FactorizationAt degree
  right : D.FactorizationAt degree
  deriving DecidableEq

namespace SemigroupPresentationRelation

variable {D : FourGeneratedNumericalSemigroup}

@[ext] theorem ext {r s : SemigroupPresentationRelation D}
    (hdegree : r.degree = s.degree)
    (hleft : r.left.1 = s.left.1) (hright : r.right.1 = s.right.1) : r = s := by
  cases r with
  | mk d l r =>
    cases s with
    | mk e l' r' =>
      simp only at hdegree
      subst e
      cases Subtype.ext hleft
      cases Subtype.ext hright
      rfl

end SemigroupPresentationRelation

variable {k : Type*} [Field k]

namespace FourGeneratedNumericalSemigroup

variable (D : FourGeneratedNumericalSemigroup)

def relationDegree (r : SemigroupPresentationRelation D) : ℕ := r.degree

def presentationRelationBinomial (r : SemigroupPresentationRelation D) :
    FourPoly k :=
  D.fiberBinomial (k := k) r.left r.right

theorem presentationRelationBinomial_eq_fiberBinomial
    (r : SemigroupPresentationRelation D) :
    D.presentationRelationBinomial (k := k) r =
      D.fiberBinomial (k := k) r.left r.right := rfl

def presentationIdeal (R : Finset (SemigroupPresentationRelation D)) :
    Ideal (FourPoly k) :=
  Ideal.span {p | ∃ r ∈ R, p = D.presentationRelationBinomial (k := k) r}

def IsSemigroupPresentation (R : Finset (SemigroupPresentationRelation D)) : Prop :=
  D.presentationIdeal (k := k) R = D.toricIdeal (k := k)

/-- The subtype of genuine Betti degrees.  Finiteness is proved below.-/
abbrev BettiDegreeIndex := {d : ℕ // D.IsBettiDegree d}

/-- A connector tagged by its Betti degree.-/
abbrev GlobalConnector :=
  Σ d : D.BettiDegreeIndex, D.ComponentConnector d.2

def globalConnectorRelation (g : D.GlobalConnector) :
    SemigroupPresentationRelation D where
  degree := g.1.1
  left := (D.connectorEndpoints g.1.2 g.2).1
  right := (D.connectorEndpoints g.1.2 g.2).2

def globalConnectorBinomial (g : D.GlobalConnector) : FourPoly k :=
  D.presentationRelationBinomial (k := k) (D.globalConnectorRelation g)

@[simp] theorem globalConnectorRelation_degree (g : D.GlobalConnector) :
    (D.globalConnectorRelation g).degree = g.1.1 := rfl

@[simp] theorem globalConnectorBinomial_eq (g : D.GlobalConnector) :
    D.globalConnectorBinomial (k := k) g =
      D.fiberBinomial (k := k)
        (D.connectorEndpoints g.1.2 g.2).1
        (D.connectorEndpoints g.1.2 g.2).2 := rfl

private theorem betti_of_distinct_components {d : ℕ}
    {C E : D.BettiComponent d} (h : C ≠ E) : D.IsBettiDegree d := by
  unfold IsBettiDegree componentCount
  have hcard : 1 < Fintype.card (D.BettiComponent d) :=
    Fintype.one_lt_card_iff.mpr ⟨C, E, h⟩
  omega

private theorem lowerToricIdeal_le_globalConnectorSpan
    (d : ℕ)
    (ih : ∀ e < d, ∀ (u v : D.FactorizationAt e),
      D.fiberBinomial (k := k) u v ∈
        Ideal.span (Set.range (D.globalConnectorBinomial (k := k)))) :
    D.lowerToricIdeal (k := k) d ≤
      Ideal.span (Set.range (D.globalConnectorBinomial (k := k))) := by
  unfold lowerToricIdeal
  rw [Ideal.span_le]
  rintro p ⟨e, hed, u, v, rfl⟩
  exact ih e hed u v

private theorem representativeBinomial_mem_globalConnectorSpan
    {d : ℕ} (hd : D.IsBettiDegree d)
    (C E : D.BettiComponent d) :
    D.fiberBinomial (k := k) (D.componentRepresentative C)
        (D.componentRepresentative E) ∈
      Ideal.span (Set.range (D.globalConnectorBinomial (k := k))) := by
  classical
  by_cases hC : C = D.rootComponent hd
  · subst C
    by_cases hE : E = D.rootComponent hd
    · subst E
      simp
    · let e : D.ComponentConnector hd := ⟨E, hE⟩
      apply Ideal.subset_span
      refine ⟨⟨⟨d, hd⟩, e⟩, ?_⟩
      change D.fiberBinomial (k := k)
        (D.componentRepresentative (D.rootComponent hd))
        (D.componentRepresentative E) = _
      rfl
  · by_cases hE : E = D.rootComponent hd
    · subst E
      let e : D.ComponentConnector hd := ⟨C, hC⟩
      have hg : D.globalConnectorBinomial (k := k) ⟨⟨d, hd⟩, e⟩ ∈
          Ideal.span (Set.range (D.globalConnectorBinomial (k := k))) :=
        Ideal.subset_span ⟨_, rfl⟩
      have hneg : -D.globalConnectorBinomial (k := k) ⟨⟨d, hd⟩, e⟩ ∈
          Ideal.span (Set.range (D.globalConnectorBinomial (k := k))) := neg_mem hg
      simpa only [globalConnectorBinomial, globalConnectorRelation,
        presentationRelationBinomial, connectorEndpoints, fiberBinomial,
        neg_sub] using hneg
    · let eC : D.ComponentConnector hd := ⟨C, hC⟩
      let eE : D.ComponentConnector hd := ⟨E, hE⟩
      have hGC : D.globalConnectorBinomial (k := k) ⟨⟨d, hd⟩, eC⟩ ∈
          Ideal.span (Set.range (D.globalConnectorBinomial (k := k))) :=
        Ideal.subset_span ⟨_, rfl⟩
      have hGE : D.globalConnectorBinomial (k := k) ⟨⟨d, hd⟩, eE⟩ ∈
          Ideal.span (Set.range (D.globalConnectorBinomial (k := k))) :=
        Ideal.subset_span ⟨_, rfl⟩
      have hsub := Ideal.sub_mem _ hGE hGC
      have heq :
          D.globalConnectorBinomial (k := k) ⟨⟨d, hd⟩, eE⟩ -
              D.globalConnectorBinomial (k := k) ⟨⟨d, hd⟩, eC⟩ =
            D.fiberBinomial (k := k) (D.componentRepresentative C)
              (D.componentRepresentative E) := by
        change
          (D.fiberMonomial (k := k) (D.componentRepresentative (D.rootComponent hd)) -
              D.fiberMonomial (k := k) (D.componentRepresentative E)) -
            (D.fiberMonomial (k := k) (D.componentRepresentative (D.rootComponent hd)) -
              D.fiberMonomial (k := k) (D.componentRepresentative C)) =
            D.fiberMonomial (k := k) (D.componentRepresentative C) -
              D.fiberMonomial (k := k) (D.componentRepresentative E)
        abel
      rw [← heq]
      exact hsub

/-- Every same-fiber binomial is generated by the root-star connectors over
all Betti degrees.-/
theorem fiberBinomial_mem_span_globalConnectorBinomials
    {d : ℕ} (u v : D.FactorizationAt d) :
    D.fiberBinomial (k := k) u v ∈
      Ideal.span (Set.range (D.globalConnectorBinomial (k := k))) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases hcomp : D.componentOf u = D.componentOf v
      · exact D.lowerToricIdeal_le_globalConnectorSpan d ih
          (D.fiberBinomial_mem_lower_of_sameComponent (k := k) hcomp)
      · let C := D.componentOf u
        let E := D.componentOf v
        have hd : D.IsBettiDegree d := D.betti_of_distinct_components hcomp
        let ru := D.componentRepresentative C
        let rv := D.componentRepresentative E
        have hucomp : D.componentOf u = D.componentOf ru := by
          simp [ru, C, D.componentRepresentative_component]
        have hvcomp : D.componentOf rv = D.componentOf v := by
          simp [rv, E, D.componentRepresentative_component]
        have hu : D.fiberBinomial (k := k) u ru ∈
            Ideal.span (Set.range (D.globalConnectorBinomial (k := k))) :=
          D.lowerToricIdeal_le_globalConnectorSpan d ih
            (D.fiberBinomial_mem_lower_of_sameComponent (k := k) hucomp)
        have hv : D.fiberBinomial (k := k) rv v ∈
            Ideal.span (Set.range (D.globalConnectorBinomial (k := k))) :=
          D.lowerToricIdeal_le_globalConnectorSpan d ih
            (D.fiberBinomial_mem_lower_of_sameComponent (k := k) hvcomp)
        have hm := D.representativeBinomial_mem_globalConnectorSpan
          (k := k) hd C E
        have hadd := Ideal.add_mem _ (Ideal.add_mem _ hu hm) hv
        simpa [ru, rv, fiberBinomial] using hadd

theorem toricIdeal_eq_span_globalConnectorBinomials :
    D.toricIdeal (k := k) =
      Ideal.span (Set.range (D.globalConnectorBinomial (k := k))) := by
  apply le_antisymm
  · rw [D.toricIdeal_eq_span_fiberBinomials (k := k), Ideal.span_le]
    rintro p ⟨d, u, v, rfl⟩
    exact D.fiberBinomial_mem_span_globalConnectorBinomials (k := k) u v
  · rw [Ideal.span_le]
    rintro p ⟨g, rfl⟩
    exact D.fiberBinomial_mem_toricIdeal _ _

private def relationOfFiberBinomial
    (p : {p : FourPoly ℚ // p ∈ D.fiberBinomialSet (k := ℚ)}) :
    SemigroupPresentationRelation D :=
  let d := Classical.choose p.2
  let hd := Classical.choose_spec p.2
  let u := Classical.choose hd
  let hu := Classical.choose_spec hd
  let v := Classical.choose hu
  ⟨d, u, v⟩

private theorem relationOfFiberBinomial_spec
    (p : {p : FourPoly ℚ // p ∈ D.fiberBinomialSet (k := ℚ)}) :
    D.presentationRelationBinomial (k := ℚ) (D.relationOfFiberBinomial p) = p.1 := by
  change D.fiberBinomial (k := ℚ)
      (Classical.choose (Classical.choose_spec p.2))
      (Classical.choose (Classical.choose_spec
        (Classical.choose_spec p.2))) = p.1
  exact (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec p.2))).symm

/-- A finite presentation by genuine factorization relations exists.  The
proof uses Noetherianity only to extract a finite subset from the frozen
same-fiber-binomial spanning set.-/
theorem exists_finite_semigroupPresentation :
    ∃ R : Finset (SemigroupPresentationRelation D),
      D.IsSemigroupPresentation (k := ℚ) R := by
  classical
  have hfg : (Ideal.span (D.fiberBinomialSet (k := ℚ)) :
      Ideal (FourPoly ℚ)).FG := by
    rw [← D.toricIdeal_eq_span_fiberBinomials (k := ℚ)]
    exact Ideal.FG.of_isNoetherianRing _
  obtain ⟨S, hSsub, hSspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset
      (D.fiberBinomialSet (k := ℚ))).1 hfg
  let R : Finset (SemigroupPresentationRelation D) :=
    S.attach.image fun p => D.relationOfFiberBinomial
      ⟨p.1, hSsub p.2⟩
  refine ⟨R, ?_⟩
  unfold IsSemigroupPresentation
  rw [D.toricIdeal_eq_span_fiberBinomials (k := ℚ)]
  change Submodule.span (FourPoly ℚ)
      {p | ∃ r ∈ R, p = D.presentationRelationBinomial (k := ℚ) r} =
    Submodule.span (FourPoly ℚ) (D.fiberBinomialSet (k := ℚ))
  rw [hSspan]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro p ⟨r, hr, rfl⟩
    unfold R at hr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    apply Ideal.subset_span
    change D.presentationRelationBinomial (k := ℚ)
        (D.relationOfFiberBinomial ⟨q.1, hSsub q.2⟩) ∈ S
    rw [D.relationOfFiberBinomial_spec]
    exact q.2
  · rw [Ideal.span_le]
    intro p hp
    have hpFiber : p ∈ D.fiberBinomialSet (k := ℚ) := hSsub hp
    let q : {q : FourPoly ℚ // q ∈ D.fiberBinomialSet (k := ℚ)} := ⟨p, hpFiber⟩
    have hr : D.relationOfFiberBinomial q ∈ R := by
      unfold R
      apply Finset.mem_image.mpr
      refine ⟨⟨p, hp⟩, Finset.mem_attach _ _, ?_⟩
      rfl
    apply Submodule.subset_span
    refine ⟨D.relationOfFiberBinomial q, hr, ?_⟩
    exact (D.relationOfFiberBinomial_spec q).symm

/-- Degree-zero scalar coefficient used by the exact-degree detector.-/
def relationMultiplierConstantCoeff (p : FourPoly k) : k :=
  MvPolynomial.constantCoeff p

private theorem weightedDegree_pos_of_ne_zero
    (w : Fin 4 →₀ ℕ) (hw : w ≠ 0) : 0 < D.weightedDegree w := by
  classical
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hw
  have hwj : 0 < w j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
  have hterm : 0 < w j * D.n j := Nat.mul_pos hwj (D.positive j)
  have hle : w j * D.n j ≤ ∑ i : Fin 4, w i * D.n i :=
    Finset.single_le_sum (s := Finset.univ) (f := fun i => w i * D.n i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  change 0 < ∑ i : Fin 4, w i * D.n i
  exact lt_of_lt_of_le hterm hle

def relationComponentDeltaAt (d : ℕ)
    (r : SemigroupPresentationRelation D) (h : r.degree = d) :
    D.BettiComponent d → k := by
  subst d
  exact D.componentDelta (k := k) r.left r.right

/-- Strictly lower relation degrees disappear under the degree-`d` detector.-/
theorem degreeComponentCoeffVector_mul_relation_of_lt
    (d : ℕ) (r : SemigroupPresentationRelation D) (p : FourPoly k)
    (h : r.degree < d) :
    D.degreeComponentCoeffVector (k := k) d
        (p * D.presentationRelationBinomial (k := k) r) = 0 :=
  D.degreeComponentCoeffVector_mul_fiberBinomial h r.left r.right p

private theorem degreeComponentCoeffVector_monomial_mul_relation_of_gt
    (d : ℕ) (r : SemigroupPresentationRelation D)
    (h : d < r.degree) (w : Fin 4 →₀ ℕ) (c : k) :
    D.degreeComponentCoeffVector (k := k) d
        (MvPolynomial.monomial w c *
          D.presentationRelationBinomial (k := k) r) = 0 := by
  have hleft : D.weightedDegree (w + r.left.1) ≠ d := by
    change weightedDegreeOf D.n (w + r.left.1) ≠ d
    rw [weightedDegreeOf_add]
    have hdeg := D.factorizationAt_degree r.left
    change weightedDegreeOf D.n r.left.1 = r.degree at hdeg
    rw [hdeg]
    omega
  have hright : D.weightedDegree (w + r.right.1) ≠ d := by
    change weightedDegreeOf D.n (w + r.right.1) ≠ d
    rw [weightedDegreeOf_add]
    have hdeg := D.factorizationAt_degree r.right
    change weightedDegreeOf D.n r.right.1 = r.degree at hdeg
    rw [hdeg]
    omega
  have hpoly : MvPolynomial.monomial w c *
        D.presentationRelationBinomial (k := k) r =
      MvPolynomial.monomial (w + r.left.1) c -
        MvPolynomial.monomial (w + r.right.1) c := by
    simp [presentationRelationBinomial, fiberBinomial, fiberMonomial, mul_sub,
      MvPolynomial.monomial_mul_monomial]
  rw [hpoly, map_sub,
    D.degreeComponentCoeffVector_monomial_of_degree_ne d _ _ hleft,
    D.degreeComponentCoeffVector_monomial_of_degree_ne d _ _ hright,
    sub_zero]

/-- Strictly higher relation degrees cannot contribute to degree `d`.-/
theorem degreeComponentCoeffVector_mul_relation_of_gt
    (d : ℕ) (r : SemigroupPresentationRelation D) (p : FourPoly k)
    (h : d < r.degree) :
    D.degreeComponentCoeffVector (k := k) d
        (p * D.presentationRelationBinomial (k := k) r) = 0 := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  simp only [Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro w _
  exact D.degreeComponentCoeffVector_monomial_mul_relation_of_gt d r h w _

private theorem degreeComponentCoeffVector_monomial_mul_relation_of_eq
    (r : SemigroupPresentationRelation D) (w : Fin 4 →₀ ℕ) (c : k) :
    D.degreeComponentCoeffVector (k := k) r.degree
        (MvPolynomial.monomial w c *
          D.presentationRelationBinomial (k := k) r) =
      (if w = 0 then c else 0) •
        D.componentDelta (k := k) r.left r.right := by
  classical
  by_cases hw : w = 0
  · subst w
    simp only [ite_eq_left, MvPolynomial.monomial_zero']
    have hpoly : MvPolynomial.C c *
          D.presentationRelationBinomial (k := k) r =
        c • D.fiberBinomial (k := k) r.left r.right := by
      simp [presentationRelationBinomial, Algebra.smul_def]
    rw [hpoly]
    rw [← D.fiberPolynomial_fiberDelta r.left r.right, map_smul,
      D.degreeComponentCoeffVector_fiberPolynomial]
    have hcomp : D.componentCoeff (k := k) r.degree
          (D.fiberDelta (k := k) r.left r.right) =
        D.componentDelta (k := k) r.left r.right :=
      congrArg Subtype.val
        (D.fiberToComponentRelation_fiberDelta (k := k) r.left r.right)
    rw [hcomp]
  · have hpos := D.weightedDegree_pos_of_ne_zero w hw
    change 0 < weightedDegreeOf D.n w at hpos
    have hleft : D.weightedDegree (w + r.left.1) ≠ r.degree := by
      change weightedDegreeOf D.n (w + r.left.1) ≠ r.degree
      rw [weightedDegreeOf_add]
      have hdeg := D.factorizationAt_degree r.left
      change weightedDegreeOf D.n r.left.1 = r.degree at hdeg
      rw [hdeg]
      omega
    have hright : D.weightedDegree (w + r.right.1) ≠ r.degree := by
      change weightedDegreeOf D.n (w + r.right.1) ≠ r.degree
      rw [weightedDegreeOf_add]
      have hdeg := D.factorizationAt_degree r.right
      change weightedDegreeOf D.n r.right.1 = r.degree at hdeg
      rw [hdeg]
      omega
    have hpoly : MvPolynomial.monomial w c *
          D.presentationRelationBinomial (k := k) r =
        MvPolynomial.monomial (w + r.left.1) c -
          MvPolynomial.monomial (w + r.right.1) c := by
      simp [presentationRelationBinomial, fiberBinomial, fiberMonomial, mul_sub,
        MvPolynomial.monomial_mul_monomial]
    rw [hpoly, map_sub,
      D.degreeComponentCoeffVector_monomial_of_degree_ne _ _ _ hleft,
      D.degreeComponentCoeffVector_monomial_of_degree_ne _ _ _ hright,
      sub_zero, ite_eq_right hw, zero_smul]

/-- At equal degree, only the multiplier's degree-zero monomial survives.-/
theorem degreeComponentCoeffVector_mul_relation_of_eq
    (d : ℕ) (r : SemigroupPresentationRelation D) (p : FourPoly k)
    (h : r.degree = d) :
    D.degreeComponentCoeffVector (k := k) d
        (p * D.presentationRelationBinomial (k := k) r) =
      relationMultiplierConstantCoeff p •
        D.relationComponentDeltaAt (k := k) d r h := by
  subst d
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  simp only [Finset.sum_mul, map_sum,
    D.degreeComponentCoeffVector_monomial_mul_relation_of_eq]
  rw [Finset.sum_eq_single 0]
  · simp [relationMultiplierConstantCoeff, MvPolynomial.constantCoeff_eq,
      relationComponentDeltaAt]
  · intro b hb hb0
    simp [hb0]
  · intro h0
    have hc0 : MvPolynomial.coeff 0 p = 0 := by
      simpa [MvPolynomial.mem_support_iff] using h0
    simp [hc0, relationMultiplierConstantCoeff, MvPolynomial.constantCoeff_eq]

def relationsAtDegree (R : Finset (SemigroupPresentationRelation D)) (d : ℕ) :
    Finset (SemigroupPresentationRelation D) :=
  R.filter fun r => r.degree = d

@[simp] theorem mem_relationsAtDegree
    {R : Finset (SemigroupPresentationRelation D)} {d : ℕ}
    {r : SemigroupPresentationRelation D} :
    r ∈ D.relationsAtDegree R d ↔ r ∈ R ∧ r.degree = d := by
  simp [relationsAtDegree]

def relationFiberAtDegree (d : ℕ) (r : SemigroupPresentationRelation D)
    (h : r.degree = d) : D.FiberRelationSpace k d := by
  subst d
  exact D.fiberDeltaRelation (k := k) r.left r.right

def relationsAtDegreeFiberFinset
    (R : Finset (SemigroupPresentationRelation D)) (d : ℕ) :
    Finset (D.FiberRelationSpace k d) := by
  classical
  exact (D.relationsAtDegree R d).attach.image fun r =>
    D.relationFiberAtDegree (k := k) d r.1
      ((D.mem_relationsAtDegree.mp r.2).2)

def fiberToComponentVector (d : ℕ) :
    D.FiberRelationSpace k d →ₗ[k] (D.BettiComponent d → k) :=
  (D.ComponentRelationSpace k d).subtype.comp
    (D.fiberToComponentRelation (k := k) d)

def relationsAtDegreeComponentVectorFinset
    (R : Finset (SemigroupPresentationRelation D)) (d : ℕ) :
    Finset (D.BettiComponent d → k) := by
  classical
  exact (D.relationsAtDegreeFiberFinset (k := k) R d).image
    (D.fiberToComponentVector (k := k) d)

private theorem relationComponentDeltaAt_mem_componentVectorFinset
    {R : Finset (SemigroupPresentationRelation D)} {d : ℕ}
    {r : SemigroupPresentationRelation D} (hr : r ∈ R)
    (h : r.degree = d) :
    D.relationComponentDeltaAt (k := k) d r h ∈
      D.relationsAtDegreeComponentVectorFinset (k := k) R d := by
  classical
  unfold relationsAtDegreeComponentVectorFinset relationsAtDegreeFiberFinset
  apply Finset.mem_image.mpr
  let rr : {s // s ∈ D.relationsAtDegree R d} :=
    ⟨r, Finset.mem_filter.mpr ⟨hr, h⟩⟩
  refine ⟨D.relationFiberAtDegree (k := k) d r h, ?_, ?_⟩
  · apply Finset.mem_image.mpr
    refine ⟨rr, Finset.mem_attach _ _, ?_⟩
    rfl
  · subst d
    exact congrArg Subtype.val
      (D.fiberToComponentRelation_fiberDelta (k := k) r.left r.right)

private theorem detector_mem_span_componentVectors_of_mem_presentationIdeal
    (R : Finset (SemigroupPresentationRelation D)) (d : ℕ)
    (p : FourPoly k) (hp : p ∈ D.presentationIdeal (k := k) R) :
    D.degreeComponentCoeffVector (k := k) d p ∈
      Submodule.span k
        (D.relationsAtDegreeComponentVectorFinset (k := k) R d :
          Set (D.BettiComponent d → k)) := by
  classical
  unfold presentationIdeal at hp
  have hall : ∀ q : FourPoly k,
      D.degreeComponentCoeffVector (k := k) d (q * p) ∈
        Submodule.span k
          (D.relationsAtDegreeComponentVectorFinset (k := k) R d :
            Set (D.BettiComponent d → k)) := by
    refine Submodule.span_induction
      (p := fun x (_hx : x ∈ Submodule.span (FourPoly k)
        {p | ∃ r ∈ R, p = D.presentationRelationBinomial (k := k) r}) =>
        ∀ q : FourPoly k,
          D.degreeComponentCoeffVector (k := k) d (q * x) ∈
            Submodule.span k
              (D.relationsAtDegreeComponentVectorFinset (k := k) R d :
                Set (D.BettiComponent d → k))) ?_ ?_ ?_ ?_ hp
    · intro x hx
      rcases hx with ⟨r, hr, rfl⟩
      intro q
      rcases lt_trichotomy r.degree d with hlt | heq | hgt
      · rw [D.degreeComponentCoeffVector_mul_relation_of_lt d r q hlt]
        exact Submodule.zero_mem _
      · rw [D.degreeComponentCoeffVector_mul_relation_of_eq d r q heq]
        exact Submodule.smul_mem _ _
          (Submodule.subset_span
            (D.relationComponentDeltaAt_mem_componentVectorFinset hr heq))
      · rw [D.degreeComponentCoeffVector_mul_relation_of_gt d r q hgt]
        exact Submodule.zero_mem _
    · intro q
      simpa using (Submodule.zero_mem
        (Submodule.span k
          (D.relationsAtDegreeComponentVectorFinset (k := k) R d :
            Set (D.BettiComponent d → k))))
    · intro x y hx hy ihx ihy q
      rw [mul_add, map_add]
      exact Submodule.add_mem _ (ihx q) (ihy q)
    · intro a x hx ih q
      simpa [smul_eq_mul, mul_assoc] using ih (q * a)
  simpa using hall 1

private theorem componentVectorFinset_eq_image
    (R : Finset (SemigroupPresentationRelation D)) (d : ℕ) :
    (D.relationsAtDegreeComponentVectorFinset (k := k) R d :
        Set (D.BettiComponent d → k)) =
      (fun a : D.FiberRelationSpace k d =>
        D.fiberToComponentVector (k := k) d a) ''
        (D.relationsAtDegreeFiberFinset (k := k) R d :
          Set (D.FiberRelationSpace k d)) := by
  classical
  ext z
  simp [relationsAtDegreeComponentVectorFinset]

/-- The exact-degree relations in any genuine global presentation generate
the repaired actual degree-new quotient.-/
theorem relationsAtDegree_span_actualDegreeNew
    (R : Finset (SemigroupPresentationRelation D))
    (hR : D.IsSemigroupPresentation (k := k) R) (d : ℕ) :
    D.GeneratesActualDegreeNewRelations (k := k)
      (D.relationsAtDegreeFiberFinset (k := k) R d) := by
  rw [← D.generatesDegreeDModuloLower_iff_actual]
  intro a
  have hpT : D.fiberPolynomial (k := k) d a.1 ∈ D.toricIdeal (k := k) :=
    (D.fiberPolynomial_mem_toricIdeal_iff d a.1).2 a.2
  have hpP : D.fiberPolynomial (k := k) d a.1 ∈
      D.presentationIdeal (k := k) R := by
    rw [hR]
    exact hpT
  have hdet := D.detector_mem_span_componentVectors_of_mem_presentationIdeal
    R d (D.fiberPolynomial (k := k) d a.1) hpP
  rw [D.degreeComponentCoeffVector_fiberPolynomial,
    D.componentVectorFinset_eq_image] at hdet
  change D.fiberToComponentVector (k := k) d a ∈ _ at hdet
  rw [← LinearMap.map_span] at hdet
  rcases hdet with ⟨b, hb, hab⟩
  refine ⟨b, hb, ?_⟩
  apply (D.fiberPolynomial_mem_lower_iff_componentKernel (k := k) (a - b)).2
  change D.fiberToComponentRelation (k := k) d (a - b) = 0
  rw [map_sub]
  apply sub_eq_zero.mpr
  apply Subtype.ext
  exact hab.symm

/-- Local exact Betti contribution lower bound inside every global
presentation.-/
theorem globalPresentation_degree_card_lower_bound
    (R : Finset (SemigroupPresentationRelation D))
    (hR : D.IsSemigroupPresentation (k := k) R)
    {d : ℕ} (hd : D.IsBettiDegree d) :
    D.bettiContribution d ≤ (D.relationsAtDegree R d).card := by
  classical
  have hlocal := D.actualDegreeToricRelation_generator_card_lower_bound
    (k := k) hd (D.relationsAtDegreeFiberFinset (k := k) R d)
    (D.relationsAtDegree_span_actualDegreeNew R hR d)
  refine hlocal.trans ?_
  unfold relationsAtDegreeFiberFinset
  calc
    ((D.relationsAtDegree R d).attach.image fun
        (r : {s // s ∈ D.relationsAtDegree R d}) =>
      D.relationFiberAtDegree (k := k) d r.1
        ((D.mem_relationsAtDegree.mp r.2).2)).card ≤
        (D.relationsAtDegree R d).attach.card := Finset.card_image_le
    _ = (D.relationsAtDegree R d).card := Finset.card_attach

private def finitePresentation : Finset (SemigroupPresentationRelation D) :=
  Classical.choose D.exists_finite_semigroupPresentation

private theorem finitePresentation_isPresentation :
    D.IsSemigroupPresentation (k := ℚ) D.finitePresentation :=
  Classical.choose_spec D.exists_finite_semigroupPresentation

private theorem relationsAtDegree_finitePresentation_nonempty
    (d : D.BettiDegreeIndex) :
    (D.relationsAtDegree D.finitePresentation d.1).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hlower := D.globalPresentation_degree_card_lower_bound
    D.finitePresentation D.finitePresentation_isPresentation d.2
  rw [hempty] at hlower
  simp only [Finset.card_empty] at hlower
  exact (Nat.not_succ_le_zero 0)
    ((D.bettiContribution_pos d.2).trans_le hlower)

private def bettiWitnessRelation (d : D.BettiDegreeIndex) :
    SemigroupPresentationRelation D :=
  Classical.choose (D.relationsAtDegree_finitePresentation_nonempty d)

private theorem bettiWitnessRelation_mem (d : D.BettiDegreeIndex) :
    D.bettiWitnessRelation d ∈ D.relationsAtDegree D.finitePresentation d.1 :=
  Classical.choose_spec (D.relationsAtDegree_finitePresentation_nonempty d)

private def bettiWitnessInPresentation (d : D.BettiDegreeIndex) :
    {r // r ∈ D.finitePresentation} :=
  ⟨D.bettiWitnessRelation d,
    (D.mem_relationsAtDegree.mp (D.bettiWitnessRelation_mem d)).1⟩

@[simp] private theorem bettiWitnessRelation_degree (d : D.BettiDegreeIndex) :
    (D.bettiWitnessRelation d).degree = d.1 :=
  (D.mem_relationsAtDegree.mp (D.bettiWitnessRelation_mem d)).2

/-- Betti degrees are finite because every one consumes an exact-degree
relation in a single finite genuine presentation.-/
theorem finite_bettiDegrees : Finite D.BettiDegreeIndex := by
  apply Finite.of_injective D.bettiWitnessInPresentation
  intro d e h
  apply Subtype.ext
  have hr : D.bettiWitnessRelation d = D.bettiWitnessRelation e :=
    congrArg Subtype.val h
  calc
    d.1 = (D.bettiWitnessRelation d).degree :=
      (D.bettiWitnessRelation_degree d).symm
    _ = (D.bettiWitnessRelation e).degree := congrArg (·.degree) hr
    _ = e.1 := D.bettiWitnessRelation_degree e

noncomputable instance bettiDegreeIndexFintype : Fintype D.BettiDegreeIndex :=
  @Fintype.ofFinite D.BettiDegreeIndex D.finite_bettiDegrees

private theorem globalConnectorRelation_injective :
    Function.Injective D.globalConnectorRelation := by
  classical
  rintro ⟨gd, gc⟩ ⟨hd, hc⟩ heq
  have hdeg : gd.1 = hd.1 := congrArg (fun r => r.degree) heq
  have htag : gd = hd := Subtype.ext hdeg
  subst hd
  have hrightVal :
      (D.connectorEndpoints gd.2 gc).2.1 =
        (D.connectorEndpoints gd.2 hc).2.1 :=
    congrArg (fun r => r.right.1) heq
  have hright :
      (D.connectorEndpoints gd.2 gc).2 =
        (D.connectorEndpoints gd.2 hc).2 :=
    Subtype.ext hrightVal
  congr 1
  apply Subtype.ext
  have hc := congrArg D.componentOf hright
  simpa [D.connectorEndpoints_components] using hc

/-- The finite canonical family consisting of every root-star connector.-/
def globalConnectorFinset : Finset (SemigroupPresentationRelation D) := by
  classical
  exact Finset.univ.image D.globalConnectorRelation

theorem globalConnectorFinset_isPresentation :
    D.IsSemigroupPresentation (k := k) D.globalConnectorFinset := by
  unfold IsSemigroupPresentation presentationIdeal globalConnectorFinset
  rw [D.toricIdeal_eq_span_globalConnectorBinomials (k := k)]
  congr 1
  ext p
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    refine ⟨D.globalConnectorRelation g, ?_, rfl⟩
    exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩

theorem globalConnectorFinset_card :
    D.globalConnectorFinset.card =
      ∑ d : D.BettiDegreeIndex, D.bettiContribution d.1 := by
  classical
  unfold globalConnectorFinset
  rw [Finset.card_image_of_injective _ D.globalConnectorRelation_injective]
  change Fintype.card D.GlobalConnector = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro d _
  exact D.degreeToricRelation_connector_card_exact d.2

end FourGeneratedNumericalSemigroup

end

end P23.Semigroup
