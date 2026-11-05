import Tengoku.NsP23.P23.Semigroup.BaseAdaptedPresentation
import Tengoku.NsP23.P23.Presentation.KernelMinimality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The genuine chosen-base first-order relation space, over the coefficient field. -/
namespace P23.Semigroup
noncomputable section
open scoped BigOperators
open FourGeneratedNumericalSemigroup P23.Presentation
variable {k : Type*} [Field k]
variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def chosenBaseRelationSubmodule : Submodule k (chosenBaseDefiningIdeal (k := k) D i) :=
  (Submodule.comap (chosenBaseDefiningIdeal (k := k) D i).subtype
    ((polyVariableIdeal (k := k) * chosenBaseDefiningIdeal D i : Ideal (TailPoly k)) :
      Submodule (TailPoly k) (TailPoly k))).restrictScalars k

abbrev ChosenBaseRelationSpace (k : Type*) [Field k]
    (D : FourGeneratedNumericalSemigroup) (i : Fin 4) :=
  (chosenBaseDefiningIdeal (k := k) D i) ⧸ chosenBaseRelationSubmodule (k := k) D i

/--
@isnad1 id=iff.0h4v.s11.3c9d8c3efb0a from=translated src=- shape=68884ae9 vocab=4ec4a641
-/
@[simp] theorem mem_chosenBaseRelationSubmodule_iff
    (f : chosenBaseDefiningIdeal (k := k) D i) :
    f ∈ chosenBaseRelationSubmodule D i ↔
      (f : TailPoly k) ∈ polyVariableIdeal * chosenBaseDefiningIdeal D i := Iff.rfl

def chosenBaseRelationClass (f : TailPoly k) (hf : f ∈ chosenBaseDefiningIdeal D i) :
    ChosenBaseRelationSpace k D i :=
  (chosenBaseRelationSubmodule D i).mkQ ⟨f, hf⟩

/--
@isnad1 id=eq.0h3v.s9.cdfc4fbf2668 from=translated src=- shape=c424b081 vocab=cce7b401
-/
@[simp] theorem chosenBaseRelationClass_zero :
    chosenBaseRelationClass (k := k) D i 0 (chosenBaseDefiningIdeal D i).zero_mem = 0 := by
  exact map_zero (chosenBaseRelationSubmodule (k := k) D i).mkQ

/--
@isnad1 id=eq.2h5v.s10.5d0352dfa4fb from=translated src=- shape=c6b6cf6b vocab=8c697d72
-/
theorem chosenBaseRelationClass_add (f g : TailPoly k)
    (hf : f ∈ chosenBaseDefiningIdeal D i) (hg : g ∈ chosenBaseDefiningIdeal D i) :
    chosenBaseRelationClass D i (f + g) ((chosenBaseDefiningIdeal D i).add_mem hf hg) =
      chosenBaseRelationClass D i f hf + chosenBaseRelationClass D i g hg := by
  exact map_add (chosenBaseRelationSubmodule D i).mkQ ⟨f, hf⟩ ⟨g, hg⟩

/--
@isnad1 id=eq.1h5v.s9.5d6e22125710 from=translated src=- shape=9cf3835d vocab=b8475cbc
-/
theorem chosenBaseRelationClass_smul (r : k) (f : TailPoly k)
    (hf : f ∈ chosenBaseDefiningIdeal D i) :
    chosenBaseRelationClass D i (r • f)
      ((chosenBaseDefiningIdeal D i).restrictScalars k |>.smul_mem r hf) =
      r • chosenBaseRelationClass D i f hf := by
  exact map_smul (chosenBaseRelationSubmodule D i).mkQ r ⟨f, hf⟩

/--
@isnad1 id=eq.1h5v.s10.5f4d3e8604a2 from=translated src=- shape=d209f069 vocab=344ffd82
-/
theorem chosenBaseRelationClass_mul_eq_smul (q f : TailPoly k)
    (hf : f ∈ chosenBaseDefiningIdeal D i) :
    chosenBaseRelationClass D i (q * f) ((chosenBaseDefiningIdeal D i).mul_mem_left q hf) =
      MvPolynomial.constantCoeff q • chosenBaseRelationClass D i f hf := by
  change Submodule.Quotient.mk
      (⟨q * f, _⟩ : chosenBaseDefiningIdeal D i) =
    MvPolynomial.constantCoeff q • Submodule.Quotient.mk
      (⟨f, hf⟩ : chosenBaseDefiningIdeal D i)
  rw [← Submodule.Quotient.mk_smul]
  apply (Submodule.Quotient.eq (chosenBaseRelationSubmodule D i)).2
  apply (mem_chosenBaseRelationSubmodule_iff D i _).2
  have hmem : q * f - MvPolynomial.C (MvPolynomial.constantCoeff q) * f ∈
      polyVariableIdeal * chosenBaseDefiningIdeal D i := by
    rw [← sub_mul]
    apply Ideal.mul_mem_mul
    · apply (mem_polyVariableIdeal_iff _).2
      simp
    · exact hf
  simpa [Algebra.smul_def] using hmem

def specializedConnectorFinset : Finset (TailPoly k) :=
  Finset.univ.image (D.specializedConnectorPolynomial (k := k) i)

/--
@isnad1 id=eq.0h3v.s6.00bf345abf37 from=translated src=- shape=2b0b2eaa vocab=bf0c01ba
-/
theorem specializedConnectorFinset_span_eq :
    Ideal.span (↑(specializedConnectorFinset (k := k) D i) : Set (TailPoly k)) =
      chosenBaseDefiningIdeal D i := by
  rw [specializedConnectorFinset, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact (D.chosenBaseDefiningIdeal_eq_span_specializedConnectors i).symm

/--
@isnad1 id=eq.0h2v.s7.fb0c46b5b732 from=translated src=- shape=8cc5c399 vocab=3276d4f0
-/
theorem baseAdaptedGlobalConnector_card_eq_rho :
    Fintype.card (D.BaseAdaptedGlobalConnector i) = D.semigroupRho := by
  have h := D.baseAdaptedConnectorRelationFinset_card_eq_rho i
  rw [baseAdaptedConnectorRelationFinset,
    Finset.card_image_of_injective _ (D.baseAdaptedGlobalConnectorRelation_injective i)] at h
  exact h

/--
@isnad1 id=le.0h3v.s5.76eb4fe50323 from=translated src=- shape=3d5e6b69 vocab=75b85fdf
-/
theorem specializedConnectorFinset_card_le_rho :
    (specializedConnectorFinset (k := k) D i).card ≤ D.semigroupRho := by
  calc
    _ ≤ (Finset.univ : Finset (D.BaseAdaptedGlobalConnector i)).card := Finset.card_image_le
    _ = D.semigroupRho := baseAdaptedGlobalConnector_card_eq_rho D i

def chosenBaseConnectorCoeff (g : D.BaseAdaptedGlobalConnector i) : TailPoly k →ₗ[k] k :=
  - ((D.degreeComponentCoeff (k := k) g.1.1 g.2.1).comp (tailEmbedding D i).toLinearMap)

/--
@isnad1 id=eq.0h5v.s10.98b15bce8afa from=translated src=- shape=c8733182 vocab=3e121bb4
-/
@[simp] theorem chosenBaseConnectorCoeff_apply (g : D.BaseAdaptedGlobalConnector i)
    (p : TailPoly k) :
    chosenBaseConnectorCoeff D i g p =
      -(D.degreeComponentCoeffVector g.1.1 (tailEmbedding D i p)) g.2.1 := rfl

/-- Every vertex read by a non-root target detector is base-free.
@isnad1 id=eq.1h4v.s8.864c3c729aea from=translated src=- shape=ce6b8a46 vocab=3d5330a4
-/
theorem connectorTargetFactorization_base_zero (g : D.BaseAdaptedGlobalConnector i)
    (u : D.FactorizationAt g.1.1) (hu : D.componentOf u = g.2.1) : u.1 i = 0 := by
  by_cases hi : i ∈ D.combinedSupport g.1.1
  · apply D.factorization_base_zero_of_other_component i g.1.2 hi
    rw [hu]
    simpa only [baseAdaptedRootComponent, dite_eq_left hi] using g.2.2
  · exact D.factorization_base_zero_of_internal i hi u

/--
@isnad1 id=eq.1h5v.s9.e6027f5249cf from=translated src=- shape=aa2c208f vocab=8aa15a69
-/
theorem coeff_tailEmbedding_specialization_of_base_zero (p : FourPoly k)
    (u : Fin 4 →₀ ℕ) (hu : u i = 0) :
    (tailEmbedding D i (baseSpecialization D i p)).coeff u = p.coeff u := by
  let v := restrictToTails D i u
  have hm : v.mapDomain (D.tailIndex i) = u :=
    (tailEmbeddingExponent_eq_mapDomain D i v).symm.trans
      (tailEmbedding_restrictToTails D i u hu)
  rw [← hm]
  calc
    _ = (baseSpecialization D i p).coeff v :=
      MvPolynomial.coeff_rename_mapDomain (D.tailIndex i) (D.tailIndex i).injective (baseSpecialization D i p) v
    _ = p.coeff (v.mapDomain (D.tailIndex i)) :=
      MvPolynomial.coeff_killCompl (D.tailIndex i).injective

/--
@isnad1 id=eq.0h5v.s11.0f4dab0c59bc from=translated src=- shape=d60f18af vocab=1171b335
-/
theorem degreeComponentCoeffVector_tailEmbedding_specialization_target
    (g : D.BaseAdaptedGlobalConnector i) (p : FourPoly k) :
    (D.degreeComponentCoeffVector g.1.1 (tailEmbedding D i (baseSpecialization D i p))) g.2.1 =
      (D.degreeComponentCoeffVector g.1.1 p) g.2.1 := by
  simp only [degreeComponentCoeffVector, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro u hu
  exact coeff_tailEmbedding_specialization_of_base_zero D i p u.1
    (connectorTargetFactorization_base_zero D i g u (Finset.mem_filter.mp hu).2)

/-- Restore the full four-variable polynomial, including a deleted base-root.
@isnad1 id=eq.0h5v.s10.d8a69c6c9ca1 from=translated src=- shape=980c39bb vocab=82909797
-/
theorem chosenBaseConnectorCoeff_specialization (g : D.BaseAdaptedGlobalConnector i)
    (p : FourPoly k) :
    chosenBaseConnectorCoeff D i g (baseSpecialization D i p) =
      -(D.degreeComponentCoeffVector g.1.1 p) g.2.1 := by
  rw [chosenBaseConnectorCoeff_apply,
    degreeComponentCoeffVector_tailEmbedding_specialization_target D i g p]

/--
@isnad1 id=eq.0h5v.s8.04ed0ae9d759 from=translated src=- shape=43e6e564 vocab=3e485bff
-/
theorem degreeComponentCoeffVector_fiberBinomial {d : ℕ}
    (u v : D.FactorizationAt d) :
    D.degreeComponentCoeffVector (k := k) d (D.fiberBinomial u v) =
      D.componentDelta u v := by
  rw [← D.fiberPolynomial_fiberDelta u v, D.degreeComponentCoeffVector_fiberPolynomial]
  exact congrArg Subtype.val (D.fiberToComponentRelation_fiberDelta (k := k) u v)

/--
@isnad1 id=eq.0h5v.s8.7980ca739b19 from=translated src=- shape=7ab922b0 vocab=bf82a90f
-/
theorem chosenBaseConnectorCoeff_specializedConnector
    (g h : D.BaseAdaptedGlobalConnector i) :
    chosenBaseConnectorCoeff (k := k) D i g (D.specializedConnectorPolynomial i h) =
      if g = h then 1 else 0 := by
  rcases g with ⟨d, g⟩
  rcases h with ⟨e, h⟩
  simp only [specializedConnectorPolynomial, chosenBaseConnectorCoeff_specialization]
  by_cases hde : d = e
  · subst e
    change -(D.degreeComponentCoeffVector d.1
      (D.fiberBinomial (D.baseAdaptedRootFactorization i d.2)
        (D.componentRepresentative h.1))) g.1 = _
    rw [degreeComponentCoeffVector_fiberBinomial]
    by_cases hgh : g = h
    · subst h
      simp [componentDelta, D.baseAdaptedRootFactorization_component,
        D.componentRepresentative_component, g.2, Ne.symm g.2]
    · have hval : g.1 ≠ h.1 := fun hv => hgh (Subtype.ext hv)
      have hsig : (⟨d, g⟩ : D.BaseAdaptedGlobalConnector i) ≠ ⟨d, h⟩ := by
        intro hs
        exact hgh (eq_of_heq (Sigma.mk.inj hs).2)
      simp [componentDelta, D.baseAdaptedRootFactorization_component,
        D.componentRepresentative_component, g.2, Ne.symm g.2, hval, Ne.symm hval, hsig]
  · have hval : d.1 ≠ e.1 := fun hv => hde (Subtype.ext hv)
    have hsig : (⟨d, g⟩ : D.BaseAdaptedGlobalConnector i) ≠ ⟨e, h⟩ :=
      fun hs => hde (congrArg Sigma.fst hs)
    have hz : D.degreeComponentCoeffVector (k := k) d.1
        (D.baseAdaptedGlobalConnectorBinomial i ⟨e, h⟩) = 0 := by
      rcases lt_or_gt_of_ne (Ne.symm hval) with hlt | hgt
      · simpa only [one_mul, baseAdaptedGlobalConnectorBinomial, baseAdaptedConnectorBinomial,
          baseAdaptedGlobalConnectorRelation] using D.degreeComponentCoeffVector_mul_relation_of_lt
          (k := k) d.1 (D.baseAdaptedGlobalConnectorRelation i ⟨e,h⟩) 1 hlt
      · simpa only [one_mul, baseAdaptedGlobalConnectorBinomial, baseAdaptedConnectorBinomial,
          baseAdaptedGlobalConnectorRelation] using D.degreeComponentCoeffVector_mul_relation_of_gt
          (k := k) d.1 (D.baseAdaptedGlobalConnectorRelation i ⟨e,h⟩) 1 hgt
    rw [hz]
    simp [hsig]

/--
@isnad1 id=eq.1h5v.s8.769b78927a16 from=translated src=- shape=575f92a0 vocab=9fce41cd
-/
theorem chosenBaseConnectorCoeff_of_degree_ne (g h : D.BaseAdaptedGlobalConnector i)
    (hne : g.1.1 ≠ h.1.1) :
    chosenBaseConnectorCoeff (k := k) D i g (D.specializedConnectorPolynomial i h) = 0 := by
  have hgh : g ≠ h := fun hh => hne (congrArg (fun t => t.1.1) hh)
  rw [chosenBaseConnectorCoeff_specializedConnector, ite_eq_right hgh]

/--
@isnad1 id=eq.1h6v.s8.7626b0996870 from=translated src=- shape=074a06d2 vocab=c0269c71
-/
theorem chosenBaseConnectorCoeff_same_degree_other_target (d : D.BettiDegreeIndex)
    (g h : D.BaseAdaptedConnector i d.2) (hne : g.1 ≠ h.1) :
    chosenBaseConnectorCoeff (k := k) D i ⟨d,g⟩
      (D.specializedConnectorPolynomial i ⟨d,h⟩) = 0 := by
  have hgh : (⟨d,g⟩ : D.BaseAdaptedGlobalConnector i) ≠ ⟨d,h⟩ := by
    intro hh
    exact hne (congrArg Subtype.val (eq_of_heq (Sigma.mk.inj hh).2))
  rw [chosenBaseConnectorCoeff_specializedConnector, ite_eq_right hgh]

/--
@isnad1 id=eq.1h6v.s8.0c3c026873aa from=translated src=- shape=77db69cb vocab=52df186f
-/
theorem chosenBaseConnectorCoeff_mul_specializedConnector_eq_zero
    (g h : D.BaseAdaptedGlobalConnector i) (q : TailPoly k)
    (hq : q ∈ polyVariableIdeal) :
    chosenBaseConnectorCoeff D i g (q * D.specializedConnectorPolynomial i h) = 0 := by
  have hp : baseSpecialization D i
      (tailEmbedding D i q * D.baseAdaptedGlobalConnectorBinomial i h) =
      q * D.specializedConnectorPolynomial i h := by
    simp only [map_mul, baseSpecialization_tailEmbedding, specializedConnectorPolynomial]
  rw [← hp, chosenBaseConnectorCoeff_specialization]
  have hc : relationMultiplierConstantCoeff (tailEmbedding D i q) = 0 := by
    simpa only [relationMultiplierConstantCoeff, tailEmbedding, MvPolynomial.constantCoeff_rename]
      using (mem_polyVariableIdeal_iff q).mp hq
  have hz : D.degreeComponentCoeffVector (k := k) g.1.1
      (tailEmbedding D i q * D.baseAdaptedGlobalConnectorBinomial i h) = 0 := by
    change D.degreeComponentCoeffVector g.1.1
      (tailEmbedding D i q * D.presentationRelationBinomial
        (D.baseAdaptedGlobalConnectorRelation i h)) = 0
    by_cases he : (D.baseAdaptedGlobalConnectorRelation i h).degree = g.1.1
    · rw [D.degreeComponentCoeffVector_mul_relation_of_eq _ _ _ he, hc, zero_smul]
    · rcases lt_or_gt_of_ne he with hlt | hgt
      · exact D.degreeComponentCoeffVector_mul_relation_of_lt _ _ _ hlt
      · exact D.degreeComponentCoeffVector_mul_relation_of_gt _ _ _ hgt
  rw [hz]
  simp

/--
@isnad1 id=eq.2h6v.s9.629319263db5 from=translated src=- shape=d5634da0 vocab=f105990c
-/
theorem chosenBaseConnectorCoeff_mul_external_eq_zero
    (g h : D.BaseAdaptedGlobalConnector i) (q : TailPoly k)
    (hq : q ∈ polyVariableIdeal) (hi : i ∈ D.combinedSupport h.1.1) :
    chosenBaseConnectorCoeff D i g
      (q * (-MvPolynomial.monomial (D.connectorRightTail i h) 1)) = 0 := by
  rw [← D.specializedConnectorPolynomial_external i h hi]
  exact chosenBaseConnectorCoeff_mul_specializedConnector_eq_zero D i g h q hq

/--
@isnad1 id=eq.2h6v.s10.3644a09aac65 from=translated src=- shape=57cacc6b vocab=9dd36a32
-/
theorem chosenBaseConnectorCoeff_mul_internal_eq_zero
    (g h : D.BaseAdaptedGlobalConnector i) (q : TailPoly k)
    (hq : q ∈ polyVariableIdeal) (hi : i ∉ D.combinedSupport h.1.1) :
    chosenBaseConnectorCoeff D i g
      (q * (MvPolynomial.monomial (D.connectorLeftTail i h) 1 -
        MvPolynomial.monomial (D.connectorRightTail i h) 1)) = 0 := by
  rw [← D.specializedConnectorPolynomial_internal i h hi]
  exact chosenBaseConnectorCoeff_mul_specializedConnector_eq_zero D i g h q hq

/--
@isnad1 id=eq.2h7v.s10.6fce34ef88d7 from=translated src=- shape=1b4b529c vocab=8e788fde
-/
theorem chosenBaseConnectorCoeff_positive_monomial_mul_external
    (g h : D.BaseAdaptedGlobalConnector i) (w : Fin 3 →₀ ℕ) (c : k)
    (hw : w ≠ 0) (hi : i ∈ D.combinedSupport h.1.1) :
    chosenBaseConnectorCoeff D i g
      (MvPolynomial.monomial w c * (-MvPolynomial.monomial (D.connectorRightTail i h) 1)) = 0 := by
  apply chosenBaseConnectorCoeff_mul_external_eq_zero D i g h _ _ hi
  simp [mem_polyVariableIdeal_iff, MvPolynomial.constantCoeff_monomial, hw]

/--
@isnad1 id=eq.1h5v.s9.52f7fbe1f193 from=translated src=- shape=5164589d vocab=5416daa1
-/
theorem chosenBaseConnectorCoeff_eq_zero_of_mem_mul
    (g : D.BaseAdaptedGlobalConnector i) (p : TailPoly k)
    (hp : p ∈ polyVariableIdeal * chosenBaseDefiningIdeal D i) :
    chosenBaseConnectorCoeff D i g p = 0 := by
  have hp' : p ∈ polyVariableIdeal (k := k) •
      Submodule.span (TailPoly k)
        ((id : TailPoly k → TailPoly k) '' (↑(specializedConnectorFinset (k := k) D i) : Set (TailPoly k))) := by
    change p ∈ polyVariableIdeal •
      (chosenBaseDefiningIdeal D i : Submodule (TailPoly k) (TailPoly k)) at hp
    rw [← specializedConnectorFinset_span_eq D i] at hp
    simpa using hp
  obtain ⟨coeff, hcoeff, hsum⟩ :=
    (Submodule.mem_ideal_smul_span_iff_exists_sum' (polyVariableIdeal (k := k))
      (↑(specializedConnectorFinset (k := k) D i) : Set (TailPoly k)) (id : TailPoly k → TailPoly k) p).1 hp'
  rw [← hsum]
  simp only [Finsupp.sum, id_eq, smul_eq_mul, map_sum]
  apply Finset.sum_eq_zero
  intro b _
  obtain ⟨h, _, hh⟩ := Finset.mem_image.mp b.2
  simpa only [hh] using chosenBaseConnectorCoeff_mul_specializedConnector_eq_zero D i g h
    (coeff b) (hcoeff b)

def chosenBaseRelationDetector : ChosenBaseRelationSpace k D i →ₗ[k]
    (D.BaseAdaptedGlobalConnector i → k) :=
  (chosenBaseRelationSubmodule D i).liftQ
    ((LinearMap.pi (chosenBaseConnectorCoeff (k := k) D i)).comp
      ((chosenBaseDefiningIdeal D i).subtype.restrictScalars k)) <| by
    intro f hf
    apply LinearMap.mem_ker.mpr
    funext g
    exact chosenBaseConnectorCoeff_eq_zero_of_mem_mul D i g f.1 hf

/--
@isnad1 id=eq.1h5v.s11.4a4258c7bef3 from=translated src=- shape=9e51aaba vocab=067b619d
-/
@[simp] theorem chosenBaseRelationDetector_class (f : TailPoly k)
    (hf : f ∈ chosenBaseDefiningIdeal D i) (g : D.BaseAdaptedGlobalConnector i) :
    chosenBaseRelationDetector D i (chosenBaseRelationClass D i f hf) g =
      chosenBaseConnectorCoeff D i g f := rfl

def displayedChosenBaseRelation (g : D.BaseAdaptedGlobalConnector i) :
    ChosenBaseRelationSpace k D i :=
  chosenBaseRelationClass D i (D.specializedConnectorPolynomial i g) <| by
    rw [D.chosenBaseDefiningIdeal_eq_span_specializedConnectors i]
    exact Ideal.subset_span ⟨g, rfl⟩

/--
@isnad1 id=eq.0h4v.s11.4c124c8180df from=translated src=- shape=a8043edf vocab=da51f4a9
-/
@[simp] theorem chosenBaseRelationDetector_displayed (g : D.BaseAdaptedGlobalConnector i) :
    chosenBaseRelationDetector (k := k) D i (displayedChosenBaseRelation D i g) =
      Pi.single g 1 := by
  funext h
  change chosenBaseConnectorCoeff D i h (D.specializedConnectorPolynomial i g) = _
  rw [chosenBaseConnectorCoeff_specializedConnector]
  simp only [Pi.single_apply, eq_comm]

def chosenBaseGeneratorClass (G : Finset (TailPoly k))
    (hG : Ideal.span (↑G : Set (TailPoly k)) = chosenBaseDefiningIdeal D i) :
    ↥G → ChosenBaseRelationSpace k D i := fun g =>
  chosenBaseRelationClass D i g.1 (by rw [← hG]; exact Ideal.subset_span g.2)

/-- Arbitrary finite ideal generators span the actual quotient; no grading hypothesis.
@isnad1 id=eq.1h4v.s12.6fca99ef9291 from=translated src=- shape=331bba72 vocab=b917ef19
-/
theorem chosenBaseGeneratorClasses_span_eq_top (G : Finset (TailPoly k))
    (hG : Ideal.span (↑G : Set (TailPoly k)) = chosenBaseDefiningIdeal D i) :
    Submodule.span k (Set.range (chosenBaseGeneratorClass D i G hG)) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨f, rfl⟩ := (chosenBaseRelationSubmodule (k := k) D i).mkQ_surjective z
  change chosenBaseRelationClass D i f.1 f.2 ∈ _
  have hf : f.1 ∈ Ideal.span (↑G : Set (TailPoly k)) := by rw [hG]; exact f.2
  let W := Submodule.span k (Set.range (chosenBaseGeneratorClass D i G hG))
  have claim : ∀ (x : TailPoly k) (hx : x ∈ Ideal.span (↑G : Set (TailPoly k))),
      chosenBaseRelationClass D i x (by rw [← hG]; exact hx) ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨⟨x,hx⟩, rfl⟩
    | zero => exact W.zero_mem
    | add x y hx hy ihx ihy =>
        have hxI : x ∈ chosenBaseDefiningIdeal D i := by rw [← hG]; exact hx
        have hyI : y ∈ chosenBaseDefiningIdeal D i := by rw [← hG]; exact hy
        rw [chosenBaseRelationClass_add D i x y hxI hyI]
        exact W.add_mem ihx ihy
    | smul q x hx ih =>
        have hxI : x ∈ chosenBaseDefiningIdeal D i := by rw [← hG]; exact hx
        change chosenBaseRelationClass D i (q*x) _ ∈ W
        rw [chosenBaseRelationClass_mul_eq_smul D i q x hxI]
        exact W.smul_mem _ ih
  exact claim f.1 hf

/--
@isnad1 id=eq.0h3v.s12.cc10c81bd1ab from=translated src=- shape=6595ff96 vocab=fd98614c
-/
theorem displayedChosenBaseRelations_span_eq_top :
    Submodule.span k (Set.range (displayedChosenBaseRelation (k := k) D i)) = ⊤ := by
  apply top_unique
  rw [← chosenBaseGeneratorClasses_span_eq_top D i (specializedConnectorFinset D i)
    (specializedConnectorFinset_span_eq D i)]
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  obtain ⟨g, _, hg⟩ := Finset.mem_image.mp p.2
  apply Submodule.subset_span
  refine ⟨g, ?_⟩
  simp only [displayedChosenBaseRelation, chosenBaseGeneratorClass, hg]

/--
@isnad1 id=finite.0h3v.s10.c47a683fa712 from=translated src=- shape=c5e121a9 vocab=8ee437ec
-/
instance chosenBaseRelationSpace_finite : Module.Finite k (ChosenBaseRelationSpace k D i) :=
  Module.Finite.of_fg_top <| by
    rw [← displayedChosenBaseRelations_span_eq_top (k := k) D i]
    exact Submodule.fg_span (Set.finite_range _)

/--
@isnad1 id=surjecti.0h3v.s11.ffa6d67845fb from=translated src=- shape=c388c795 vocab=6ff6459c
-/
theorem chosenBaseRelationDetector_surjective :
    Function.Surjective (chosenBaseRelationDetector (k := k) D i) := by
  intro v
  refine ⟨∑ g, v g • displayedChosenBaseRelation D i g, ?_⟩
  rw [map_sum]
  simp_rw [map_smul, chosenBaseRelationDetector_displayed]
  ext h
  simp only [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single h]
  · simp
  · intro g _ hgh
    simp [Pi.single_apply, hgh, Ne.symm hgh]
  · simp

/--
@isnad1 id=eq.0h3v.s10.44f6ad80fc70 from=translated src=- shape=465e2638 vocab=775ce285
-/
theorem chosenBaseRelationSpace_finrank :
    Module.finrank k (ChosenBaseRelationSpace k D i) = D.semigroupRho := by
  apply Nat.le_antisymm
  · have h := finrank_le_of_span_eq_top (displayedChosenBaseRelations_span_eq_top (k := k) D i)
    simpa only [baseAdaptedGlobalConnector_card_eq_rho] using h
  · have h := LinearMap.finrank_le_finrank_of_surjective
      (chosenBaseRelationDetector_surjective (k := k) D i)
    simpa only [Module.finrank_pi, Module.finrank_self, mul_one,
      baseAdaptedGlobalConnector_card_eq_rho] using h

/--
@isnad1 id=bijectiv.0h3v.s11.340601684ff2 from=translated src=- shape=c388c795 vocab=88b01723
-/
theorem chosenBaseRelationDetector_bijective :
    Function.Bijective (chosenBaseRelationDetector (k := k) D i) := by
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
  · exact chosenBaseRelationDetector_surjective D i
  · rw [chosenBaseRelationSpace_finrank]
    rw [Module.finrank_pi, baseAdaptedGlobalConnector_card_eq_rho]

def chosenBaseRelationDetectorEquiv : ChosenBaseRelationSpace k D i ≃ₗ[k]
    (D.BaseAdaptedGlobalConnector i → k) :=
  LinearEquiv.ofBijective (chosenBaseRelationDetector D i) (chosenBaseRelationDetector_bijective D i)

def chosenBaseRelationBasis : Module.Basis (D.BaseAdaptedGlobalConnector i) k
    (ChosenBaseRelationSpace k D i) :=
  (Pi.basisFun k (D.BaseAdaptedGlobalConnector i)).map (chosenBaseRelationDetectorEquiv D i).symm

/--
@isnad1 id=eq.0h4v.s11.ff2373f8a23e from=translated src=- shape=1813bb45 vocab=316f7f6d
-/
theorem chosenBaseRelationBasis_apply (g : D.BaseAdaptedGlobalConnector i) :
    chosenBaseRelationBasis (k := k) D i g = displayedChosenBaseRelation D i g := by
  apply (chosenBaseRelationDetector_bijective (k := k) D i).1
  simp [chosenBaseRelationBasis, chosenBaseRelationDetectorEquiv]

end
end P23.Semigroup
