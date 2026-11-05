import Tengoku.NsP23.P23.Semigroup.OneTieNormalization
import Tengoku.NsP23.P23.Presentation.FinitePolynomialQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Intrinsic monomial membership and survivors in the normalized monoid algebra. -/
namespace P23.Semigroup
noncomputable section
open P23.OneTie P23.Artin P23.Presentation
variable {a b c : ℕ} [NeZero a]
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def normalGeneratorIdeal (G : Finset (Normal a b c)) :
    Ideal (NormalMonoidAlgebra ℚ a b c) :=
  Ideal.span (monomial (k := ℚ) '' (↑G : Set (Normal a b c)))

def normalKilledSet (G : Finset (Normal a b c)) : Set (Normal a b c) :=
  {p | ∃ g ∈ G, g ∣ p}

private def upwardNormalSpan (G : Finset (Normal a b c)) :
    Submodule ℚ (NormalMonoidAlgebra ℚ a b c) :=
  Submodule.span ℚ (monomial (k := ℚ) '' normalKilledSet G)

private theorem mul_mem_upwardNormalSpan (G : Finset (Normal a b c))
    (r f : NormalMonoidAlgebra ℚ a b c) (hf : f ∈ upwardNormalSpan G) :
    r * f ∈ upwardNormalSpan G := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨p,⟨g,hg,hgp⟩,rfl⟩ := hf
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r t hr ht => simpa [add_mul] using (upwardNormalSpan G).add_mem hr ht
    | single q t =>
      have hmem : monomial (k := ℚ) (q * p) ∈ upwardNormalSpan G :=
        Submodule.subset_span ⟨q*p,⟨g,hg,dvd_trans hgp (dvd_mul_left p q)⟩,rfl⟩
      have hs := (upwardNormalSpan G).smul_mem t hmem
      simpa [monomial, MonoidAlgebra.single_mul_single, MonoidAlgebra.smul_single] using hs
  | zero => simp
  | add f t hf ht hr ht' => simpa [mul_add] using (upwardNormalSpan G).add_mem hr ht'
  | smul t f hf hi => simpa [mul_smul_comm] using (upwardNormalSpan G).smul_mem t hi

private def upwardNormalIdeal (G : Finset (Normal a b c)) :
    Ideal (NormalMonoidAlgebra ℚ a b c) where
  carrier := upwardNormalSpan G
  zero_mem' := (upwardNormalSpan G).zero_mem
  add_mem' := (upwardNormalSpan G).add_mem
  smul_mem' r f hf := mul_mem_upwardNormalSpan G r f hf

private theorem normalGeneratorIdeal_eq_upward (G : Finset (Normal a b c)) :
    normalGeneratorIdeal G = upwardNormalIdeal G := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro f ⟨g,hg,rfl⟩
    exact Submodule.subset_span ⟨g,⟨g,hg,dvd_refl g⟩,rfl⟩
  · intro f hf
    change f ∈ upwardNormalSpan G at hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨p,⟨g,hg,⟨q,rfl⟩⟩,rfl⟩ := hf
      have hm : monomial (k := ℚ) g ∈ normalGeneratorIdeal G := Ideal.subset_span ⟨g,hg,rfl⟩
      simpa [monomial_mul, mul_comm] using (normalGeneratorIdeal G).mul_mem_left (monomial q) hm
    | zero => exact (normalGeneratorIdeal G).zero_mem
    | add f t hf ht hr ht' => exact (normalGeneratorIdeal G).add_mem hr ht'
    | smul t f hf hi =>
      simpa [Algebra.smul_def] using (normalGeneratorIdeal G).mul_mem_left (algebraMap ℚ _ t) hi

theorem monomial_mem_normalGeneratorIdeal_iff (G : Finset (Normal a b c)) (p : Normal a b c) :
    monomial (k := ℚ) p ∈ normalGeneratorIdeal G ↔ ∃ g ∈ G, g ∣ p := by
  rw [normalGeneratorIdeal_eq_upward]
  change monomial (k := ℚ) p ∈ upwardNormalSpan G ↔ p ∈ normalKilledSet G
  exact MonoidAlgebra.single_mem_span_single

theorem normalGeneratorIdeal_coeff_zero (G : Finset (Normal a b c)) (p : Normal a b c)
    (hp : monomial (k := ℚ) p ∉ normalGeneratorIdeal G)
    (f : NormalMonoidAlgebra ℚ a b c) (hf : f ∈ normalGeneratorIdeal G) : f.coeff p = 0 := by
  rw [normalGeneratorIdeal_eq_upward] at hf
  change f ∈ upwardNormalSpan G at hf
  have hpk : p ∉ normalKilledSet G := fun h => hp ((monomial_mem_normalGeneratorIdeal_iff G p).mpr h)
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨q,hq,rfl⟩ := hf
    have hqp : q ≠ p := fun he => hpk (he ▸ hq)
    simp [hqp]
  | zero => simp
  | add f g hf hg hi hj => simp [hi,hj]
  | smul t f hf hi => simp [hi]

theorem normal_survivor_downward (G : Finset (Normal a b c)) {d p : Normal a b c}
    (hp : monomial (k := ℚ) p ∉ normalGeneratorIdeal G) (hdiv : d ∣ p) :
    monomial (k := ℚ) d ∉ normalGeneratorIdeal G := by
  intro hd
  obtain ⟨g,hg,hgd⟩ := (monomial_mem_normalGeneratorIdeal_iff G d).mp hd
  exact hp ((monomial_mem_normalGeneratorIdeal_iff G p).mpr ⟨g,hg,dvd_trans hgd hdiv⟩)

theorem normal_surviving_quotient_monomials_independent (G : Finset (Normal a b c)) :
    LinearIndependent ℚ (fun p : {p : Normal a b c | monomial (k := ℚ) p ∉ normalGeneratorIdeal G} =>
      Ideal.Quotient.mk (normalGeneratorIdeal G) (monomial (k := ℚ) p.1)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s t hz j hj
  have hm : (∑ q ∈ s, t q • monomial (k := ℚ) q.1) ∈ normalGeneratorIdeal G := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (Ideal.Quotient.mkₐ ℚ (normalGeneratorIdeal G)) (∑ q ∈ s, t q • monomial q.1) = 0
    simpa only [map_sum, map_smul, Ideal.Quotient.mkₐ_eq_mk] using hz
  have hc := normalGeneratorIdeal_coeff_zero G j.1 j.2 _ hm
  have hmono (q : {p : Normal a b c | monomial (k := ℚ) p ∉ normalGeneratorIdeal G}) :
      (monomial (k := ℚ) q.1).coeff j.1 = if q = j then 1 else 0 := by
    simp only [monomial_coeff, Subtype.val_inj]
  simpa [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul, hmono, hj] using hc

theorem normal_survivors_finite (G : Finset (Normal a b c))
    [Module.Finite ℚ (NormalMonoidAlgebra ℚ a b c ⧸ normalGeneratorIdeal G)] :
    {p : Normal a b c | monomial (k := ℚ) p ∉ normalGeneratorIdeal G}.Finite := by
  haveI := (normal_surviving_quotient_monomials_independent G).finite
  exact Set.toFinite _

theorem normalizedMonomialIdeal_map {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
    {p : TailPoly ℚ} (C : OneTieCoordinates D i p) (E : Finset (Fin 3 →₀ ℕ))
    (hspan : Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) = renamedChosenBaseIdeal C) :
    (renamedChosenBaseIdeal C).map
        (polyToNormalAlg (k := ℚ) (a := C.a) (b := C.b) (c := C.c)).toRingHom =
      normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E) := by
  rw [← hspan, ← normalizedLiftGeneratorFinset_span_eq]
  simp [normalizedLiftGeneratorFinset, normalGeneratorIdeal, Ideal.map_span,
    Finset.coe_insert, Finset.coe_image, Set.image_insert_eq, Set.image_image, Function.comp_def]

/-- A surjective algebra map identifies a quotient by any ideal containing its kernel.-/
def surjectiveAlgHomQuotientEquiv {R T : Type*} [CommRing R] [CommRing T]
    [Algebra ℚ R] [Algebra ℚ T] (f : R →ₐ[ℚ] T) (hf : Function.Surjective f)
    (I : Ideal R) (hker : RingHom.ker f.toRingHom ≤ I) :
    (R ⧸ I) ≃ₐ[ℚ] (T ⧸ I.map f.toRingHom) := by
  let q := (Ideal.Quotient.mkₐ ℚ (I.map f.toRingHom)).comp f
  have hq : Function.Surjective q :=
    (Ideal.Quotient.mkₐ_surjective (R₁ := ℚ) (I.map f.toRingHom)).comp hf
  have hk : RingHom.ker q.toRingHom = I := by
    ext x
    change q x = 0 ↔ x ∈ I
    simp only [q, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    change x ∈ (I.map f.toRingHom).comap f.toRingHom ↔ x ∈ I
    rw [Ideal.comap_map_of_surjective f.toRingHom hf I,
      ← RingHom.ker_eq_comap_bot, sup_of_le_left hker]
  exact (Ideal.quotientEquivAlgOfEq ℚ hk.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hq)

def chosenBaseQuotientEquivNormalGenerators {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
    {p : TailPoly ℚ} (C : OneTieCoordinates D i p) (E : Finset (Fin 3 →₀ ℕ))
    (hspan : Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) = renamedChosenBaseIdeal C) :
    ChosenBaseQuotient (k := ℚ) D i ≃ₐ[ℚ]
      (NormalMonoidAlgebra ℚ C.a C.b C.c ⧸ normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E)) := by
  have hker : RingHom.ker
      (polyToNormalAlg (k := ℚ) (a := C.a) (b := C.b) (c := C.c)).toRingHom ≤
      renamedChosenBaseIdeal C := by
    rw [polyToNormalAlg_ker, ← hspan]
    apply Ideal.span_le.mpr
    intro f hf
    rw [Set.mem_singleton_iff.mp hf]
    exact Ideal.subset_span (Finset.mem_insert_self _ _)
  exact (chosenBaseQuotientEquivRenamed C).trans
    ((surjectiveAlgHomQuotientEquiv _ polyToNormalAlg_surjective _ hker).trans
      (Ideal.quotientEquivAlgOfEq ℚ (normalizedMonomialIdeal_map C E hspan)))

theorem chosenBase_normal_survivorQuotient_finite {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
    {p : TailPoly ℚ} (C : OneTieCoordinates D i p) (E : Finset (Fin 3 →₀ ℕ))
    (hspan : Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) = renamedChosenBaseIdeal C) :
    Module.Finite ℚ (NormalMonoidAlgebra ℚ C.a C.b C.c ⧸
      normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E)) := by
  letI : Module.Finite ℚ (ChosenBaseQuotient (k := ℚ) D i) :=
    (chosenBaseEquivApery (k := ℚ) D i).symm.toLinearEquiv.finiteDimensional
  exact (chosenBaseQuotientEquivNormalGenerators C E hspan).toLinearEquiv.finiteDimensional

/-- Divisibility-maximal actual survivors, selected from the proved finite set.-/
def normalSurvivorRoots (G : Finset (Normal a b c))
    (hf : {p : Normal a b c | monomial (k := ℚ) p ∉ normalGeneratorIdeal G}.Finite) :
    Finset (Normal a b c) :=
  hf.toFinset.filter (fun p => ∀ q ∈ hf.toFinset, p ∣ q → p = q)

theorem normalSurvivorRoots_antichain (G : Finset (Normal a b c))
    (hf : {p : Normal a b c | monomial (k := ℚ) p ∉ normalGeneratorIdeal G}.Finite) :
    IsRootAntichain (normalSurvivorRoots G hf) := by
  intro p hp q hq hne hd
  have hpmax := (Finset.mem_filter.mp hp).2
  have hqsurv := (Finset.mem_filter.mp hq).1
  exact hne (hpmax q hqsurv hd)

theorem normalSurvivorRoots_standardSet_iff (G : Finset (Normal a b c))
    (hf : {p : Normal a b c | monomial (k := ℚ) p ∉ normalGeneratorIdeal G}.Finite)
    (hdom : IsLiveParameterDomain a b c) (p : Normal a b c) :
    p ∈ standardSet (normalSurvivorRoots G hf) ↔ monomial (k := ℚ) p ∉ normalGeneratorIdeal G := by
  classical
  constructor
  · rintro ⟨s,hs,hps⟩
    have hsurv : monomial (k := ℚ) s ∉ normalGeneratorIdeal G :=
      hf.mem_toFinset.mp (Finset.mem_filter.mp hs).1
    exact normal_survivor_downward G hsurv hps
  · intro hp
    let K := hf.toFinset.filter (fun q => p ∣ q)
    have hpK : p ∈ K := Finset.mem_filter.mpr ⟨hf.mem_toFinset.mpr hp, dvd_refl p⟩
    obtain ⟨s,hs,hmax⟩ := K.exists_max_image normalWeight ⟨p,hpK⟩
    have hsu : s ∈ hf.toFinset := (Finset.mem_filter.mp hs).1
    have hps : p ∣ s := (Finset.mem_filter.mp hs).2
    have hsm : ∀ q ∈ hf.toFinset, s ∣ q → s = q := by
      intro q hq hsq
      by_contra hne
      have hqK : q ∈ K := Finset.mem_filter.mpr ⟨hq,dvd_trans hps hsq⟩
      have hle := hmax q hqK
      have hlt := normalWeight_lt_of_proper_dvd hdom hsq hne
      omega
    exact ⟨s,Finset.mem_filter.mpr ⟨hsu,hsm⟩,hps⟩

theorem normalSurvivorRoots_nonempty (G : Finset (Normal a b c))
    (hf : {p : Normal a b c | monomial (k := ℚ) p ∉ normalGeneratorIdeal G}.Finite)
    (hdom : IsLiveParameterDomain a b c)
    (h1 : monomial (k := ℚ) (1 : Normal a b c) ∉ normalGeneratorIdeal G) :
    (normalSurvivorRoots G hf).Nonempty := by
  obtain ⟨s,hs,_⟩ := (normalSurvivorRoots_standardSet_iff G hf hdom 1).mpr h1
  exact ⟨s,hs⟩

def normalPresentationFinset (G : Finset (Normal a b c)) : Finset (ThreePoly ℚ) :=
  insert (tiePolynomial a b c) (G.image (polynomialLift (k := ℚ)))

theorem normalPresentationFinset_card (G : Finset (Normal a b c)) :
    (normalPresentationFinset G).card = G.card + 1 := by
  have hn : tiePolynomial a b c ∉ G.image (polynomialLift (k := ℚ)) := by
    rintro h
    obtain ⟨q,_,he⟩ := Finset.mem_image.mp h
    exact tiePolynomial_ne_polynomialLift a b c q he.symm
  rw [normalPresentationFinset, Finset.card_insert_of_notMem hn,
    Finset.card_image_of_injective _ polynomialLift_injective]

theorem normalPresentationFinset_map (G : Finset (Normal a b c)) :
    (Ideal.span (↑(normalPresentationFinset G) : Set (ThreePoly ℚ))).map
      (polyToNormalAlg (k := ℚ) (a := a) (b := b) (c := c)).toRingHom = normalGeneratorIdeal G := by
  simp [normalPresentationFinset, normalGeneratorIdeal, Ideal.map_span,
    Finset.coe_insert, Finset.coe_image, Set.image_insert_eq, Set.image_image]

theorem normalGeneratorIdeal_comap (G : Finset (Normal a b c)) :
    (normalGeneratorIdeal G).comap
      (polyToNormalAlg (k := ℚ) (a := a) (b := b) (c := c)).toRingHom =
      Ideal.span (↑(normalPresentationFinset G) : Set (ThreePoly ℚ)) := by
  rw [← normalPresentationFinset_map G,
    Ideal.comap_map_of_surjective
      (polyToNormalAlg (k := ℚ) (a := a) (b := b) (c := c)).toRingHom
      (polyToNormalAlg_surjective (k := ℚ) (a := a) (b := b) (c := c)),
    ← RingHom.ker_eq_comap_bot, polyToNormalAlg_ker]
  apply sup_of_le_left
  apply Ideal.span_le.mpr
  intro f hf
  rw [Set.mem_singleton_iff.mp hf]
  exact Ideal.subset_span (Finset.mem_insert_self _ _)

theorem normalGenerators_incomparable_of_minimal (G : Finset (Normal a b c)) (n : ℕ)
    (hm : HasMinimalGeneratorCard (Ideal.span (↑(normalPresentationFinset G) : Set (ThreePoly ℚ))) n)
    (hc : (normalPresentationFinset G).card = n) :
    ∀ g ∈ G, ∀ q ∈ G, q ∣ g → q = g := by
  intro g hg q hq hqg
  by_contra hne
  let R := Ideal.span (↑(normalPresentationFinset (G.erase g)) : Set (ThreePoly ℚ))
  have hgR : polynomialLift (k := ℚ) g ∈ R := by
    change polynomialLift (k := ℚ) g ∈ Ideal.span (↑(normalPresentationFinset (G.erase g)) : Set (ThreePoly ℚ))
    rw [← normalGeneratorIdeal_comap]
    change polyToNormalAlg (polynomialLift g) ∈ normalGeneratorIdeal (G.erase g)
    rw [polyToNormalAlg_polynomialLift, monomial_mem_normalGeneratorIdeal_iff]
    exact ⟨q,Finset.mem_erase.mpr ⟨hne,hq⟩,hqg⟩
  have hs : Ideal.span (↑(normalPresentationFinset G) : Set (ThreePoly ℚ)) = R := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro f hf
      rcases Finset.mem_insert.mp hf with he | hf
      · subst f; exact Ideal.subset_span (Finset.mem_insert_self _ _)
      · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hf
        by_cases he : t = g
        · subst t; exact hgR
        · exact Ideal.subset_span (Finset.mem_insert_of_mem
            (Finset.mem_image.mpr ⟨t,Finset.mem_erase.mpr ⟨he,ht⟩,rfl⟩))
    · apply Ideal.span_le.mpr
      intro f hf
      rcases Finset.mem_insert.mp hf with he | hf
      · subst f; exact Ideal.subset_span (Finset.mem_insert_self _ _)
      · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hf
        exact Ideal.subset_span (Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨t,(Finset.mem_erase.mp ht).2,rfl⟩))
  have hl := hm.2 (normalPresentationFinset (G.erase g)) hs.symm
  rw [normalPresentationFinset_card, Finset.card_erase_of_mem hg] at hl
  rw [normalPresentationFinset_card] at hc
  have hpos : 0 < G.card := Finset.card_pos.mpr ⟨g,hg⟩
  omega

private theorem normalWeight_le_of_dvd {p q : Normal a b c} (h : p ∣ q) :
    normalWeight p ≤ normalWeight q := by
  obtain ⟨t,rfl⟩ := h
  rw [normalWeight_mul]
  omega

theorem normalGenerators_eq_exact_border (G : Finset (Normal a b c))
    (hf : {p : Normal a b c | monomial (k := ℚ) p ∉ normalGeneratorIdeal G}.Finite)
    (hd : IsLiveParameterDomain a b c)
    (h1 : monomial (k := ℚ) (1 : Normal a b c) ∉ normalGeneratorIdeal G)
    (hm : ∀ g ∈ G, ∀ q ∈ G, q ∣ g → q = g) :
    G = borderFinset (normalSurvivorRoots G hf) := by
  let S := normalSurvivorRoots G hf
  have hS : S.Nonempty := normalSurvivorRoots_nonempty G hf hd h1
  have hstd (p : Normal a b c) : p ∈ standardSet S ↔ monomial (k := ℚ) p ∉ normalGeneratorIdeal G :=
    normalSurvivorRoots_standardSet_iff G hf hd p
  have hkilled (g : Normal a b c) (hg : g ∈ G) : g ∉ standardSet S := by
    intro hs
    exact (hstd g).mp hs ((monomial_mem_normalGeneratorIdeal_iff G g).mpr ⟨g,hg,dvd_refl g⟩)
  have hvars := variableGenerators_ne_one_of_two_le (a := a) (b := b) (c := c) hd.1
  ext g
  constructor
  · intro hg
    apply (mem_borderFinset_iff hS g).mpr
    apply (isMinimalBorder_iff_isDivisibilityMinimalKilled S g hvars).mpr
    refine ⟨hkilled g hg, ?_⟩
    intro d hdg hdne
    apply (hstd d).mpr
    intro hdI
    obtain ⟨q,hq,hqd⟩ := (monomial_mem_normalGeneratorIdeal_iff G d).mp hdI
    have he := hm g hg q hq (dvd_trans hqd hdg)
    have hgd : g ∣ d := he ▸ hqd
    have hle := normalWeight_le_of_dvd hgd
    have hlt := normalWeight_lt_of_proper_dvd hd hdg hdne
    omega
  · intro hg
    have hb := (mem_borderFinset_iff hS g).mp hg
    have hmkill := (isMinimalBorder_iff_isDivisibilityMinimalKilled S g hvars).mp hb
    have hgI : monomial (k := ℚ) g ∈ normalGeneratorIdeal G := by
      by_contra hn
      exact hmkill.1 ((hstd g).mpr hn)
    obtain ⟨q,hq,hqg⟩ := (monomial_mem_normalGeneratorIdeal_iff G g).mp hgI
    by_cases he : q = g
    · exact he ▸ hq
    · exact False.elim (hkilled q hq (hmkill.2 q hqg he))

section ChosenBaseSurvival
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4} {p : TailPoly ℚ}

theorem renamedChosenBaseIdeal_mem_iff (C : OneTieCoordinates D i p) (f : TailPoly ℚ) :
    renameToOneTie C f ∈ renamedChosenBaseIdeal C ↔ f ∈ chosenBaseDefiningIdeal D i := by
  constructor
  · intro h
    obtain ⟨q,hq,he⟩ := (Ideal.mem_map_iff_of_surjective
      (renameToOneTie C).toRingHom (renameToOneTie C).surjective).mp h
    exact (renameToOneTie C).injective he ▸ hq
  · exact Ideal.mem_map_of_mem _

theorem normalGeneratorIdeal_comap_of_raw_span (C : OneTieCoordinates D i p)
    (E : Finset (Fin 3 →₀ ℕ))
    (hs : Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) = renamedChosenBaseIdeal C) :
    (normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E)).comap
      (polyToNormalAlg (k := ℚ) (a := C.a) (b := C.b) (c := C.c)).toRingHom =
      renamedChosenBaseIdeal C := by
  rw [normalGeneratorIdeal_comap]
  change Ideal.span (↑(normalizedLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) = _
  rw [normalizedLiftGeneratorFinset_span_eq, hs]

theorem chosenBase_normal_unit_survives (C : OneTieCoordinates D i p)
    (E : Finset (Fin 3 →₀ ℕ))
    (hs : Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) = renamedChosenBaseIdeal C) :
    monomial (k := ℚ) (1 : Normal C.a C.b C.c) ∉
      normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E) := by
  intro h
  have hr : (1 : ThreePoly ℚ) ∈ renamedChosenBaseIdeal C := by
    rw [← normalGeneratorIdeal_comap_of_raw_span C E hs]
    simpa using h
  have hj : (1 : TailPoly ℚ) ∈ chosenBaseDefiningIdeal D i := by
    apply (renamedChosenBaseIdeal_mem_iff C 1).mp
    simpa using hr
  have hz : (1 : ChosenBaseQuotient (k := ℚ) D i) = 0 := by
    simpa using (RingHom.mem_ker.mp hj)
  apply tailVariableChosenBase_ne_zero (k := ℚ) D i 0
  calc
    tailPolyToChosenBase D i (MvPolynomial.X 0) =
      tailPolyToChosenBase D i (MvPolynomial.X 0) * 1 := (mul_one _).symm
    _ = 0 := by rw [hz, mul_zero]

theorem chosenBase_renamed_variable_survives (C : OneTieCoordinates D i p)
    (j : Fin 3) : (MvPolynomial.X j : ThreePoly ℚ) ∉ renamedChosenBaseIdeal C := by
  intro h
  have he : renameToOneTie C (MvPolynomial.X (C.sigma.symm j)) = MvPolynomial.X j := by
    simp [renameToOneTie, MvPolynomial.renameEquiv]
  have hj : (MvPolynomial.X (C.sigma.symm j) : TailPoly ℚ) ∈ chosenBaseDefiningIdeal D i := by
    apply (renamedChosenBaseIdeal_mem_iff C _).mp
    simpa only [he] using h
  exact tailVariableChosenBase_ne_zero (k := ℚ) D i _ (RingHom.mem_ker.mp hj)

theorem chosenBase_normal_variables_survive (C : OneTieCoordinates D i p)
    (E : Finset (Fin 3 →₀ ℕ))
    (hs : Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) = renamedChosenBaseIdeal C) :
    monomial (k := ℚ) (Normal.xGenerator : Normal C.a C.b C.c) ∉ normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E) ∧
    monomial (k := ℚ) (Normal.yGenerator : Normal C.a C.b C.c) ∉ normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E) ∧
    monomial (k := ℚ) (Normal.zGenerator : Normal C.a C.b C.c) ∉ normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E) := by
  have hx := chosenBase_renamed_variable_survives C 0
  have hy := chosenBase_renamed_variable_survives C 1
  have hz := chosenBase_renamed_variable_survives C 2
  rw [← normalGeneratorIdeal_comap_of_raw_span C E hs] at hx hy hz
  change (polyToNormalAlg (k := ℚ) (a := C.a) (b := C.b) (c := C.c)) polyX ∉
    normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E) at hx
  change (polyToNormalAlg (k := ℚ) (a := C.a) (b := C.b) (c := C.c)) polyY ∉
    normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E) at hy
  change (polyToNormalAlg (k := ℚ) (a := C.a) (b := C.b) (c := C.c)) polyZ ∉
    normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E) at hz
  simpa using And.intro hx (And.intro hy hz)

theorem chosenBase_normal_tie_survives (C : OneTieCoordinates D i p)
    (E : Finset (Fin 3 →₀ ℕ))
    (hs : Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) = renamedChosenBaseIdeal C) :
    monomial (k := ℚ) (liveTiePoint : Normal C.a C.b C.c) ∉
      normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E) := by
  let d : Fin 3 →₀ ℕ := Finsupp.single 0 C.a
  have ha : C.a ≠ 0 := by have := C.liveDomain.1; omega
  have hneq : d ≠ Finsupp.single 1 C.b + Finsupp.single 2 C.c := by
    intro h
    have he := congrArg (fun w : Fin 3 →₀ ℕ => w 0) h
    simp [d] at he
    exact ha he
  have ht : MvPolynomial.coeff d (tiePolynomial (k := ℚ) C.a C.b C.c) = 1 := by
    simp [tiePolynomial, polyX, polyY, polyZ, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial, d, Ne.symm hneq]
  have he : renameToOneTie C p =
      MvPolynomial.monomial (C.original.u.mapDomain C.sigma) 1 -
      MvPolynomial.monomial (C.original.v.mapDomain C.sigma) 1 := by
    calc
      renameToOneTie C p = renameToOneTie C
          (MvPolynomial.monomial C.original.u 1 - MvPolynomial.monomial C.original.v 1) :=
        congrArg (renameToOneTie C) C.original.equation
      _ = _ := by simp [renameToOneTie, MvPolynomial.rename_monomial]
  have hmatch : C.original.u.mapDomain C.sigma = d ∨ C.original.v.mapDomain C.sigma = d := by
    by_contra hn
    push_neg at hn
    have hc : MvPolynomial.coeff d (renameToOneTie C p) = 0 := by
      simp [he, hn.1, hn.2]
    rcases renameToOneTie_live C with h | h
    · rw [h,ht] at hc; norm_num at hc
    · rw [h, MvPolynomial.coeff_neg, ht] at hc; norm_num at hc
  intro h
  have hd : normalizeExponent C.a C.b C.c d = (liveTiePoint : Normal C.a C.b C.c) := by
    apply Normal.ext <;> simp [normalizeExponent, exponentRaw, d, Normal.normalize, liveTiePoint,
      Nat.pos_of_ne_zero ha]
  have hm : (MvPolynomial.monomial d (1 : ℚ)) ∈ renamedChosenBaseIdeal C := by
    rw [← normalGeneratorIdeal_comap_of_raw_span C E hs]
    change (polyToNormalAlg (k := ℚ) (a := C.a) (b := C.b) (c := C.c))
      (MvPolynomial.monomial d (1 : ℚ)) ∈ normalGeneratorIdeal (normalizedMonomialGeneratorFinset C E)
    simpa [polyToNormalAlg_monomial, hd] using h
  have hkill (w : Fin 3 →₀ ℕ) (hw : w.mapDomain C.sigma = d) :
      tailPolyToChosenBase (k := ℚ) D i (MvPolynomial.monomial w 1) = 0 := by
    apply RingHom.mem_ker.mp
    apply (renamedChosenBaseIdeal_mem_iff C _).mp
    simpa [renameToOneTie, MvPolynomial.rename_monomial, hw] using hm
  rcases hmatch with hu | hv
  · exact C.original.liveImage (hkill _ hu)
  · exact C.original.liveImage (C.original.equalImage.trans (hkill _ hv))
end ChosenBaseSurvival

/-- Data obtained from the actual minimal chosen-base presentation, not a
surrogate quotient or an assumed finite exponent box.-/
structure BudgetOneNormalizedPresentation (D : FourGeneratedNumericalSemigroup) (i : Fin 4) where
  live : TailPoly ℚ
  coordinates : OneTieCoordinates D i live
  rawExponents : Finset (Fin 3 →₀ ℕ)
  spanEq : Ideal.span (↑(rawLiftGeneratorFinset coordinates rawExponents) : Set (ThreePoly ℚ)) =
    renamedChosenBaseIdeal coordinates
  rawCard : rawExponents.card = D.semigroupRho - 1
  rhoPos : 0 < D.semigroupRho
  survivorsFinite : {q : Normal coordinates.a coordinates.b coordinates.c |
    monomial (k := ℚ) q ∉ normalGeneratorIdeal
      (normalizedMonomialGeneratorFinset coordinates rawExponents)}.Finite

theorem budgetOneNormalizedPresentation (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hB : D.fourBaseBudget i = 1) : Nonempty (BudgetOneNormalizedPresentation D i) := by
  obtain ⟨p,C,E,hs,hc,hpos⟩ := budgetOne_raw_normalization_data D i hB
  letI := chosenBase_normal_survivorQuotient_finite C E hs
  exact ⟨⟨p,C,E,hs,hc,hpos,normal_survivors_finite _⟩⟩

namespace BudgetOneNormalizedPresentation
variable {D : FourGeneratedNumericalSemigroup} {i : Fin 4}
variable (B : BudgetOneNormalizedPresentation D i)
abbrev generators := normalizedMonomialGeneratorFinset B.coordinates B.rawExponents
def roots := normalSurvivorRoots B.generators B.survivorsFinite

theorem roots_nonempty : B.roots.Nonempty :=
  normalSurvivorRoots_nonempty _ _ B.coordinates.liveDomain
    (chosenBase_normal_unit_survives _ _ B.spanEq)

theorem roots_antichain : IsRootAntichain B.roots := normalSurvivorRoots_antichain _ _

theorem survivor_iff_standard (q : Normal B.coordinates.a B.coordinates.b B.coordinates.c) :
    monomial (k := ℚ) q ∉ normalGeneratorIdeal B.generators ↔ q ∈ standardSet B.roots :=
  (normalSurvivorRoots_standardSet_iff _ _ B.coordinates.liveDomain q).symm

theorem roots_live : IsLiveTie B.roots := by
  obtain ⟨hx,hy,hz⟩ := chosenBase_normal_variables_survive _ _ B.spanEq
  exact ⟨(B.survivor_iff_standard _).mp hx, (B.survivor_iff_standard _).mp hy,
    (B.survivor_iff_standard _).mp hz,
    (B.survivor_iff_standard _).mp (chosenBase_normal_tie_survives _ _ B.spanEq)⟩

theorem normalized_span : Ideal.span (↑(normalPresentationFinset B.generators) : Set (ThreePoly ℚ)) =
    renamedChosenBaseIdeal B.coordinates := by
  change Ideal.span (↑(normalizedLiftGeneratorFinset B.coordinates B.rawExponents) : Set (ThreePoly ℚ)) = _
  rw [normalizedLiftGeneratorFinset_span_eq, B.spanEq]

theorem normalized_card : (normalPresentationFinset B.generators).card = D.semigroupRho ∧
    B.generators.card = D.semigroupRho - 1 :=
  normalizedGeneratorFinsets_card _ _ B.spanEq B.rawCard B.rhoPos

theorem raw_family_card : (rawLiftGeneratorFinset B.coordinates B.rawExponents).card = D.semigroupRho := by
  have hlo := (renamedChosenBaseIdeal_minimalGeneratorCard B.coordinates).2 _ B.spanEq
  have hup : (rawLiftGeneratorFinset B.coordinates B.rawExponents).card ≤ B.rawExponents.card + 1 := by
    unfold rawLiftGeneratorFinset
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
  have hc := B.rawCard
  have hp := B.rhoPos
  omega

theorem tie_ne_raw_monomial (d : Fin 3 →₀ ℕ) :
    tiePolynomial (k := ℚ) B.coordinates.a B.coordinates.b B.coordinates.c ≠ MvPolynomial.monomial d 1 := by
  intro h
  have he := congrArg (polyToNormalAlg (k := ℚ) (a := B.coordinates.a)
    (b := B.coordinates.b) (c := B.coordinates.c)) h
  simp only [polyToNormalAlg_tiePolynomial, polyToNormalAlg_monomial, one_smul] at he
  exact normalMonomial_ne_zero _ _ _ _ he.symm

theorem normalized_lift_ne_zero (q : Normal B.coordinates.a B.coordinates.b B.coordinates.c) :
    polynomialLift (k := ℚ) q ≠ 0 := by
  intro h
  have he := congrArg (polyToNormalAlg (k := ℚ) (a := B.coordinates.a)
    (b := B.coordinates.b) (c := B.coordinates.c)) h
  simp only [polyToNormalAlg_polynomialLift, map_zero] at he
  exact normalMonomial_ne_zero _ _ _ _ he

theorem normalization_injective : Set.InjOn
    (normalizeExponent B.coordinates.a B.coordinates.b B.coordinates.c) B.rawExponents := by
  apply Finset.card_image_iff.mp
  exact B.normalized_card.2.trans B.rawCard.symm

theorem generators_ne_one (q : Normal B.coordinates.a B.coordinates.b B.coordinates.c)
    (hq : q ∈ B.generators) : q ≠ 1 := by
  intro h; subst q
  exact chosenBase_normal_unit_survives _ _ B.spanEq
    ((monomial_mem_normalGeneratorIdeal_iff _ _).mpr ⟨1,hq,dvd_refl _⟩)

theorem generators_exact_border : B.generators = borderFinset B.roots := by
  apply normalGenerators_eq_exact_border _ _ B.coordinates.liveDomain
    (chosenBase_normal_unit_survives _ _ B.spanEq)
  apply normalGenerators_incomparable_of_minimal _ D.semigroupRho
  · rw [B.normalized_span]
    exact renamedChosenBaseIdeal_minimalGeneratorCard B.coordinates
  · exact B.normalized_card.1

theorem border_card : (borderFinset B.roots).card = D.semigroupRho - 1 := by
  rw [← B.generators_exact_border]
  exact B.normalized_card.2

theorem canonical_ideal : renamedChosenBaseIdeal B.coordinates =
    finitePresentationIdeal (k := ℚ) B.roots := by
  rw [← B.normalized_span, ← normalGeneratorIdeal_comap, B.generators_exact_border]
  have he : normalGeneratorIdeal (borderFinset B.roots) = borderMonomialIdeal (k := ℚ) B.roots := by
    unfold normalGeneratorIdeal borderMonomialIdeal
    congr 1
    ext f
    simp [borderMonomialSet, eq_comm]
  rw [he, borderMonomialIdeal_comap]

def chosenBaseEquivCanonicalOneTie : ChosenBaseQuotient (k := ℚ) D i ≃ₐ[ℚ]
    FinitePolynomialQuotient ℚ B.roots :=
  (chosenBaseQuotientEquivRenamed B.coordinates).trans
    (Ideal.quotientEquivAlgOfEq ℚ B.canonical_ideal)
end BudgetOneNormalizedPresentation
end
end P23.Semigroup
