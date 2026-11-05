import Tengoku.NsP23.P23.Semigroup.ChosenBaseMinimality
import Tengoku.NsP23.P23.Presentation.PolynomialBorder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact live coordinates and ideal-preserving one-tie normalization. -/
namespace P23.Semigroup
noncomputable section
set_option maxHeartbeats 800000
open FourGeneratedNumericalSemigroup P23.Presentation P23.OneTie P23.Artin
open scoped BigOperators

variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)

/-- The original relation, before any orientation or relabeling.-/
structure LiveTailTieData (p : TailPoly ℚ) where
  u : Fin 3 →₀ ℕ
  v : Fin 3 →₀ ℕ
  equation : p = MvPolynomial.monomial u 1 - MvPolynomial.monomial v 1
  uNonempty : u.support.Nonempty
  vNonempty : v.support.Nonempty
  disjoint : Disjoint u.support v.support
  distinct : u ≠ v
  nonzero : p ≠ 0
  equalImage : tailPolyToChosenBase (k := ℚ) D i (MvPolynomial.monomial u 1) =
    tailPolyToChosenBase (k := ℚ) D i (MvPolynomial.monomial v 1)
  liveImage : tailPolyToChosenBase (k := ℚ) D i (MvPolynomial.monomial u 1) ≠ 0
  singletonSide : u.support.card = 1 ∨ v.support.card = 1

/--
@isnad1 id=nonempty.1h3v.s4.ecd34eca8669 from=translated src=- shape=8df1eb62 vocab=baab3e1b
-/
theorem liveTailTieData_exists (p : TailPoly ℚ) (hp : D.LiveTailBinomial i p) :
    Nonempty (LiveTailTieData D i p) := by
  obtain ⟨u,v,he,hu,hv,hd,hn,hp,hi,hl⟩ := hp
  exact ⟨⟨u,v,he,hu,hv,hd,hn,hp,hi,hl,
    disjoint_three_supports_one_singleton u v hu hv hd⟩⟩

variable {D i}

/--
@isnad1 id=eq.0h4v.s5.eb0d90114e7a from=translated src=- shape=a78f939c vocab=2ef7cf3a
-/
theorem LiveTailTieData.degree_eq {p : TailPoly ℚ} (T : LiveTailTieData D i p) :
    tailDegree D i T.u = tailDegree D i T.v := by
  have hE := congrArg (chosenBaseEquivApery (k := ℚ) D i) T.equalImage
  simp only [tailPolyToChosenBase_monomial, one_smul] at hE
  have hu : D.IsApery i (tailDegreeGamma D i T.u) := by
    by_contra hn
    apply T.liveImage
    apply (chosenBaseEquivApery (k := ℚ) D i).injective
    simp [tailPolyToChosenBase_monomial, truncatedAperyMonomial, hn]
  have hv : D.IsApery i (tailDegreeGamma D i T.v) := by
    by_contra hn
    have hz : tailPolyToChosenBase (k := ℚ) D i (MvPolynomial.monomial T.v 1) = 0 := by
      apply (chosenBaseEquivApery (k := ℚ) D i).injective
      simp [tailPolyToChosenBase_monomial, truncatedAperyMonomial, hn]
    exact T.liveImage (T.equalImage.trans hz)
  have hg : tailDegreeGamma D i T.u = tailDegreeGamma D i T.v := by
    by_contra hn
    have hc := congrArg (fun x : AperyArtin ℚ D i =>
      x.coeff ⟨tailDegreeGamma D i T.u, hu⟩) hE
    simp [truncatedAperyMonomial, hu, hv, AperyArtin.coeff_A, hn, Ne.symm hn] at hc
  exact congrArg Subtype.val hg

/-- Original generator minimality excludes exponent one on either singleton side.
@isnad1 id=le.3h5v.s7.ddba2567b438 from=translated src=- shape=b768344b vocab=11326d98
-/
theorem singleton_live_exponent_two_le (u v : Fin 3 →₀ ℕ)
    (hd : Disjoint u.support v.support) (he : tailDegree D i u = tailDegree D i v)
    (x : Fin 3) (hu : u.support = {x}) : 2 ≤ u x := by
  have hx : u x ≠ 0 := Finsupp.mem_support_iff.mp (hu ▸ Finset.mem_singleton_self x)
  by_contra hn
  have hx1 : u x = 1 := by omega
  have hu1 : u = Finsupp.single x 1 := by
    ext j
    by_cases hj : j = x
    · subst j; simp [hx1]
    · have hz : u j = 0 := Finsupp.notMem_support_iff.mp (by simp [hu, hj])
      simp [Finsupp.single_apply, hj, hz]
  have hv1 : v = Finsupp.single x 1 := (tailDegree_eq_tailGen_iff D i).mp (by
    rw [← he, hu1, tailDegree_single, one_mul])
  have hvx : x ∈ v.support := by simp [hv1]
  exact Finset.disjoint_left.mp hd (by simp [hu]) hvx

private theorem axisPermutation (x y : Fin 3) (hne : x ≠ y) :
    ∃ σ : Fin 3 ≃ Fin 3, σ x = 0 ∧ σ y = 1 := by
  let τ := Equiv.swap x 0
  have hy0 : τ y ≠ 0 := by
    intro hy
    have hx : τ x = 0 := by simp [τ]
    exact hne (τ.injective (hx.trans hy.symm))
  refine ⟨τ.trans (Equiv.swap (τ y) 1), ?_, ?_⟩
  · simp [τ, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne, Ne.symm hy0]
  · simp [Equiv.trans_apply]

private theorem oriented_live_coordinates {p : TailPoly ℚ} (T : LiveTailTieData D i p)
    (hcard : T.u.support.card = 1) :
    ∃ (σ : Fin 3 ≃ Fin 3) (a b c : ℕ), IsLiveParameterDomain a b c ∧
      MvPolynomial.renameEquiv ℚ σ p = tiePolynomial a b c := by
  classical
  obtain ⟨x,hx⟩ := Finset.card_eq_one.mp hcard
  obtain ⟨y,hy⟩ := T.vNonempty
  have hvx : T.v x = 0 := Finsupp.notMem_support_iff.mp (by
    intro h
    exact Finset.disjoint_left.mp T.disjoint (by simp [hx]) h)
  have hxy : x ≠ y := by
    intro h; subst y
    exact (Finsupp.mem_support_iff.mp hy) hvx
  obtain ⟨σ,hσx,hσy⟩ := axisPermutation x y hxy
  let a := T.u x
  let w := T.v.mapDomain σ
  let b := w 1
  let c := w 2
  have ha : 2 ≤ a := singleton_live_exponent_two_le T.u T.v T.disjoint T.degree_eq x hx
  have hu : T.u = Finsupp.single x a := by
    ext j
    by_cases hj : j = x
    · subst j; simp [a]
    · have hz : T.u j = 0 := Finsupp.notMem_support_iff.mp (by simp [hx, hj])
      simp [Finsupp.single_apply, hj, hz]
  have hw0 : w 0 = 0 := by
    have he : w (σ x) = T.v x := Finsupp.mapDomain_apply σ.injective T.v x
    simpa [hσx, hvx] using he
  have hb : 1 ≤ b := by
    have he : w (σ y) = T.v y := Finsupp.mapDomain_apply σ.injective T.v y
    have hypos : 0 < T.v y := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hy)
    change 1 ≤ w 1
    rw [← hσy, he]
    omega
  have hw : w = Finsupp.single 1 b + Finsupp.single 2 c := by
    ext j; fin_cases j <;> simp [hw0, b, c]
  have hdom : IsLiveParameterDomain a b c := by
    refine ⟨ha, ?_⟩
    by_cases hc : c = 0
    · right
      have hv : T.v = Finsupp.single y b := by
        apply Finsupp.mapDomain_injective σ.injective
        simp only [Finsupp.mapDomain_single, hσy]
        simpa [hc] using hw
      have hbn : b ≠ 0 := by omega
      have hvs : T.v.support = {y} := by simp [hv, hbn]
      have hvb := singleton_live_exponent_two_le T.v T.u T.disjoint.symm T.degree_eq.symm y hvs
      exact ⟨by simpa [hv] using hvb, hc⟩
    · left; exact ⟨hb, by omega⟩
  refine ⟨σ,a,b,c,hdom,?_⟩
  change MvPolynomial.rename σ p = tiePolynomial a b c
  calc
    MvPolynomial.rename σ p = MvPolynomial.rename σ
        (MvPolynomial.monomial T.u 1 - MvPolynomial.monomial T.v 1) :=
      congrArg (MvPolynomial.rename σ) T.equation
    _ = tiePolynomial a b c := by
      rw [map_sub, MvPolynomial.rename_monomial, MvPolynomial.rename_monomial]
      rw [hu, Finsupp.mapDomain_single, hσx]
      change MvPolynomial.monomial (Finsupp.single 0 a) 1 - MvPolynomial.monomial w 1 = _
      rw [hw]
      simp [tiePolynomial, polyX, polyY, polyZ, MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.monomial_mul_monomial]

/-- Coordinates retain the exact original relation and an actual variable permutation.-/
structure OneTieCoordinates (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (p : TailPoly ℚ) where
  original : LiveTailTieData D i p
  sigma : Fin 3 ≃ Fin 3
  a : ℕ
  b : ℕ
  c : ℕ
  liveDomain : IsLiveParameterDomain a b c
  signedEquation : MvPolynomial.renameEquiv ℚ sigma p = tiePolynomial a b c ∨
    MvPolynomial.renameEquiv ℚ sigma p = -tiePolynomial a b c

/--
@isnad1 id=nonempty.0h4v.s4.f4ea59c230e2 from=translated src=- shape=aef267c2 vocab=c3da97f0
-/
theorem oneTieCoordinates_exists {p : TailPoly ℚ} (T : LiveTailTieData D i p) :
    Nonempty (OneTieCoordinates D i p) := by
  rcases T.singletonSide with hu | hv
  · obtain ⟨σ,a,b,c,hd,he⟩ := oriented_live_coordinates T hu
    exact ⟨⟨T,σ,a,b,c,hd,Or.inl he⟩⟩
  · let T' : LiveTailTieData D i (-p) :=
      ⟨T.v,T.u,(congrArg Neg.neg T.equation).trans (neg_sub _ _),T.vNonempty,T.uNonempty,
        T.disjoint.symm,Ne.symm T.distinct,neg_ne_zero.mpr T.nonzero,
        T.equalImage.symm,by rw [← T.equalImage]; exact T.liveImage,Or.inl hv⟩
    obtain ⟨σ,a,b,c,hd,he⟩ := oriented_live_coordinates T' hv
    refine ⟨⟨T,σ,a,b,c,hd,Or.inr ?_⟩⟩
    have := congrArg Neg.neg he
    simpa only [map_neg, neg_neg] using this

/--
@isnad1 id=ex.1h2v.s7.3af2f157d766 from=translated src=- shape=e3b22b7c vocab=0d7682c5
-/
theorem oneTieCoordinates_of_budget_one (D : FourGeneratedNumericalSemigroup)
    (i : Fin 4) (hB : D.fourBaseBudget i = 1) :
    ∃ p : TailPoly ℚ, p ∈ chosenBaseDefiningIdeal D i ∧
      Nonempty (OneTieCoordinates D i p) := by
  obtain ⟨G,g,hspan,_,hmem,hlive,_⟩ :=
    chosenBase_minimal_one_live_binomial_of_budget_one (k := ℚ) D i hB
  obtain ⟨T⟩ := liveTailTieData_exists D i _ hlive
  refine ⟨D.specializedConnectorPolynomial i g, ?_, oneTieCoordinates_exists T⟩
  rw [← hspan]
  exact Ideal.subset_span hmem

def renameToOneTie {p : TailPoly ℚ} (C : OneTieCoordinates D i p) :
    TailPoly ℚ ≃ₐ[ℚ] ThreePoly ℚ := MvPolynomial.renameEquiv ℚ C.sigma

/--
@isnad1 id=islivepa.0h4v.s5.7582be001ba5 from=translated src=- shape=9525bfd2 vocab=ccabae34
-/
theorem oneTieCoordinates_liveDomain {p : TailPoly ℚ} (C : OneTieCoordinates D i p) :
    IsLiveParameterDomain C.a C.b C.c := C.liveDomain

/--
@isnad1 id=or.0h4v.s9.6e0335516d49 from=translated src=- shape=04b1f532 vocab=1ff2bc5f
-/
theorem renameToOneTie_live {p : TailPoly ℚ} (C : OneTieCoordinates D i p) :
    renameToOneTie C p = tiePolynomial C.a C.b C.c ∨
      renameToOneTie C p = -tiePolynomial C.a C.b C.c := C.signedEquation

def renamedChosenBaseIdeal {p : TailPoly ℚ} (C : OneTieCoordinates D i p) :
    Ideal (ThreePoly ℚ) := (chosenBaseDefiningIdeal D i).map (renameToOneTie C).toRingHom

def chosenBaseQuotientEquivRenamed {p : TailPoly ℚ} (C : OneTieCoordinates D i p) :
    ChosenBaseQuotient (k := ℚ) D i ≃ₐ[ℚ] (ThreePoly ℚ ⧸ renamedChosenBaseIdeal C) :=
  (tailPolynomialQuotientEquiv D i).symm.trans
    (Ideal.quotientEquivAlg _ _ (renameToOneTie C) rfl)

/--
@isnad1 id=mem.1h4v.s8.b2bb97af2052 from=translated src=- shape=c5e18188 vocab=10c26513
-/
theorem tiePolynomial_mem_renamedChosenBaseIdeal {p : TailPoly ℚ}
    (C : OneTieCoordinates D i p) (hp : p ∈ chosenBaseDefiningIdeal D i) :
    tiePolynomial C.a C.b C.c ∈ renamedChosenBaseIdeal C := by
  have hm : renameToOneTie C p ∈ renamedChosenBaseIdeal C := Ideal.mem_map_of_mem _ hp
  rcases C.signedEquation with he | he
  · rwa [← he]
  · have hneg : -tiePolynomial C.a C.b C.c ∈ renamedChosenBaseIdeal C := he ▸ hm
    simpa only [neg_neg] using neg_mem hneg

/--
@isnad1 id=eq.0h2v.s10.a8a431bd3d96 from=translated src=- shape=d3046ff0 vocab=45ac94fc
-/
theorem span_image_algEquiv (e : ThreePoly ℚ ≃ₐ[ℚ] ThreePoly ℚ)
    (G : Finset (ThreePoly ℚ)) :
    Ideal.span (↑(G.image e) : Set (ThreePoly ℚ)) =
      (Ideal.span (↑G : Set (ThreePoly ℚ))).map e.toRingHom := by
  classical
  rw [Ideal.map_span]
  congr 1
  exact Finset.coe_image

/-- Transport includes the lower bound for every finite polynomial generating family.
@isnad1 id=hasminim.1h3v.s9.f9b48501b0f0 from=translated src=- shape=b0e66960 vocab=ed5f9557
-/
theorem minimalGeneratorCard_map_algEquiv (e : ThreePoly ℚ ≃ₐ[ℚ] ThreePoly ℚ)
    (I : Ideal (ThreePoly ℚ)) (n : ℕ) (h : HasMinimalGeneratorCard I n) :
    HasMinimalGeneratorCard (I.map e.toRingHom) n := by
  classical
  constructor
  · obtain ⟨G,hG,hc⟩ := h.1
    exact ⟨G.image e, by rw [span_image_algEquiv, hG],
      by rw [Finset.card_image_of_injective _ e.injective, hc]⟩
  · intro G hG
    have hs : Ideal.span (↑(G.image e.symm) : Set (ThreePoly ℚ)) = I := by
      rw [span_image_algEquiv, hG]
      exact Ideal.map_of_equiv e.toRingEquiv
    have hl := h.2 _ hs
    rwa [Finset.card_image_of_injective _ e.symm.injective] at hl

/--
@isnad1 id=hasminim.0h4v.s4.58cdb032751b from=translated src=- shape=5d26b9d8 vocab=d1a51ad8
-/
theorem renamedChosenBaseIdeal_minimalGeneratorCard {p : TailPoly ℚ}
    (C : OneTieCoordinates D i p) :
    HasMinimalGeneratorCard (renamedChosenBaseIdeal C) D.semigroupRho :=
  minimalGeneratorCard_map_algEquiv (renameToOneTie C) _ _
    (chosenBaseDefiningIdeal_minimalGeneratorCard D i)

/--
@isnad1 id=nezero.0h4v.s4.8e11bd585c55 from=translated src=- shape=deead888 vocab=2cf71236
-/
instance OneTieCoordinates.neZeroA {p : TailPoly ℚ} (C : OneTieCoordinates D i p) :
    NeZero C.a := ⟨by have := C.liveDomain.1; omega⟩

def rawLiftGeneratorFinset {p : TailPoly ℚ} (C : OneTieCoordinates D i p)
    (E : Finset (Fin 3 →₀ ℕ)) : Finset (ThreePoly ℚ) := by
  classical
  exact insert (tiePolynomial C.a C.b C.c) (E.image (fun d => MvPolynomial.monomial d 1))

def normalizedMonomialGeneratorFinset {p : TailPoly ℚ} (C : OneTieCoordinates D i p)
    (E : Finset (Fin 3 →₀ ℕ)) : Finset (Normal C.a C.b C.c) := by
  classical
  exact E.image (normalizeExponent C.a C.b C.c)

def normalizedLiftGeneratorFinset {p : TailPoly ℚ} (C : OneTieCoordinates D i p)
    (E : Finset (Fin 3 →₀ ℕ)) : Finset (ThreePoly ℚ) := by
  classical
  exact insert (tiePolynomial C.a C.b C.c)
    ((normalizedMonomialGeneratorFinset C E).image (polynomialLift (k := ℚ)))

/--
@isnad1 id=eq.0h5v.s7.90188d3137dc from=translated src=- shape=25a58019 vocab=9e162bf5
-/
theorem normalizedLiftGeneratorFinset_span_eq {p : TailPoly ℚ}
    (C : OneTieCoordinates D i p) (E : Finset (Fin 3 →₀ ℕ)) :
    Ideal.span (↑(normalizedLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) =
      Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) := by
  classical
  let R := Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ))
  let N := Ideal.span (↑(normalizedLiftGeneratorFinset C E) : Set (ThreePoly ℚ))
  have hrTie : tieIdeal ℚ C.a C.b C.c ≤ R := by
    apply Ideal.span_le.mpr
    intro f hf
    rw [Set.mem_singleton_iff.mp hf]
    exact Ideal.subset_span (Finset.mem_insert_self _ _)
  have hnTie : tieIdeal ℚ C.a C.b C.c ≤ N := by
    apply Ideal.span_le.mpr
    intro f hf
    rw [Set.mem_singleton_iff.mp hf]
    exact Ideal.subset_span (Finset.mem_insert_self _ _)
  have hdiff (d : Fin 3 →₀ ℕ) :
      MvPolynomial.monomial d (1 : ℚ) - polynomialLift (normalizeExponent C.a C.b C.c d) ∈
        tieIdeal ℚ C.a C.b C.c := monomial_sub_normalMonomial_mem_tieIdeal d 1
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro f hf
    rcases Finset.mem_insert.mp hf with he | hm
    · subst f; exact hrTie (tiePolynomial_mem_tieIdeal)
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hq
      change polynomialLift (normalizeExponent C.a C.b C.c d) ∈ R
      have hraw : MvPolynomial.monomial d (1 : ℚ) ∈ R :=
        Ideal.subset_span (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hd,rfl⟩))
      simpa only [sub_sub_cancel, R] using R.sub_mem hraw (hrTie (hdiff d))
  · apply Ideal.span_le.mpr
    intro f hf
    rcases Finset.mem_insert.mp hf with he | hm
    · subst f; exact hnTie tiePolynomial_mem_tieIdeal
    · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hm
      change MvPolynomial.monomial d (1 : ℚ) ∈ N
      have hnorm : polynomialLift (normalizeExponent C.a C.b C.c d) ∈ N :=
        Ideal.subset_span (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨_,Finset.mem_image.mpr ⟨d,hd,rfl⟩,rfl⟩))
      simpa only [add_sub_cancel, N] using N.add_mem hnorm (hnTie (hdiff d))

/--
@isnad1 id=ne.0h4v.s6.5e8f5862418a from=translated src=- shape=13e716d5 vocab=5ddcc3ce
-/
theorem normalMonomial_ne_zero (a b c : ℕ) [NeZero a] (q : Normal a b c) :
    monomial (k := ℚ) q ≠ 0 := by
  intro hz
  have hc := congrArg (fun f : NormalMonoidAlgebra ℚ a b c => f.coeff q) hz
  simpa using hc

/--
@isnad1 id=ne.0h4v.s5.5e6729f74717 from=translated src=- shape=8ebc4144 vocab=ec71ff72
-/
theorem tiePolynomial_ne_polynomialLift (a b c : ℕ) [NeZero a] (q : Normal a b c) :
    tiePolynomial (k := ℚ) a b c ≠ polynomialLift q := by
  intro he
  have hm := congrArg (polyToNormalAlg (k := ℚ) (a := a) (b := b) (c := c)) he
  have hz : monomial (k := ℚ) q = 0 := by simpa using hm.symm
  exact normalMonomial_ne_zero a b c q hz

/--
@isnad1 id=and.3h5v.s7.764519523919 from=translated src=- shape=41fca642 vocab=b681816c
-/
theorem normalizedGeneratorFinsets_card {p : TailPoly ℚ} (C : OneTieCoordinates D i p)
    (E : Finset (Fin 3 →₀ ℕ))
    (hspan : Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) =
      renamedChosenBaseIdeal C) (hcard : E.card = D.semigroupRho - 1)
    (hpos : 0 < D.semigroupRho) :
    (normalizedLiftGeneratorFinset C E).card = D.semigroupRho ∧
      (normalizedMonomialGeneratorFinset C E).card = D.semigroupRho - 1 := by
  classical
  have hs := (normalizedLiftGeneratorFinset_span_eq C E).trans hspan
  have hl := (renamedChosenBaseIdeal_minimalGeneratorCard C).2 _ hs
  have hn : tiePolynomial C.a C.b C.c ∉
      (normalizedMonomialGeneratorFinset C E).image (polynomialLift (k := ℚ)) := by
    rintro hm
    obtain ⟨q,_,he⟩ := Finset.mem_image.mp hm
    exact tiePolynomial_ne_polynomialLift C.a C.b C.c q he.symm
  have hc : (normalizedLiftGeneratorFinset C E).card =
      (normalizedMonomialGeneratorFinset C E).card + 1 := by
    rw [normalizedLiftGeneratorFinset, Finset.card_insert_of_notMem hn,
      Finset.card_image_of_injective _ polynomialLift_injective]
  have hle : (normalizedMonomialGeneratorFinset C E).card ≤ E.card := Finset.card_image_le
  constructor <;> omega

/-- The actual budget-one family supplies every premise of normalization.
@isnad1 id=ex.1h2v.s7.17f039f87559 from=translated src=- shape=981544c1 vocab=03ad026d
-/
theorem budgetOne_raw_normalization_data (D : FourGeneratedNumericalSemigroup)
    (i : Fin 4) (hB : D.fourBaseBudget i = 1) :
    ∃ (p : TailPoly ℚ) (C : OneTieCoordinates D i p) (E : Finset (Fin 3 →₀ ℕ)),
      Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ)) = renamedChosenBaseIdeal C ∧
      E.card = D.semigroupRho - 1 ∧ 0 < D.semigroupRho := by
  classical
  obtain ⟨G,g,hspan,hcard,hmem,hlive,_,hmon,hErase,_,_⟩ :=
    chosenBase_minimal_one_live_binomial_of_budget_one (k := ℚ) D i hB
  let p := D.specializedConnectorPolynomial (k := ℚ) i g
  obtain ⟨T⟩ := liveTailTieData_exists D i p hlive
  obtain ⟨C⟩ := oneTieCoordinates_exists T
  let M := G.erase p
  have hshape (q : ↥M) : ∃ w, (q : TailPoly ℚ) = -MvPolynomial.monomial w 1 := by
    obtain ⟨w,he,_⟩ := hmon q.1 (Finset.mem_erase.mp q.2).2 (Finset.mem_erase.mp q.2).1
    exact ⟨w,he⟩
  let w (q : ↥M) : Fin 3 →₀ ℕ := Classical.choose (hshape q)
  let E := M.attach.image (fun q => (w q).mapDomain C.sigma)
  have heq (q : ↥M) : renameToOneTie C (q : TailPoly ℚ) =
      -MvPolynomial.monomial ((w q).mapDomain C.sigma) 1 := by
    change MvPolynomial.rename C.sigma (q : TailPoly ℚ) = _
    have hq : (q : TailPoly ℚ) = -MvPolynomial.monomial (w q) 1 := Classical.choose_spec (hshape q)
    calc
      MvPolynomial.rename C.sigma (q : TailPoly ℚ) =
          MvPolynomial.rename C.sigma (-MvPolynomial.monomial (w q) 1) :=
        congrArg (MvPolynomial.rename C.sigma) hq
      _ = _ := by simp [MvPolynomial.rename_monomial]
  have hEcard : E.card ≤ D.semigroupRho - 1 := by
    calc E.card ≤ M.attach.card := Finset.card_image_le
         _ = M.card := Finset.card_attach
         _ = D.semigroupRho - 1 := by
           dsimp only [M]
           rw [Finset.card_erase_of_mem hmem, hcard]
  have hpI : p ∈ chosenBaseDefiningIdeal D i := by
    rw [← hspan]; exact Ideal.subset_span hmem
  let R := Ideal.span (↑(rawLiftGeneratorFinset C E) : Set (ThreePoly ℚ))
  have hraw : R = renamedChosenBaseIdeal C := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro f hf
      rcases Finset.mem_insert.mp hf with he | hm
      · subst f; exact tiePolynomial_mem_renamedChosenBaseIdeal C hpI
      · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hm
        obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hd
        change MvPolynomial.monomial ((w q).mapDomain C.sigma) (1 : ℚ) ∈ renamedChosenBaseIdeal C
        have hqI : (q : TailPoly ℚ) ∈ chosenBaseDefiningIdeal D i := by
          rw [← hspan]
          exact Ideal.subset_span (Finset.mem_erase.mp q.2).2
        have hmI : renameToOneTie C (q : TailPoly ℚ) ∈ renamedChosenBaseIdeal C :=
          Ideal.mem_map_of_mem (renameToOneTie C).toRingHom hqI
        rw [heq] at hmI
        simpa only [neg_neg] using neg_mem hmI
    · change (chosenBaseDefiningIdeal D i).map (renameToOneTie C).toRingHom ≤ R
      rw [← hspan, Ideal.map_span]
      apply Ideal.span_le.mpr
      rintro f ⟨q,hq,rfl⟩
      change renameToOneTie C q ∈ R
      by_cases hqp : q = p
      · rw [hqp]
        have ht : tiePolynomial C.a C.b C.c ∈ R := Ideal.subset_span (Finset.mem_insert_self _ _)
        rcases renameToOneTie_live C with he | he
        · rwa [he]
        · rw [he]; exact neg_mem ht
      · let q' : ↥M := ⟨q, Finset.mem_erase.mpr ⟨hqp,hq⟩⟩
        have hd : (w q').mapDomain C.sigma ∈ E :=
          Finset.mem_image.mpr ⟨q',Finset.mem_attach _ _,rfl⟩
        have hm : MvPolynomial.monomial ((w q').mapDomain C.sigma) (1 : ℚ) ∈ R :=
          Ideal.subset_span (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_,hd,rfl⟩))
        change renameToOneTie C (q' : TailPoly ℚ) ∈ R
        rw [heq]; exact neg_mem hm
  have hpos : 0 < D.semigroupRho := by
    rw [← hcard]
    exact Finset.card_pos.mpr ⟨p,hmem⟩
  have hl := (renamedChosenBaseIdeal_minimalGeneratorCard C).2 (rawLiftGeneratorFinset C E) hraw
  have hu : (rawLiftGeneratorFinset C E).card ≤ E.card + 1 := by
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
  exact ⟨p,C,E,hraw,by omega,hpos⟩

end
end P23.Semigroup
