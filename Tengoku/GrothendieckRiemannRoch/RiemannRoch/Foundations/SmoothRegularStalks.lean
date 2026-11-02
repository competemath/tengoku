/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.Smooth.StandardSmooth
import Tengoku.Seed.RingTheory.Ideal.KrullsHeightTheorem
import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Ideal
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.RelativeRiemannRoch.PolynomialRegularF14

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Smooth algebras over regular rings are regular (G2POL5)

Jacobian route (no étale ascent needed):

* `isRegularLocalRing_quotient_of_linearIndependent` : if `R` is regular local and `f : σ → m` has
  `κ`-linearly independent images in `m/m²`, then `R ⧸ (f)` is regular local
  (Nakayama + Krull's height theorem `ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank`).
* `linearIndependent_locRel` : in `R0[X_ι]_Q`, relations `f_j ∈ Q` whose Jacobian minor
  `det (∂f_j/∂X_{a i})` lies outside `Q` are independent in the cotangent space
  (via the maps `x ↦ ∂x/∂X_a mod Q`, which kill `Q²`).
* `isRegularLocalRing_localization_of_submersivePresentation`,
  `isRegularRing_of_isStandardSmooth` : a standard smooth algebra over a regular ring is regular.
-/

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace RRC.SmoothRegularStalks

section QuotientRegular

/-- The range of a function on a finite type has at most `card` elements.-/
theorem ncard_range_le_card {α β : Type*} [Fintype α] (f : α → β) :
    (Set.range f).ncard ≤ Fintype.card α := by
  rw [← Set.image_univ]
  exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])

variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

/-- **Cutting a regular local ring by part of a regular system of parameters.**  If `f : σ → m`
has `κ`-linearly independent images in `m/m²`, then `R ⧸ (f)` is a regular local ring.-/
theorem isRegularLocalRing_quotient_of_linearIndependent {σ : Type*} [Fintype σ]
    (f : σ → maximalIdeal R)
    (hf : LinearIndependent (ResidueField R) fun i => (maximalIdeal R).toCotangent (f i)) :
    IsRegularLocalRing (R ⧸ Ideal.span (Set.range fun i => (f i : R))) := by
  classical
  set I : Ideal R := Ideal.span (Set.range fun i => (f i : R)) with hI
  have hIm : I ≤ maximalIdeal R := by
    rw [hI, Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact (f i).2
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIm
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  -- the cotangent space and a complement of the span of the `f i`
  let v : σ → CotangentSpace R := fun i => (maximalIdeal R).toCotangent (f i)
  set W : Submodule (ResidueField R) (CotangentSpace R) :=
    Submodule.span (ResidueField R) (Set.range v) with hW
  obtain ⟨C, hWC⟩ := Submodule.exists_isCompl W
  let bC := Module.finBasis (ResidueField R) C
  have hgex : ∀ j, ∃ g : maximalIdeal R, (maximalIdeal R).toCotangent g = (bC j : _) :=
    fun j => (maximalIdeal R).toCotangent_surjective _
  choose g hg using hgex
  -- `f ∪ g` generates `m`
  have hspan : Submodule.span R (Set.range f ∪ Set.range g) = ⊤ := by
    rw [← CotangentSpace.span_image_eq_top_iff, eq_top_iff, ← hWC.sup_eq_top]
    refine sup_le ?_ ?_
    · rw [hW, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨f i, Or.inl ⟨i, rfl⟩, rfl⟩
    · intro c hc
      have hc' : (⟨c, hc⟩ : C) ∈ Submodule.span (ResidueField R) (Set.range bC) := by
        rw [bC.span_eq]; trivial
      have := Submodule.mem_map_of_mem (f := C.subtype) hc'
      rw [Submodule.map_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨g j, Or.inr ⟨j, rfl⟩, hg j⟩
  have hm : maximalIdeal R =
      Ideal.span (Set.range (fun i => (f i : R)) ∪ Set.range (fun j => (g j : R))) := by
    have := congrArg (Submodule.map (maximalIdeal R).subtype) hspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Set.image_union,
      ← Set.range_comp, ← Set.range_comp] at this
    exact this.symm
  -- the maximal ideal of the quotient
  have hmT : maximalIdeal (R ⧸ I) = Ideal.span (Set.range fun j => Ideal.Quotient.mk I (g j)) := by
    have hmax : ((maximalIdeal R).map (Ideal.Quotient.mk I)).IsMaximal := by
      refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
        (maximalIdeal.isMaximal R)).resolve_left fun h => (maximalIdeal.isMaximal R).ne_top ?_
      have := congrArg (Ideal.comap (Ideal.Quotient.mk I)) h
      rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIm, Ideal.comap_top] at this
    rw [← IsLocalRing.eq_maximalIdeal hmax, congrArg (Ideal.map (Ideal.Quotient.mk I)) hm,
      Ideal.map_span, Set.image_union,
      Ideal.span_union, ← Set.range_comp, ← Set.range_comp]
    have h0 : Ideal.span (Set.range (Ideal.Quotient.mk I ∘ fun i => (f i : R))) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    rw [h0, bot_sup_eq]
    rfl
  -- numerical bookkeeping
  have hT : (maximalIdeal (R ⧸ I)).spanFinrank ≤ Module.finrank (ResidueField R) C := by
    rw [hmT]
    refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)) ?_
    exact le_trans (ncard_range_le_card _) (by simp)
  have hWr : Module.finrank (ResidueField R) W = Fintype.card σ := finrank_span_eq_card hf
  have hVr : Module.finrank (ResidueField R) W + Module.finrank (ResidueField R) C =
      (maximalIdeal R).spanFinrank := by
    rw [Submodule.finrank_add_eq_of_isCompl hWC, spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  have hIr : I.spanFinrank ≤ Fintype.card σ := by
    refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)) ?_
    exact ncard_range_le_card _
  have hKrull := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I
    (le_trans hIm (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal]))
  have hreg := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  have hle := ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ I)
  have hne : ringKrullDim (R ⧸ I) ≠ ⊥ := fun h => by
    have := ringKrullDim_nonneg_of_nontrivial (R := R ⧸ I)
    rw [h] at this
    exact absurd this (by simp)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim (R ⧸ I) = n := by
    rcases h : ringKrullDim (R ⧸ I) with _ | n
    · exact absurd h hne
    · rcases n with _ | n
      · have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤
            (((maximalIdeal (R ⧸ I)).spanFinrank : ℕ∞) : WithBot ℕ∞) := by
          rw [h] at hle; exact hle
        rw [WithBot.coe_le_coe, top_le_iff] at h'
        exact absurd h' (ENat.natCast_ne_top _)
      · exact ⟨n, rfl⟩
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [hn] at hKrull ⊢
  rw [← hreg] at hKrull
  have : (maximalIdeal R).spanFinrank ≤ n + I.spanFinrank := by exact_mod_cast hKrull
  exact_mod_cast (show (maximalIdeal (R ⧸ I)).spanFinrank ≤ n by omega)

end QuotientRegular

section Jacobian

open MvPolynomial

variable {R0 : Type*} [CommRing R0] {ι : Type*}

/-- `x ↦ (∂x/∂X_a mod Q)` kills `Q²`.-/
theorem residue_pderiv_eq_zero_of_mem_sq (Q : Ideal (MvPolynomial ι R0)) [Q.IsPrime] (a : ι)
    {z : MvPolynomial ι R0} (hz : z ∈ Q ^ 2) :
    algebraMap _ Q.ResidueField (pderiv a z) = 0 := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · rw [(pderiv a).leibniz x y, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
      Ideal.algebraMap_residueField_eq_zero.mpr hx, Ideal.algebraMap_residueField_eq_zero.mpr hy]
    simp
  · rw [map_add, map_add, hx, hy, add_zero]

/-- The images of the relations in the localization at a prime containing them.-/
def locRel (Q : Ideal (MvPolynomial ι R0)) [Q.IsPrime] {σ : Type*} (f : σ → MvPolynomial ι R0)
    (hfQ : ∀ i, f i ∈ Q) (i : σ) : maximalIdeal (Localization.AtPrime Q) :=
  ⟨algebraMap _ _ (f i), (IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q _).mpr (hfQ i)⟩

/-- **Jacobian criterion, independence half.**  If `f_j ∈ Q` and the Jacobian minor
`det (∂f_j/∂X_{a i})` is not in `Q`, then the `f_j` have linearly independent images in the
cotangent space of `A_Q`.-/
theorem linearIndependent_locRel (Q : Ideal (MvPolynomial ι R0)) [Q.IsPrime] {σ : Type*}
    [Fintype σ] [DecidableEq σ] (f : σ → MvPolynomial ι R0) (hfQ : ∀ i, f i ∈ Q) (a : σ → ι)
    (hdet : (Matrix.of fun i j => pderiv (a i) (f j)).det ∉ Q) :
    LinearIndependent (ResidueField (Localization.AtPrime Q))
      fun i => (maximalIdeal (Localization.AtPrime Q)).toCotangent (locRel Q f hfQ i) := by
  classical
  set L := Localization.AtPrime Q
  rw [Fintype.linearIndependent_iff]
  intro c hc
  choose a' ha' using fun i => IsLocalRing.residue_surjective (c i)
  obtain ⟨⟨b, hb⟩, hbint⟩ := IsLocalization.exist_integer_multiples Q.primeCompl Finset.univ a'
  choose p hp using fun i => hbint i (Finset.mem_univ i)
  -- the relation in `m²`
  have key : (maximalIdeal L).toCotangent (∑ i, a' i • locRel Q f hfQ i) = 0 := by
    rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← ha', ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  have hsum : (∑ i, a' i * algebraMap _ L (f i)) ∈ maximalIdeal L ^ 2 := by
    have := (Ideal.toCotangent_eq_zero _ _).mp key
    simpa [locRel, smul_eq_mul] using this
  -- clear denominators
  have hp' : ∀ i, algebraMap _ L (p i) = algebraMap _ L b * a' i := fun i => by
    rw [hp i]; exact Algebra.smul_def _ _
  set X : MvPolynomial ι R0 := ∑ i, p i * f i with hX
  have hXQ : X ∈ Q := Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hfQ i)
  have hXL : algebraMap _ L X = algebraMap _ L b * ∑ i, a' i * algebraMap _ L (f i) := by
    simp only [hX, map_sum, map_mul, hp', Finset.mul_sum, mul_assoc]
  have hXmem : algebraMap _ L X ∈ (Q ^ 2).map (algebraMap _ L) := by
    rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal, hXL]
    exact Ideal.mul_mem_left _ _ hsum
  obtain ⟨⟨y, s⟩, hys⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl L).mp hXmem
  rw [← map_mul] at hys
  obtain ⟨c', hc'⟩ := (IsLocalization.eq_iff_exists Q.primeCompl L).mp hys
  have ht : (c' : MvPolynomial ι R0) * s ∉ Q := (Q.primeCompl.mul_mem c'.2 s.2 :)
  have htX : ((c' : MvPolynomial ι R0) * s) * X ∈ Q ^ 2 := by
    rw [show ((c' : MvPolynomial ι R0) * s) * X = c' * (X * s) by ring, hc']
    exact Ideal.mul_mem_left _ _ y.2
  generalize (c' : MvPolynomial ι R0) * s = t at ht htX
  -- differentiate
  have hfQ' : ∀ i, algebraMap _ Q.ResidueField (f i) = 0 := fun i =>
    Ideal.algebraMap_residueField_eq_zero.mpr (hfQ i)
  have hrow : ∀ j, ∑ i, algebraMap _ Q.ResidueField (pderiv (a j) (f i)) *
      algebraMap _ Q.ResidueField (p i) = 0 := by
    intro j
    have h0 := residue_pderiv_eq_zero_of_mem_sq Q (a j) htX
    rw [(pderiv (a j)).leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul _ t, map_mul _ X,
      Ideal.algebraMap_residueField_eq_zero.mpr hXQ, zero_mul, add_zero] at h0
    have ht' : algebraMap _ Q.ResidueField t ≠ 0 :=
      mt Ideal.algebraMap_residueField_eq_zero.mp ht
    have h1 := (mul_eq_zero.mp h0).resolve_left ht'
    rw [hX, map_sum, map_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(pderiv _).leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hfQ' i]
    ring
  set N := (Matrix.of fun i j => pderiv (a i) (f j)).map (algebraMap _ Q.ResidueField) with hN
  have hNdet : N.det ≠ 0 := by
    have : N.det = algebraMap _ Q.ResidueField (Matrix.of fun i j => pderiv (a i) (f j)).det := by
      rw [RingHom.map_det]; rfl
    rw [this]
    exact mt Ideal.algebraMap_residueField_eq_zero.mp hdet
  have hv : N.mulVec (fun i => algebraMap _ Q.ResidueField (p i)) = 0 := by
    ext j
    simpa [N, Matrix.mulVec, dotProduct] using hrow j
  have hpv := Matrix.eq_zero_of_mulVec_eq_zero hNdet hv
  intro i
  have hpi : p i ∈ Q := Ideal.algebraMap_residueField_eq_zero.mp (congrFun hpv i)
  have hbu : IsUnit (algebraMap _ L b) := IsLocalization.map_units L (⟨b, hb⟩ : Q.primeCompl)
  have : residue L (algebraMap _ L b) * c i = 0 := by
    rw [← ha', ← map_mul, ← hp', IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L Q (p i)).mpr hpi
  exact (mul_eq_zero.mp this).resolve_left ((residue_ne_zero_iff_isUnit _).mpr hbu)

end Jacobian

section StandardSmooth

/-- Polynomial rings in finitely many variables over a regular ring are regular.-/
theorem isRegularRing_mvPolynomial_fin (R0 : Type*) [CommRing R0] [IsRegularRing R0] (n : ℕ) :
    IsRegularRing (MvPolynomial (Fin n) R0) := by
  induction n with
  | zero =>
    exact IsRegularRing.of_ringEquiv (MvPolynomial.isEmptyRingEquiv R0 (Fin 0)).symm
  | succ n ih =>
    haveI := ih
    exact IsRegularRing.of_ringEquiv (MvPolynomial.finSuccEquiv R0 n).toRingEquiv.symm

/-- `R0[X_ι]` is regular for `R0` regular and `ι` finite.-/
theorem isRegularRing_mvPolynomial (R0 : Type*) [CommRing R0] [IsRegularRing R0] (ι : Type*)
    [Finite ι] : IsRegularRing (MvPolynomial ι R0) := by
  haveI := isRegularRing_mvPolynomial_fin R0 (Nat.card ι)
  exact IsRegularRing.of_ringEquiv
    (MvPolynomial.renameEquiv R0 (Finite.equivFin ι).symm).toRingEquiv

/-- **Localizations of a submersively presented algebra over a regular ring are regular.**-/
theorem isRegularLocalRing_localization_of_submersivePresentation {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [IsRegularRing R] {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.SubmersivePresentation R S ι σ) (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  classical
  haveI := Fintype.ofFinite σ
  haveI : IsRegularRing P.Ring := isRegularRing_mvPolynomial R ι
  set g : P.Ring →+* S := algebraMap P.Ring S with hgdef
  have hg : Function.Surjective g := P.algebraMap_surjective
  set Q : Ideal P.Ring := q.comap g with hQ
  have hrel : ∀ i, P.relation i ∈ Q := fun i => by
    rw [hQ, Ideal.mem_comap]
    have : g (P.relation i) = 0 := by
      rw [← RingHom.mem_ker]
      exact P.relation_mem_ker i
    rw [this]; exact q.zero_mem
  have hjac : P.jacobiMatrix = Matrix.of fun i j => MvPolynomial.pderiv (P.map i) (P.relation j) := by
    exact Matrix.ext fun i j => P.jacobiMatrix_apply i j
  have hdet : (Matrix.of fun i j => MvPolynomial.pderiv (P.map i) (P.relation j)).det ∉ Q := by
    intro h
    rw [hQ, Ideal.mem_comap, ← hjac] at h
    have hu := P.jacobian_isUnit
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det] at hu
    exact (inferInstance : q.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  have hT := isRegularLocalRing_quotient_of_linearIndependent (locRel Q P.relation hrel)
    (linearIndependent_locRel Q P.relation hrel P.map hdet)
  -- identify the quotient with `S_q`
  have hM : Q.primeCompl.map g = q.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := hg x
      exact ⟨y, hx, rfl⟩
  haveI : IsLocalization (Q.primeCompl.map g) (Localization.AtPrime q) := by
    rw [hM]; infer_instance
  have hsurj := IsLocalization.map_surjective_of_surjective (M := Q.primeCompl)
    (S := Localization.AtPrime Q) (g := g) (Q := Localization.AtPrime q) hg
  have hker := IsLocalization.ker_map (S := Localization.AtPrime Q) (M := Q.primeCompl)
    (Localization.AtPrime q) g hM
  have hkerg : RingHom.ker g = Ideal.span (Set.range P.relation) := by
    rw [P.span_range_relation_eq_ker]; rfl
  have hspan : Ideal.span (Set.range fun i => ((locRel Q P.relation hrel i : _) :
      Localization.AtPrime Q)) = RingHom.ker (IsLocalization.map (Localization.AtPrime q) g
        Q.primeCompl.le_comap_map : Localization.AtPrime Q →+* Localization.AtPrime q) := by
    refine Eq.trans ?_ hker.symm
    rw [hkerg, Ideal.map_span, ← Set.range_comp]
    rfl
  let e : (Localization.AtPrime Q ⧸ Ideal.span (Set.range fun i =>
      ((locRel Q P.relation hrel i : _) : Localization.AtPrime Q))) ≃+* Localization.AtPrime q :=
    (Ideal.quotEquivOfEq hspan).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  exact @IsRegularLocalRing.of_ringEquiv _ _ hT _ _ e

/-- **A standard smooth algebra over a regular ring is a regular ring.**-/
theorem isRegularRing_of_isStandardSmooth (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularRing R] [Algebra.IsStandardSmooth R S] : IsRegularRing S := by
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  refine ⟨fun q _ => ?_⟩
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹Algebra.IsStandardSmooth R S›.out
  exact isRegularLocalRing_localization_of_submersivePresentation P q

end StandardSmooth

end RRC.SmoothRegularStalks
