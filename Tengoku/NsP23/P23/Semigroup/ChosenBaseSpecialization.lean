import Tengoku.NsP23.P23.Semigroup.ChosenBase
import Tengoku.NsP23.P23.Semigroup.ToricPresentation
import Tengoku.Seed.Algebra.MvPolynomial.Rename
import Tengoku.Seed.RingTheory.MvPolynomial.Ideal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact base-variable specialization to the frozen three-tail order. -/
namespace P23.Semigroup
noncomputable section
open FourGeneratedNumericalSemigroup
variable {k : Type*} [Field k]
variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)

def tailIndexEquiv : Fin 3 ≃ {j : Fin 4 // j ≠ i} :=
  Equiv.ofBijective (fun j => ⟨D.tailIndex i j, D.tailIndex_ne_base i j⟩) (by
    constructor
    · intro j l h
      exact (D.tailIndex i).injective (congrArg Subtype.val h)
    · intro j
      have hj : j.1 ∈ Set.range (D.tailIndex i) := by
        change j.1 ∈ Set.range i.succAbove
        simpa only [Fin.range_succAbove, Set.mem_compl_iff, Set.mem_singleton_iff] using j.2
      obtain ⟨l, hl⟩ := hj
      exact ⟨l, Subtype.ext hl⟩)

/--
@isnad1 id=eq.0h3v.s8.7f9c8d7eef2e from=translated src=- shape=64efb303 vocab=664b1a28
-/
@[simp] theorem tailIndexEquiv_apply (j : Fin 3) :
    (tailIndexEquiv D i j).1 = D.tailIndex i j := rfl

/--
@isnad1 id=eq.1h3v.s8.91f6eab0fa7f from=translated src=- shape=c2beb7dc vocab=0e38098b
-/
@[simp] theorem tailIndexEquiv_symm_apply (j : Fin 4) (hj : j ≠ i) :
    D.tailIndex i ((tailIndexEquiv D i).symm ⟨j, hj⟩) = j :=
  congrArg Subtype.val ((tailIndexEquiv D i).apply_symm_apply ⟨j, hj⟩)

def baseSpecialization : FourPoly k →ₐ[k] TailPoly k :=
  MvPolynomial.killCompl (D.tailIndex i).injective

def tailEmbedding : TailPoly k →ₐ[k] FourPoly k :=
  MvPolynomial.rename (D.tailIndex i)

/--
@isnad1 id=eq.0h3v.s8.c808f4d7b44e from=translated src=- shape=4ef6273e vocab=223e4431
-/
@[simp] theorem baseSpecialization_X_base :
    baseSpecialization (k := k) D i (MvPolynomial.X i) = 0 := by
  have hi : i ∉ Set.range (D.tailIndex i) := by
    rintro ⟨j, hj⟩
    exact D.tailIndex_ne_base i j hj
  simp [baseSpecialization, MvPolynomial.killCompl, hi]

/--
@isnad1 id=eq.0h4v.s8.2a7cee382785 from=translated src=- shape=cc9c2f71 vocab=f9390866
-/
@[simp] theorem baseSpecialization_X_tail (j : Fin 3) :
    baseSpecialization (k := k) D i (MvPolynomial.X (D.tailIndex i j)) =
      MvPolynomial.X j := by
  simpa [baseSpecialization, ← MvPolynomial.rename_X (D.tailIndex i) j] using
    MvPolynomial.killCompl_rename_app (D.tailIndex i).injective (MvPolynomial.X j : TailPoly k)

/--
@isnad1 id=eq.0h3v.s8.4471f3f16dac from=translated src=- shape=5f81e7db vocab=7ac4d770
-/
@[simp] theorem baseSpecialization_comp_tailEmbedding :
    (baseSpecialization (k := k) D i).comp (tailEmbedding D i) = AlgHom.id k _ :=
  MvPolynomial.killCompl_comp_rename (D.tailIndex i).injective

/--
@isnad1 id=eq.0h4v.s9.6073aa458885 from=translated src=- shape=b57b8527 vocab=59851f6c
-/
@[simp] theorem baseSpecialization_tailEmbedding (p : TailPoly k) :
    baseSpecialization D i (tailEmbedding D i p) = p :=
  MvPolynomial.killCompl_rename_app (D.tailIndex i).injective p

/--
@isnad1 id=surjecti.0h3v.s8.e1797bea1c5c from=translated src=- shape=93ceda27 vocab=a38b88cd
-/
theorem baseSpecialization_surjective :
    Function.Surjective (baseSpecialization (k := k) D i) :=
  fun p => ⟨tailEmbedding D i p, baseSpecialization_tailEmbedding D i p⟩

abbrev restrictToTails := tailExponent D i
abbrev tailEmbeddingExponent := extendTailExponent i

/--
@isnad1 id=eq.0h4v.s7.28b5304c986e from=translated src=- shape=8d1d89cf vocab=50b20157
-/
@[simp] theorem restrictToTails_apply (u : Fin 4 →₀ ℕ) (j : Fin 3) :
    restrictToTails D i u j = u (D.tailIndex i j) := tailExponent_apply D i u j

/--
@isnad1 id=eq.0h3v.s6.43989c9470bf from=translated src=- shape=a5a3fb5d vocab=d74ef9c1
-/
theorem tailEmbeddingExponent_eq_mapDomain (v : Fin 3 →₀ ℕ) :
    tailEmbeddingExponent i v = v.mapDomain (D.tailIndex i) := by
  ext j
  refine Fin.succAboveCases i ?_ (fun l => ?_) j
  · rw [extendTailExponent_base, Finsupp.mapDomain_of_notMem_range]
    rintro ⟨l, hl⟩
    exact D.tailIndex_ne_base i l hl
  · change extendTailExponent i v (i.succAbove l) =
      v.mapDomain (D.tailIndex i) (D.tailIndex i l)
    rw [Finsupp.mapDomain_apply (D.tailIndex i).injective]
    exact extendTailExponent_tail i v l

/--
@isnad1 id=eq.1h3v.s6.de4708a7a503 from=translated src=- shape=b25481da vocab=7b2585e6
-/
theorem tailEmbedding_restrictToTails (u : Fin 4 →₀ ℕ) (hu : u i = 0) :
    tailEmbeddingExponent i (restrictToTails D i u) = u := by
  ext j
  refine Fin.succAboveCases i ?_ (fun l => ?_) j
  · simpa using hu.symm
  · simp [tailEmbeddingExponent, restrictToTails]

/--
@isnad1 id=eq.1h3v.s6.41b6000bc9df from=translated src=- shape=beced1c3 vocab=2d7ed583
-/
theorem restrictToTails_degree (u : Fin 4 →₀ ℕ) (hu : u i = 0) :
    tailDegree D i (restrictToTails D i u) = D.weightedDegree u :=
  (weightedDegree_eq_tailDegree_of_base_zero D i u hu).symm

/--
@isnad1 id=eq.1h5v.s9.04a0eb1ba12c from=translated src=- shape=02b11247 vocab=ddcec87d
-/
theorem baseSpecialization_monomial_of_base_pos (u : Fin 4 →₀ ℕ) (r : k)
    (hu : 0 < u i) : baseSpecialization D i (MvPolynomial.monomial u r) = 0 := by
  apply MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range
  · exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hu)
  · rintro ⟨j, hj⟩
    exact D.tailIndex_ne_base i j hj

/--
@isnad1 id=eq.1h5v.s9.845e8b20ad46 from=translated src=- shape=61bbe99f vocab=0121e23c
-/
theorem baseSpecialization_monomial_of_base_zero (u : Fin 4 →₀ ℕ) (r : k)
    (hu : u i = 0) : baseSpecialization D i (MvPolynomial.monomial u r) =
      MvPolynomial.monomial (restrictToTails D i u) r := by
  have h := tailEmbedding_restrictToTails D i u hu
  rw [tailEmbeddingExponent_eq_mapDomain D i] at h
  conv_lhs => rw [← h]
  exact MvPolynomial.killCompl_monomial_mapDomain (R := k) (D.tailIndex i).injective

/--
@isnad1 id=eq.0h3v.s9.aac7441cfeeb from=translated src=- shape=e2d5fa72 vocab=65821064
-/
theorem baseSpecialization_ker :
    RingHom.ker (baseSpecialization (k := k) D i).toRingHom =
      Ideal.span {MvPolynomial.X i} := by
  classical
  apply le_antisymm
  · intro p hp
    change baseSpecialization D i p = 0 at hp
    have h := (MvPolynomial.mem_ideal_span_X_image
      (x := p) (s := ({i} : Set (Fin 4))))
    rw [Set.image_singleton] at h
    apply h.mpr
    intro u hu
    refine ⟨i, Set.mem_singleton _, ?_⟩
    intro hui
    have hrecon := tailEmbedding_restrictToTails D i u hui
    rw [tailEmbeddingExponent_eq_mapDomain D i] at hrecon
    have hc := congrArg (MvPolynomial.coeff (restrictToTails D i u)) hp
    change MvPolynomial.coeff _ (MvPolynomial.killCompl (D.tailIndex i).injective p) = _ at hc
    rw [MvPolynomial.coeff_killCompl, hrecon, MvPolynomial.coeff_zero] at hc
    exact (MvPolynomial.mem_support_iff.mp hu) hc
  · rw [Ideal.span_le]
    rintro p (rfl : p = _)
    exact baseSpecialization_X_base D i

def fourPolyToChosenBase : FourPoly k →ₐ[k] ChosenBaseQuotient (k := k) D i :=
  (Ideal.Quotient.mkₐ k (baseMonomialIdeal D i)).comp D.semigroupPolyMap

/--
@isnad1 id=eq.0h3v.s9.1857a001d87b from=translated src=- shape=50c07593 vocab=72d3ac5b
-/
theorem fourPolyToChosenBase_eq : fourPolyToChosenBase (k := k) D i =
    (tailPolyToChosenBase D i).comp (baseSpecialization D i) := by
  apply MvPolynomial.algHom_ext
  intro j
  refine Fin.succAboveCases i ?_ (fun l => ?_) j
  · apply (chosenBaseEquivApery (k := k) D i).injective
    have hnot : ¬D.IsApery i (D.generator i) := D.base_not_isApery i
    simp [fourPolyToChosenBase, semigroupPolyMap,
      baseSpecialization_X_base, semigroupToAperyAlg_T, truncatedAperyMonomial,
      hnot]
  · change fourPolyToChosenBase D i (MvPolynomial.X (D.tailIndex i l)) =
      tailPolyToChosenBase D i (baseSpecialization D i (MvPolynomial.X (D.tailIndex i l)))
    rw [baseSpecialization_X_tail]
    apply (chosenBaseEquivApery (k := k) D i).injective
    simp only [fourPolyToChosenBase, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      semigroupPolyMap, MvPolynomial.aeval_X, chosenBaseEquivApery_mk,
      semigroupToAperyAlg_T, tailPolyToChosenBase, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply, tailPolyToApery]
    exact truncatedAperyMonomial_tail D i l

/--
@isnad1 id=eq.0h3v.s9.d1bf35d3f439 from=translated src=- shape=5410ca16 vocab=e4b865c0
-/
theorem fourPolyToChosenBase_ker :
    RingHom.ker (fourPolyToChosenBase (k := k) D i).toRingHom =
      D.toricIdeal ⊔ Ideal.span {MvPolynomial.X i} := by
  have hmap : Ideal.map D.semigroupPolyMap.toRingHom
      (Ideal.span {MvPolynomial.X i}) = baseMonomialIdeal (k := k) D i := by
    rw [Ideal.map_span, Set.image_singleton]
    simp [semigroupPolyMap, baseMonomialIdeal, base]
  change RingHom.ker ((Ideal.Quotient.mk (baseMonomialIdeal D i)).comp
    D.semigroupPolyMap.toRingHom) = _
  rw [← RingHom.comap_ker, Ideal.mk_ker, ← hmap,
    Ideal.comap_map_of_surjective D.semigroupPolyMap.toRingHom D.semigroupPolyMap_surjective,
    ← RingHom.ker_eq_comap_bot]
  exact sup_comm _ _

/--
@isnad1 id=eq.0h3v.s9.c67b22f0bb9a from=translated src=- shape=74a6db53 vocab=0dcf2634
-/
theorem fourPolyToChosenBase_ker_comap :
    RingHom.ker (fourPolyToChosenBase (k := k) D i).toRingHom =
      Ideal.comap (baseSpecialization D i).toRingHom (chosenBaseDefiningIdeal D i) := by
  rw [fourPolyToChosenBase_eq]
  exact (RingHom.comap_ker _ _).symm

/--
@isnad1 id=eq.0h3v.s8.4eeac80ff4bf from=translated src=- shape=557f1e71 vocab=04164fc3
-/
theorem map_toricIdeal_eq_chosenBaseDefiningIdeal :
    Ideal.map (baseSpecialization (k := k) D i).toRingHom D.toricIdeal =
      chosenBaseDefiningIdeal D i := by
  have h := congrArg (Ideal.map (baseSpecialization (k := k) D i).toRingHom)
    ((fourPolyToChosenBase_ker D i).symm.trans (fourPolyToChosenBase_ker_comap D i))
  have hX : (baseSpecialization (k := k) D i).toRingHom (MvPolynomial.X i) = 0 :=
    baseSpecialization_X_base D i
  simpa only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hX,
    Ideal.span_singleton_zero, sup_bot_eq,
    Ideal.map_comap_of_surjective (baseSpecialization D i).toRingHom
      (baseSpecialization_surjective D i)] using h

end
end P23.Semigroup
