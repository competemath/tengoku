/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.RegularLocalRing.Defs
import Tengoku.Seed.RingTheory.KrullDimension.Regular
import Tengoku.Seed.RingTheory.Ideal.KrullsHeightTheorem
import Tengoku.Seed.RingTheory.Regular.Flat
import Tengoku.Seed.RingTheory.Localization.Away.Basic
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.RelativeRiemannRoch.PolynomialRegularF14

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# AR12 (stage 1): ascent of regularity along a non-zero-divisor

Local-algebra input for the regularity of blow-ups of regular schemes along regular centres
(blow-up chart `C` with `rC = I C` a non-zero-divisor and `C/rC` a polynomial ring over the
regular `R/I`).

* `isRegularLocalRing_of_quotient_span_singleton` : a Noetherian local ring `S` with a
  non-zero-divisor `x` in the maximal ideal and `S/(x)` regular is regular.
-/

open IsLocalRing

universe u

noncomputable section

namespace BlowupRegularAR12

/-- **Ascent.**  `S` Noetherian local, `x ∈ 𝔪` a non-zero-divisor, `S/(x)` regular ⟹ `S` regular.
@isnad1 id=isregula.2h2v.s7.e94fdfbb5d7c from=translated src=- shape=ade4ec50 vocab=e77a9d8a
-/
theorem isRegularLocalRing_of_quotient_span_singleton {S : Type u} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] {x : S} (hx : IsSMulRegular S x) (hxm : x ∈ maximalIdeal S)
    [IsRegularLocalRing (S ⧸ Ideal.span {x})] : IsRegularLocalRing S := by
  classical
  let π : S →+* S ⧸ Ideal.span {x} := Ideal.Quotient.mk _
  have hπs : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal S).map π = maximalIdeal (S ⧸ Ideal.span {x}) :=
    map_maximalIdeal_of_surjective π hπs
  obtain ⟨T, hTcard, hTspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (maximalIdeal (S ⧸ Ideal.span {x})).fg_of_isNoetherianRing
  set d := (maximalIdeal (S ⧸ Ideal.span {x})).spanFinrank with hd
  let G : Finset S := T.image (Function.surjInv hπs)
  have hGimg : π '' (G : Set S) = (T : Set (S ⧸ Ideal.span {x})) := by
    ext y
    simp only [G, Set.mem_image, Finset.coe_image, Finset.mem_coe]
    constructor
    · rintro ⟨g, ⟨t, ht, rfl⟩, rfl⟩
      simpa [Function.surjInv_eq hπs] using ht
    · intro hy
      exact ⟨_, ⟨y, hy, rfl⟩, Function.surjInv_eq hπs y⟩
  have hGmap : (Ideal.span (G : Set S)).map π = maximalIdeal (S ⧸ Ideal.span {x}) := by
    rw [Ideal.map_span, hGimg]; exact hTspan
  have hker : RingHom.ker π = Ideal.span {x} := Ideal.mk_ker
  have hxle : Ideal.span {x} ≤ maximalIdeal S := by
    rw [Ideal.span_le]; simpa using hxm
  have hc : Ideal.comap π ⊥ = Ideal.span {x} := by
    rw [← RingHom.ker_eq_comap_bot]; exact hker
  have hm : maximalIdeal S = Ideal.span (G : Set S) ⊔ Ideal.span {x} := by
    have h1 : (maximalIdeal S).map π = (Ideal.span (G : Set S)).map π := hmap.trans hGmap.symm
    have e1 := Ideal.comap_map_of_surjective π hπs (maximalIdeal S)
    have e2 := Ideal.comap_map_of_surjective π hπs (Ideal.span (G : Set S))
    rw [h1, hc] at e1
    rw [hc] at e2
    rw [sup_eq_left.mpr hxle] at e1
    exact (e2.symm.trans e1).symm
  have hdimq : ringKrullDim (S ⧸ Ideal.span {x}) = (d : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := S ⧸ Ideal.span {x})).symm
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hx hxm
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← hdim, hdimq]
  have hle : (maximalIdeal S).spanFinrank ≤ d + 1 := by
    have hfin : ((G : Set S) ∪ {x}).Finite := G.finite_toSet.union (Set.finite_singleton x)
    have hspan : Ideal.span ((G : Set S) ∪ {x}) = maximalIdeal S := by
      rw [Ideal.span_union, hm]
    rw [← hspan]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite hfin).trans ?_
    calc ((G : Set S) ∪ {x}).ncard ≤ (G : Set S).ncard + ({x} : Set S).ncard :=
          Set.ncard_union_le _ _
      _ ≤ d + 1 := by
          rw [Set.ncard_singleton, Set.ncard_coe_finset]
          have : G.card ≤ T.card := Finset.card_image_le
          omega
  have : (((maximalIdeal S).spanFinrank : ℕ) : WithBot ℕ∞) ≤ (((d + 1 : ℕ)) : WithBot ℕ∞) := by
    exact_mod_cast hle
  simpa using this

section Global

/-- A non-zero-divisor stays a non-zero-divisor in every localization at a prime.
@isnad1 id=issmulre.1h3v.s8.c810d54f71a9 from=translated src=- shape=8846b677 vocab=afc1ba18
-/
theorem isSMulRegular_localization_of_mem_nonZeroDivisors {R : Type u} [CommRing R] {x : R}
    (hx : x ∈ nonZeroDivisors R) (Q : Ideal R) [Q.IsPrime] :
    IsSMulRegular (Localization.AtPrime Q) (algebraMap R (Localization.AtPrime Q) x) := by
  have key : ∀ c : Localization.AtPrime Q, algebraMap R _ x * c = 0 → c = 0 := by
    intro c hc
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq Q.primeCompl c
    rw [← IsLocalization.mk'_one (M := Q.primeCompl) (Localization.AtPrime Q) x,
      ← IsLocalization.mk'_mul, IsLocalization.mk'_eq_zero_iff] at hc
    obtain ⟨m, hm⟩ := hc
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨m, ?_⟩
    have h2 : (m.1 * a) * x = 0 := by rw [← hm]; ring
    exact (mem_nonZeroDivisors_iff.mp hx).2 _ h2
  intro a b hab
  have : algebraMap R _ x * (a - b) = 0 := by
    rw [mul_sub]; exact sub_eq_zero.mpr hab
  exact sub_eq_zero.mp (key _ this)

/-- `R_Q / I R_Q` is a localization of `R/I` at the image of `Q`, hence regular if `R/I` is.
@isnad1 id=isregula.1h3v.s9.df9e9aacff86 from=translated src=- shape=558053fd vocab=743b1c73
-/
theorem isRegularLocalRing_quotient_localization {R : Type u} [CommRing R] (I : Ideal R)
    (Q : Ideal R) [Q.IsPrime] (hIQ : I ≤ Q) [IsRegularRing (R ⧸ I)] :
    IsRegularLocalRing (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) := by
  classical
  haveI hQbar : (Q.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) Q.primeCompl)
      (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) := inferInstance
  have hsub : Algebra.algebraMapSubmonoid (R ⧸ I) Q.primeCompl =
      (Q.map (Ideal.Quotient.mk I)).primeCompl := by
    ext y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨b, hb, hab⟩ hmem
      rw [Ideal.Quotient.algebraMap_eq] at hab
      have h1 : Ideal.Quotient.mk I b ∈ Q.map (Ideal.Quotient.mk I) := by rw [hab]; exact hmem
      obtain ⟨c, hcQ, hc⟩ := (Ideal.mem_map_iff_of_surjective _
        Ideal.Quotient.mk_surjective).mp h1
      have h2 : b - c ∈ I := by rw [← Ideal.Quotient.eq]; exact hc.symm
      apply hb
      have : b = (b - c) + c := by ring
      rw [this]
      exact Q.add_mem (hIQ h2) hcQ
    · intro h
      exact ⟨a, fun ha => h (Ideal.mem_map_of_mem _ ha), by simp [Ideal.Quotient.algebraMap_eq]⟩
  rw [hsub] at hloc
  haveI : IsRegularLocalRing (Localization.AtPrime (Q.map (Ideal.Quotient.mk I))) :=
    IsRegularRing.isRegularLocalRing_localization _
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (Q.map (Ideal.Quotient.mk I)).primeCompl
      (Localization.AtPrime (Q.map (Ideal.Quotient.mk I)))
      (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q)))).toRingEquiv

/-- **Ascent, global form.**  `R` Noetherian, `x` a non-zero-divisor, `R/(x)` a regular ring, `Q`
a prime containing `x`: then `R_Q` is a regular local ring.
@isnad1 id=isregula.2h3v.s7.e6ab0b2f5805 from=translated src=- shape=780c1041 vocab=b493e261
-/
theorem isRegularLocalRing_localization_of_quotient_span_singleton {R : Type u} [CommRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ nonZeroDivisors R) (Q : Ideal R) [Q.IsPrime]
    (hxQ : x ∈ Q) [IsRegularRing (R ⧸ Ideal.span {x})] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  classical
  set S := Localization.AtPrime Q with hS
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing Q.primeCompl S inferInstance
  set I : Ideal R := Ideal.span {x} with hI
  have hIQ : I ≤ Q := by rw [hI, Ideal.span_le]; simpa using hxQ
  have hxm : algebraMap R S x ∈ maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hxQ
  have hmapI : Ideal.span {algebraMap R S x} = I.map (algebraMap R S) := by
    rw [hI, Ideal.map_span, Set.image_singleton]
  haveI : IsRegularLocalRing (S ⧸ Ideal.span {algebraMap R S x}) := by
    rw [hmapI]
    exact isRegularLocalRing_quotient_localization I Q hIQ
  exact isRegularLocalRing_of_quotient_span_singleton
    (isSMulRegular_localization_of_mem_nonZeroDivisors hx Q) hxm

end Global

section Loc

variable {A : Type u} {T : Type u} [CommRing A] [CommRing T] [Algebra A T]

/-- The stalk of `T` at `q'` is the stalk of `A` at the contraction of `q'`, when `T` is a
localization of `A`.-/
noncomputable def localizationAtPrimeEquivComap (M : Submonoid A) [IsLocalization M T]
    (q' : Ideal T) [q'.IsPrime] :
    Localization.AtPrime (q'.comap (algebraMap A T)) ≃+* Localization.AtPrime q' := by
  haveI : IsLocalization (q'.comap (algebraMap A T)).primeCompl (Localization.AtPrime q') :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q') q'
  exact (IsLocalization.algEquiv (q'.comap (algebraMap A T)).primeCompl
    (Localization.AtPrime (q'.comap (algebraMap A T))) (Localization.AtPrime q')).toRingEquiv

/-- Localizations of regular rings are regular.
@isnad1 id=isregula.0h3v.s5.b67af2e89ece from=translated src=- shape=7171065f vocab=e71ed8b6
-/
theorem isRegularRing_of_isLocalization (M : Submonoid A) [IsLocalization M T]
    [IsRegularRing A] : IsRegularRing T := by
  haveI : IsNoetherianRing T := IsLocalization.isNoetherianRing M T inferInstance
  refine ⟨fun q' _ => ?_⟩
  exact IsRegularLocalRing.of_ringEquiv (localizationAtPrimeEquivComap M q')

/-- A prime of `A` missing `M` has regular stalk when the localization `T` of `A` at `M`
is regular.
@isnad1 id=isregula.1h4v.s7.b2db082e8014 from=translated src=- shape=c74d3496 vocab=5b55ee93
-/
theorem isRegularLocalRing_of_isLocalization (M : Submonoid A) [IsLocalization M T]
    [IsRegularRing T] (q : Ideal A) [q.IsPrime] (hq : Disjoint (M : Set A) q) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  haveI hq' : (q.map (algebraMap A T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M T q inferInstance hq
  have hc : (q.map (algebraMap A T)).comap (algebraMap A T) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M T inferInstance hq
  haveI : IsRegularLocalRing (Localization.AtPrime (q.map (algebraMap A T))) :=
    IsRegularRing.isRegularLocalRing_localization _
  have key : ∀ (p : Ideal A) [p.IsPrime],
      p = (q.map (algebraMap A T)).comap (algebraMap A T) →
        IsRegularLocalRing (Localization.AtPrime p) := by
    rintro p hp rfl
    exact IsRegularLocalRing.of_ringEquiv
      (localizationAtPrimeEquivComap M (q.map (algebraMap A T))).symm
  exact key q hc.symm

end Loc

section Weak

open RingTheory.Sequence

variable {R : Type u} [CommRing R]

/-- A common element outside the prime `P` witnessing a family of elementwise conditions that
are stable under multiplication.
@isnad1 id=ex.1h6v.s7.a49ee62730df from=translated src=- shape=45176953 vocab=e66de268
-/
theorem exists_common_unit {ι : Type*} (P : Ideal R) [P.IsPrime] (s : Finset ι)
    (Q : ι → R → Prop) (hQ : ∀ i u v, Q i u → Q i (u * v))
    (h : ∀ i ∈ s, ∃ u ∉ P, Q i u) : ∃ u ∉ P, ∀ i ∈ s, Q i u := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, P.primeCompl.one_mem, by simp⟩
  | insert a s ha ih =>
    obtain ⟨u1, hu1, hQ1⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨u2, hu2, hQ2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨u1 * u2, fun hm => ?_, ?_⟩
    · rcases (Ideal.IsPrime.mul_mem_iff_mem_or_mem inferInstance).mp hm with h1 | h1
      exacts [hu1 h1, hu2 h1]
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hQ _ _ _ hQ1
      · rw [mul_comm]; exact hQ _ _ _ (hQ2 i hi)

/-- **Local regularity of the sequence entries.**  Let `ys` be a weakly regular sequence in a
Noetherian ring, contained in a prime `P`.  Then there is `u ∉ P` such that every `y ∈ ys` is a
non-zero-divisor after inverting `u` (precisely: `u` kills the annihilator of every `y`).
@isnad1 id=ex.2h3v.s10.beace717207a from=translated src=- shape=e552b4be vocab=984216b1
-/
theorem exists_unit_killing_ann [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] (ys : List R)
    (hA : IsWeaklyRegular (Localization.AtPrime P) (ys.map (algebraMap R (Localization.AtPrime P))))
    (hmax : ∀ y ∈ ys, algebraMap R (Localization.AtPrime P) y ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    ∃ u ∉ P, ∀ y ∈ ys, ∀ x : R, y * x = 0 → u * x = 0 := by
  classical
  set A := Localization.AtPrime P
  have hreg : ∀ y ∈ ys, IsSMulRegular A (algebraMap R A y) := by
    intro y hy
    have hperm : List.Perm (ys.map (algebraMap R A))
        ((y :: ys.erase y).map (algebraMap R A)) :=
      (List.perm_cons_erase hy).map _
    have h2 := IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hA hperm (by
      intro r hr
      obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hr
      exact hmax y' hy')
    simp only [List.map_cons] at h2
    exact (isWeaklyRegular_cons_iff _ _ _ |>.mp h2).1
  have key : ∀ y ∈ ys, ∃ u ∉ P, ∀ x : R, y * x = 0 → u * x = 0 := by
    intro y hy
    set I : Ideal R := LinearMap.ker (LinearMap.mulLeft R y) with hI
    obtain ⟨G, hG⟩ := IsNoetherian.noetherian I
    have hloc : ∀ g ∈ G, ∃ u ∉ P, u * g = 0 := by
      intro g hg
      have hgI : g ∈ I := hG ▸ Submodule.subset_span hg
      have hg0 : y * g = 0 := hgI
      have : algebraMap R A g = 0 := by
        have h0 : algebraMap R A y * algebraMap R A g = 0 := by rw [← map_mul, hg0, map_zero]
        exact hreg y hy (a₁ := algebraMap R A g) (a₂ := 0) (by simp [smul_eq_mul, h0])
      obtain ⟨⟨u, hu⟩, hu0⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl A g).mp this
      exact ⟨u, hu, hu0⟩
    obtain ⟨u, hu, hk⟩ := exists_common_unit P G (fun g u => u * g = 0)
      (fun g u v h => by rw [mul_assoc, mul_comm v, ← mul_assoc, h, zero_mul]) hloc
    have hspan : ∀ x ∈ Submodule.span R (G : Set R), u * x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem g hg => exact hk g hg
      | zero => simp
      | add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]
      | smul c a _ ha => rw [smul_eq_mul, mul_left_comm, ha, mul_zero]
    refine ⟨u, hu, fun x hx => hspan x ?_⟩
    rw [hG]
    exact hx
  obtain ⟨u, hu, hall⟩ := exists_common_unit P ys.toFinset
    (fun y u => ∀ x : R, y * x = 0 → u * x = 0)
    (fun y u v h x hx => by rw [mul_assoc, mul_comm v, ← mul_assoc, h x hx, zero_mul])
    (fun y hy => key y (List.mem_toFinset.mp hy))
  exact ⟨u, hu, fun y hy => hall y (List.mem_toFinset.mpr hy)⟩

end Weak

section MvPoly

/-- Polynomial rings in finitely many variables over a regular ring are regular.
@isnad1 id=isregula.0h2v.s5.5ae1ae8bc647 from=translated src=- shape=65f277ad vocab=86aa29ff
-/
theorem isRegularRing_mvPolynomial_fin_of_regular (R : Type u) [CommRing R] [IsRegularRing R]
    (n : ℕ) : IsRegularRing (MvPolynomial (Fin n) R) := by
  induction n with
  | zero => exact IsRegularRing.of_ringEquiv (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm
  | succ n ih =>
    haveI := ih
    haveI : IsRegularRing (Polynomial (MvPolynomial (Fin n) R)) :=
      SchemeKTheory.F14.isRegularRing_polynomial _
    exact IsRegularRing.of_ringEquiv (MvPolynomial.finSuccEquiv R n).toRingEquiv.symm

/--
@isnad1 id=isregula.0h2v.s5.f35c3c73caae from=translated src=- shape=3e551672 vocab=4383a8c8
-/
theorem isRegularRing_mvPolynomial_of_regular (R : Type u) [CommRing R] [IsRegularRing R]
    (σ : Type) [Finite σ] : IsRegularRing (MvPolynomial σ R) := by
  haveI := isRegularRing_mvPolynomial_fin_of_regular R (Nat.card σ)
  exact IsRegularRing.of_ringEquiv
    (MvPolynomial.renameEquiv R (Finite.equivFin σ).symm).toRingEquiv

end MvPoly

end BlowupRegularAR12

end
