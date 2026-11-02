/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.RegularLocalRing.Defs
import Tengoku.Seed.RingTheory.KrullDimension.Polynomial
import Tengoku.Seed.RingTheory.Localization.Algebra
import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Polynomial
import Tengoku.Seed.RingTheory.Ideal.Height

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial rings over regular rings are regular (route F14)

If `R` is a regular ring (Noetherian with regular local localizations) then so is `R[X]`
(`IsRegularRing` of `Polynomial`), and hence of `MvPolynomial` over a field.  This supplies the
regularity of the stalks of `ℙⁿ_k`.
-/

open Polynomial IsLocalRing

universe u

noncomputable section

namespace SchemeKTheory.F14

section Core

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- **Core step.**  Let `A` be a regular local ring and `P` a prime of `A[X]` lying over the maximal
ideal of `A`.  Then `A[X]_P` is regular local.-/
theorem isRegularLocalRing_localization_polynomial_of_comap (P : Ideal A[X]) [P.IsPrime]
    (hP : P.comap C = maximalIdeal A) : IsRegularLocalRing (Localization.AtPrime P) := by
  classical
  set m := maximalIdeal A with hm
  haveI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  obtain ⟨G, hGcard, hGspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (m.fg_of_isNoetherianRing)
  set d := m.spanFinrank with hd
  have hmd : m.height = (d : ℕ∞) := by
    have h1 := (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A))
    have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [← h2] at h1
    exact_mod_cast h1
  let ψ : A[X] →+* (ResidueField A)[X] := Polynomial.mapRingHom (residue A)
  have hψs : Function.Surjective ψ := Polynomial.map_surjective _ (residue_surjective)
  have hψk : RingHom.ker ψ = m.map C := by
    rw [Polynomial.ker_mapRingHom, ker_residue]
  have hmP : m.map C ≤ P := by
    rw [← hP]; exact Ideal.map_comap_le
  haveI : (P.map ψ).IsPrime := Ideal.map_isPrime_of_surjective hψs (by rw [hψk]; exact hmP)
  set fb := Submodule.IsPrincipal.generator (P.map ψ) with hfb
  have hfbmem : fb ∈ P.map ψ := Submodule.IsPrincipal.generator_mem _
  obtain ⟨f, hfP, hfψ⟩ := (Ideal.mem_map_iff_of_surjective ψ hψs).mp hfbmem
  have hPeq : P = m.map C ⊔ Ideal.span {f} := by
    apply le_antisymm
    · intro x hx
      have hxψ : ψ x ∈ P.map ψ := Ideal.mem_map_of_mem ψ hx
      rw [← Submodule.IsPrincipal.span_singleton_generator (P.map ψ), Ideal.mem_span_singleton']
        at hxψ
      obtain ⟨a, ha⟩ := hxψ
      obtain ⟨g, rfl⟩ := hψs a
      have hk : x - g * f ∈ RingHom.ker ψ := by
        rw [RingHom.mem_ker, map_sub, map_mul, hfψ]
        exact sub_eq_zero.mpr ha.symm
      rw [hψk] at hk
      have : x = (x - g * f) + g * f := by ring
      rw [this]
      exact add_mem (Ideal.mem_sup_left hk)
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)))
    · exact sup_le hmP (Ideal.span_le.mpr (by simpa using hfP))
  have hmG : m = Ideal.span (G : Set A) := hGspan.symm
  have hmapC : m.map C = Ideal.span (C '' (G : Set A)) := by
    rw [hmG, Ideal.map_span]
  have hCG : (C '' (G : Set A)).Finite := G.finite_toSet.image _
  have hCGcard : (C '' (G : Set A)).ncard ≤ d := by
    calc (C '' (G : Set A)).ncard ≤ (G : Set A).ncard := Set.ncard_image_le G.finite_toSet
      _ = d := by rw [Set.ncard_coe_finset, hGcard]
  have hmPrime : (m.map C).IsPrime := inferInstance
  have hht : (m.map C).height = (d : ℕ∞) := by
    rw [Polynomial.height_map_C m, hmd]
  obtain ⟨T, hTfin, hTspan, hTle⟩ : ∃ T : Set A[X], T.Finite ∧ Ideal.span T = P ∧
      ((T.ncard : ℕ) : ℕ∞) ≤ P.height := by
    by_cases hf : f ∈ m.map C
    · have hPm : P = m.map C := by
        rw [hPeq]; exact sup_eq_left.mpr (Ideal.span_le.mpr (by simpa using hf))
      refine ⟨C '' (G : Set A), hCG, by rw [← hmapC, hPm], ?_⟩
      rw [hPm, hht]
      exact_mod_cast hCGcard
    · have hlt : m.map C < P := lt_of_le_of_ne hmP fun h => hf (h ▸ hfP)
      have hlt' := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
      rw [hht] at hlt'
      have hle1 : (d : ℕ∞) + 1 ≤ P.height := (ENat.add_one_le_iff (by simp)).mpr hlt'
      refine ⟨C '' (G : Set A) ∪ {f}, hCG.union (Set.finite_singleton f), ?_, ?_⟩
      · rw [Ideal.span_union, ← hmapC, ← hPeq]
      · refine le_trans ?_ hle1
        have : (C '' (G : Set A) ∪ {f}).ncard ≤ (C '' (G : Set A)).ncard + 1 := by
          calc (C '' (G : Set A) ∪ {f}).ncard ≤ (C '' (G : Set A)).ncard + ({f} : Set A[X]).ncard :=
                Set.ncard_union_le _ _
            _ = (C '' (G : Set A)).ncard + 1 := by rw [Set.ncard_singleton]
        have h2 : (C '' (G : Set A) ∪ {f}).ncard ≤ d + 1 := this.trans (by omega)
        exact_mod_cast h2
  have hB : maximalIdeal (Localization.AtPrime P) = Ideal.map (algebraMap A[X] _) P :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hspan : (maximalIdeal (Localization.AtPrime P)).spanFinrank ≤ T.ncard := by
    have hmapT := Ideal.map_span (algebraMap A[X] (Localization.AtPrime P)) T
    rw [hTspan] at hmapT
    rw [hB, hmapT]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (hTfin.image _)).trans
      (Set.ncard_image_le hTfin)
  have hdim : ringKrullDim (Localization.AtPrime P) = (P.height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height P _
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [hdim]
  have : ((maximalIdeal (Localization.AtPrime P)).spanFinrank : ℕ∞) ≤ P.height :=
    le_trans (by exact_mod_cast hspan) hTle
  exact_mod_cast this

end Core

section Reduction

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
/-- **Polynomial rings over regular rings are regular** (localizations at primes).-/
theorem isRegularLocalRing_localization_polynomial {R : Type u} [CommRing R] [IsRegularRing R]
    (P : Ideal R[X]) [P.IsPrime] : IsRegularLocalRing (Localization.AtPrime P) := by
  classical
  set Q : Ideal R := P.comap C with hQ
  haveI : Q.IsPrime := inferInstance
  haveI hA : IsRegularLocalRing (Localization.AtPrime Q) := inferInstance
  haveI : IsLocalization (Q.primeCompl.map C) (Localization.AtPrime Q)[X] :=
    Polynomial.isLocalization Q.primeCompl (Localization.AtPrime Q)
  have disj : Disjoint ((Q.primeCompl.map C : Submonoid R[X]) : Set R[X]) P := by
    refine Set.disjoint_left.mpr fun a ⟨b, hb⟩ ha => hb.1 ?_
    rw [← hb.2] at ha
    exact ha
  set P' : Ideal (Localization.AtPrime Q)[X] :=
    P.map (algebraMap R[X] (Localization.AtPrime Q)[X]) with hP'
  haveI hP'prime : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Q.primeCompl.map C) _ P inferInstance disj
  have hcomapP : P'.comap (algebraMap R[X] (Localization.AtPrime Q)[X]) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (Q.primeCompl.map C) _ inferInstance disj
  have hcomapC : P'.comap (C : Localization.AtPrime Q →+* (Localization.AtPrime Q)[X]) =
      maximalIdeal (Localization.AtPrime Q) := by
    have h1 : (P'.comap (C : Localization.AtPrime Q →+* (Localization.AtPrime Q)[X])).comap
        (algebraMap R (Localization.AtPrime Q)) = Q := by
      rw [Ideal.comap_comap]
      have : (C : Localization.AtPrime Q →+* (Localization.AtPrime Q)[X]).comp
          (algebraMap R (Localization.AtPrime Q)) =
          (algebraMap R[X] (Localization.AtPrime Q)[X]).comp C := by
        ext r
        simp
      rw [this, ← Ideal.comap_comap, hcomapP]
    have := IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q)
      (P'.comap (C : Localization.AtPrime Q →+* (Localization.AtPrime Q)[X]))
    have h1' : Ideal.under R (P'.comap (C : Localization.AtPrime Q →+*
        (Localization.AtPrime Q)[X])) = Q := h1
    rw [h1'] at this
    rw [← this, Localization.AtPrime.map_eq_maximalIdeal]
  haveI := isRegularLocalRing_localization_polynomial_of_comap P' hcomapC
  haveI hloc : IsLocalization.AtPrime (Localization.AtPrime P') P := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (R := R[X]) (Q.primeCompl.map C) (Localization.AtPrime P') P'
    have this' : IsLocalization
        (P'.comap (algebraMap R[X] (Localization.AtPrime Q)[X])).primeCompl
        (Localization.AtPrime P') := this
    have hsub : (P'.comap (algebraMap R[X] (Localization.AtPrime Q)[X])).primeCompl =
        P.primeCompl := by
      ext x
      simp only [Ideal.mem_primeCompl_iff]
      rw [hcomapP]
    rw [hsub] at this'
    exact this'
  let e : Localization.AtPrime P' ≃+* Localization.AtPrime P :=
    (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
      (Localization.AtPrime P')).symm.toRingEquiv
  exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime P')
    (R' := Localization.AtPrime P) e

end Reduction

section Instances

/-- **`R[X]` is a regular ring when `R` is.**-/
instance isRegularRing_polynomial (R : Type u) [CommRing R] [IsRegularRing R] :
    IsRegularRing R[X] :=
  ⟨fun P _ => isRegularLocalRing_localization_polynomial P⟩

/-- A field is a regular ring.-/
instance isRegularRing_of_field (k : Type u) [Field k] : IsRegularRing k := inferInstance

/-- Multivariate polynomial rings over a field in finitely many variables are regular.-/
theorem isRegularRing_mvPolynomial_fin (k : Type u) [Field k] (n : ℕ) :
    IsRegularRing (MvPolynomial (Fin n) k) := by
  induction n with
  | zero =>
    exact IsRegularRing.of_ringEquiv (MvPolynomial.isEmptyRingEquiv k (Fin 0)).symm
  | succ n ih =>
    haveI := ih
    exact IsRegularRing.of_ringEquiv (MvPolynomial.finSuccEquiv k n).toRingEquiv.symm

theorem isRegularRing_mvPolynomial (k : Type u) [Field k] (σ : Type*) [Finite σ] :
    IsRegularRing (MvPolynomial σ k) := by
  haveI := isRegularRing_mvPolynomial_fin k (Nat.card σ)
  exact IsRegularRing.of_ringEquiv (MvPolynomial.renameEquiv k (Finite.equivFin σ).symm).toRingEquiv

end Instances

end SchemeKTheory.F14

end
