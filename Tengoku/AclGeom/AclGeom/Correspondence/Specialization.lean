/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Tengoku.Seed.RingTheory.Spectrum.Prime.Chevalley
import Tengoku.Seed.RingTheory.Jacobson.Ring
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.Algebra.Polynomial.Roots
import Tengoku.Seed.Algebra.MvPolynomial.Equiv
import Tengoku.Seed.RingTheory.Algebraic.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coherent specialization of finite polynomial relations

A finite-type domain over an algebraically closed field admits a specialization
that sends one transcendental parameter into a given infinite subfield.
Chevalley's theorem supplies an open set of admissible values, and the finite
root theorem excludes the values that annihilate the prescribed incidence
polynomials. One algebra homomorphism preserves all relations simultaneously.

`exists_multiplier_descent` consumes this result to descend the simultaneous
multiplication-corner normalization to the original base.
-/

namespace AclGeom

open Polynomial PrimeSpectrum

/-- An injective finitely presented map of domains has a principal open
subset of its spectrum image. Used to choose a specializable parameter.-/
private theorem exists_basicOpen_in_comap_range
    {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (f : A →+* B) (hf : Function.Injective f) (hfp : f.FinitePresentation) :
    ∃ g : A, g ≠ 0 ∧ ∀ p : PrimeSpectrum A,
      g ∉ p.asIdeal → p ∈ Set.range (PrimeSpectrum.comap f) := by
  classical
  let z : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  have hz : z ∈ Set.range (PrimeSpectrum.comap f) := by
    refine ⟨⟨⊥, inferInstance⟩, ?_⟩
    apply PrimeSpectrum.ext
    exact ((RingHom.injective_iff_ker_eq_bot f).mp hf)
  obtain ⟨S, hS⟩ := exists_constructibleSetData_iff.mpr
    (isConstructible_range_comap hfp)
  rw [← hS] at hz
  obtain ⟨C, hC, hzC⟩ := Set.mem_iUnion₂.mp hz
  have hg : ∀ i, C.g i = 0 := by
    intro i
    exact Ideal.mem_bot.mp ((mem_zeroLocus z _).mp hzC.1 ⟨i, rfl⟩)
  have hfn : C.f ≠ 0 := by
    intro he
    apply hzC.2
    rw [mem_zeroLocus, Set.singleton_subset_iff]
    change C.f ∈ (⊥ : Ideal A)
    simp [he]
  refine ⟨C.f, hfn, fun p hp ↦ ?_⟩
  rw [← hS]
  apply Set.mem_iUnion₂.mpr ⟨C, hC, ?_⟩
  constructor
  · rw [mem_zeroLocus]
    rintro _ ⟨i, rfl⟩
    rw [hg]
    exact p.asIdeal.zero_mem
  · simpa only [mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe] using hp

/-- A nonzero polynomial cannot vanish on an infinite subfield.-/
private theorem exists_subfield_eval_ne_zero
    {k F : Type*} [Field k] [Infinite k] [Field F] [Algebra k F]
    (p : F[X]) (hp : p ≠ 0) : ∃ c : k, p.eval (algebraMap k F c) ≠ 0 := by
  classical
  by_contra! h
  exact (Set.infinite_of_injective_forall_mem (algebraMap k F).injective h)
    (Polynomial.finite_setOfPred_isRoot hp)

/-- A prime above an evaluation point in a finite-type algebra supplies
an actual point over an algebraically closed base.-/
private theorem exists_algHom_of_evaluation_in_comap_range
    {F R : Type*} [Field F] [IsAlgClosed F] [CommRing R] [Algebra F R]
    [Algebra.FiniteType F R] (f : F[X] →ₐ[F] R) (c : F)
    (hc : PrimeSpectrum.comap (Polynomial.evalRingHom c)
      ⟨⊥, inferInstance⟩ ∈ Set.range (PrimeSpectrum.comap f.toRingHom)) :
    ∃ φ : R →ₐ[F] F, φ (f X) = c := by
  classical
  obtain ⟨Q, hQ⟩ := hc
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q.asIdeal Q.isPrime.ne_top
  let : M.IsMaximal := hM
  let : Field (R ⧸ M) := Ideal.Quotient.field M
  let : Module.Finite F (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing F (R ⧸ M)
  let φ : R →ₐ[F] F := (IsAlgClosed.lift : (R ⧸ M) →ₐ[F] F).comp
    (Ideal.Quotient.mkₐ F M)
  have hmem : f (X - C c) ∈ Q.asIdeal := by
    change X - C c ∈ (PrimeSpectrum.comap f.toRingHom Q).asIdeal
    rw [hQ]
    change (X - C c).eval c ∈ (⊥ : Ideal F)
    simp
  have hz : φ (f (X - C c)) = 0 := by
    change IsAlgClosed.lift (Ideal.Quotient.mk M (f (X - C c))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hQM hmem), map_zero]
  refine ⟨φ, ?_⟩
  have hfc : f (C c) = algebraMap F R c := f.commutes c
  rw [map_sub, map_sub, hfc, φ.commutes, Algebra.algebraMap_self_apply] at hz
  exact sub_eq_zero.mp hz

/-- Coherent specialization of a finite-type domain to an algebraically
closed base can send a transcendental parameter into any infinite subfield.
The geometric consumer descends a common multiplier and all of its
finite polynomial incidence relations by this one algebra homomorphism.-/
private theorem exists_algHom_specializing_into_subfield
    {k F R : Type*} [Field k] [Infinite k] [Field F] [IsAlgClosed F]
    [Algebra k F] [CommRing R] [IsDomain R] [Algebra F R]
    [Algebra.FiniteType F R] (f : F[X] →ₐ[F] R) (hf : Function.Injective f) :
    ∃ (c : k) (φ : R →ₐ[F] F), φ (f X) = algebraMap k F c := by
  have hft : f.toRingHom.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap F F[X])
    have hcomp : f.toRingHom.comp (algebraMap F F[X]) = algebraMap F R := by
      ext c
      exact f.commutes c
    rw [hcomp]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨g, hg, hrange⟩ := exists_basicOpen_in_comap_range f.toRingHom hf
    (RingHom.FinitePresentation.of_finiteType.mp hft)
  obtain ⟨c, hc⟩ := exists_subfield_eval_ne_zero (k := k) g hg
  have hm : PrimeSpectrum.comap (Polynomial.evalRingHom (algebraMap k F c))
      ⟨⊥, inferInstance⟩ ∈ Set.range (PrimeSpectrum.comap f.toRingHom) := by
    apply hrange
    change g.eval (algebraMap k F c) ∉ (⊥ : Ideal F)
    simpa only [Ideal.mem_bot] using hc
  obtain ⟨φ, hφ⟩ := exists_algHom_of_evaluation_in_comap_range f _ hm
  exact ⟨c, φ, hφ⟩

/-- A nonzero multivariable polynomial becomes zero after specializing its
first variable at only finitely many base-field values.-/
private theorem finite_zero_specializations {k : Type*} [Field k] {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) k) (hP : P ≠ 0) :
    Set.Finite {c : k | (MvPolynomial.finSuccEquiv k n P).eval (MvPolynomial.C c) = 0} := by
  have hp : MvPolynomial.finSuccEquiv k n P ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv k n).injective).mpr hP
  exact Set.Finite.preimage (MvPolynomial.C_injective (σ := Fin n) (R := k)).injOn
    (Polynomial.finite_setOfPred_isRoot hp)

/-- A transcendental parameter in an ambient field can be specialized to a
base-field value outside any finite forbidden set, while one homomorphism
simultaneously specializes any prescribed finite set of ambient elements.-/
private theorem exists_finite_specialization
    {k F K : Type*} [Field k] [Infinite k] [Field F] [IsAlgClosed F]
    [Field K] [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K]
    {t : K} (ht : Transcendental F t) (s : Finset K) (bad : Finset k) :
    ∃ (R : Subalgebra F K) (htR : t ∈ R), (↑s : Set K) ⊆ R ∧
      ∃ (c : k) (φ : R →ₐ[F] F), c ∉ bad ∧ φ ⟨t, htR⟩ = algebraMap k F c := by
  classical
  let d : K := ∏ c ∈ bad, (t - algebraMap k K c)
  have hd : d ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro c _
    apply sub_ne_zero.mpr
    intro he
    apply ht
    rw [he, IsScalarTower.algebraMap_apply k F K]
    exact isAlgebraic_algebraMap (algebraMap k F c)
  let R := Algebra.adjoin F (↑(insert t (insert d⁻¹ s)) : Set K)
  have htR : t ∈ R := Algebra.subset_adjoin (by simp)
  have hsR : (↑s : Set K) ⊆ R := by
    intro z hz
    exact Algebra.subset_adjoin (by simp [hz])
  have hiR : d⁻¹ ∈ R := Algebra.subset_adjoin (by simp)
  let : Algebra.FiniteType F R := Algebra.FiniteType.adjoin_of_finite (Finset.finite_toSet _)
  let tR : R := ⟨t, htR⟩
  have htr : Transcendental F tR := by
    intro h
    exact ht (by simpa only [tR, Subalgebra.val_apply] using h.isIntegral.map R.val |>.isAlgebraic)
  obtain ⟨c, φ, hφ⟩ := exists_algHom_specializing_into_subfield (k := k)
    (Polynomial.aeval tR) (transcendental_iff_injective.mp htr)
  have hφt : φ tR = algebraMap k F c := by simpa only [Polynomial.aeval_X] using hφ
  refine ⟨R, htR, hsR, c, φ, ?_, hφt⟩
  intro hc
  let dR : R := ∏ b ∈ bad, (tR - algebraMap F R (algebraMap k F b))
  have hdR : (dR : K) = d := by
    simp [dR, d, tR, ← IsScalarTower.algebraMap_apply k F K]
  have hunit : dR * (⟨d⁻¹, hiR⟩ : R) = 1 := by
    apply Subtype.ext
    change (dR : K) * d⁻¹ = 1
    rw [hdR, mul_inv_cancel₀ hd]
  have hz : φ dR = 0 := by
    simp only [dR, map_prod, map_sub, φ.commutes, hφt, Algebra.algebraMap_self_apply]
    apply Finset.prod_eq_zero hc
    exact sub_self _
  have hh := congrArg φ hunit
  rw [map_mul, hz, zero_mul, map_one] at hh
  exact zero_ne_one hh

/-- Evaluation commutes with specializing the first variable at a base-field
value. The finite-specialization consumer applies this to every corner relation.
@isnad1 id=eq.0h6v.s10.62f1c34f1d09 from=translated src=- shape=7cbd476b vocab=766da2a1
-/
theorem aeval_specialize_first {k K : Type*} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) k) (c : k) (v : Fin n → K) :
    MvPolynomial.aeval v ((MvPolynomial.finSuccEquiv k n P).eval (MvPolynomial.C c)) =
      MvPolynomial.aeval (Fin.cons (algebraMap k K c) v) P := by
  have heq : (MvPolynomial.aeval v).toRingHom.comp
      ((Polynomial.evalRingHom (MvPolynomial.C c)).comp
        (MvPolynomial.finSuccEquiv k n).toRingEquiv.toRingHom) =
      (MvPolynomial.aeval (Fin.cons (algebraMap k K c) v)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [MvPolynomial.finSuccEquiv_X_zero]
      · simp [MvPolynomial.finSuccEquiv_X_succ]
  exact congrArg (fun f : MvPolynomial (Fin (n + 1)) k →+* K ↦ f P) heq

/-- Coherent specialization preserving finitely many nonzero incidence
polynomials in their remaining variables.
@isnad1 id=ex.2h7v.s11.a62ed1eec368 from=translated src=- shape=5bc95fbd vocab=69475d2c
-/
theorem exists_finite_specialization_preserving_polynomials
    {k F K : Type*} [Field k] [Infinite k] [Field F] [IsAlgClosed F]
    [Field K] [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K]
    {t : K} (ht : Transcendental F t) (s : Finset K) {n : ℕ}
    (ps : Finset (MvPolynomial (Fin (n + 1)) k)) (hps : ∀ P ∈ ps, P ≠ 0) :
    ∃ (R : Subalgebra F K) (htR : t ∈ R), (↑s : Set K) ⊆ R ∧
      ∃ (c : k) (φ : R →ₐ[F] F), φ ⟨t, htR⟩ = algebraMap k F c ∧
        ∀ P ∈ ps, (MvPolynomial.finSuccEquiv k n P).eval (MvPolynomial.C c) ≠ 0 := by
  classical
  let bad := ⋃ P ∈ (↑ps : Set (MvPolynomial (Fin (n + 1)) k)),
    {c : k | (MvPolynomial.finSuccEquiv k n P).eval (MvPolynomial.C c) = 0}
  have hbad : bad.Finite := ps.finite_toSet.biUnion
    (fun P hP ↦ finite_zero_specializations P (hps P hP))
  obtain ⟨R, htR, hsR, c, φ, hc, hφ⟩ := exists_finite_specialization ht s hbad.toFinset
  refine ⟨R, htR, hsR, c, φ, hφ, fun P hP hzero ↦ hc ?_⟩
  apply hbad.mem_toFinset.mpr
  exact Set.mem_iUnion₂.mpr ⟨P, hP, hzero⟩

end AclGeom
