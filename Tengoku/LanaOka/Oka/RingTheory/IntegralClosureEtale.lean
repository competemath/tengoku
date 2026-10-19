/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.RingTheory.Smooth.IntegralClosure
import Tengoku.Seed.RingTheory.Etale.Field
import Tengoku.Seed.RingTheory.IntegralClosure.GoingDown
import Tengoku.Seed.RingTheory.Localization.BaseChange
import Tengoku.Seed.RingTheory.Flat.TorsionFree
import Tengoku.LanaOka.Oka.RingTheory.FiniteNormalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integral closure in étale algebras

Let `A` be a noetherian finite product of normal domains, `a ∈ A` a nonzerodivisor and `C` a finite
étale algebra over `Aₐ`. The integral closure of `A` in `C` is finite over `A`, a finite product
of normal domains, and satisfies going down over `A`
(`finite_isFiniteProductOfNormalDomains_hasGoingDown_integralClosure`). Writing `A ≃ ∏ Dᵢ`, it is
the product of the integral closures of `Dᵢ` in the finite étale `Frac Dᵢ`-algebras
`Frac Dᵢ ⊗[Aₐ] C`, which are products of finite separable field extensions of `Frac Dᵢ`
(`finite_isFiniteProductOfNormalDomains_hasGoingDown_of_fractionRing`). That `C` contains all
elements of `Frac Dᵢ ⊗[Aₐ] C` integral over `A` is smooth base change of integral closure
(`TensorProduct.toIntegralClosure_bijective_of_smooth`).

Locally: an étale algebra `S` over a normal domain `R` embeds into its localization at a nonzero
`r ∈ R` (`injective_algebraMap_away_of_etale`), and every element of that localization integral
over `R` lies in `S` (`exists_algebraMap_eq_of_isIntegral_of_etale`).

## Main results

- `finite_isFiniteProductOfNormalDomains_hasGoingDown_integralClosure`
- `injective_algebraMap_away_of_etale`, `exists_algebraMap_eq_of_isIntegral_of_etale`
- `subsingleton_or_isDomain_of_isLocalization_single`: localizations of `A ≃ ∏ Dᵢ` at elements
  supported on one factor are zero or normal domains.
- `exists_mem_nonZeroDivisors_of_forall_not_le`: prime avoidance for nonzerodivisors.
-/

open scoped nonZeroDivisors TensorProduct

universe u

/-- An algebra over a subsingleton ring is a subsingleton. -/
lemma subsingleton_of_algebra_of_subsingleton (R S : Type*) [CommRing R] [Semiring S]
    [Algebra R S] [Subsingleton R] : Subsingleton S :=
  subsingleton_of_zero_eq_one (by
    rw [← map_zero (algebraMap R S), ← map_one (algebraMap R S), Subsingleton.elim (0 : R) 1])

section Local

variable {R S Sᵣ : Type*} [CommRing R] [CommRing S] [CommRing Sᵣ] [Algebra R S]
  [Algebra S Sᵣ]

/-- Localizing an étale algebra over a normal domain at a nonzero element of the base is
injective. -/
theorem injective_algebraMap_away_of_etale [Algebra.Etale R S] {r : R}
    (hR : Subsingleton R ∨ (IsDomain R ∧ IsIntegrallyClosed R ∧ r ≠ 0))
    [IsLocalization.Away (algebraMap R S r) Sᵣ] : Function.Injective (algebraMap S Sᵣ) := by
  rcases hR with hR | ⟨_, _, hr⟩
  · haveI := subsingleton_of_algebra_of_subsingleton R S
    exact fun _ _ _ ↦ Subsingleton.elim _ _
  · refine IsLocalization.injective Sᵣ (M := Submonoid.powers (algebraMap R S r)) ?_
    rintro _ ⟨n, rfl⟩
    change algebraMap R S r ^ n ∈ S⁰
    rw [← map_pow]
    have hreg : IsSMulRegular S (r ^ n) :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (pow_mem (mem_nonZeroDivisors_of_ne_zero hr) n)
    refine mem_nonZeroDivisors_iff_right.mpr fun x hx ↦ hreg ?_
    change (r ^ n) • x = (r ^ n) • (0 : S)
    rw [smul_zero, Algebra.smul_def, mul_comm]
    exact hx

end Local

section SmoothBaseChange

variable {R S B : Type*} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]

/-- If every element of `B` integral over `R` comes from `R`, then after a smooth base change
`R → S` every element of `S ⊗[R] B` integral over `S` comes from `S`. -/
theorem exists_algebraMap_eq_of_isIntegral_tensor [Algebra.Smooth R S]
    (hB : ∀ b : B, IsIntegral R b → ∃ r : R, algebraMap R B r = b) (y : S ⊗[R] B)
    (hy : IsIntegral S y) : ∃ s : S, algebraMap S (S ⊗[R] B) s = y := by
  obtain ⟨t, ht⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S)
    (B := B)).2 ⟨y, hy⟩
  have hy' : y = Algebra.TensorProduct.map (AlgHom.id S S) (integralClosure R B).val t :=
    (congrArg Subtype.val ht).symm
  rw [hy']
  clear ht hy'
  induction t with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  | tmul s b =>
    obtain ⟨r, hr⟩ := hB b.1 b.2
    refine ⟨algebraMap R S r * s, ?_⟩
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Subalgebra.coe_val, ← hr,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.algebraMap_eq_smul_one (A := B) r, ← TensorProduct.smul_tmul, Algebra.smul_def]

end SmoothBaseChange

section Local

variable {R S Sᵣ : Type*} [CommRing R] [CommRing S] [CommRing Sᵣ] [Algebra R S]
  [Algebra S Sᵣ]

/-- In a localization `Rᵣ` of a normal domain at a nonzero element, the elements integral over
`R` come from `R`. -/
theorem exists_algebraMap_eq_of_isIntegral_away [IsDomain R] [IsIntegrallyClosed R] {r : R}
    (hr : r ≠ 0) {Rᵣ : Type*} [CommRing Rᵣ] [Algebra R Rᵣ] [IsLocalization.Away r Rᵣ] (b : Rᵣ)
    (hb : IsIntegral R b) : ∃ z : R, algebraMap R Rᵣ z = b := by
  let K := FractionRing R
  have hu : ∀ y : Submonoid.powers r, IsUnit (algebraMap R K y) := fun y ↦ by
    refine IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ?_)
    obtain ⟨n, hn⟩ := y.2
    rw [← hn]
    exact pow_ne_zero n hr
  let ψ : Rᵣ →+* K := IsLocalization.lift (M := Submonoid.powers r) hu
  have hψ : ψ.comp (algebraMap R Rᵣ) = algebraMap R K := IsLocalization.lift_comp hu
  have hint : IsIntegral R (ψ b) :=
    IsIntegral.map_of_comp_eq (RingHom.id R) ψ (by rw [hψ]; rfl) hb
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) b
  refine ⟨z, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul]
  have h1 : ψ (IsLocalization.mk' Rᵣ x y) * algebraMap R K y = algebraMap R K x := by
    rw [← hψ, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
  rw [← hz, ← map_mul] at h1
  rw [IsFractionRing.injective R K h1]

/-- Every element of a localization of an étale algebra over a normal domain at a nonzero
element of the base which is integral over the base comes from the étale algebra. -/
theorem exists_algebraMap_eq_of_isIntegral_of_etale [Algebra.Etale R S] [Algebra R Sᵣ]
    [IsScalarTower R S Sᵣ] {r : R}
    (hR : Subsingleton R ∨ (IsDomain R ∧ IsIntegrallyClosed R ∧ r ≠ 0))
    [IsLocalization.Away (algebraMap R S r) Sᵣ] (x : Sᵣ) (hx : IsIntegral R x) :
    ∃ s : S, algebraMap S Sᵣ s = x := by
  rcases hR with hR | ⟨_, _, hr⟩
  · haveI := subsingleton_of_algebra_of_subsingleton R Sᵣ
    exact ⟨0, Subsingleton.elim _ _⟩
  let Rᵣ := Localization.Away r
  let T := S ⊗[R] Rᵣ
  have h : Algebra.algebraMapSubmonoid S (Submonoid.powers r) =
      Submonoid.powers (algebraMap R S r) := Submonoid.map_powers _ _
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers r)) Sᵣ := by
    rw [h]; infer_instance
  let eT : T ≃ₐ[S] Sᵣ :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid S (Submonoid.powers r)) T Sᵣ
  have hx' : IsIntegral S (eT.symm x) := (hx.tower_top (A := S)).map eT.symm.toAlgHom
  obtain ⟨s, hs⟩ := exists_algebraMap_eq_of_isIntegral_tensor
    (fun b hb ↦ exists_algebraMap_eq_of_isIntegral_away hr b hb) _ hx'
  refine ⟨s, ?_⟩
  rw [← eT.commutes, hs, AlgEquiv.apply_symm_apply]

end Local

section Product

variable {A : Type u} [CommRing A] {ι : Type u} {D : ι → Type u}
  [∀ i, CommRing (D i)]

/-- The projection `A → D i` of a ring `A ≃ ∏ D`. -/
def piProj (e : A ≃+* ∀ i, D i) (i : ι) : A →+* D i :=
  (Pi.evalRingHom D i).comp e.toRingHom

/-- The `i`-th component of `e x`. -/
lemma piProj_apply (e : A ≃+* ∀ i, D i) (i : ι) (x : A) : piProj e i x = e x i := rfl

/-- The projection `A → D i` is surjective. -/
lemma surjective_piProj (e : A ≃+* ∀ i, D i) (i : ι) : Function.Surjective (piProj e i) :=
  fun d ↦ by classical exact ⟨e.symm (Pi.single i d), by simp [piProj_apply]⟩

/-- Multiplying by `e⁻¹ (Pi.single i d)` only retains the `i`-th component. -/
lemma symm_single_mul_eq [DecidableEq ι] (e : A ≃+* ∀ i, D i) (i : ι) (d : D i) (x : A) :
    e.symm (Pi.single i d) * x = e.symm (Pi.single i (d * e x i)) := by
  apply e.injective
  rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- A factor `D i` of `A ≃ ∏ D` is the localization of `A` at the corresponding idempotent. -/
lemma isLocalization_away_piProj [DecidableEq ι] (e : A ≃+* ∀ i, D i) (i : ι) :
    letI := (piProj e i).toAlgebra
    IsLocalization.Away (e.symm (Pi.single i 1)) (D i) := by
  letI := (piProj e i).toAlgebra
  refine IsLocalization.away_of_isIdempotentElem_of_mul (S := D i) ?_ (fun x y ↦ ?_)
    (surjective_piProj e i)
  · change _ * _ = _
    rw [symm_single_mul_eq]
    simp
  · change e x i = e y i ↔ _
    rw [symm_single_mul_eq, symm_single_mul_eq, one_mul, one_mul]
    exact ⟨fun h ↦ by rw [h], fun h ↦ by simpa using congrFun (e.symm.injective h) i⟩

/-- The localization of `A ≃ ∏ D` at `e⁻¹ (Pi.single i d)` is the localization of `D i` at
`d`. -/
lemma isLocalization_away_single [DecidableEq ι] (e : A ≃+* ∀ i, D i) (i : ι) (d : D i) :
    letI := (piProj e i).toAlgebra
    IsLocalization.Away (e.symm (Pi.single i d)) (Localization.Away d) := by
  letI := (piProj e i).toAlgebra
  haveI := isLocalization_away_piProj e i
  have h : algebraMap A (D i) (e.symm (Pi.single i d)) = d := by
    change e (e.symm _) i = d
    simp
  haveI : IsLocalization.Away (algebraMap A (D i) (e.symm (Pi.single i d)))
      (Localization.Away d) := by rw [h]; infer_instance
  have hmul : e.symm (Pi.single i 1) * e.symm (Pi.single i d) = e.symm (Pi.single i d) := by
    rw [symm_single_mul_eq, RingEquiv.apply_symm_apply, Pi.single_eq_same, one_mul]
  rw [← hmul]
  exact IsLocalization.Away.mul' (D i) (Localization.Away d) _ _

/-- The components of a nonzerodivisor of a product of domains are nonzero. -/
lemma apply_ne_zero_of_mem_nonZeroDivisors [∀ i, Nontrivial (D i)] (e : A ≃+* ∀ i, D i)
    {a : A} (ha : a ∈ nonZeroDivisors A) (i : ι) : e a i ≠ 0 := by
  classical
  intro h2
  have h3 : e.symm (Pi.single i 1) * a = 0 := by rw [symm_single_mul_eq, h2, mul_zero]; simp
  have := (mem_nonZeroDivisors_iff_right.mp ha) _ h3
  have h4 := congrArg (fun x ↦ e x i) this
  simp at h4

/-- The localization of a finite product `A ≃ ∏ D` of normal domains at `e⁻¹ (Pi.single i d)` is
zero or a normal domain in which every nonzerodivisor of `A` stays nonzero. -/
theorem subsingleton_or_isDomain_of_isLocalization_single [DecidableEq ι] [∀ i, IsDomain (D i)]
    [∀ i, IsIntegrallyClosed (D i)] (e : A ≃+* ∀ i, D i) (i : ι) (d : D i)
    (R : Type*) [CommRing R] [Algebra A R] [IsLocalization.Away (e.symm (Pi.single i d)) R]
    {a : A} (ha : a ∈ nonZeroDivisors A) :
    Subsingleton R ∨ (IsDomain R ∧ IsIntegrallyClosed R ∧ algebraMap A R a ≠ 0) := by
  letI := (piProj e i).toAlgebra
  haveI := isLocalization_away_single e i d
  let φ : R ≃ₐ[A] Localization.Away d :=
    IsLocalization.algEquiv (Submonoid.powers (e.symm (Pi.single i d))) R _
  by_cases hd : d = 0
  · left
    haveI : Subsingleton (Localization.Away d) := by
      subst hd
      exact IsLocalization.subsingleton (M := Submonoid.powers (0 : D i)) ⟨1, pow_one 0⟩
    exact φ.toEquiv.subsingleton
  · right
    have hM : Submonoid.powers d ≤ (D i)⁰ :=
      powers_le_nonZeroDivisors_of_noZeroDivisors hd
    haveI : IsDomain (Localization.Away d) := IsLocalization.isDomain_localization hM
    refine ⟨φ.toMulEquiv.isDomain _, ?_, ?_⟩
    · haveI := isIntegrallyClosed_of_isLocalization (Localization.Away d) _ hM
      exact IsIntegrallyClosed.of_equiv φ.toRingEquiv.symm
    · intro h0
      have h1 : algebraMap A (Localization.Away d) a = 0 := by rw [← φ.commutes, h0, map_zero]
      change algebraMap (D i) (Localization.Away d) (piProj e i a) = 0 at h1
      rw [map_eq_zero_iff _ (IsLocalization.injective _ hM)] at h1
      exact apply_ne_zero_of_mem_nonZeroDivisors e ha i h1

end Product

section NonZeroDivisor

/-- A finite product of domains is reduced. -/
lemma IsFiniteProductOfNormalDomains.isReduced {A : Type u} [CommRing A]
    (hA : IsFiniteProductOfNormalDomains A) : IsReduced A := by
  obtain ⟨ι, _, D, _, _, _, ⟨e⟩⟩ := hA
  exact isReduced_of_injective e.toRingHom e.injective

/-- In a noetherian finite product of domains, an ideal contained in no minimal prime contains a
nonzerodivisor. -/
theorem exists_mem_nonZeroDivisors_of_forall_not_le {A : Type u} [CommRing A]
    [IsNoetherianRing A] (hA : IsFiniteProductOfNormalDomains A) (I : Ideal A)
    (hI : ∀ P ∈ minimalPrimes A, ¬ I ≤ P) : ∃ a ∈ I, a ∈ nonZeroDivisors A := by
  haveI := hA.isReduced
  have hsub : ¬ ((I : Set A) ⊆ ⋃ P ∈ minimalPrimes A, ((id P : Ideal A) : Set A)) := by
    rw [Ideal.subset_union_prime_finite (f := id) (minimalPrimes.finite_of_isNoetherianRing A) ⊥ ⊥
      (fun P hP _ _ ↦ hP.1.1)]
    rintro ⟨P, hP, hle⟩
    exact hI P hP hle
  obtain ⟨a, haI, ha⟩ := Set.not_subset.mp hsub
  simp only [Set.mem_iUnion, not_exists] at ha
  refine ⟨a, haI, mem_nonZeroDivisors_iff_right.mpr fun x hx ↦ ?_⟩
  have hmem : x ∈ sInf (minimalPrimes A) := by
    refine Submodule.mem_sInf.2 fun P hP ↦ ?_
    have hxa : x * a ∈ P := hx ▸ P.zero_mem
    exact (hP.1.1.mem_or_mem hxa).resolve_right (ha P hP)
  rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hmem
  have h0 : x ∈ nilradical A := hmem
  rwa [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] at h0

end NonZeroDivisor

section Pi

variable {R : Type*} [CommRing R] {ι : Type*} {S : ι → Type*} [∀ i, CommRing (S i)]
  [∀ i, Algebra R (S i)]

open Polynomial in
/-- An element of a finite product is integral if and only if its components are. -/
theorem isIntegral_pi_iff [Finite ι] (x : ∀ i, S i) :
    IsIntegral R x ↔ ∀ i, IsIntegral R (x i) := by
  refine ⟨fun hx i ↦ hx.map (Pi.evalAlgHom R S i), fun hx ↦ ?_⟩
  haveI := Fintype.ofFinite ι
  choose p hpm hp using hx
  refine ⟨∏ i, p i, monic_prod_of_monic _ _ fun i _ ↦ hpm i, ?_⟩
  rw [← aeval_def]
  funext j
  have h := Polynomial.aeval_algHom_apply (Pi.evalAlgHom R S j) x (∏ i, p i)
  change (aeval x (∏ i, p i)) j = 0
  rw [show (aeval x (∏ i, p i)) j = Pi.evalAlgHom R S j (aeval x (∏ i, p i)) from rfl, ← h,
    map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [aeval_def]; exact hp j)

/-- The integral closure in a finite product is the product of the integral closures. -/
noncomputable def integralClosurePiEquiv [Finite ι] :
    integralClosure R (∀ i, S i) ≃ₐ[R] ∀ i, integralClosure R (S i) :=
  AlgEquiv.ofBijective
    (AlgHom.pi fun i ↦ ((Pi.evalAlgHom R S i).comp (integralClosure R _).val).codRestrict
      (integralClosure R (S i)) fun y ↦ ((isIntegral_pi_iff y.1).mp y.2) i)
    ⟨fun _ _ h ↦ Subtype.ext (funext fun i ↦ congrArg Subtype.val (congrFun h i)),
      fun z ↦ ⟨⟨fun i ↦ (z i).1, (isIntegral_pi_iff _).mpr fun i ↦ (z i).2⟩, rfl⟩⟩

/-- Going down transfers to `T` along algebra maps `T → S i` pulling back all primes. -/
theorem Algebra.HasGoingDown.of_forall_exists_comap {T : Type*} [CommRing T] [Algebra R T]
    [∀ i, Algebra.HasGoingDown R (S i)] (f : ∀ i, T →ₐ[R] S i)
    (hf : ∀ Q : Ideal T, Q.IsPrime → ∃ i, ∃ Q' : Ideal (S i), Q'.IsPrime ∧ Q'.comap (f i) = Q) :
    Algebra.HasGoingDown R T where
  exists_ideal_le_liesOver_of_lt {p} _ Q _ hlt := by
    obtain ⟨i, Q', hQ', rfl⟩ := hf Q inferInstance
    have hunder : (Q'.comap (f i)).under R = Q'.under R := by
      ext x
      simp [Ideal.under, Ideal.mem_comap]
    rw [hunder] at hlt
    obtain ⟨P, hPQ, hP, hlies⟩ :=
      Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt (S := S i) Q' hlt
    refine ⟨P.comap (f i), Ideal.comap_mono hPQ, Ideal.comap_isPrime _ _, ⟨?_⟩⟩
    rw [hlies.over]
    ext x
    simp [Ideal.under, Ideal.mem_comap]

/-- Going down for a finite product. -/
theorem Algebra.HasGoingDown.pi [Finite ι] [∀ i, Algebra.HasGoingDown R (S i)] :
    Algebra.HasGoingDown R (∀ i, S i) :=
  Algebra.HasGoingDown.of_forall_exists_comap (fun i ↦ Pi.evalAlgHom R S i) fun Q hQ ↦ by
    obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq ⟨Q, hQ⟩
    exact ⟨i, q.asIdeal, q.2, congrArg PrimeSpectrum.asIdeal hq⟩

/-- Going down is invariant under isomorphisms of algebras. -/
theorem Algebra.HasGoingDown.of_algEquiv {T T' : Type*} [CommRing T] [CommRing T'] [Algebra R T]
    [Algebra R T'] [Algebra.HasGoingDown R T] (e : T ≃ₐ[R] T') : Algebra.HasGoingDown R T' :=
  Algebra.HasGoingDown.of_forall_exists_comap (S := fun _ : Unit ↦ T) (fun _ ↦ e.symm.toAlgHom)
    fun Q hQ ↦ ⟨(), Q.comap e.toAlgHom, Ideal.comap_isPrime _ _, by
      ext x
      simp [Ideal.mem_comap]⟩

end Pi

/-- A finite product of finite products of normal domains is a finite product of normal
domains. -/
theorem IsFiniteProductOfNormalDomains.pi {ι : Type u} [Finite ι] {S : ι → Type u}
    [∀ i, CommRing (S i)] (h : ∀ i, IsFiniteProductOfNormalDomains (S i)) :
    IsFiniteProductOfNormalDomains (∀ i, S i) := by
  choose J hJ D _ _ _ e using h
  refine ⟨Σ i, J i, inferInstance, fun σ ↦ D σ.1 σ.2, fun _ ↦ inferInstance,
    fun _ ↦ inferInstance, fun _ ↦ inferInstance, ⟨?_⟩⟩
  refine (RingEquiv.piCongrRight fun i ↦ (e i).some).trans ?_
  exact { (Equiv.piCurry fun i j ↦ D i j).symm with
    map_mul' := fun _ _ ↦ rfl
    map_add' := fun _ _ ↦ rfl }

/-- A normal domain is a finite product of normal domains. -/
lemma IsFiniteProductOfNormalDomains.of_isDomain (T : Type u) [CommRing T] [IsDomain T]
    [IsIntegrallyClosed T] : IsFiniteProductOfNormalDomains T :=
  ⟨PUnit, inferInstance, fun _ ↦ T, fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    fun _ ↦ inferInstance, ⟨(RingEquiv.piUnique fun _ : PUnit ↦ T).symm⟩⟩

section Core

variable {D : Type u} [CommRing D] [IsDomain D] [IsIntegrallyClosed D] [IsNoetherianRing D]
  (L : Type u) [CommRing L] [Algebra (FractionRing D) L] [Algebra D L]
  [IsScalarTower D (FractionRing D) L] [Module.Finite (FractionRing D) L]
  [Algebra.Etale (FractionRing D) L]

/-- The integral closure of a noetherian normal domain `D` in a finite étale algebra over its
fraction field is finite over `D`, a finite product of normal domains, and satisfies going down
over `D`. -/
theorem finite_isFiniteProductOfNormalDomains_hasGoingDown_of_fractionRing :
    Module.Finite D (integralClosure D L) ∧
      IsFiniteProductOfNormalDomains (integralClosure D L) ∧
      Algebra.HasGoingDown D (integralClosure D L) := by
  let K := FractionRing D
  obtain ⟨I, _, F, _, _, φ, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod K L).mp inferInstance
  letI : ∀ j, Algebra D (F j) := fun j ↦ ((algebraMap K (F j)).comp (algebraMap D K)).toAlgebra
  haveI : ∀ j, IsScalarTower D K (F j) := fun j ↦ IsScalarTower.of_algebraMap_eq' rfl
  let ψ : integralClosure D L ≃ₐ[D] ∀ j, integralClosure D (F j) :=
    (φ.restrictScalars D).mapIntegralClosure.trans integralClosurePiEquiv
  haveI hfin : ∀ j, Module.Finite K (F j) := fun j ↦
    Module.Finite.of_surjective ((Pi.evalAlgHom K F j).comp φ.toAlgHom).toLinearMap
      fun y ↦ by classical exact ⟨φ.symm (Pi.single j y), by simp⟩
  haveI : ∀ j, Module.Finite D (integralClosure D (F j)) := fun j ↦
    IsIntegralClosure.finite D K (F j) (integralClosure D (F j))
  haveI : ∀ j, FaithfulSMul D (integralClosure D (F j)) := fun j ↦ by
    refine (faithfulSMul_iff_algebraMap_injective _ _).2 fun x y h ↦ ?_
    have h' := congrArg Subtype.val h
    change algebraMap K (F j) (algebraMap D K x) = algebraMap K (F j) (algebraMap D K y) at h'
    exact IsFractionRing.injective D K ((algebraMap K (F j)).injective h')
  haveI : ∀ j, IsIntegrallyClosed (integralClosure D (F j)) := fun j ↦
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  refine ⟨Module.Finite.equiv ψ.symm.toLinearEquiv, ?_, ?_⟩
  · exact IsFiniteProductOfNormalDomains.of_ringEquiv ψ.toRingEquiv
      (IsFiniteProductOfNormalDomains.pi fun j ↦ .of_isDomain _)
  · haveI : Algebra.HasGoingDown D (∀ j, integralClosure D (F j)) := Algebra.HasGoingDown.pi
    exact Algebra.HasGoingDown.of_algEquiv ψ.symm

end Core

section Helpers

open Polynomial

/-- Integrality is preserved by ring homomorphisms. -/
lemma RingHom.IsIntegralElem.comp_apply {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {g : R →+* S} {x : S} (hx : g.IsIntegralElem x) (w : S →+* T) :
    (w.comp g).IsIntegralElem (w x) := by
  obtain ⟨p, hpm, hp⟩ := hx
  exact ⟨p, hpm, by rw [← hom_eval₂, hp, map_zero]⟩

/-- Integrality over `D` transfers to integrality over `S` if `D` is a quotient of `A` and
`A → D → L` agrees with `A → S → L`. -/
lemma RingHom.IsIntegralElem.of_surjective {A D S L : Type*} [CommRing A] [CommRing D]
    [CommRing S] [CommRing L] {f : A →+* D} (hf : Function.Surjective f) (g : A →+* S)
    {u : D →+* L} (v : S →+* L) (hcomm : u.comp f = v.comp g) {x : L} (hx : u.IsIntegralElem x) :
    v.IsIntegralElem x := by
  obtain ⟨p, hpm, hp⟩ := hx
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic
    (lifts_iff_coeff_lifts _ |>.2 fun n ↦ hf _) hpm
  refine ⟨q.map g, hqm.map g, ?_⟩
  rw [eval₂_map, ← hcomm, ← eval₂_map, hq, hp]

/-- For `C` flat over `R` and `R → ∏ K i` injective, `c ↦ (1 ⊗ c)ᵢ` is injective. -/
lemma eq_zero_of_forall_one_tmul_eq_zero {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    [Module.Flat R C] {ι : Type*} [Finite ι] {K : ι → Type*} [∀ i, CommRing (K i)]
    [∀ i, Algebra R (K i)] (hinj : Function.Injective (algebraMap R (∀ i, K i))) (c : C)
    (h : ∀ i, (1 : K i) ⊗ₜ[R] c = 0) : c = 0 := by
  classical
  haveI := Fintype.ofFinite ι
  have h1 : c ⊗ₜ[R] (1 : ∀ i, K i) = 0 := by
    apply (TensorProduct.piRight R R C K).injective
    funext i
    simp only [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, Pi.one_apply,
      map_zero, Pi.zero_apply]
    rw [← TensorProduct.comm_tmul R (K i) C, h i, map_zero]
  have h2 : c ⊗ₜ[R] (1 : R) = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := C)
      (Algebra.linearMap R (∀ i, K i)) hinj
    rw [LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one, h1, map_zero]
  simpa using congrArg (TensorProduct.rid R C) h2

/-- After a smooth base change `R → C`, an element of `K ⊗[R] C` integral over `C` comes from `C`
if every element of `K` integral over `R` comes from `R`. -/
lemma exists_one_tmul_eq_of_isIntegralElem {R C K : Type*} [CommRing R] [CommRing C]
    [CommRing K] [Algebra R C] [Algebra R K] [Algebra.Smooth R C]
    (hB : ∀ b : K, IsIntegral R b → ∃ r : R, algebraMap R K r = b) (ℓ : K ⊗[R] C)
    (hℓ : (Algebra.TensorProduct.includeRight : C →ₐ[R] K ⊗[R] C).toRingHom.IsIntegralElem ℓ) :
    ∃ c : C, (1 : K) ⊗ₜ[R] c = ℓ := by
  let w := (Algebra.TensorProduct.comm R K C).toRingEquiv.toRingHom
  have hw : w.comp (Algebra.TensorProduct.includeRight : C →ₐ[R] K ⊗[R] C).toRingHom =
      algebraMap C (C ⊗[R] K) := by
    ext c
    simp [w]
  have h := hℓ.comp_apply w
  rw [hw] at h
  obtain ⟨s, hs⟩ := exists_algebraMap_eq_of_isIntegral_tensor hB (w ℓ) h
  refine ⟨s, (Algebra.TensorProduct.comm R K C).injective ?_⟩
  change _ = w ℓ
  rw [← hs]
  simp

end Helpers

open Polynomial in
/-- Let `C` be an `A`-algebra with maps `C → L i` that are jointly injective, and quotients
`A → D i` compatible with ring maps `D i → L i`. If the image of `c` in each `L i` is integral over
`D i`, then `c` is integral over `A`. -/
lemma isIntegral_of_forall_isIntegralElem {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    {ι : Type*} [Finite ι] {D L : ι → Type*} [∀ i, CommRing (D i)] [∀ i, CommRing (L i)]
    (π : ∀ i, A →+* D i) (hπ : ∀ i, Function.Surjective (π i)) (ιC : ∀ i, C →+* L i)
    (u : ∀ i, D i →+* L i) (hcomm : ∀ i, (ιC i).comp (algebraMap A C) = (u i).comp (π i))
    (hb : ∀ c : C, (∀ i, ιC i c = 0) → c = 0) (c : C)
    (hc : ∀ i, (u i).IsIntegralElem (ιC i c)) : IsIntegral A c := by
  haveI := Fintype.ofFinite ι
  choose p hpm hp using hc
  choose q hq _ hqm using fun i ↦ lifts_and_natDegree_eq_and_monic
    (lifts_iff_coeff_lifts _ |>.2 fun n ↦ hπ i _) (hpm i)
  refine ⟨∏ i, q i, monic_prod_of_monic _ _ fun i _ ↦ hqm i, hb _ fun j ↦ ?_⟩
  rw [hom_eval₂, hcomm, ← eval₂_map, Polynomial.map_prod, eval₂_finsetProd]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hq j, hp j])

/-- Let `A` be a noetherian finite product of normal domains, `a ∈ A` a nonzerodivisor and `C` a
finite étale algebra over the localization `Aₐ`. Then the integral closure of `A` in `C` is finite
over `A`, a finite product of normal domains, and satisfies going down over `A`. -/
theorem finite_isFiniteProductOfNormalDomains_hasGoingDown_integralClosure
    {A : Type u} [CommRing A] [IsNoetherianRing A] (hA : IsFiniteProductOfNormalDomains A)
    {a : A} (ha : a ∈ nonZeroDivisors A) (Aₐ : Type u) [CommRing Aₐ] [Algebra A Aₐ]
    [IsLocalization.Away a Aₐ] (C : Type u) [CommRing C] [Algebra A C] [Algebra Aₐ C]
    [IsScalarTower A Aₐ C] [Module.Finite Aₐ C] [Algebra.Etale Aₐ C] :
    Module.Finite A (integralClosure A C) ∧
      IsFiniteProductOfNormalDomains (integralClosure A C) ∧
      Algebra.HasGoingDown A (integralClosure A C) := by
  classical
  obtain ⟨ι, _, D, _, _, _, ⟨e⟩⟩ := hA
  haveI := Fintype.ofFinite ι
  have hai := apply_ne_zero_of_mem_nonZeroDivisors e ha
  letI : ∀ i, Algebra A (D i) := fun i ↦ (piProj e i).toAlgebra
  let K := fun i ↦ FractionRing (D i)
  have hK0 : ∀ i (x : D i), algebraMap (D i) (K i) x = 0 → x = 0 := fun i x h ↦
    (map_eq_zero_iff _ (IsFractionRing.injective (D i) (K i))).1 h
  have hunit : ∀ i, IsUnit ((algebraMap (D i) (K i)).comp (piProj e i) a) := fun i ↦
    IsUnit.mk0 _ fun h ↦ hai i (hK0 i _ h)
  let φ : ∀ i, Aₐ →+* K i := fun i ↦ IsLocalization.Away.lift a (hunit i)
  have hφ : ∀ i, (φ i).comp (algebraMap A Aₐ) = (algebraMap (D i) (K i)).comp (piProj e i) :=
    fun i ↦ IsLocalization.Away.lift_comp _ (hunit i)
  letI : ∀ i, Algebra Aₐ (K i) := fun i ↦ (φ i).toAlgebra
  let L := fun i ↦ K i ⊗[Aₐ] C
  haveI : ∀ i, IsScalarTower (D i) (K i) (L i) := fun i ↦ inferInstance
  let T := fun i ↦ integralClosure (D i) (L i)
  haveI : ∀ i, IsNoetherianRing (D i) := fun i ↦
    isNoetherianRing_of_surjective A (D i) (piProj e i) (surjective_piProj e i)
  have core := fun i ↦
    finite_isFiniteProductOfNormalDomains_hasGoingDown_of_fractionRing (D := D i) (L i)
  letI : ∀ i, Algebra A (T i) := fun i ↦ ((algebraMap (D i) (T i)).comp (piProj e i)).toAlgebra
  haveI : ∀ i, IsScalarTower A (D i) (T i) := fun i ↦ .of_algebraMap_eq' rfl
  let ιC : ∀ i, C →+* L i := fun i ↦
    (Algebra.TensorProduct.includeRight : C →ₐ[Aₐ] K i ⊗[Aₐ] C).toRingHom
  have hcomm : ∀ i, (ιC i).comp (algebraMap A C) =
      (algebraMap (D i) (L i)).comp (piProj e i) := fun i ↦ by
    ext x
    have h1 := congrArg (fun g ↦ g x) (hφ i)
    simp only [RingHom.comp_apply] at h1
    simp only [RingHom.comp_apply, IsScalarTower.algebraMap_apply A Aₐ C, ιC,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes,
      IsScalarTower.algebraMap_apply (D i) (K i) (L i)]
    rw [← h1]
    rfl
  -- `Aₐ → ∏ K i` is injective
  have hinj : Function.Injective (algebraMap Aₐ (∀ i, K i)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) x
    have hy : ∀ i, piProj e i y = 0 := fun i ↦ by
      have h1 : φ i (IsLocalization.mk' Aₐ y s) = 0 := congrFun hx i
      have h2 := congrArg (φ i) (IsLocalization.mk'_spec Aₐ y s)
      rw [map_mul, h1, zero_mul, ← RingHom.comp_apply, hφ, RingHom.comp_apply] at h2
      exact hK0 i _ h2.symm
    have : y = 0 := e.injective (funext fun i ↦ by rw [map_zero]; exact hy i)
    subst this
    exact IsLocalization.mk'_zero s
  have hb : ∀ c : C, (∀ i, ιC i c = 0) → c = 0 := fun c hc ↦
    eq_zero_of_forall_one_tmul_eq_zero hinj c hc
  -- elements of `K i` integral over `Aₐ` come from `Aₐ`
  have hB : ∀ i, ∀ b : K i, IsIntegral Aₐ b → ∃ r : Aₐ, algebraMap Aₐ (K i) r = b := by
    intro i b hb'
    haveI : IsScalarTower A Aₐ (K i) := .of_algebraMap_eq' (by
      rw [IsScalarTower.algebraMap_eq A (D i) (K i)]
      exact (hφ i).symm)
    obtain ⟨⟨_, n, rfl⟩, hm⟩ :=
      IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers a) b hb'
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hm.tower_top (A := D i))
    obtain ⟨y, rfl⟩ := surjective_piProj e i z
    refine ⟨IsLocalization.mk' Aₐ y (⟨a ^ n, n, rfl⟩ : Submonoid.powers a), ?_⟩
    have hs : algebraMap Aₐ (K i) (algebraMap A Aₐ (a ^ n)) ≠ 0 := by
      change φ i (algebraMap A Aₐ (a ^ n)) ≠ 0
      rw [← RingHom.comp_apply, hφ, RingHom.comp_apply, map_pow, map_pow]
      exact pow_ne_zero n fun h ↦ hai i (hK0 i _ h)
    refine mul_left_cancel₀ hs ?_
    rw [mul_comm, ← map_mul, IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A (D i) (K i)]
    change algebraMap (D i) (K i) (piProj e i y) = _
    rw [hz, Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply A Aₐ (K i)]
  -- the comparison map
  have hint : ∀ i (x : integralClosure A C), ιC i x.1 ∈ T i := fun i x ↦ by
    have h := (show (algebraMap A C).IsIntegralElem x.1 from x.2).comp_apply (ιC i)
    rw [hcomm] at h
    exact h.of_comp
  let θ : integralClosure A C →ₐ[A] ∀ i, T i := AlgHom.pi fun i ↦
    { toRingHom := ((ιC i).comp (integralClosure A C).val.toRingHom).codRestrict (T i)
        (hint i)
      commutes' := fun x ↦ Subtype.ext (congrArg (fun g ↦ g x) (hcomm i)) }
  have hθ : Function.Bijective θ := by
    refine ⟨fun x y hxy ↦ Subtype.ext (sub_eq_zero.mp (hb _ fun i ↦ ?_)), fun t ↦ ?_⟩
    · have h := congrArg (fun t ↦ (t i : L i)) hxy
      rw [map_sub, sub_eq_zero]
      exact h
    · have hc : ∀ i, ∃ c : C, ιC i c = (t i).1 := fun i ↦
        exists_one_tmul_eq_of_isIntegralElem (hB i) _
          (RingHom.IsIntegralElem.of_surjective (surjective_piProj e i) (algebraMap A C)
            (ιC i) (hcomm i).symm (t i).2)
      choose c hc using hc
      let c' := ∑ j, algebraMap A C (e.symm (Pi.single j 1)) * c j
      have hc' : ∀ i, ιC i c' = (t i).1 := fun i ↦ by
        simp only [c', map_sum, map_mul]
        rw [Finset.sum_eq_single i]
        · rw [← RingHom.comp_apply, hcomm, RingHom.comp_apply, piProj_apply,
            RingEquiv.apply_symm_apply, Pi.single_eq_same, map_one, one_mul, hc]
        · intro j _ hj
          rw [← RingHom.comp_apply, hcomm, RingHom.comp_apply, piProj_apply,
            RingEquiv.apply_symm_apply, Pi.single_eq_of_ne (Ne.symm hj), map_zero, zero_mul]
        · simp
      have hc'int : IsIntegral A c' :=
        isIntegral_of_forall_isIntegralElem (piProj e) (surjective_piProj e) ιC
          (fun i ↦ algebraMap (D i) (L i)) hcomm hb c' fun i ↦ by
            rw [hc']
            exact (t i).2
      exact ⟨⟨c', hc'int⟩, funext fun i ↦ Subtype.ext (hc' i)⟩
  let Θ := AlgEquiv.ofBijective θ hθ
  refine ⟨?_, ?_, ?_⟩
  · haveI : ∀ i, Module.Finite A (D i) := fun i ↦
      Module.Finite.of_surjective (Algebra.linearMap A (D i)) (surjective_piProj e i)
    haveI : ∀ i, Module.Finite (D i) (T i) := fun i ↦ (core i).1
    haveI : ∀ i, Module.Finite A (T i) := fun i ↦ Module.Finite.trans (D i) (T i)
    exact Module.Finite.equiv Θ.symm.toLinearEquiv
  · exact IsFiniteProductOfNormalDomains.of_ringEquiv Θ.toRingEquiv
      (IsFiniteProductOfNormalDomains.pi fun i ↦ (core i).2.1)
  · haveI : ∀ i, Algebra.HasGoingDown A (T i) := fun i ↦ by
      haveI := isLocalization_away_piProj e i
      haveI : Module.Flat A (D i) :=
        IsLocalization.flat (D i) (Submonoid.powers (e.symm (Pi.single i 1)))
      haveI : Algebra.HasGoingDown (D i) (T i) := (core i).2.2
      exact Algebra.HasGoingDown.trans A (D i) (T i)
    haveI : Algebra.HasGoingDown A (∀ i, T i) := Algebra.HasGoingDown.pi
    exact Algebra.HasGoingDown.of_algEquiv Θ.symm
