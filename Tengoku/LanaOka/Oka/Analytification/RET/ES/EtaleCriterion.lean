/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.RingTheory.Smooth.Fiber
import Tengoku.Seed.RingTheory.Unramified.Pi
import Tengoku.Seed.RingTheory.Kaehler.TensorProduct
import Tengoku.Seed.RingTheory.Flat.Localization
import Tengoku.Seed.RingTheory.Flat.FaithfullyFlat.Basic
import Tengoku.Seed.RingTheory.TensorProduct.Pi
import Tengoku.Seed.RingTheory.TensorProduct.Quotient
import Tengoku.Seed.RingTheory.Localization.BaseChange
import Tengoku.Seed.LinearAlgebra.TensorProduct.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Étaleness from split fibres over faithfully flat local extensions

Let `A → B` be a finite ring map. Suppose that at every maximal ideal `P` of `A` there is a
faithfully flat extension `A_P → O` of the localisation over which `B` splits:
`O ⊗[A] B ≅ O^ι` as `O`-algebras, for a finite set `ι`. Then `B` is flat over `A`, and if
moreover the residue field `K` of `P` is a quotient of `O`, the fibre `K ⊗[A] B ≅ K^ι` is
unramified. Together this makes `A → B` étale when `A` is noetherian.

## Main results

- `Algebra.TensorProduct.fibreAlgEquivOfBijective`: an `O`-algebra isomorphism
  `O ⊗[A] B ≅ (ι → O)` induces `K ⊗[A] B ≅ (ι → K)` for every `O`-algebra `K`.
- `Algebra.TensorProduct.exists_forall_mem_iff_fibre_eq_zero`,
  `Algebra.TensorProduct.eq_of_forall_fibre_eq_zero_iff`: when `A → K` is a surjection onto a
  field, the primes of `B` over its kernel are the kernels of the `ι` coordinates of the fibre.
- `Module.flat_localizedModule_of_faithfullyFlat`: flatness of `M_P` over `A` from flatness of
  `O ⊗[A] M` over a faithfully flat extension `O` of `A_P`.
- `Module.subsingleton_of_forall_isMaximal_tensor`: a finite module vanishing after base change
  to the residue field at every maximal ideal is zero.
- `Algebra.Etale.of_forall_isMaximal`: the étale criterion.
-/

open TensorProduct

universe w

namespace Algebra.TensorProduct

section Fibre

variable {A B O : Type*} [CommRing A] [CommRing B] [CommRing O] [Algebra A B] [Algebra A O]
  {ι : Type*} [Finite ι]

/-- An `O`-algebra isomorphism `O ⊗[A] B ≅ O^ι` makes `O ⊗[A] B` a flat `O`-module. -/
theorem flat_of_bijective (Ψ : O ⊗[A] B →ₐ[O] (ι → O)) (hΨ : Function.Bijective Ψ) :
    Module.Flat O (O ⊗[A] B) :=
  Module.Flat.of_linearEquiv (AlgEquiv.ofBijective Ψ hΨ).toLinearEquiv

variable (Ψ : O ⊗[A] B →ₐ[O] (ι → O)) (hΨ : Function.Bijective Ψ)
  (K : Type*) [CommRing K] [Algebra O K] [Algebra A K] [IsScalarTower A O K]

/-- **The fibre of a split algebra**: an `O`-algebra isomorphism `O ⊗[A] B ≅ O^ι` induces a
`K`-algebra isomorphism `K ⊗[A] B ≅ K^ι` for every `O`-algebra `K`. -/
noncomputable def fibreAlgEquivOfBijective : K ⊗[A] B ≃ₐ[K] (ι → K) :=
  letI := Fintype.ofFinite ι
  letI := Classical.decEq ι
  (Algebra.TensorProduct.cancelBaseChange A O K K B).symm.trans <|
    (Algebra.TensorProduct.congr AlgEquiv.refl (AlgEquiv.ofBijective Ψ hΨ)).trans <|
      Algebra.TensorProduct.piScalarRight O K K ι

theorem fibreAlgEquivOfBijective_one_tmul (b : B) (i : ι) :
    fibreAlgEquivOfBijective Ψ hΨ K (1 ⊗ₜ b) i = algebraMap O K (Ψ (1 ⊗ₜ b) i) := by
  simp [fibreAlgEquivOfBijective, Algebra.algebraMap_eq_smul_one]

end Fibre

/-- The fibre `K ⊗[A] B ≅ K^ι` of a split algebra over a field is unramified. -/
theorem formallyUnramified_of_bijective {A B O : Type*} [CommRing A] [CommRing B] [CommRing O]
    [Algebra A B] [Algebra A O] {ι : Type*} [Finite ι] (Ψ : O ⊗[A] B →ₐ[O] (ι → O))
    (hΨ : Function.Bijective Ψ) (K : Type*) [Field K] [Algebra O K] [Algebra A K]
    [IsScalarTower A O K] : Algebra.FormallyUnramified K (K ⊗[A] B) :=
  .of_equiv (fibreAlgEquivOfBijective Ψ hΨ K).symm

section Kernel

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The kernel of `b ↦ 1 ⊗ b : B → K ⊗[A] B` lies in every ideal `n` of `B` whose contraction
contains the kernel of a surjection `A → K`. -/
theorem mem_of_includeRight_eq_zero {K : Type*} [CommRing K] [Algebra A K]
    (hK : Function.Surjective (algebraMap A K)) (n : Ideal B)
    (hn : RingHom.ker (algebraMap A K) ≤ n.comap (algebraMap A B)) {b : B}
    (hb : (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B) b = 0) : b ∈ n := by
  set I := RingHom.ker (algebraMap A K)
  let e : (A ⧸ I) ≃ₐ[A] K := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A K) hK
  let e' : (A ⧸ I) ⊗[A] B ≃ₐ[A] K ⊗[A] B :=
    Algebra.TensorProduct.congr e AlgEquiv.refl
  have h1 : e'.symm (1 ⊗ₜ b) = 1 ⊗ₜ b := by
    simp [e', Algebra.TensorProduct.congr_symm_apply]
  have h2 : (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm (1 ⊗ₜ b) =
      Ideal.Quotient.mk _ b := by
    apply (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).injective
    simp
  have h0 : (Ideal.Quotient.mk (I.map (algebraMap A B)) b) = 0 := by
    rw [← h2, ← h1]
    change _ = 0 at hb
    simp only [Algebra.TensorProduct.includeRight_apply] at hb
    rw [hb, map_zero, map_zero]
  exact (Ideal.map_le_iff_le_comap.2 hn) (Ideal.Quotient.eq_zero_iff_mem.1 h0)

end Kernel

section Primes

/-- **The prime ideals of a finite product of fields** are the kernels of the projections. -/
theorem _root_.Pi.exists_eq_ker_evalRingHom_of_isPrime {ι K : Type*} [Finite ι] [Field K]
    (Q : Ideal (ι → K)) [hQ : Q.IsPrime] : ∃ i, Q = RingHom.ker (Pi.evalRingHom (fun _ ↦ K) i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i, hi⟩ : ∃ i, (Pi.single i 1 : ι → K) ∉ Q := by
    by_contra! h
    apply hQ.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : ι → K) = ∑ i, Pi.single i 1 := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact Q.sum_mem fun i _ ↦ h i
  refine ⟨i, le_antisymm (fun f hf ↦ ?_) fun f hf ↦ ?_⟩
  · rw [RingHom.mem_ker, Pi.evalRingHom_apply]
    by_contra hfi
    apply hi
    have : (Pi.single i 1 : ι → K) = (fun _ ↦ (f i)⁻¹) * Pi.single i 1 * f := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp [hfi]
      · simp [hj]
    rw [this]
    exact Q.mul_mem_left _ hf
  · rw [RingHom.mem_ker, Pi.evalRingHom_apply] at hf
    have h0 : (Pi.single i 1 : ι → K) * f = 0 := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp [hf]
      · simp [hj]
    exact (hQ.mem_or_mem (h0 ▸ Q.zero_mem)).resolve_left hi

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {K : Type*} [Field K]
  [Algebra A K] (hK : Function.Surjective (algebraMap A K)) {ι : Type*} [Finite ι]
  (E : K ⊗[A] B ≃ₐ[K] (ι → K))

include hK

/-- **The primes of `B` over the kernel of a surjection `A → K` onto a field**: if the fibre
`K ⊗[A] B` is `K^ι`, every prime of `B` whose contraction contains the kernel is the kernel of
one of the coordinates `b ↦ E (1 ⊗ b) i`. -/
theorem exists_forall_mem_iff_fibre_eq_zero (n : Ideal B) [n.IsPrime]
    (hn : RingHom.ker (algebraMap A K) ≤ n.comap (algebraMap A B)) :
    ∃ i, ∀ b, b ∈ n ↔ E (1 ⊗ₜ b) i = 0 := by
  let β : B →+* ι → K := E.toRingHom.comp
    (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B).toRingHom
  have hβ : Function.Surjective β :=
    E.surjective.comp (includeRight_surjective B hK)
  have hker : RingHom.ker β ≤ n := fun b hb ↦
    mem_of_includeRight_eq_zero hK n hn (E.injective (by
      rw [map_zero]
      exact hb))
  haveI := Ideal.map_isPrime_of_surjective hβ hker
  obtain ⟨i, hi⟩ := Pi.exists_eq_ker_evalRingHom_of_isPrime (n.map β)
  refine ⟨i, fun b ↦ ?_⟩
  have hcm : (n.map β).comap β = n := by
    rw [Ideal.comap_map_of_surjective' β hβ]
    exact sup_eq_left.2 hker
  rw [← hcm, Ideal.mem_comap, hi]
  rfl

omit [Finite ι] in
/-- Distinct coordinates of the fibre have distinct kernels on `B`. -/
theorem eq_of_forall_fibre_eq_zero_iff {i j : ι}
    (h : ∀ b, E (1 ⊗ₜ b) i = 0 ↔ E (1 ⊗ₜ b) j = 0) : i = j := by
  classical
  obtain ⟨x, hx⟩ := E.surjective (Pi.single i 1)
  obtain ⟨b, rfl⟩ := includeRight_surjective B hK x
  by_contra hij
  have h1 : E (1 ⊗ₜ b) j = 0 := by
    change E (Algebra.TensorProduct.includeRight b) j = 0
    rw [hx, Pi.single_apply, ite_eq_right (Ne.symm hij)]
  have h2 := (h b).2 h1
  change E (Algebra.TensorProduct.includeRight b) i = 0 at h2
  rw [hx, Pi.single_eq_same] at h2
  exact one_ne_zero h2

end Primes

end Algebra.TensorProduct

namespace Module

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- **Flatness of a localisation from a faithfully flat extension**: if `S` is the localisation
of `A` at the prime `P` and `O` is a faithfully flat `S`-algebra with `O ⊗[A] M` flat over `O`,
then `M_P` is flat over `A`. -/
theorem flat_localizedModule_of_faithfullyFlat (P : Ideal A) [P.IsPrime] (S O : Type*)
    [CommRing S] [CommRing O] [Algebra A S] [Algebra S O] [Algebra A O] [IsScalarTower A S O]
    [IsLocalization.AtPrime S P] [Module.FaithfullyFlat S O] [Module.Flat O (O ⊗[A] M)] :
    Module.Flat A (LocalizedModule P.primeCompl M) := by
  have : Module.Flat O (O ⊗[S] (S ⊗[A] M)) :=
    Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange A S O O M)
  have : Module.Flat S (S ⊗[A] M) := Module.Flat.of_flat_tensorProduct S (S ⊗[A] M) O
  have : Module.Flat A S := IsLocalization.flat S P.primeCompl
  have : Module.Flat A (S ⊗[A] M) := Module.Flat.trans A S (S ⊗[A] M)
  have : IsLocalizedModule P.primeCompl (TensorProduct.mk A S M 1) :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl S _).2 (TensorProduct.isBaseChange A M S)
  exact Module.Flat.of_linearEquiv (IsLocalizedModule.linearEquiv P.primeCompl
    (LocalizedModule.mkLinearMap P.primeCompl M) (TensorProduct.mk A S M 1))

/-- **Nakayama at all maximal ideals**: a finite `A`-module `M` such that `K ⊗[A] M = 0`
for a surjection `A → K` with kernel `P`, at every maximal ideal `P`, is zero. -/
theorem subsingleton_of_forall_isMaximal_tensor [Module.Finite A M]
    (H : ∀ (P : Ideal A), P.IsMaximal → ∃ (K : Type w) (_ : CommRing K) (_ : Algebra A K),
      Function.Surjective (algebraMap A K) ∧ RingHom.ker (algebraMap A K) = P ∧
        Subsingleton (K ⊗[A] M)) :
    Subsingleton M := by
  have hP : ∀ (P : Ideal A), P.IsMaximal → (⊤ : Submodule A M) ≤ P • ⊤ := by
    intro P hP
    obtain ⟨K, _, _, hK, hker, hsub⟩ := H P hP
    subst hker
    let e : (A ⧸ RingHom.ker (algebraMap A K)) ≃ₐ[A] K :=
      Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A K) hK
    have : Subsingleton ((A ⧸ RingHom.ker (algebraMap A K)) ⊗[A] M) :=
      (LinearEquiv.rTensor M e.toLinearEquiv).toEquiv.subsingleton
    have : Subsingleton (M ⧸ RingHom.ker (algebraMap A K) • (⊤ : Submodule A M)) :=
      (quotTensorEquivQuotSMul M _).symm.toEquiv.subsingleton
    rw [Submodule.Quotient.subsingleton_iff] at this
    rw [this]
  by_contra hM
  have hann : Module.annihilator A M ≠ ⊤ := by
    intro h
    apply hM
    refine ⟨fun m m' ↦ ?_⟩
    have h1 : (1 : A) ∈ Module.annihilator A M := h ▸ Submodule.mem_top
    rw [Module.mem_annihilator] at h1
    rw [← one_smul A m, ← one_smul A m', h1, h1]
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hann
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul P ⊤
    (Module.Finite.fg_top) (hP P hPmax)
  have hr' : r ∈ P := hle ((Module.mem_annihilator).2 fun m ↦ hr m Submodule.mem_top)
  exact hPmax.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.sub_mem hr' hr1))

end Module

namespace Algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- If the fibre `K ⊗[A] B` is unramified over `K`, then `K ⊗[A] Ω[B⁄A] = 0`. -/
theorem subsingleton_tensor_kaehlerDifferential (K : Type*) [CommRing K] [Algebra A K]
    [Algebra.FormallyUnramified K (K ⊗[A] B)] : Subsingleton (K ⊗[A] Ω[B⁄A]) :=
  letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := K) (B := B)
  (KaehlerDifferential.tensorKaehlerEquivBase A K B (K ⊗[A] B)).toEquiv.subsingleton

/-- **An étale criterion at maximal ideals.** Let `A` be noetherian and `B` a finite
`A`-algebra such that at every maximal ideal `P` of `A`
- the localisation `B_P` is flat over `A`, and
- there is a surjection `A → K` with kernel `P` whose fibre `K ⊗[A] B` is unramified over `K`.

Then `B` is étale over `A`. -/
theorem Etale.of_forall_isMaximal [IsNoetherianRing A] [Module.Finite A B]
    (hflat : ∀ (P : Ideal A) [P.IsMaximal], Module.Flat A (LocalizedModule P.primeCompl B))
    (hfib : ∀ (P : Ideal A), P.IsMaximal → ∃ (K : Type w) (_ : Field K) (_ : Algebra A K),
      Function.Surjective (algebraMap A K) ∧ RingHom.ker (algebraMap A K) = P ∧
        Algebra.FormallyUnramified K (K ⊗[A] B)) :
    Algebra.Etale A B := by
  have : Module.Flat A B := Module.flat_of_localized_maximal B hflat
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.1 (.of_restrictScalars_finiteType A A B)
  have : Module.Finite B Ω[B⁄A] := KaehlerDifferential.finite A B
  have : Module.Finite A Ω[B⁄A] := Module.Finite.trans B Ω[B⁄A]
  have : Subsingleton Ω[B⁄A] := by
    refine Module.subsingleton_of_forall_isMaximal_tensor (A := A) fun P hP ↦ ?_
    obtain ⟨K, _, _, hK, hker, _⟩ := hfib P hP
    exact ⟨K, inferInstance, inferInstance, hK, hker,
      subsingleton_tensor_kaehlerDifferential K⟩
  have : Algebra.FormallyUnramified A B := ⟨this⟩
  exact .of_formallyUnramified_of_flat

end Algebra
