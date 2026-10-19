/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.LinearAlgebra.TensorProduct.Pi
import Tengoku.Seed.RingTheory.Flat.Basic
import Tengoku.Seed.RingTheory.DedekindDomain.IntegralClosure
import Tengoku.Seed.RingTheory.Localization.Finiteness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Embedding a finite torsion-free algebra into a free module

Let `A` be an integrally closed domain of characteristic zero and `B` a domain which
is a finite `A`-algebra with `A → B` injective. The trace forms `b ↦ Tr(b bⱼ)` for generators
`bⱼ` of `B` take values in `A` and jointly embed `B` into `A^m`
(`exists_injective_linearMap_pi_of_finite`).

After a flat base change `A → S`, the vanishing of `∑ⱼ cⱼ ⊗ bⱼ` in `S ⊗[A] B` can then be tested
by the coordinates `∑ⱼ cⱼ λ_k(bⱼ)` (`TensorProduct.sum_tmul_eq_zero_iff_of_injective`).
-/

open TensorProduct

section Tensor

variable {R S B : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup B] [Module R B] {r m : ℕ}

/-- After a flat base change, `∑ⱼ cⱼ ⊗ bⱼ = 0` iff all coordinates of `∑ⱼ cⱼ λ(bⱼ)` vanish, for
an injective linear map `λ : B → R^r`. -/
theorem TensorProduct.sum_tmul_eq_zero_iff_of_injective (ℓ : B →ₗ[R] (Fin r → R))
    (hℓ : Function.Injective ℓ) (b : Fin m → B) (c : Fin m → S) :
    ∑ j, c j ⊗ₜ[R] b j = 0 ↔ ∀ k, ∑ j, c j * algebraMap R S (ℓ (b j) k) = 0 := by
  have hinj : Function.Injective (ℓ.lTensor S) :=
    Module.Flat.lTensor_preserves_injective_linearMap ℓ hℓ
  have key : ∀ k, piScalarRight R R S (Fin r) (ℓ.lTensor S (∑ j, c j ⊗ₜ[R] b j)) k =
      ∑ j, c j * algebraMap R S (ℓ (b j) k) := fun k ↦ by
    simp only [map_sum, LinearMap.lTensor_tmul, piScalarRight_apply, piScalarRightHom_tmul,
      Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [_root_.Algebra.smul_def, mul_comm]
  constructor
  · intro h k
    rw [← key, h, map_zero, map_zero, Pi.zero_apply]
  · intro h
    refine hinj ?_
    rw [map_zero]
    refine (piScalarRight R R S (Fin r)).injective ?_
    rw [map_zero]
    funext k
    rw [key, h k, Pi.zero_apply]

end Tensor

section Trace

variable (A B : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CharZero A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]

/-- **A finite torsion-free algebra over a normal domain of characteristic zero embeds into a
free module**, through the trace forms `b ↦ Tr(b bⱼ)` for generators `bⱼ`. -/
theorem exists_injective_linearMap_pi_of_finite (hinj : Function.Injective (algebraMap A B)) :
    ∃ (r : ℕ) (ℓ : B →ₗ[A] (Fin r → A)), Function.Injective ℓ := by
  classical
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := A) (M := B)
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  let K := FractionRing A
  let L := FractionRing B
  letI : Algebra K L := FractionRing.liftAlgebra A L
  haveI : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  haveI : Algebra.IsIntegral A B := inferInstance
  haveI : Module.Finite K L := Module.Finite.of_isLocalization A B (nonZeroDivisors A)
    (Rₚ := K) (Sₚ := L)
  haveI : Algebra.IsSeparable K L := inferInstance
  let T : B → Fin m → K := fun x k ↦ Algebra.trace K L (algebraMap B L x * algebraMap B L (b k))
  have hT : ∀ x k, ∃ a : A, algebraMap A K a = T x k := fun x k ↦ by
    have hx : IsIntegral A (algebraMap B L x * algebraMap B L (b k)) := by
      rw [← map_mul]
      exact (Algebra.IsIntegral.isIntegral (R := A) (x * b k)).map (IsScalarTower.toAlgHom A B L)
    exact IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (R := A) hx)
  choose ℓ₀ hℓ₀ using hT
  have hK := IsFractionRing.injective A K
  have hBL : ∀ a : A, algebraMap B L (algebraMap A B a) = algebraMap K L (algebraMap A K a) :=
    fun a ↦ by rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  let ℓ : B →ₗ[A] (Fin m → A) :=
    { toFun := fun x k ↦ ℓ₀ x k
      map_add' := fun x y ↦ funext fun k ↦ hK (by
        simp only [Pi.add_apply, map_add, hℓ₀, T, add_mul])
      map_smul' := fun a x ↦ funext fun k ↦ hK (by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, map_mul, hℓ₀, T,
          _root_.Algebra.smul_def, hBL, mul_assoc]
        rw [← _root_.Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]) }
  refine ⟨m, ℓ, (injective_iff_map_eq_zero ℓ).2 fun x hx ↦ ?_⟩
  have hx0 : ∀ k, T x k = 0 := fun k ↦ by
    rw [← hℓ₀]
    exact (congrArg (algebraMap A K) (congrFun hx k)).trans (map_zero _)
  -- the trace form of `x` vanishes on the image of `B`
  have hxB : ∀ y : B, Algebra.trace K L (algebraMap B L x * algebraMap B L y) = 0 := by
    intro y
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).1
      (hb ▸ Submodule.mem_top : y ∈ Submodule.span A (Set.range b))
    simp only [map_sum, Finset.mul_sum, _root_.Algebra.smul_def, map_mul, hBL]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [mul_left_comm, ← _root_.Algebra.smul_def, LinearMap.map_smul]
    change algebraMap A K (a k) • T x k = 0
    rw [hx0 k, smul_zero]
  have hxL : ∀ z : L, Algebra.trace K L (algebraMap B L x * z) = 0 := by
    intro z
    obtain ⟨⟨y, s⟩, hs⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) z
    obtain ⟨a, ha, has⟩ := s.2
    have ha0 : algebraMap A K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
    have e : Algebra.trace K L (algebraMap B L x * z) * algebraMap A K a = 0 := by
      rw [mul_comm, ← smul_eq_mul, ← LinearMap.map_smul, _root_.Algebra.smul_def, ← hBL, has,
        mul_left_comm, mul_comm (algebraMap B L (s : B)) z, hs]
      exact hxB y
    exact (mul_eq_zero.1 e).resolve_right ha0
  have h0 : algebraMap B L x = 0 := (traceForm_nondegenerate K L).1 _ fun z ↦ by
    rw [Algebra.traceForm_apply]
    exact hxL z
  exact IsFractionRing.injective B L (h0.trans (map_zero _).symm)

end Trace
