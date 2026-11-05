/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Tengoku.Seed.RingTheory.Smooth.IntegralClosure
import Tengoku.Seed.RingTheory.Etale.Field
import Tengoku.Seed.RingTheory.Flat.Basic
import Tengoku.Seed.RingTheory.Localization.Integral
import Tengoku.Seed.RingTheory.Localization.AtPrime.Basic
import Tengoku.Seed.Tactic.Push
import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Normality of etale algebras localized at primes

Integral elements in the generic fibre of a smooth algebra descend to the original
algebra. These comparisons yield the domain and integral-closure properties of an etale
algebra localized at a prime.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
universe u
open scoped TensorProduct

namespace EtaleLocNormalAux

theorem isIntegral_of_isIdempotentElem {T B : Type*} [CommRing T] [CommRing B] [Algebra T B]
    {e : B} (he : IsIdempotentElem e) : IsIntegral T e := by
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1),
    Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
    map_one, mul_sub, mul_one, he.eq, sub_self]

section Core
variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
variable (S : Type u) [CommRing S] [Algebra R S]

omit [IsDomain R] [IsIntegrallyClosed R] in
theorem algebraMap_genericFibre_injective [Module.Flat R S] :
    Function.Injective (algebraMap S (S ⊗[R] K)) := by
  have h := Algebra.TensorProduct.includeLeft_injective (S := S) (A := S) (B := K)
    (IsFractionRing.injective R K)
  intro a b hab
  apply h
  simpa [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.algebraMap_apply] using hab

end Core

theorem isIntegrallyClosed_of_integralClosure_eq_bot (T A : Type*) [CommRing T]
    [IsDomain T] [CommRing A] [IsDomain A] [Algebra T A] [FaithfulSMul T A]
    [IsIntegrallyClosed A] (h : integralClosure T A = ⊥) :
    IsIntegrallyClosed T := by
  have hg : Function.Injective (algebraMap T (FractionRing A)) := by
    rw [IsScalarTower.algebraMap_eq T A (FractionRing A)]
    exact (IsFractionRing.injective A (FractionRing A)).comp
      (FaithfulSMul.algebraMap_injective T A)
  have hg' : Function.Injective (Algebra.ofId T (FractionRing A)) := fun a b hab =>
    hg (by simpa [Algebra.ofId_apply] using hab)
  let φ : FractionRing T →ₐ[T] FractionRing A :=
    IsFractionRing.liftAlgHom (K := FractionRing T) hg'
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx
  have h1 : IsIntegral T (φ x) := hx.map φ
  have h2 : IsIntegral A (φ x) := h1.tower_top
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  have h3 : IsIntegral T a := by
    refine IsIntegral.tower_bot (IsFractionRing.injective A (FractionRing A)) ?_
    rw [ha]
    exact h1
  have h4 : a ∈ (⊥ : Subalgebra T A) := by
    rw [← h]
    exact (mem_integralClosure_iff T A).mpr h3
  rw [Algebra.mem_bot] at h4
  obtain ⟨t, ht⟩ := h4
  refine ⟨t, ?_⟩
  have hφinj : Function.Injective φ := RingHom.injective (φ : FractionRing T →+* FractionRing A)
  apply hφinj
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply T A (FractionRing A), ht]
  exact ha

end EtaleLocNormalAux

end Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
