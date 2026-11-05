/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.Algebra.Equiv
import Tengoku.Seed.FieldTheory.Galois.Notation
import Tengoku.Seed.RingTheory.SimpleRing.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Semilinear conjugation and independence of the extension

An automorphism of an extension field lying over a base automorphism conjugates
the relative Galois group. Two lifts of the same base automorphism differ by an
actual relative Galois automorphism, so their conjugations agree after mapping to
any commutative group.
-/

namespace KummerTheory

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- The inverse of a semilinear field automorphism lies over the inverse base map.
@isnad1 id=eq.1h5v.s10.9b0f71e9f9ed from=translated src=- shape=d8c9814e vocab=b0a8599d
-/
theorem semilinear_symm_algebraMap (τ : K ≃+* K) (e : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k)) (k : K) :
    e.symm (algebraMap K Ω k) = algebraMap K Ω (τ.symm k) := by
  apply e.injective
  rw [e.apply_symm_apply, he, τ.apply_symm_apply]

/-- Conjugation by a field automorphism lying over `τ` preserves base linearity.-/
def semilinearGaloisConjugate (τ : K ≃+* K) (e : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (σ : Gal(Ω/K)) : Gal(Ω/K) := by
  refine
    { toRingEquiv := (e.symm.trans σ.toRingEquiv).trans e
      commutes' := ?_ }
  intro k
  change e (σ (e.symm (algebraMap K Ω k))) = algebraMap K Ω k
  rw [semilinear_symm_algebraMap τ e he, σ.commutes, he, τ.apply_symm_apply]

/-- Evaluation of semilinear conjugation.
@isnad1 id=eq.1h6v.s10.c17b47eb8b5c from=translated src=- shape=17dd0114 vocab=a7e8b87d
-/
theorem semilinearGaloisConjugate_apply (τ : K ≃+* K) (e : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (σ : Gal(Ω/K)) (x : Ω) :
    semilinearGaloisConjugate τ e he σ x = e (σ (e.symm x)) := by
  rfl

/-- Transporting a nonzero root transports its scalar multiplier. This is the
common cancellation step for proper and open Kummer characters.
@isnad1 id=eq.4h9v.s10.b6f962ba3b74 from=translated src=- shape=587f1657 vocab=82eaf52e
-/
theorem semilinear_multiplier_eq {L : Type*} [Field L]
    (ι : L →+* Ω) (τ : L ≃+* L) (a : Ω ≃+* Ω)
    (hι : ∀ z : L, a (ι z) = ι (τ z))
    (β : Ω) (hβ : β ≠ 0) (c d : L) (z : Ω)
    (hc : ι c * β = z) (hd : ι d * a β = a z) : d = τ c := by
  apply ι.injective
  have h := congrArg a hc
  rw [map_mul, hι] at h
  have haβ : a β ≠ 0 := fun hz => hβ (a.injective (hz.trans (map_zero a).symm))
  exact mul_right_cancel₀ haβ (hd.trans h.symm)

/-- The identity extension lies over the identity base map.
@isnad1 id=eq.0h3v.s8.1f110e621b2c from=translated src=- shape=10042fa8 vocab=d5d0a227
-/
theorem semilinear_refl_algebraMap (k : K) :
    RingEquiv.refl Ω (algebraMap K Ω k) = algebraMap K Ω (RingEquiv.refl K k) := by
  rfl

/-- The identity lift acts trivially on the relative Galois group.
@isnad1 id=eq.0h3v.s7.4c84e6fabbbb from=translated src=- shape=af464108 vocab=e150c08d
-/
theorem semilinearGaloisConjugate_refl (σ : Gal(Ω/K)) :
    semilinearGaloisConjugate (RingEquiv.refl K) (RingEquiv.refl Ω)
      (semilinear_refl_algebraMap (K := K) (Ω := Ω)) σ = σ := by
  apply AlgEquiv.ext
  intro x
  rfl

/-- Composition of two semilinear extensions extends composition on the base.
@isnad1 id=eq.2h7v.s10.0d4ce9ac14fd from=translated src=- shape=0c8319a2 vocab=e47da141
-/
theorem semilinear_trans_algebraMap (τ υ : K ≃+* K) (e d : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (hd : ∀ k : K, d (algebraMap K Ω k) = algebraMap K Ω (υ k)) (k : K) :
    (e.trans d) (algebraMap K Ω k) = algebraMap K Ω ((τ.trans υ) k) := by
  change d (e (algebraMap K Ω k)) = algebraMap K Ω (υ (τ k))
  rw [he, hd]

/-- Conjugation by the composite lift is the composite of the conjugations.
@isnad1 id=eq.2h7v.s10.4f055e50ceff from=translated src=- shape=c5578c05 vocab=5a9af583
-/
theorem semilinearGaloisConjugate_trans (τ υ : K ≃+* K) (e d : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (hd : ∀ k : K, d (algebraMap K Ω k) = algebraMap K Ω (υ k))
    (σ : Gal(Ω/K)) :
    semilinearGaloisConjugate (τ.trans υ) (e.trans d)
      (semilinear_trans_algebraMap τ υ e d he hd) σ =
        semilinearGaloisConjugate υ d hd (semilinearGaloisConjugate τ e he σ) := by
  apply AlgEquiv.ext
  intro x
  simp only [semilinearGaloisConjugate_apply, RingEquiv.trans_apply,
    RingEquiv.symm_trans_apply]

/-- Semilinear conjugation is an automorphism of the relative Galois group.-/
def semilinearGaloisConjugateEquiv (τ : K ≃+* K) (e : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k)) :
    Gal(Ω/K) ≃* Gal(Ω/K) where
  toFun := semilinearGaloisConjugate τ e he
  invFun := semilinearGaloisConjugate τ.symm e.symm
    (semilinear_symm_algebraMap τ e he)
  left_inv σ := by
    apply AlgEquiv.ext
    intro x
    simp only [semilinearGaloisConjugate_apply, RingEquiv.symm_symm,
      RingEquiv.symm_apply_apply]
  right_inv σ := by
    apply AlgEquiv.ext
    intro x
    simp only [semilinearGaloisConjugate_apply, RingEquiv.symm_symm,
      RingEquiv.apply_symm_apply]
  map_mul' σ ρ := by
    apply AlgEquiv.ext
    intro x
    simp only [semilinearGaloisConjugate_apply, AlgEquiv.mul_apply,
      RingEquiv.symm_apply_apply]

/-- Evaluation of the bundled conjugation automorphism.
@isnad1 id=eq.1h5v.s10.0fa6c4b60654 from=translated src=- shape=6a4555c8 vocab=5a30a030
-/
theorem semilinearGaloisConjugateEquiv_apply (τ : K ≃+* K) (e : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (σ : Gal(Ω/K)) :
    semilinearGaloisConjugateEquiv τ e he σ = semilinearGaloisConjugate τ e he σ := by
  rfl

/-- Two extensions of the same base automorphism differ by a base-linear map.-/
def semilinearGaloisExtensionDifference (τ : K ≃+* K) (e e' : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (he' : ∀ k : K, e' (algebraMap K Ω k) = algebraMap K Ω (τ k)) :
    Gal(Ω/K) := by
  refine { toRingEquiv := e.symm.trans e', commutes' := ?_ }
  intro k
  change e' (e.symm (algebraMap K Ω k)) = algebraMap K Ω k
  rw [semilinear_symm_algebraMap τ e he, he', τ.apply_symm_apply]

/-- Evaluation of the base-linear difference of two lifts.
@isnad1 id=eq.2h6v.s10.c0873a4b63ef from=translated src=- shape=3c583f48 vocab=02e7cbff
-/
theorem semilinearGaloisExtensionDifference_apply (τ : K ≃+* K) (e e' : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (he' : ∀ k : K, e' (algebraMap K Ω k) = algebraMap K Ω (τ k)) (x : Ω) :
    semilinearGaloisExtensionDifference τ e e' he he' x = e' (e.symm x) := by
  rfl

/-- Evaluation of the inverse difference of two lifts.
@isnad1 id=eq.2h6v.s10.e2e9c1c5bfa4 from=translated src=- shape=39f42c49 vocab=3b0c0db7
-/
theorem semilinearGaloisExtensionDifference_inv_apply
    (τ : K ≃+* K) (e e' : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (he' : ∀ k : K, e' (algebraMap K Ω k) = algebraMap K Ω (τ k)) (x : Ω) :
    (semilinearGaloisExtensionDifference τ e e' he he')⁻¹ x = e (e'.symm x) := by
  rfl

/-- Changing the extension changes Galois conjugation by the inner automorphism
given by the constructed difference of the two extensions.
@isnad1 id=eq.2h6v.s10.5443748777a8 from=translated src=- shape=61764e7c vocab=0693a804
-/
theorem semilinearGaloisConjugate_eq_inner (τ : K ≃+* K) (e e' : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (he' : ∀ k : K, e' (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (σ : Gal(Ω/K)) :
    semilinearGaloisConjugate τ e' he' σ =
      semilinearGaloisExtensionDifference τ e e' he he' *
        semilinearGaloisConjugate τ e he σ *
          (semilinearGaloisExtensionDifference τ e e' he he')⁻¹ := by
  apply AlgEquiv.ext
  intro x
  simp only [AlgEquiv.mul_apply, semilinearGaloisExtensionDifference_apply,
    semilinearGaloisExtensionDifference_inv_apply, semilinearGaloisConjugate_apply,
    RingEquiv.symm_apply_apply]

/-- Every character with commutative target is independent of the chosen lift.
@isnad1 id=eq.2h8v.s10.d0dae98c9586 from=translated src=- shape=e2b74853 vocab=cfb015f8
-/
theorem map_semilinearGaloisConjugate_eq {A : Type*} [CommGroup A]
    (f : Gal(Ω/K) →* A) (τ : K ≃+* K) (e e' : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (he' : ∀ k : K, e' (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (σ : Gal(Ω/K)) :
    f (semilinearGaloisConjugate τ e' he' σ) =
      f (semilinearGaloisConjugate τ e he σ) := by
  rw [semilinearGaloisConjugate_eq_inner τ e e' he he', map_mul, map_mul, map_inv,
    mul_right_comm, mul_inv_cancel, one_mul]

end KummerTheory
