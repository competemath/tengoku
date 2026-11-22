/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.P1.BaseChange
import Tengoku.LanaBelyi.Belyi.P1.Points

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Base change of the marked points of the projective line

The base-change morphism `Belyi.P1.mapOfAlgebra k₀ K : P1 K ⟶ P1 k₀` (from
`Belyi/P1/BaseChange.lean`) acts on the underlying space by `ProjectiveSpectrum.comap`,
i.e. by contracting homogeneous prime ideals along the coefficient map
`k₀[X₀,X₁] → K[X₀,X₁]`. This file records that it sends each marked point of `ℙ¹_K` to the
corresponding marked point of `ℙ¹_{k₀}` (taxis issue #110, split out of #82). These are the
naturality facts consumed by the pair version of B3 (#48) and by the marked-curve API (#54).

## Main results

* `Belyi.P1.mapOfAlgebra_base_zero`, `Belyi.P1.mapOfAlgebra_base_one`,
  `Belyi.P1.mapOfAlgebra_base_infty`: the base-change morphism sends `0 ↦ 0`, `1 ↦ 1`,
  `∞ ↦ ∞`.

The computations reduce, via `ProjectiveSpectrum.comap`, to contractions of principal
homogeneous ideals `Ideal.comap (MvPolynomial.map (algebraMap k₀ K)) (span {g_K}) =
span {g_{k₀}}` for the linear forms `g = X₀, X₀ - X₁, X₁`. The supporting divisibility
lemmas `MvPolynomial.monomial_one_dvd_iff_forall_coeff`,
`MvPolynomial.monomial_one_dvd_map_iff` and `MvPolynomial.X_dvd_map_iff` are stated in the
`MvPolynomial` namespace as upstream candidates.
-/

universe u

namespace MvPolynomial

variable {σ : Type*} {R S : Type*} [CommRing R] [CommRing S]

/-- `x` is divisible by `monomial s 1` iff every coefficient at a multi-index not `≥ s`
vanishes.
@isnad1 id=iff.0h4v.s8.22f6923d2794 from=translated src=- shape=44b03ea2 vocab=c2e1fdf4
-/
lemma monomial_one_dvd_iff_forall_coeff (x : MvPolynomial σ R) (s : σ →₀ ℕ) :
    (monomial s 1) ∣ x ↔ ∀ d, ¬ s ≤ d → coeff d x = 0 := by
  rw [monomial_one_dvd_iff_modMonomial_eq_zero, MvPolynomial.ext_iff]
  simp only [coeff_zero]
  constructor
  · intro h d hd
    rw [← coeff_modMonomial_of_not_le x hd]
    exact h d
  · intro h d
    by_cases hd : s ≤ d
    · exact coeff_modMonomial_of_le x hd
    · rw [coeff_modMonomial_of_not_le x hd]; exact h d hd

/-- Divisibility by a monomial `monomial s 1` is reflected and preserved by an injective
coefficient extension.
@isnad1 id=iff.1h6v.s9.b9afa3b54a7d from=translated src=- shape=8bd2fce4 vocab=7c337303
-/
lemma monomial_one_dvd_map_iff {φ : R →+* S} (hφ : Function.Injective φ)
    (s : σ →₀ ℕ) (p : MvPolynomial σ R) :
    (monomial s 1 : MvPolynomial σ S) ∣ MvPolynomial.map φ p ↔
      (monomial s 1 : MvPolynomial σ R) ∣ p := by
  rw [monomial_one_dvd_iff_forall_coeff, monomial_one_dvd_iff_forall_coeff]
  refine forall_congr' fun d => imp_congr_right fun _ => ?_
  rw [coeff_map, map_eq_zero_iff φ hφ]

/-- Divisibility by `X i` is reflected and preserved by an injective coefficient
extension.
@isnad1 id=iff.1h6v.s8.6aa6429a37ce from=translated src=- shape=7c5f2351 vocab=4c13bf11
-/
lemma X_dvd_map_iff {φ : R →+* S} (hφ : Function.Injective φ) (i : σ)
    (p : MvPolynomial σ R) :
    (X i : MvPolynomial σ S) ∣ MvPolynomial.map φ p ↔ (X i : MvPolynomial σ R) ∣ p := by
  simpa only [X] using monomial_one_dvd_map_iff hφ (Finsupp.single i 1) p

end MvPolynomial

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial ProjectiveSpectrum

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K]

/-- The shear automorphism `X₀ ↦ X₀ + X₁, X₁ ↦ X₁` of `R[X₀, X₁]`, used to reduce
divisibility by the linear form `X₀ - X₁` to divisibility by `X₀`. -/
noncomputable def shear (R : Type u) [CommRing R] :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval ![X 0 + X 1, X 1]

/-- The inverse shear `X₀ ↦ X₀ - X₁, X₁ ↦ X₁`. -/
noncomputable def shearInv (R : Type u) [CommRing R] :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval ![X 0 - X 1, X 1]

/--
@isnad1 id=eq.0h1v.s9.8eb7d3a1d817 from=translated src=- shape=485a251d vocab=10f4c12d
-/
@[simp] lemma shear_X0 (R : Type u) [CommRing R] : shear R (X 0) = X 0 + X 1 := by simp [shear]

/--
@isnad1 id=eq.0h1v.s8.29e6373e0c35 from=translated src=- shape=11c5ff65 vocab=1e4f2f50
-/
@[simp] lemma shear_X1 (R : Type u) [CommRing R] : shear R (X 1) = X 1 := by simp [shear]

/--
@isnad1 id=eq.0h1v.s9.078a2bb6eb76 from=translated src=- shape=7e6f8209 vocab=7a19df5b
-/
lemma shear_X0_sub_X1 (R : Type u) [CommRing R] : shear R (X 0 - X 1) = X 0 := by simp [shear]

/--
@isnad1 id=eq.0h2v.s9.25f172b39c62 from=translated src=- shape=6ce452d9 vocab=0f2e8ab6
-/
lemma shearInv_shear (R : Type u) [CommRing R] (p : MvPolynomial (Fin 2) R) :
    shearInv R (shear R p) = p := by
  have h : (shearInv R).comp (shear R) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [shear, shearInv, sub_add_cancel]
  exact congrArg (fun f => f p) h

/-- The shear commutes with the coefficient extension `k₀[X₀,X₁] → K[X₀,X₁]`.
@isnad1 id=eq.0h3v.s10.5ce400080bab from=translated src=- shape=f4c8c2c8 vocab=b44a2877
-/
lemma map_shear (p : MvPolynomial (Fin 2) k₀) :
    MvPolynomial.map (algebraMap k₀ K) (shear k₀ p) =
      shear K (MvPolynomial.map (algebraMap k₀ K) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [shear, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      congr 1
      fin_cases i <;> simp

/-- Divisibility by the linear form `X₀ - X₁` is reflected and preserved by the coefficient
extension `k₀[X₀,X₁] → K[X₀,X₁]`.
@isnad1 id=iff.0h3v.s9.6db5609ce659 from=translated src=- shape=fddd0acc vocab=a4b196d4
-/
lemma X0_sub_X1_dvd_map_iff (p : MvPolynomial (Fin 2) k₀) :
    (X 0 - X 1 : MvPolynomial (Fin 2) K) ∣ MvPolynomial.map (algebraMap k₀ K) p ↔
      (X 0 - X 1 : MvPolynomial (Fin 2) k₀) ∣ p := by
  constructor
  · intro h
    -- shear turns `X₀ - X₁` into `X₀`, and commutes with the coefficient extension
    have h1 : (X 0 : MvPolynomial (Fin 2) K) ∣
        shear K (MvPolynomial.map (algebraMap k₀ K) p) := by
      rw [← shear_X0_sub_X1 K]; exact map_dvd _ h
    rw [← map_shear, X_dvd_map_iff (algebraMap k₀ K).injective] at h1
    have h2 := map_dvd (shearInv k₀) h1
    rwa [shearInv_shear, show shearInv k₀ (X 0) = X 0 - X 1 by simp [shearInv]] at h2
  · intro h
    have hg : MvPolynomial.map (algebraMap k₀ K) (X 0 - X 1) =
        (X 0 - X 1 : MvPolynomial (Fin 2) K) := by simp
    rw [← hg]; exact map_dvd _ h

end Belyi.P1
