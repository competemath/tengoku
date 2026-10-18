/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.P1.AffineChart
import Tengoku.Seed.RingTheory.Jacobson.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Points of `ℙ¹` attached to transcendental elements are not closed

The non-constancy input (c) to B1 (taxis issue #46): for a field extension `K/k` and
`t : K` transcendental over `k`, the image of the `K`-valued point
`P1.point k t : Spec K ⟶ P1 k` is not a closed point of `ℙ¹`.

The proof avoids the chart isomorphism `(k[X₀,X₁]_{X₁})₀ ≃ k[t]`: the image point lies
in the chart `Spec (k[X₀,X₁]_{X₁})₀` and its prime is `ker (awayEval k t)`. If it were
closed, the kernel would be maximal (`PrimeSpectrum.isClosed_singleton_iff_isMaximal`,
transported along the open immersion `Proj.awayι` by continuity), so the residue ring —
a finite-type `k`-algebra which is a field — would be finite over `k` by Zariski's
lemma (`finite_of_finite_type_of_isJacobsonRing`). But `t` is the image of the degree-1
fraction `X₀/X₁` (`Belyi.P1.affineCoord`), hence would be algebraic over `k`.

## Main definitions

* `Belyi.P1.awayEvalₐ`: `awayEval` as a `k`-algebra homomorphism (for the scoped
  `k`-algebra structure on the chart ring).
* `Belyi.P1.affineCoord`: the affine coordinate `X₀/X₁` in the chart ring, with
  `awayEval k t (affineCoord k) = t`.
* `Belyi.P1.not_isClosed_singleton_point_of_transcendental`: the main statement.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

section AlgebraStructure

variable (k : Type u) [CommRing k]

/-- The chart ring `(k[X₀,X₁]_{X₁})₀` as a `k`-algebra, through the identification of
`k` with the degree-zero part of the grading. -/
noncomputable scoped instance instAlgebraAway :
    Algebra k (Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k)) :=
  ((fromZeroRingHom (P1Grading k) (Submonoid.powers (X 1 : MvPolynomial (Fin 2) k))).comp
    (algebraMap k (P1Grading k 0))).toAlgebra

variable {R : Type u} [CommRing R] [Algebra k R]

/-- The evaluation of the chart ring at `t` as a `k`-algebra homomorphism. -/
noncomputable def awayEvalₐ (t : R) :
    Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k) →ₐ[k] R :=
  { awayEval k t with
    commutes' := fun c => by
      have h := awayEval_fromZeroRingHom k t (algebraMap k (P1Grading k 0) c)
      simp only [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq, aeval_C] at h
      exact h }

@[simp]
lemma awayEvalₐ_toRingHom (t : R) : (awayEvalₐ k t : _ →+* R) = awayEval k t := rfl

/-- The affine coordinate `X₀/X₁` of the standard chart, as an element of the chart
ring. -/
noncomputable def affineCoord : Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k) :=
  HomogeneousLocalization.mk
    ⟨1, ⟨X 0, X_mem_P1Grading k 0⟩, ⟨X 1, X_mem_P1Grading k 1⟩, 1, pow_one _⟩

/-- Evaluation at `t` sends the affine coordinate to `t`. -/
lemma awayEval_affineCoord (t : R) : awayEval k t (affineCoord k) = t := by
  have hv : ((aeval ![t, 1] : MvPolynomial (Fin 2) k →ₐ[k] R) :
      MvPolynomial (Fin 2) k →+* R) (X 1) * 1 = 1 := by simp
  have hval : (affineCoord k).val =
      Localization.mk (X 0 : MvPolynomial (Fin 2) k)
        (⟨X 1 ^ 1, 1, rfl⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 2) k)) := by
    rw [affineCoord, val_mk]
    congr 1
    exact Subtype.ext (pow_one _).symm
  rw [awayEval, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, hval,
    Localization.awayLift_mk (v := 1) (hv := hv)]
  simp

/-- The chart ring is of finite type over `k`. -/
lemma finiteType_away : Algebra.FiniteType k
    (Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k)) := by
  have h1 : (fromZeroRingHom (P1Grading k)
      (Submonoid.powers (X 1 : MvPolynomial (Fin 2) k))).FiniteType :=
    HomogeneousLocalization.Away.finiteType (X 1) 1 (X_mem_P1Grading k 1)
  have h2 : (algebraMap k (P1Grading k 0)).FiniteType :=
    RingHom.FiniteType.of_surjective _ (gradeZeroEquiv k).surjective
  exact h1.comp h2

end AlgebraStructure

section Transcendental

variable (k : Type u) [Field k] {K : Type u} [Field K] [Algebra k K]

end Transcendental

end Belyi.P1
