/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.Seed.RingTheory.Smooth.Kaehler

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A split residue map gives a conormal injection

**Status:** proved for arbitrary commutative base, source and residue algebras with an actual
algebra section. Mathlib supplies the conormal retraction from the section modulo the squared
kernel. Named consumer: the actual smooth curve stalk cotangent bound.

These are ACF dimension-one results. Projective presentation, joint regularity of extended
rational families, rational-action regularization and the full original classifier remain
owed. Original group/chunk/six-point statements, algebraization/descent and every true
bypassed auxiliary remain obligations. All eight original #21 work items and the full durable
goal remain active and incomplete.

CurveCompletion now constructs the actual proper-normal dimension-one model and the ORIGINAL
smooth separated ACF curve's open embedding internally. Its actual connected-group consumer
derives smoothness and extends every original-group scheme automorphism uniquely. Projective
presentation and jointly regular extended families remain separate obligations (#21).
-/

namespace AclGeom.SmoothCurveStalks
noncomputable section
open scoped TensorProduct
universe u v w

/-- An actual algebra section makes the conormal-to-differential map injective.
Named consumer: the cotangent bound at an actual smooth curve's closed point.
@isnad1 id=injectiv.2h4v.s10.fd0c3a0b9306 from=translated src=- shape=62e874c1 vocab=b351064d
-/
theorem kerCotangentToTensor_injective_of_section
    {k : Type u} {R : Type v} {S : Type w}
    [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    (hsurj : Function.Surjective (algebraMap R S))
    (σ : S →ₐ[k] R) (hσ : (IsScalarTower.toAlgHom k R S).comp σ = AlgHom.id k S) :
    Function.Injective (KaehlerDifferential.kerCotangentToTensor k R S) := by
  let f := IsScalarTower.toAlgHom k R S
  let g : S →ₐ[k] R ⧸ (RingHom.ker (algebraMap R S)) ^ 2 :=
    (Ideal.Quotient.mkₐ k _).comp σ
  have hg : f.kerSquareLift.comp g = AlgHom.id k S := by
    ext x
    change f.kerSquareLift (Ideal.Quotient.mk _ (σ x)) = x
    rw [AlgHom.kerSquareLift_mk]
    exact AlgHom.congr_fun hσ x
  obtain ⟨l, hl⟩ :=
    (retractionKerCotangentToTensorEquivSection (R := k) (P := R) (S := S) hsurj).symm ⟨g, hg⟩
  exact (show Function.LeftInverse l (KaehlerDifferential.kerCotangentToTensor k R S) from
    fun x ↦ LinearMap.congr_fun hl x).injective

end
end AclGeom.SmoothCurveStalks
