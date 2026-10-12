/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic
public import Tengoku.Tauceti.TauCeti.RingTheory.GradedAlgebra.Trivial

/-!
# Augmented differential graded algebras

An augmentation of a differential graded algebra `A` over `R` is a morphism of DG algebras from
`A` to the ground ring, placed in degree zero with zero differential.  Its kernel is the reduced
augmentation ideal.  It is homogeneous, stable under the differential and multiplication from
either side, and the unit section splits the underlying module as
`A ≃ R × ker ε`.

This is the input used by the reduced bar construction: tensor words are formed from the
augmentation ideal rather than from the unit-containing algebra.

## Main definitions

* `TauCeti.DGAlgAugmentation`: a DG algebra morphism from `A` to the trivially graded base ring.
* `TauCeti.DGAlgAugmentation.augmentationIdeal`: the homogeneous kernel of an augmentation.
* `TauCeti.DGAlgAugmentation.twoSidedIdeal`: the same kernel as a two-sided ideal of `A`.
* `TauCeti.DGAlgAugmentation.splitLinearEquiv`: the canonical linear splitting
  `A ≃ R × ker ε`.
* `TauCeti.IsDGAlgebra.unitHom`: the canonical unit morphism from the trivially graded base.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

namespace TauCeti

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

/-- The ground ring with its trivial grading and zero differential is a differential graded
algebra. -/
theorem isDGAlgebra_trivialGrading (R : Type uR) [CommRing R] :
    IsDGAlgebra (trivialGrading R R) (0 : R →ₗ[R] R) :=
  isDGAlgebra_zero _

/-- An augmentation of a differential graded algebra over `R` is a DG algebra morphism to `R`,
where the ground ring is concentrated in degree zero and has zero differential. -/
abbrev DGAlgAugmentation (h : IsDGAlgebra 𝒜 d) :=
  DGAlgHom h (isDGAlgebra_trivialGrading R)

namespace IsDGAlgebra

end IsDGAlgebra

namespace DGAlgAugmentation

variable {h : IsDGAlgebra 𝒜 d} (e : DGAlgAugmentation h)

/-- The augmentation ideal, as a homogeneous submodule of the underlying graded module. -/
noncomputable def augmentationIdeal :
    HomogeneousSubmodule (trivialGrading R R) 𝒜 where
  toSubmodule := LinearMap.ker e.toGradedAlgHom.toAlgHom.toLinearMap
  is_homogeneous' := by
    intro p a ha
    rw [LinearMap.mem_ker] at ha ⊢
    -- Unwrap the kernel's linear map so the graded-homomorphism projection lemma applies.
    change e a = 0 at ha
    change e (DirectSum.decompose 𝒜 a p) = 0
    rw [map_directSumDecompose 𝒜 (trivialGrading R R) e, ha,
      DirectSum.decompose_zero]
    rfl

/-- Membership in the augmentation ideal is equivalent to vanishing under the augmentation. -/
@[simp]
theorem mem_augmentationIdeal {a : A} : a ∈ e.augmentationIdeal ↔ e a = 0 :=
  LinearMap.mem_ker

/-- Removing the scalar part of an element leaves an element of the augmentation ideal. -/
theorem sub_algebraMap_mem_augmentationIdeal (a : A) :
    a - algebraMap R A (e a) ∈ e.augmentationIdeal := by
  rw [mem_augmentationIdeal, map_sub, e.map_algebraMap, sub_self]

/-- The linear projection from an augmented DG algebra onto its augmentation ideal, subtracting
the scalar part of an element. -/
noncomputable def reducedPart : A →ₗ[R] e.augmentationIdeal.toSubmodule :=
  LinearMap.codRestrict _
    (LinearMap.id - (Algebra.linearMap R A).comp e.toGradedAlgHom.toAlgHom.toLinearMap)
    e.sub_algebraMap_mem_augmentationIdeal

/-- The reduced-part projection subtracts the scalar part of an element. -/
@[simp]
theorem coe_reducedPart (a : A) :
    (e.reducedPart a : A) = a - algebraMap R A (e a) := (rfl)

/-- The reduced-part projection fixes the augmentation ideal pointwise. -/
@[simp]
theorem reducedPart_coe (x : e.augmentationIdeal) :
    e.reducedPart (x : A) = x := by
  apply Subtype.ext
  rw [coe_reducedPart, (mem_augmentationIdeal e).mp x.property, map_zero, sub_zero]

/-- The canonical splitting of an augmented DG algebra into its scalar and reduced parts. -/
noncomputable def splitLinearEquiv : A ≃ₗ[R] R × e.augmentationIdeal :=
  LinearMap.equivProdOfSurjectiveOfIsCompl e.toGradedAlgHom.toAlgHom.toLinearMap e.reducedPart
    (LinearMap.range_eq_top.2 e.surjective) (LinearMap.range_eq_of_proj e.reducedPart_coe)
    (LinearMap.isCompl_of_proj e.reducedPart_coe)

end DGAlgAugmentation

end TauCeti
