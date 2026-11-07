/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Seed.Data.Complex.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Projective representations and concrete `ℂˣ`-valued 2-cocycles

This file introduces a concrete notion of projective representation for matrix-valued
virtual symmetries:

* `ScalarCocycle G` is a function `G × G → ℂˣ` (implemented as `Units ℂ`).
* `ProjectiveRepresentation ω` is a map `X : G → GL(D, ℂ)` satisfying
  `X g * X h = ω g h • X (g * h)` at the matrix level.
* `ProjectiveRepresentation.cocycle_of_assoc` derives the standard 2-cocycle identity
  from associativity of matrix multiplication.

This is the concrete multiplicative cocycle used in MPS/SPT arguments.
-/

open scoped Matrix

namespace TNLean
namespace Algebra

/-- A concrete multiplicative scalar 2-cochain on a group.-/
abbrev ScalarCocycle (G : Type*) := G → G → Units ℂ

section Group

variable {G : Type*} [Group G]
variable {D : ℕ}

/-- A matrix-valued projective representation with factor system `ω`.-/
structure ProjectiveRepresentation (ω : ScalarCocycle G) where
  /-- Virtual action on the bond space.-/
  X : G → GL (Fin D) ℂ
  /-- Multiplication law up to the scalar cocycle.-/
  map_mul' :
    ∀ g h : G,
      ((X g : Matrix (Fin D) (Fin D) ℂ) * (X h : Matrix (Fin D) (Fin D) ℂ)) =
        (ω g h : ℂ) • (X (g * h) : Matrix (Fin D) (Fin D) ℂ)

namespace ProjectiveRepresentation

variable {ω : ScalarCocycle G} (ρ : ProjectiveRepresentation (D := D) ω)

/-- The projective multiplication law, restated as a lemma.
@isnad1 id=eq.0h6v.s7.ae6b5881cadb from=translated src=- shape=67dce3b4 vocab=bc1b2436
-/
lemma map_mul (g h : G) :
    ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) * (ρ.X h : Matrix (Fin D) (Fin D) ℂ)) =
      (ω g h : ℂ) • (ρ.X (g * h) : Matrix (Fin D) (Fin D) ℂ) :=
  ρ.map_mul' g h

/-- Left-associated triple product in terms of the cocycle.
@isnad1 id=eq.0h7v.s8.0aa5e0e92746 from=translated src=- shape=ab2cc8e1 vocab=bc1b2436
-/
lemma mul_assoc_left_scalar (g h k : G) :
    (((ρ.X g : Matrix (Fin D) (Fin D) ℂ) * (ρ.X h : Matrix (Fin D) (Fin D) ℂ)) *
        (ρ.X k : Matrix (Fin D) (Fin D) ℂ)) =
      ((ω g h : ℂ) * (ω (g * h) k : ℂ)) •
        (ρ.X ((g * h) * k) : Matrix (Fin D) (Fin D) ℂ) := by
  calc
    (((ρ.X g : Matrix (Fin D) (Fin D) ℂ) * (ρ.X h : Matrix (Fin D) (Fin D) ℂ)) *
        (ρ.X k : Matrix (Fin D) (Fin D) ℂ))
        = ((ω g h : ℂ) • (ρ.X (g * h) : Matrix (Fin D) (Fin D) ℂ)) *
            (ρ.X k : Matrix (Fin D) (Fin D) ℂ) := by rw [map_mul]
    _ = (ω g h : ℂ) •
          (((ρ.X (g * h) : Matrix (Fin D) (Fin D) ℂ) *
            (ρ.X k : Matrix (Fin D) (Fin D) ℂ))) := by
            simp
    _ = (ω g h : ℂ) • ((ω (g * h) k : ℂ) •
          (ρ.X ((g * h) * k) : Matrix (Fin D) (Fin D) ℂ)) := by rw [map_mul]
    _ = ((ω g h : ℂ) * (ω (g * h) k : ℂ)) •
          (ρ.X ((g * h) * k) : Matrix (Fin D) (Fin D) ℂ) := by simp [mul_smul]

/-- Right-associated triple product in terms of the cocycle.
@isnad1 id=eq.0h7v.s8.c3d16c15aaea from=translated src=- shape=1ba57604 vocab=bc1b2436
-/
lemma mul_assoc_right_scalar (g h k : G) :
    ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
        ((ρ.X h : Matrix (Fin D) (Fin D) ℂ) * (ρ.X k : Matrix (Fin D) (Fin D) ℂ))) =
      ((ω g (h * k) : ℂ) * (ω h k : ℂ)) •
        (ρ.X (g * (h * k)) : Matrix (Fin D) (Fin D) ℂ) := by
  calc
    ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
        ((ρ.X h : Matrix (Fin D) (Fin D) ℂ) * (ρ.X k : Matrix (Fin D) (Fin D) ℂ)))
        = (ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
            ((ω h k : ℂ) • (ρ.X (h * k) : Matrix (Fin D) (Fin D) ℂ)) := by rw [map_mul]
    _ = (ω h k : ℂ) •
          ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
            (ρ.X (h * k) : Matrix (Fin D) (Fin D) ℂ)) := by
            simp
    _ = (ω h k : ℂ) • ((ω g (h * k) : ℂ) •
          (ρ.X (g * (h * k)) : Matrix (Fin D) (Fin D) ℂ)) := by rw [map_mul]
    _ = ((ω g (h * k) : ℂ) * (ω h k : ℂ)) •
          (ρ.X (g * (h * k)) : Matrix (Fin D) (Fin D) ℂ) := by
          simp [smul_smul, mul_comm]

/-- Scalar cancellation on an invertible matrix (requires a nonempty index set).
@isnad1 id=eq.3h4v.s7.239e5f966586 from=translated src=- shape=4c0edc8c vocab=c4b5848b
-/
lemma smul_eq_smul_cancel {a b : ℂ} {M : Matrix (Fin D) (Fin D) ℂ}
    (hD : 0 < D) (hM : IsUnit M) (h : a • M = b • M) : a = b := by
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  exact smul_left_injective ℂ hM.ne_zero h

/-- Associativity forces the cocycle condition (for `D > 0`).
@isnad1 id=eq.1h7v.s6.b82430fa580c from=translated src=- shape=14e7d918 vocab=09029e63
-/
theorem cocycle_of_assoc (ρ : ProjectiveRepresentation (D := D) ω) (hD : 0 < D) (g h k : G) :
    (ω g h : ℂ) * (ω (g * h) k : ℂ) = (ω g (h * k) : ℂ) * (ω h k : ℂ) := by
  have hAssoc :
      (((ρ.X g : Matrix (Fin D) (Fin D) ℂ) * (ρ.X h : Matrix (Fin D) (Fin D) ℂ)) *
          (ρ.X k : Matrix (Fin D) (Fin D) ℂ)) =
        ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
          ((ρ.X h : Matrix (Fin D) (Fin D) ℂ) * (ρ.X k : Matrix (Fin D) (Fin D) ℂ))) := by
    simp [Matrix.mul_assoc]
  have hLeft := ρ.mul_assoc_left_scalar g h k
  have hRight := ρ.mul_assoc_right_scalar g h k
  have hScalars :
      ((ω g h : ℂ) * (ω (g * h) k : ℂ)) •
          (ρ.X ((g * h) * k) : Matrix (Fin D) (Fin D) ℂ) =
        ((ω g (h * k) : ℂ) * (ω h k : ℂ)) •
          (ρ.X (g * (h * k)) : Matrix (Fin D) (Fin D) ℂ) := by
    calc
      ((ω g h : ℂ) * (ω (g * h) k : ℂ)) •
          (ρ.X ((g * h) * k) : Matrix (Fin D) (Fin D) ℂ)
          = (((ρ.X g : Matrix (Fin D) (Fin D) ℂ) * (ρ.X h : Matrix (Fin D) (Fin D) ℂ)) *
              (ρ.X k : Matrix (Fin D) (Fin D) ℂ)) := hLeft.symm
      _ = ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
            ((ρ.X h : Matrix (Fin D) (Fin D) ℂ) * (ρ.X k : Matrix (Fin D) (Fin D) ℂ))) :=
            hAssoc
      _ = ((ω g (h * k) : ℂ) * (ω h k : ℂ)) •
            (ρ.X (g * (h * k)) : Matrix (Fin D) (Fin D) ℂ) := hRight
  have hScalars' :
      ((ω g h : ℂ) * (ω (g * h) k : ℂ)) •
          (ρ.X ((g * h) * k) : Matrix (Fin D) (Fin D) ℂ) =
        ((ω g (h * k) : ℂ) * (ω h k : ℂ)) •
          (ρ.X ((g * h) * k) : Matrix (Fin D) (Fin D) ℂ) := by
    simpa [mul_assoc] using hScalars
  exact smul_eq_smul_cancel (D := D) hD (hM := by
      refine ⟨ρ.X ((g * h) * k), rfl⟩) hScalars'

end ProjectiveRepresentation

end Group

end Algebra
end TNLean
