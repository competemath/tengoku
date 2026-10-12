/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.LinearAlgebra.Matrix.Dual
public import Tengoku

/-!
# Euclidean duals of linear codes

A linear code on a finite coordinate type is a submodule of the corresponding function space.
Its Euclidean dual consists of the words whose dot product with every codeword vanishes. This
file gives that construction its order-theoretic API and proves that dot-product duality is an
involution over a field. In particular, the dimensions of a code and its dual add to the number
of coordinates, and over a finite field their cardinalities multiply to the cardinality of the
whole word space.

The dot-product convention and the resulting Euclidean dual follow Huffman and Pless,
*Fundamentals of Error-Correcting Codes*, §§1.2–1.4.
-/

public section

namespace Submodule

open Matrix Module
open LinearMap (BilinForm)
open TauCeti

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- The Euclidean dual of a linear code: its orthogonal complement for the standard dot product. -/
def euclideanDual (C : _root_.Submodule R (ι → R)) : _root_.Submodule R (ι → R) :=
  LinearMap.BilinForm.orthogonal (dotProductBilin R R) C

/-- Membership in the Euclidean dual means having zero dot product with every codeword. -/
@[simp]
theorem mem_euclideanDual {C : _root_.Submodule R (ι → R)} {y : ι → R} :
    y ∈ euclideanDual C ↔ ∀ x ∈ C, x ⬝ᵥ y = 0 := by
  simp only [euclideanDual, LinearMap.BilinForm.mem_orthogonal_iff,
    dotProductBilin_apply_apply]

/-- Membership in the Euclidean dual can equivalently put the codeword on the right. -/
theorem mem_euclideanDual' {C : _root_.Submodule R (ι → R)} {y : ι → R} :
    y ∈ euclideanDual C ↔ ∀ x ∈ C, y ⬝ᵥ x = 0 := by
  rw [mem_euclideanDual]
  constructor <;> intro h x hx <;> simpa only [dotProduct_comm] using h x hx

/-- A word is dual to a generated code exactly when it is orthogonal to every generator. -/
@[simp high]
theorem mem_euclideanDual_span {s : Set (ι → R)} {y : ι → R} :
    y ∈ euclideanDual (Submodule.span R s) ↔ ∀ ⦃x⦄, x ∈ s → x ⬝ᵥ y = 0 := by
  simp only [euclideanDual, LinearMap.BilinForm.orthogonal, Submodule.mem_orthogonalBilin_span,
    dotProductBilin_apply_apply]

/-- The dual of the zero code is the whole word space. -/
@[simp]
theorem euclideanDual_bot_eq_top :
    euclideanDual (⊥ : Submodule R (ι → R)) = ⊤ :=
  by simp [euclideanDual]

/-- Euclidean duality reverses inclusion. -/
theorem euclideanDual_antitone : Antitone (euclideanDual (R := R) (ι := ι)) :=
  fun _ _ h ↦ LinearMap.BilinForm.orthogonal_le h

/-- Orthogonality of two codes is symmetric. -/
theorem le_euclideanDual_comm {C D : Submodule R (ι → R)} :
    C ≤ euclideanDual D ↔ D ≤ euclideanDual C := by
  have hflip :
      (dotProductBilin R R : BilinForm R (ι → R)).flip = dotProductBilin R R :=
    LinearMap.BilinForm.isSymm_iff_flip.mp
      (isSymm_dotProductBilin (R := R) (ι := ι))
  simpa only [euclideanDual, LinearMap.BilinForm.orthogonal, hflip] using
    (Submodule.le_orthogonalBilin_flip_iff_le_orthogonalBilin
      (B := dotProductBilin R R) (S := C) (T := D))

/-- A code is self-orthogonal exactly when any two of its words have zero dot product. -/
theorem le_euclideanDual_self_iff {C : Submodule R (ι → R)} :
    C ≤ euclideanDual C ↔ ∀ x ∈ C, ∀ y ∈ C, x ⬝ᵥ y = 0 := by
  constructor
  · intro h x hx y hy
    exact mem_euclideanDual.mp (h hy) x hx
  · intro h y hy
    rw [mem_euclideanDual]
    exact fun x hx ↦ h x hx y hy

/-- The Euclidean dual of a sum is the intersection of the Euclidean duals. -/
@[simp]
theorem euclideanDual_sup (C D : Submodule R (ι → R)) :
    euclideanDual (C ⊔ D) = euclideanDual C ⊓ euclideanDual D := by
  simp only [euclideanDual, LinearMap.BilinForm.orthogonal]
  exact Submodule.orthogonalBilin_sup (B := dotProductBilin R R) C D

section Field

variable {K : Type*} [Field K]

end Field

end Submodule
