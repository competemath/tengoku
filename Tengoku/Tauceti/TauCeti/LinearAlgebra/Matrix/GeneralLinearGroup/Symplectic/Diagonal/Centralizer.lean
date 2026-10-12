/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Basic
import Tengoku.Tauceti.TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The centralizer of the symplectic diagonal torus

The diagonal symplectic matrices are exactly the image of the paired diagonal homomorphism.
Over a domain with a unit different from its inverse, this image is its own centralizer, hence
maximal among commutative subgroups. In particular these conclusions hold over every infinite
field, in all characteristics and in every rank.

This pointwise centralizer calculation supplies the matrix comparison used to prove maximality
of the diagonal torus as a closed subgroup scheme. The unit hypothesis distinguishes the two
weights on each symplectic plane; it cannot simply be omitted over small finite fields.

## References

* The general-linear centralizer formalization in
  `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic`.
* J. E. Humphreys, *Linear Algebraic Groups*, §16.1 and §26.3.
-/

public section

open Matrix

namespace TauCeti.GLSymplecticFin

variable {m : ℕ} {R : Type*}

/-- A unit different from its inverse lets paired diagonal coordinates separate any two
positions. -/
theorem exists_diagonalCoordinates_ne [Monoid R] (u : Rˣ) (hu : u ≠ u⁻¹)
    {i j : Fin (m + m)} (hij : i ≠ j) :
    ∃ t : Fin m → Rˣ, diagonalCoordinates t i ≠ diagonalCoordinates t j := by
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hu (inv_one.symm)
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;>
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
  · have h : i ≠ j := fun h => hij (by simp [h])
    exact ⟨fun k => if k = i then u else 1, by simp [Ne.symm h, hu1]⟩
  · refine ⟨fun k => if k = i then u else 1, ?_⟩
    by_cases h : j = i <;> simp [Fin.natAdd_eq_addNat, h, hu, hu1]
  · refine ⟨fun k => if k = j then u else 1, ?_⟩
    by_cases h : i = j <;> simp [Fin.natAdd_eq_addNat, h, Ne.symm hu, Ne.symm hu1]
  · have h : i ≠ j := fun h => hij (by simp [h])
    exact ⟨fun k => if k = i then u else 1, by
      simp [Fin.natAdd_eq_addNat, Ne.symm h, hu1]⟩

section Domain

variable [CommRing R] [IsCancelMulZero R]

end Domain

section InfiniteField

variable [Field R] [Infinite R]

end InfiniteField

end TauCeti.GLSymplecticFin
