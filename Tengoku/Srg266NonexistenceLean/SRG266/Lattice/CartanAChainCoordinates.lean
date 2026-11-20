/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CoordinateRootStar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

def aFourPrefixes {X : Type*} [Add X] (r : Fin 4 → X) : Fin 4 → X :=
  ![r 0, r 0+r 1, r 0+r 1+r 2, r 0+r 1+r 2+r 3]

theorem aFourPrefixes_gram {X : Type*} [AddCommGroup X] [Module ℚ X]
    (B : LinearMap.BilinForm ℚ X) (r : Fin 4 → X)
    (hgram : ∀ i j, B (r i) (r j) = (gramA 4 i j : ℚ)) (i j : Fin 4) :
    B (aFourPrefixes r i) (aFourPrefixes r j) = if i = j then 2 else 1 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [aFourPrefixes, map_add, LinearMap.add_apply, hgram, gramA, gramAEntry]

theorem aFourPrefixes_mem {X : Type*} [AddCommGroup X] [Module ℤ X]
    (L : Submodule ℤ X) (r : Fin 4 → X) (hr : ∀ i, r i ∈ L) (i : Fin 4) :
    aFourPrefixes r i ∈ L := by
  have h01 := L.add_mem (hr 0) (hr 1)
  have h012 := L.add_mem h01 (hr 2)
  have h0123 := L.add_mem h012 (hr 3)
  fin_cases i
  · simpa [aFourPrefixes] using hr 0
  · simpa [aFourPrefixes] using h01
  · simpa [aFourPrefixes] using h012
  · simpa [aFourPrefixes] using h0123

theorem aFourPrefixes_orthogonal {X : Type*} [AddCommGroup X] [Module ℚ X]
    (B : LinearMap.BilinForm ℚ X) (r : Fin 4 → X) (x : X)
    (hr : ∀ i, B (r i) x = 0) (i : Fin 4) : B (aFourPrefixes r i) x = 0 := by
  fin_cases i <;> simp [aFourPrefixes, map_add, LinearMap.add_apply, hr]

end SRG266.Lattice
