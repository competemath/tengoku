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

/--
@isnad1 id=eq.1h5v.s9.d48a5cbdfebf from=translated src=- shape=ada12325 vocab=5139189f
-/
theorem aFourPrefixes_gram {X : Type*} [AddCommGroup X] [Module ℚ X]
    (B : LinearMap.BilinForm ℚ X) (r : Fin 4 → X)
    (hgram : ∀ i j, B (r i) (r j) = (gramA 4 i j : ℚ)) (i j : Fin 4) :
    B (aFourPrefixes r i) (aFourPrefixes r j) = if i = j then 2 else 1 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [aFourPrefixes, map_add, LinearMap.add_apply, hgram, gramA, gramAEntry]

/--
@isnad1 id=mem.1h4v.s6.59143586b02c from=translated src=- shape=e6202b56 vocab=a05841fb
-/
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

/--
@isnad1 id=eq.1h5v.s9.23992f3f743a from=translated src=- shape=90bddf82 vocab=aa61b81a
-/
theorem aFourPrefixes_orthogonal {X : Type*} [AddCommGroup X] [Module ℚ X]
    (B : LinearMap.BilinForm ℚ X) (r : Fin 4 → X) (x : X)
    (hr : ∀ i, B (r i) x = 0) (i : Fin 4) : B (aFourPrefixes r i) x = 0 := by
  fin_cases i <;> simp [aFourPrefixes, map_add, LinearMap.add_apply, hr]

end SRG266.Lattice
