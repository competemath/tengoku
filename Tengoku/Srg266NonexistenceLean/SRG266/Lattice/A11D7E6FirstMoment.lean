/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.A11D7E6A11Transport
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.A11D7E6E6Transport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

def a11D7E6A11PartLinear : (Fin 24 → ℚ) →ₗ[ℚ] (Fin 11 → ℚ) where
  toFun := a11D7E6A11Part
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def a11D7E6E6PartLinear : (Fin 24 → ℚ) →ₗ[ℚ] (Fin 6 → ℚ) where
  toFun := a11D7E6E6Part
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {W U Y : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]
  [AddCommGroup Y] [Module ℚ Y]

/--
@isnad1 id=eq.2h7v.s10.ff1e24ba44ac from=translated src=- shape=84c95d10 vocab=c0d8f842
-/
theorem sum_common_marked_projection_zero {ι : Type*} [Fintype ι]
    (P : ((W × (Fin 7 → ℚ)) × U) →ₗ[ℚ] Y) (g : ι → W) (s : Fin 7 → ℚ)
    (hsum : (∑ i, g i) = 0) (hP : P (middleCoordinateInclusion 7 s) = 0) :
    (∑ i, P ((g i, s), 0)) = 0 := by
  let I : W →ₗ[ℚ] ((W × (Fin 7 → ℚ)) × U) :=
    (LinearMap.inl ℚ (W × (Fin 7 → ℚ)) U).comp (LinearMap.inl ℚ W (Fin 7 → ℚ))
  have hsplit (i) : ((g i, s), (0 : U)) = I (g i)+middleCoordinateInclusion 7 s := by
    simp [I, middleCoordinateInclusion]
  simp_rw [hsplit, map_add, hP, add_zero]
  change (∑ i, (P.comp I) (g i)) = 0
  rw [← map_sum, hsum, map_zero]

end SRG266.Lattice
