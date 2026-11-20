/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEGram
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.IntegerCoordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Even
import Tengoku.Seed.LinearAlgebra.Matrix.BilinearForm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice.E6Cartan

open scoped BigOperators

def form : LinearMap.BilinForm ℚ (Fin 6 → ℚ) :=
  Matrix.toBilin' (fun i j => (gramE 6 i j : ℚ))

def weight : Fin 6 → ℚ := ![4/3, 5/3, 2, 4/3, 2/3, 1]

theorem three_smul_weight_mem : (3 : ℤ) • weight ∈ coordinateIntegerLattice 6 := by
  refine mem_coordinateIntegerLattice.mpr ⟨![4, 5, 6, 4, 2, 3], ?_⟩
  intro i
  fin_cases i <;> norm_num [weight, zsmul_eq_mul]

theorem weight_order (m : ℤ) :
    m • weight ∈ coordinateIntegerLattice 6 ↔ 3 ∣ m := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := mem_coordinateIntegerLattice.mp h
    have h := hz 0
    change (z 0 : ℚ) = m • (4/3 : ℚ) at h
    rw [zsmul_eq_mul] at h
    have heq : (3 : ℚ) * z 0 = 4 * m := by linarith
    have heqZ : 3 * z 0 = 4 * m := by exact_mod_cast heq
    omega
  · rintro ⟨k, rfl⟩
    have h : (3*k) • weight = k • ((3 : ℤ) • weight) := by module
    rw [h]
    exact Submodule.smul_mem _ k three_smul_weight_mem

end SRG266.Lattice.E6Cartan
