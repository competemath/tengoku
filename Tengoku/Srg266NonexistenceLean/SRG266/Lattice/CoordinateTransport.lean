/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Glue
import Tengoku.Seed.LinearAlgebra.Matrix.BilinearForm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open Module
open scoped Matrix

section TransportLemmas

variable {X : Type*} [AddCommGroup X] [Module ℚ X] {n : ℕ}

def coordSum (b : Fin n → X) (v : Fin n → ℤ) : X := ∑ i, (v i : ℚ) • b i

theorem coordSum_eq_zsmul_sum (b : Fin n → X) (v : Fin n → ℤ) :
    coordSum b v = ∑ i, v i • b i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]

theorem coordSum_mem_span (b : Fin n → X) (v : Fin n → ℤ) :
    coordSum b v ∈ Submodule.span ℤ (Set.range b) := by
  rw [coordSum_eq_zsmul_sum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem coordSum_eq_zero {b : Fin n → X} (hli : LinearIndependent ℚ b) {v : Fin n → ℤ}
    (h : coordSum b v = 0) : v = 0 := by
  funext i
  have hz := Fintype.linearIndependent_iff.mp hli (fun i => (v i : ℚ)) h i
  exact_mod_cast hz

theorem toBilin'_coordSum {F : LinearMap.BilinForm ℚ X} (b : Fin n → X)
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : ∀ i j, ((A i j : ℤ) : ℚ) = F (b i) (b j))
    (v w : Fin n → ℤ) :
    ((Matrix.toBilin' A v w : ℤ) : ℚ) = F (coordSum b v) (coordSum b w) := by
  have hRHS : F (coordSum b v) (coordSum b w)
      = ∑ i, ∑ j, (v i : ℚ) * ((w j : ℚ) * F (b i) (b j)) := by
    rw [show coordSum b v = ∑ i, (v i : ℚ) • b i from rfl, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul,
      show coordSum b w = ∑ j, (w j : ℚ) • b j from rfl, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
  rw [hRHS, Matrix.toBilin'_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hA i j]
  ring

end TransportLemmas

end SRG266.Lattice
