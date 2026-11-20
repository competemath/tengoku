/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Discriminant
import Tengoku.Seed.Algebra.Module.LocalizedModule.Int
import Tengoku.Seed.LinearAlgebra.Dimension.Free
import Tengoku.Seed.LinearAlgebra.Matrix.DotProduct
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open Module
open scoped BigOperators

def intCoordsToRat {n : ℕ} : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) where
  toFun v i := (v i : ℚ)
  map_add' v w := by
    ext i
    change (((v + w) i : ℤ) : ℚ) = (v i : ℚ) + (w i : ℚ)
    simp
  map_smul' a v := by
    ext i
    change (((a • v) i : ℤ) : ℚ) = a • (v i : ℚ)
    simp only [Pi.smul_apply, zsmul_eq_mul]
    push_cast
    ring

@[simp]
theorem intCoordsToRat_apply {n : ℕ} (v : Fin n → ℤ) (i : Fin n) :
    intCoordsToRat v i = (v i : ℚ) := rfl

def coordinateIntegerLattice (n : ℕ) : Submodule ℤ (Fin n → ℚ) :=
  LinearMap.range intCoordsToRat

theorem mem_coordinateIntegerLattice {n : ℕ} {v : Fin n → ℚ} :
    v ∈ coordinateIntegerLattice n ↔
      ∃ z : Fin n → ℤ, ∀ i, (z i : ℚ) = v i := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, fun _ => rfl⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, funext fun i => hz i⟩

theorem intCoordsToRat_mem {n : ℕ} (v : Fin n → ℤ) :
    intCoordsToRat v ∈ coordinateIntegerLattice n :=
  ⟨v, rfl⟩

theorem coordinateIntegerLattice_isLattice (n : ℕ) :
    IsLattice ℚ (coordinateIntegerLattice n) := by
  constructor
  · have htop : (⊤ : Submodule ℤ (Fin n → ℤ)).FG := Module.Finite.fg_top
    have hmap := htop.map intCoordsToRat
    rwa [Submodule.map_top] at hmap
  · refine top_unique ?_
    rw [← (Pi.basisFun ℚ (Fin n)).span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ?_
    refine ⟨fun j => if j = i then 1 else 0, funext fun j => ?_⟩
    by_cases hj : j = i <;> simp [hj]

def standardRatForm (m : ℕ) : LinearMap.BilinForm ℚ (Fin m → ℚ) :=
  dotProductBilin ℚ ℚ

@[simp]
theorem standardRatForm_apply {m : ℕ} (x y : Fin m → ℚ) :
    standardRatForm m x y = ∑ i, x i * y i :=
  rfl

theorem standardRatForm_isSymm (m : ℕ) : (standardRatForm m).IsSymm := by
  constructor
  intro x y
  simp only [standardRatForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem standardRatForm_posDef (m : ℕ) :
    ∀ x : Fin m → ℚ, x ≠ 0 → 0 < standardRatForm m x x := by
  intro x hx
  have hex : ∃ i, x i ≠ 0 := by
    simpa only [Function.ne_iff, Pi.zero_apply] using hx
  obtain ⟨i, hi⟩ := hex
  rw [standardRatForm_apply]
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg (x j))
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

theorem standardRatForm_dual_coordinateIntegerLattice (m : ℕ) :
    (standardRatForm m).dualSubmodule (coordinateIntegerLattice m) =
      coordinateIntegerLattice m := by
  ext x
  constructor
  · intro hx
    let z : Fin m → ℤ := fun i =>
      (mem_one_iff.mp (hx (intCoordsToRat (Pi.single i 1))
        (intCoordsToRat_mem (Pi.single i 1)))).choose
    refine mem_coordinateIntegerLattice.mpr ⟨z, ?_⟩
    intro i
    have hi := (mem_one_iff.mp (hx (intCoordsToRat (Pi.single i 1))
      (intCoordsToRat_mem (Pi.single i 1)))).choose_spec
    change ((z i : ℤ) : ℚ) = x i
    calc
      ((z i : ℤ) : ℚ) = standardRatForm m x
          (intCoordsToRat (Pi.single i 1)) := hi
      _ = x i := by
        rw [standardRatForm_apply, Finset.sum_eq_single i]
        · simp [intCoordsToRat]
        · intro j _ hji
          simp [intCoordsToRat, hji]
        · exact fun hiu => absurd (Finset.mem_univ i) hiu
  · intro hx y hy
    obtain ⟨a, ha⟩ := mem_coordinateIntegerLattice.mp hx
    obtain ⟨b, hb⟩ := mem_coordinateIntegerLattice.mp hy
    apply mem_one_iff.mpr
    refine ⟨∑ i, a i * b i, ?_⟩
    rw [standardRatForm_apply]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [ha i, hb i]

end SRG266.Lattice
