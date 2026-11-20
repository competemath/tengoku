/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.IntegerCoordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Even
import Tengoku.Seed.LinearAlgebra.Matrix.BilinearForm
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice.Q15Coordinates

abbrev Space := Fin 2 → ℚ
def form : LinearMap.BilinForm ℚ Space := Matrix.toBilin' !![(4 : ℚ), 1; 1, 4]
def lattice : Submodule ℤ Space := coordinateIntegerLattice 2
def dualThree : Space := ![1/3, -1/3]
def dualFive : Space := ![1/5, 1/5]

theorem form_apply (x y : Space) :
    form x y = 4*x 0*y 0+x 0*y 1+x 1*y 0+4*x 1*y 1 := by
  simp [form, Matrix.toBilin'_apply, Fin.sum_univ_two]
  ring

theorem form_isSymm : form.IsSymm := by
  constructor
  intro x y
  simp only [form_apply]
  ring

theorem form_posDef : ∀ x : Space, x ≠ 0 → 0 < form x x := by
  intro x hx
  have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    ext i
    fin_cases i <;> simp [h.1, h.2]
  rw [form_apply]
  rcases hne with h | h
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 1), sq_nonneg (x 0+x 1)]
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0), sq_nonneg (x 0+x 1)]

theorem lattice_isLattice : IsLattice ℚ lattice := coordinateIntegerLattice_isLattice 2

theorem lattice_isIntegral : IsIntegral form lattice := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  refine mem_one_iff.mpr ⟨4*x 0*y 0+x 0*y 1+x 1*y 0+4*x 1*y 1, ?_⟩
  simp only [form_apply, intCoordsToRat_apply]
  push_cast
  ring

theorem lattice_isEven : IsEven form lattice := by
  rintro _ ⟨x, rfl⟩
  refine ⟨2*(x 0)^2+x 0*x 1+2*(x 1)^2, ?_⟩
  simp only [form_apply, intCoordsToRat_apply]
  push_cast
  ring

theorem dualThree_pair (x : Space) : form dualThree x = x 0-x 1 := by
  norm_num [form_apply, dualThree]
  ring

theorem dualFive_pair (x : Space) : form dualFive x = x 0+x 1 := by
  norm_num [form_apply, dualFive]
  ring

theorem dualThree_norm : form dualThree dualThree = 2/3 := by
  rw [dualThree_pair]
  norm_num [dualThree]

theorem dualFive_norm : form dualFive dualFive = 2/5 := by
  rw [dualFive_pair]
  norm_num [dualFive]

theorem dualThree_pair_dualFive : form dualThree dualFive = 0 := by
  norm_num [dualThree_pair, dualFive]

theorem dualThree_mem_dual : dualThree ∈ form.dualSubmodule lattice := by
  rintro _ ⟨z, rfl⟩
  refine mem_one_iff.mpr ⟨z 0-z 1, ?_⟩
  simp [dualThree_pair]

theorem dualFive_mem_dual : dualFive ∈ form.dualSubmodule lattice := by
  rintro _ ⟨z, rfl⟩
  refine mem_one_iff.mpr ⟨z 0+z 1, ?_⟩
  simp [dualFive_pair]

theorem three_smul_dualThree_mem : (3 : ℤ) • dualThree ∈ lattice := by
  refine ⟨![1, -1], ?_⟩
  ext i
  fin_cases i <;> norm_num [dualThree, intCoordsToRat_apply, zsmul_eq_mul]

theorem five_smul_dualFive_mem : (5 : ℤ) • dualFive ∈ lattice := by
  refine ⟨![1, 1], ?_⟩
  ext i
  fin_cases i <;> norm_num [dualFive, intCoordsToRat_apply, zsmul_eq_mul]

theorem lattice_dual : form.dualSubmodule lattice =
    lattice ⊔ Submodule.span ℤ {dualThree, dualFive} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨m, hm'⟩ := mem_one_iff.mp
      (hx (intCoordsToRat ![1, 0]) (intCoordsToRat_mem ![1, 0]))
    obtain ⟨n, hn'⟩ := mem_one_iff.mp
      (hx (intCoordsToRat ![0, 1]) (intCoordsToRat_mem ![0, 1]))
    have hm : 4*x 0+x 1 = (m : ℚ) := by simpa [form_apply] using hm'.symm
    have hn : x 0+4*x 1 = (n : ℚ) := by simpa [form_apply] using hn'.symm
    have he : x = intCoordsToRat ![-n, -m]+(n-m) • dualThree+(3*(m+n)) • dualFive := by
      ext i
      fin_cases i <;> norm_num [intCoordsToRat, dualThree, dualFive,
        Matrix.vecHead, Matrix.vecTail, zsmul_eq_mul] <;> linarith
    have h3 : dualThree ∈ Submodule.span ℤ {dualThree, dualFive} := Submodule.subset_span (by simp)
    have h5 : dualFive ∈ Submodule.span ℤ {dualThree, dualFive} := Submodule.subset_span (by simp)
    rw [he]
    exact Submodule.add_mem _
      (Submodule.add_mem _ (Submodule.mem_sup_left (intCoordsToRat_mem ![-n, -m]))
        (Submodule.mem_sup_right (Submodule.smul_mem _ (n-m) h3)))
      (Submodule.mem_sup_right (Submodule.smul_mem _ (3*(m+n)) h5))
  · refine sup_le lattice_isIntegral (Submodule.span_le.mpr ?_)
    intro x hx
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx :
      x = dualThree ∨ x = dualFive) with rfl | rfl
    · exact dualThree_mem_dual
    · exact dualFive_mem_dual

end SRG266.Lattice.Q15Coordinates
