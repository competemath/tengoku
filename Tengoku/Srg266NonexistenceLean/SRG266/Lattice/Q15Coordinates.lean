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

/--
@isnad1 id=eq.0h2v.s9.25e797644cd9 from=translated src=- shape=aaffd2f0 vocab=049b3547
-/
theorem form_apply (x y : Space) :
    form x y = 4*x 0*y 0+x 0*y 1+x 1*y 0+4*x 1*y 1 := by
  simp [form, Matrix.toBilin'_apply, Fin.sum_univ_two]
  ring

/--
@isnad1 id=issymm.0h0v.s5.3f742b13a718 from=translated src=- shape=54c8eceb vocab=645f0772
-/
theorem form_isSymm : form.IsSymm := by
  constructor
  intro x y
  simp only [form_apply]
  ring

/--
@isnad1 id=lt.1h1v.s9.e2cc84e6d17d from=translated src=- shape=e7c936f8 vocab=27e76de5
-/
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

/--
@isnad1 id=islattic.0h0v.s6.5a8c79516320 from=translated src=- shape=93eefbde vocab=2650c20f
-/
theorem lattice_isLattice : IsLattice ℚ lattice := coordinateIntegerLattice_isLattice 2

/--
@isnad1 id=isintegr.0h0v.s6.e532e7761be9 from=translated src=- shape=8175f13d vocab=27360ef4
-/
theorem lattice_isIntegral : IsIntegral form lattice := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  refine mem_one_iff.mpr ⟨4*x 0*y 0+x 0*y 1+x 1*y 0+4*x 1*y 1, ?_⟩
  simp only [form_apply, intCoordsToRat_apply]
  push_cast
  ring

/--
@isnad1 id=iseven.0h0v.s5.dcc47f025c98 from=translated src=- shape=54c8eceb vocab=bcedacd6
-/
theorem lattice_isEven : IsEven form lattice := by
  rintro _ ⟨x, rfl⟩
  refine ⟨2*(x 0)^2+x 0*x 1+2*(x 1)^2, ?_⟩
  simp only [form_apply, intCoordsToRat_apply]
  push_cast
  ring

/--
@isnad1 id=eq.0h1v.s9.72f0bd176cbf from=translated src=- shape=6997c508 vocab=7fa99e56
-/
theorem dualThree_pair (x : Space) : form dualThree x = x 0-x 1 := by
  norm_num [form_apply, dualThree]
  ring

/--
@isnad1 id=eq.0h1v.s9.d355ac3e7d97 from=translated src=- shape=6997c508 vocab=8392f08e
-/
theorem dualFive_pair (x : Space) : form dualFive x = x 0+x 1 := by
  norm_num [form_apply, dualFive]
  ring

/--
@isnad1 id=eq.0h0v.s9.fa5bbb892cee from=translated src=- shape=1a9fa12e vocab=2e609e61
-/
theorem dualThree_norm : form dualThree dualThree = 2/3 := by
  rw [dualThree_pair]
  norm_num [dualThree]

/--
@isnad1 id=eq.0h0v.s9.b04bafa83a0d from=translated src=- shape=1a9fa12e vocab=f67d2735
-/
theorem dualFive_norm : form dualFive dualFive = 2/5 := by
  rw [dualFive_pair]
  norm_num [dualFive]

/--
@isnad1 id=eq.0h0v.s9.97fc5c2fe0ec from=translated src=- shape=0775d00c vocab=f27f5a5e
-/
theorem dualThree_pair_dualFive : form dualThree dualFive = 0 := by
  norm_num [dualThree_pair, dualFive]

/--
@isnad1 id=mem.0h0v.s8.359f5a18058c from=translated src=- shape=568e8a8c vocab=f5902c48
-/
theorem dualThree_mem_dual : dualThree ∈ form.dualSubmodule lattice := by
  rintro _ ⟨z, rfl⟩
  refine mem_one_iff.mpr ⟨z 0-z 1, ?_⟩
  simp [dualThree_pair]

/--
@isnad1 id=mem.0h0v.s8.c90600d6882c from=translated src=- shape=568e8a8c vocab=2d42a3cb
-/
theorem dualFive_mem_dual : dualFive ∈ form.dualSubmodule lattice := by
  rintro _ ⟨z, rfl⟩
  refine mem_one_iff.mpr ⟨z 0+z 1, ?_⟩
  simp [dualFive_pair]

/--
@isnad1 id=mem.0h0v.s7.7d9f9744bce2 from=translated src=- shape=cddf0ccc vocab=394a44c5
-/
theorem three_smul_dualThree_mem : (3 : ℤ) • dualThree ∈ lattice := by
  refine ⟨![1, -1], ?_⟩
  ext i
  fin_cases i <;> norm_num [dualThree, intCoordsToRat_apply, zsmul_eq_mul]

/--
@isnad1 id=mem.0h0v.s7.176d3828f0bf from=translated src=- shape=cddf0ccc vocab=95eab789
-/
theorem five_smul_dualFive_mem : (5 : ℤ) • dualFive ∈ lattice := by
  refine ⟨![1, 1], ?_⟩
  ext i
  fin_cases i <;> norm_num [dualFive, intCoordsToRat_apply, zsmul_eq_mul]

/--
@isnad1 id=eq.0h0v.s8.131f511b8ba4 from=translated src=- shape=a049e693 vocab=3bc24ec0
-/
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
