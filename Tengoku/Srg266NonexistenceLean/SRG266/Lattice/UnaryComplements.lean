/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.E6Coordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.K8Coordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CyclicSelfDual
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.OddPrimaryNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {N : Submodule ℤ W} {u : W}

def ternaryTwoLattice (N : Submodule ℤ W) (u : W) : Submodule ℤ (W × E6Coordinates.Space) :=
  cyclicGlueLattice N E6Coordinates.lattice u E6Coordinates.dualVector

def ternaryFourLattice (N : Submodule ℤ W) (u : W) : Submodule ℤ (W × (Fin 2 → ℚ)) :=
  cyclicGlueLattice N (coordinateIntegerLattice 2) u (simplexWeight 2)

def quinaryFourLattice (N : Submodule ℤ W) (u : W) : Submodule ℤ (W × (Fin 4 → ℚ)) :=
  cyclicGlueLattice N (coordinateIntegerLattice 4) u ((2 : ℤ) • simplexWeight 4)

def quinaryTwoLattice (N : Submodule ℤ W) (u : W) : Submodule ℤ (W × K8Coordinates.Space) :=
  cyclicGlueLattice N K8Coordinates.lattice u ((2 : ℤ) • K8Coordinates.dualVector)

theorem complete_ternary_two (hsB : B.IsSymm) (hlN : IsLattice ℚ N)
    (hiN : IsIntegral B N) (heN : IsEven B N)
    (hdN : B.dualSubmodule N = N ⊔ Submodule.span ℤ {u})
    (hnorm : ∃ k : ℤ, B u u = 2 / 3 + 2 * (k : ℚ)) :
    IsLattice ℚ (ternaryTwoLattice N u) ∧
      IsEven (prodForm B E6Coordinates.form) (ternaryTwoLattice N u) ∧
      (prodForm B E6Coordinates.form).dualSubmodule (ternaryTwoLattice N u) =
        ternaryTwoLattice N u := by
  obtain ⟨k, hk⟩ := hnorm
  apply complete_even_cyclic_glue hsB E6Coordinates.form_isSymm hlN E6Coordinates.lattice_isLattice
    hiN E6Coordinates.lattice_isIntegral heN E6Coordinates.lattice_isEven
    hdN E6Coordinates.lattice_dual E6Coordinates.three_smul_dualVector_mem
  · refine ⟨k + 2, ?_⟩
    rw [hk, E6Coordinates.dualVector_norm]
    push_cast
    ring
  · exact norm_denominator_unit (p := 3) (r := 2) (by norm_num)
      ⟨1, -1, by norm_num⟩ (by simpa using hk)

theorem complete_ternary_four (hsB : B.IsSymm) (hlN : IsLattice ℚ N)
    (hiN : IsIntegral B N) (heN : IsEven B N)
    (hdN : B.dualSubmodule N = N ⊔ Submodule.span ℤ {u})
    (hnorm : ∃ k : ℤ, B u u = 4 / 3 + 2 * (k : ℚ)) :
    IsLattice ℚ (ternaryFourLattice N u) ∧
      IsEven (prodForm B (simplexRatForm 2)) (ternaryFourLattice N u) ∧
      (prodForm B (simplexRatForm 2)).dualSubmodule (ternaryFourLattice N u) =
        ternaryFourLattice N u := by
  obtain ⟨k, hk⟩ := hnorm
  apply complete_even_cyclic_glue (p := 3) hsB (simplexRatForm_isSymm 2)
    hlN (coordinateIntegerLattice_isLattice 2) hiN (simplexRatForm_isIntegral 2)
    heN (simplexRatForm_isEven 2) hdN (simplexRatForm_dual 2)
    (by simpa using succ_smul_simplexWeight_mem 2)
  · refine ⟨k + 1, ?_⟩
    rw [hk, simplexWeight_norm]
    push_cast
    ring
  · exact norm_denominator_unit (p := 3) (r := 4) (by norm_num)
      ⟨-1, 1, by norm_num⟩ (by simpa using hk)

omit [AddCommGroup W] [Module ℚ W] in
theorem a4_twice_weight_dual :
    (simplexRatForm 4).dualSubmodule (coordinateIntegerLattice 4) =
      coordinateIntegerLattice 4 ⊔ Submodule.span ℤ {(2 : ℤ) • simplexWeight 4} := by
  rw [sup_span_smul_eq_of_bezout (p := 5) (b := 3) (k := -1)
    (by simpa using succ_smul_simplexWeight_mem 4) (by norm_num)]
  exact simplexRatForm_dual 4

omit [AddCommGroup W] [Module ℚ W] in
theorem a4_twice_weight_norm :
    simplexRatForm 4 ((2 : ℤ) • simplexWeight 4) ((2 : ℤ) • simplexWeight 4) = 16 / 5 := by
  norm_num [simplexRatForm_apply, simplexWeight, Fin.sum_univ_succ]

theorem complete_quinary_four (hsB : B.IsSymm) (hlN : IsLattice ℚ N)
    (hiN : IsIntegral B N) (heN : IsEven B N)
    (hdN : B.dualSubmodule N = N ⊔ Submodule.span ℤ {u})
    (hnorm : ∃ k : ℤ, B u u = 4 / 5 + 2 * (k : ℚ)) :
    IsLattice ℚ (quinaryFourLattice N u) ∧
      IsEven (prodForm B (simplexRatForm 4)) (quinaryFourLattice N u) ∧
      (prodForm B (simplexRatForm 4)).dualSubmodule (quinaryFourLattice N u) =
        quinaryFourLattice N u := by
  obtain ⟨k, hk⟩ := hnorm
  have hm : (5 : ℤ) • ((2 : ℤ) • simplexWeight 4) ∈ coordinateIntegerLattice 4 := by
    have heq : (5 : ℤ) • ((2 : ℤ) • simplexWeight 4) =
        (2 : ℤ) • ((5 : ℤ) • simplexWeight 4) := by module
    rw [heq]
    exact Submodule.smul_mem _ (2 : ℤ) (by simpa using succ_smul_simplexWeight_mem 4)
  apply complete_even_cyclic_glue hsB (simplexRatForm_isSymm 4)
    hlN (coordinateIntegerLattice_isLattice 4) hiN (simplexRatForm_isIntegral 4)
    heN (simplexRatForm_isEven 4) hdN a4_twice_weight_dual hm
  · refine ⟨k + 2, ?_⟩
    rw [hk, a4_twice_weight_norm]
    push_cast
    ring
  · exact norm_denominator_unit (p := 5) (r := 4) (by norm_num)
      ⟨1, -1, by norm_num⟩ (by simpa using hk)

omit [AddCommGroup W] [Module ℚ W] in
theorem k8_twice_dualVector_dual :
    K8Coordinates.form.dualSubmodule K8Coordinates.lattice =
      K8Coordinates.lattice ⊔ Submodule.span ℤ {(2 : ℤ) • K8Coordinates.dualVector} := by
  rw [sup_span_smul_eq_of_bezout (p := 5) (b := 3) (k := -1)
    K8Coordinates.five_smul_dualVector_mem (by norm_num)]
  exact K8Coordinates.lattice_dual

omit [AddCommGroup W] [Module ℚ W] in
theorem k8_twice_dualVector_norm :
    K8Coordinates.form ((2 : ℤ) • K8Coordinates.dualVector)
      ((2 : ℤ) • K8Coordinates.dualVector) = 8 / 5 := by
  have heq : (2 : ℤ) • K8Coordinates.dualVector = (2 : ℚ) • K8Coordinates.dualVector := by module
  rw [heq]
  norm_num [K8Coordinates.dualVector_norm]

theorem complete_quinary_two (hsB : B.IsSymm) (hlN : IsLattice ℚ N)
    (hiN : IsIntegral B N) (heN : IsEven B N)
    (hdN : B.dualSubmodule N = N ⊔ Submodule.span ℤ {u})
    (hnorm : ∃ k : ℤ, B u u = 2 / 5 + 2 * (k : ℚ)) :
    IsLattice ℚ (quinaryTwoLattice N u) ∧
      IsEven (prodForm B K8Coordinates.form) (quinaryTwoLattice N u) ∧
      (prodForm B K8Coordinates.form).dualSubmodule (quinaryTwoLattice N u) =
        quinaryTwoLattice N u := by
  obtain ⟨k, hk⟩ := hnorm
  have hm : (5 : ℤ) • ((2 : ℤ) • K8Coordinates.dualVector) ∈ K8Coordinates.lattice := by
    have heq : (5 : ℤ) • ((2 : ℤ) • K8Coordinates.dualVector) =
        (2 : ℤ) • ((5 : ℤ) • K8Coordinates.dualVector) := by module
    rw [heq]
    exact Submodule.smul_mem _ (2 : ℤ) K8Coordinates.five_smul_dualVector_mem
  apply complete_even_cyclic_glue hsB K8Coordinates.form_isSymm
    hlN K8Coordinates.lattice_isLattice hiN K8Coordinates.lattice_isIntegral
    heN K8Coordinates.lattice_isEven hdN k8_twice_dualVector_dual hm
  · refine ⟨k + 1, ?_⟩
    rw [hk, k8_twice_dualVector_norm]
    push_cast
    ring
  · exact norm_denominator_unit (p := 5) (r := 2) (by norm_num)
      ⟨1, -2, by norm_num⟩ (by simpa using hk)

end SRG266.Lattice
