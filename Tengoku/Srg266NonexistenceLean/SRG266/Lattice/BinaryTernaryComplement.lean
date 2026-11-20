/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.SimplexCoordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.PrimarySpan
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.EvenGlue
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.OddPrimaryNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

namespace A2SquareCoordinates

abbrev Space := (Fin 2 → ℚ) × (Fin 2 → ℚ)
def form : LinearMap.BilinForm ℚ Space := prodForm (simplexRatForm 2) (simplexRatForm 2)
def lattice : Submodule ℤ Space := (coordinateIntegerLattice 2).prod (coordinateIntegerLattice 2)
def leftWeight : Space := (simplexWeight 2, 0)
def rightWeight : Space := (0, simplexWeight 2)
def matchingVector (i : Fin 2) : Space :=
  if i = 0 then leftWeight + rightWeight else leftWeight - rightWeight

theorem form_isSymm : form.IsSymm :=
  prodForm_isSymm (simplexRatForm_isSymm 2) (simplexRatForm_isSymm 2)
theorem form_posDef : ∀ z : Space, z ≠ 0 → 0 < form z z :=
  prodForm_posDef (simplexRatForm_posDef 2) (simplexRatForm_posDef 2)
theorem lattice_isLattice : IsLattice ℚ lattice :=
  isLattice_prod (coordinateIntegerLattice_isLattice 2) (coordinateIntegerLattice_isLattice 2)
theorem lattice_isIntegral : IsIntegral form lattice :=
  isIntegral_prod (simplexRatForm_isIntegral 2) (simplexRatForm_isIntegral 2)
theorem lattice_isEven : IsEven form lattice :=
  isEven_prod (simplexRatForm_isEven 2) (simplexRatForm_isEven 2)
theorem finrank_space : Module.finrank ℚ Space = 4 := by
  rw [Module.finrank_prod]
  simp

theorem lattice_dual : form.dualSubmodule lattice =
    lattice ⊔ Submodule.span ℤ {leftWeight, rightWeight} := by
  change (prodForm (simplexRatForm 2) (simplexRatForm 2)).dualSubmodule
    ((coordinateIntegerLattice 2).prod (coordinateIntegerLattice 2)) =
    (coordinateIntegerLattice 2).prod (coordinateIntegerLattice 2) ⊔
      Submodule.span ℤ {(simplexWeight 2, (0 : Fin 2 → ℚ)), ((0 : Fin 2 → ℚ), simplexWeight 2)}
  rw [dualSubmodule_prodForm]
  simp only [simplexRatForm_dual]
  exact prod_sup_span_singletons _ _ _ _

theorem three_smul_leftWeight_mem : (3 : ℤ) • leftWeight ∈ lattice := by
  change (3 : ℤ) • simplexWeight 2 ∈ coordinateIntegerLattice 2 ∧
    (3 : ℤ) • (0 : Fin 2 → ℚ) ∈ coordinateIntegerLattice 2
  exact ⟨by simpa using succ_smul_simplexWeight_mem 2, by simp⟩

theorem three_smul_rightWeight_mem : (3 : ℤ) • rightWeight ∈ lattice := by
  change (3 : ℤ) • (0 : Fin 2 → ℚ) ∈ coordinateIntegerLattice 2 ∧
    (3 : ℤ) • simplexWeight 2 ∈ coordinateIntegerLattice 2
  exact ⟨by simp, by simpa using succ_smul_simplexWeight_mem 2⟩

theorem matchingVector_three_smul_mem (i : Fin 2) : (3 : ℤ) • matchingVector i ∈ lattice := by
  unfold matchingVector
  split_ifs
  · simpa only [smul_add] using lattice.add_mem three_smul_leftWeight_mem three_smul_rightWeight_mem
  · simpa only [smul_sub] using lattice.sub_mem three_smul_leftWeight_mem three_smul_rightWeight_mem

theorem matchingVector_norm (i : Fin 2) : form (matchingVector i) (matchingVector i) = 4 / 3 := by
  fin_cases i <;>
    norm_num [form, matchingVector, leftWeight, rightWeight, prodForm_apply, simplexRatForm_apply,
      simplexWeight, Fin.sum_univ_succ]

theorem matchingVector_cross (i j : Fin 2) (hij : i ≠ j) :
    form (matchingVector i) (matchingVector j) = 0 := by
  fin_cases i <;> fin_cases j <;> first
    | exact (hij rfl).elim
    | norm_num [form, matchingVector, leftWeight, rightWeight, prodForm_apply, simplexRatForm_apply,
        simplexWeight, Fin.sum_univ_succ]

theorem matchingVector_dual : form.dualSubmodule lattice =
    lattice ⊔ Submodule.span ℤ (Set.range matchingVector) := by
  rw [range_fin_two_eq_pair]
  change form.dualSubmodule lattice =
    lattice ⊔ Submodule.span ℤ {leftWeight + rightWeight, leftWeight - rightWeight}
  rw [sup_span_pair_hadamard_eq (p := 3) ⟨-1, 1, by norm_num⟩
    three_smul_leftWeight_mem three_smul_rightWeight_mem]
  exact lattice_dual

end A2SquareCoordinates

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {N : Submodule ℤ W}

def ternaryBinaryLattice (N : Submodule ℤ W) (u : Fin 2 → W) :
    Submodule ℤ (W × A2SquareCoordinates.Space) :=
  glueLattice N A2SquareCoordinates.lattice (fun i => (u i, A2SquareCoordinates.matchingVector i))

theorem complete_ternary_binary (u : Fin 2 → W)
    (hsB : B.IsSymm) (hlN : IsLattice ℚ N) (hiN : IsIntegral B N) (heN : IsEven B N)
    (hdN : B.dualSubmodule N = N ⊔ Submodule.span ℤ (Set.range u))
    (hcross : ∀ i j, i ≠ j → B (u i) (u j) ∈ (1 : Submodule ℤ ℚ))
    (hnorm : ∀ i, ∃ k : ℤ, B (u i) (u i) = 2 / 3 + 2 * (k : ℚ)) :
    IsLattice ℚ (ternaryBinaryLattice N u) ∧
      IsEven (prodForm B A2SquareCoordinates.form) (ternaryBinaryLattice N u) ∧
      (prodForm B A2SquareCoordinates.form).dualSubmodule (ternaryBinaryLattice N u) =
        ternaryBinaryLattice N u := by
  apply complete_even_glue u A2SquareCoordinates.matchingVector (fun _ => 3)
    hsB A2SquareCoordinates.form_isSymm hlN A2SquareCoordinates.lattice_isLattice
    hiN A2SquareCoordinates.lattice_isIntegral heN A2SquareCoordinates.lattice_isEven
    hdN A2SquareCoordinates.matchingVector_dual A2SquareCoordinates.matchingVector_three_smul_mem
    hcross
  · intro i j hij
    rw [A2SquareCoordinates.matchingVector_cross i j hij]
    exact zero_mem _
  · intro i
    obtain ⟨k, hk⟩ := hnorm i
    refine ⟨k + 1, ?_⟩
    rw [hk, A2SquareCoordinates.matchingVector_norm]
    push_cast
    ring
  · intro i
    obtain ⟨k, hk⟩ := hnorm i
    exact norm_denominator_unit (p := 3) (r := 2) (by norm_num) ⟨1, -1, by norm_num⟩ hk

end SRG266.Lattice
