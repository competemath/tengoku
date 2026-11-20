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

/--
@isnad1 id=issymm.0h0v.s7.54a60d2e7425 from=translated src=- shape=54c8eceb vocab=64046640
-/
theorem form_isSymm : form.IsSymm :=
  prodForm_isSymm (simplexRatForm_isSymm 2) (simplexRatForm_isSymm 2)
/--
@isnad1 id=lt.1h1v.s10.d8c588ca03fa from=translated src=- shape=e7c936f8 vocab=e8c03394
-/
theorem form_posDef : ∀ z : Space, z ≠ 0 → 0 < form z z :=
  prodForm_posDef (simplexRatForm_posDef 2) (simplexRatForm_posDef 2)
/--
@isnad1 id=islattic.0h0v.s8.3738d55387aa from=translated src=- shape=93eefbde vocab=67fa833e
-/
theorem lattice_isLattice : IsLattice ℚ lattice :=
  isLattice_prod (coordinateIntegerLattice_isLattice 2) (coordinateIntegerLattice_isLattice 2)
/--
@isnad1 id=isintegr.0h0v.s7.8abfbd36b810 from=translated src=- shape=8175f13d vocab=c6ef8502
-/
theorem lattice_isIntegral : IsIntegral form lattice :=
  isIntegral_prod (simplexRatForm_isIntegral 2) (simplexRatForm_isIntegral 2)
/--
@isnad1 id=iseven.0h0v.s7.63e27dbe1c68 from=translated src=- shape=54c8eceb vocab=205e3dae
-/
theorem lattice_isEven : IsEven form lattice :=
  isEven_prod (simplexRatForm_isEven 2) (simplexRatForm_isEven 2)
/--
@isnad1 id=eq.0h0v.s7.996997260eb6 from=translated src=- shape=b3c4969c vocab=8a65d214
-/
theorem finrank_space : Module.finrank ℚ Space = 4 := by
  rw [Module.finrank_prod]
  simp

/--
@isnad1 id=eq.0h0v.s10.b549a0c27133 from=translated src=- shape=a049e693 vocab=1d58488a
-/
theorem lattice_dual : form.dualSubmodule lattice =
    lattice ⊔ Submodule.span ℤ {leftWeight, rightWeight} := by
  change (prodForm (simplexRatForm 2) (simplexRatForm 2)).dualSubmodule
    ((coordinateIntegerLattice 2).prod (coordinateIntegerLattice 2)) =
    (coordinateIntegerLattice 2).prod (coordinateIntegerLattice 2) ⊔
      Submodule.span ℤ {(simplexWeight 2, (0 : Fin 2 → ℚ)), ((0 : Fin 2 → ℚ), simplexWeight 2)}
  rw [dualSubmodule_prodForm]
  simp only [simplexRatForm_dual]
  exact prod_sup_span_singletons _ _ _ _

/--
@isnad1 id=mem.0h0v.s8.403fcdf99073 from=translated src=- shape=cddf0ccc vocab=bf4c0f6e
-/
theorem three_smul_leftWeight_mem : (3 : ℤ) • leftWeight ∈ lattice := by
  change (3 : ℤ) • simplexWeight 2 ∈ coordinateIntegerLattice 2 ∧
    (3 : ℤ) • (0 : Fin 2 → ℚ) ∈ coordinateIntegerLattice 2
  exact ⟨by simpa using succ_smul_simplexWeight_mem 2, by simp⟩

/--
@isnad1 id=mem.0h0v.s8.08e2f3b95c22 from=translated src=- shape=cddf0ccc vocab=b6b80271
-/
theorem three_smul_rightWeight_mem : (3 : ℤ) • rightWeight ∈ lattice := by
  change (3 : ℤ) • (0 : Fin 2 → ℚ) ∈ coordinateIntegerLattice 2 ∧
    (3 : ℤ) • simplexWeight 2 ∈ coordinateIntegerLattice 2
  exact ⟨by simp, by simpa using succ_smul_simplexWeight_mem 2⟩

/--
@isnad1 id=mem.0h1v.s8.e431d2855f26 from=translated src=- shape=d979743c vocab=ac1281d1
-/
theorem matchingVector_three_smul_mem (i : Fin 2) : (3 : ℤ) • matchingVector i ∈ lattice := by
  unfold matchingVector
  split_ifs
  · simpa only [smul_add] using lattice.add_mem three_smul_leftWeight_mem three_smul_rightWeight_mem
  · simpa only [smul_sub] using lattice.sub_mem three_smul_leftWeight_mem three_smul_rightWeight_mem

/--
@isnad1 id=eq.0h1v.s10.b8de0e8c8adf from=translated src=- shape=d0400104 vocab=e153dceb
-/
theorem matchingVector_norm (i : Fin 2) : form (matchingVector i) (matchingVector i) = 4 / 3 := by
  fin_cases i <;>
    norm_num [form, matchingVector, leftWeight, rightWeight, prodForm_apply, simplexRatForm_apply,
      simplexWeight, Fin.sum_univ_succ]

/--
@isnad1 id=eq.1h2v.s10.2d022cf8e5aa from=translated src=- shape=1d2ac976 vocab=dca629af
-/
theorem matchingVector_cross (i j : Fin 2) (hij : i ≠ j) :
    form (matchingVector i) (matchingVector j) = 0 := by
  fin_cases i <;> fin_cases j <;> first
    | exact (hij rfl).elim
    | norm_num [form, matchingVector, leftWeight, rightWeight, prodForm_apply, simplexRatForm_apply,
        simplexWeight, Fin.sum_univ_succ]

/--
@isnad1 id=eq.0h0v.s10.c80c7e6833ae from=translated src=- shape=d3d8e21a vocab=fa72c9b0
-/
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

/--
@isnad1 id=and.7h4v.s11.e61898bd6bab from=translated src=- shape=d2904d30 vocab=3d9cc68e
-/
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
