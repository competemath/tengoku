/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.UnaryComplements
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.BinaryTernaryComplement
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.BinaryQuinaryComplement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

inductive SmallOddPrime | three | five deriving DecidableEq
inductive PrimaryShape | zero | two | four | binary deriving DecidableEq

def SmallOddPrime.modulus : SmallOddPrime → ℕ | .three => 3 | .five => 5
def SmallOddPrime.binaryNumerator : SmallOddPrime → ℤ | .three => 2 | .five => 4
abbrev PrimaryShape.arity : PrimaryShape → ℕ | .zero => 0 | .two => 1 | .four => 1 | .binary => 2

def primaryNumerator : (p : SmallOddPrime) → (s : PrimaryShape) → Fin s.arity → ℤ
  | _, .four, _ => 4
  | .five, .binary, i => if i = 0 then 2 else 4
  | _, _, _ => 2

def primaryFraction (p : SmallOddPrime) (s : PrimaryShape) (i : Fin s.arity) : ℚ :=
  (primaryNumerator p s i : ℚ) / (p.modulus : ℚ)

abbrev primaryModelSpace : SmallOddPrime → PrimaryShape → Type
  | .three, .zero => Fin 0 → ℚ
  | .three, .two => E6Coordinates.Space
  | .three, .four => Fin 2 → ℚ
  | .three, .binary => A2SquareCoordinates.Space
  | .five, .zero => Fin 0 → ℚ
  | .five, .two => K8Coordinates.Space
  | .five, .four => Fin 4 → ℚ
  | .five, .binary => K4Coordinates.Space

instance : (p : SmallOddPrime) → (s : PrimaryShape) → AddCommGroup (primaryModelSpace p s)
  | .three, .zero => inferInstanceAs (AddCommGroup (Fin 0 → ℚ))
  | .three, .two => inferInstanceAs (AddCommGroup E6Coordinates.Space)
  | .three, .four => inferInstanceAs (AddCommGroup (Fin 2 → ℚ))
  | .three, .binary => inferInstanceAs (AddCommGroup A2SquareCoordinates.Space)
  | .five, .zero => inferInstanceAs (AddCommGroup (Fin 0 → ℚ))
  | .five, .two => inferInstanceAs (AddCommGroup K8Coordinates.Space)
  | .five, .four => inferInstanceAs (AddCommGroup (Fin 4 → ℚ))
  | .five, .binary => inferInstanceAs (AddCommGroup K4Coordinates.Space)
instance : (p : SmallOddPrime) → (s : PrimaryShape) → Module ℚ (primaryModelSpace p s)
  | .three, .zero => inferInstanceAs (Module ℚ (Fin 0 → ℚ))
  | .three, .two => inferInstanceAs (Module ℚ E6Coordinates.Space)
  | .three, .four => inferInstanceAs (Module ℚ (Fin 2 → ℚ))
  | .three, .binary => inferInstanceAs (Module ℚ A2SquareCoordinates.Space)
  | .five, .zero => inferInstanceAs (Module ℚ (Fin 0 → ℚ))
  | .five, .two => inferInstanceAs (Module ℚ K8Coordinates.Space)
  | .five, .four => inferInstanceAs (Module ℚ (Fin 4 → ℚ))
  | .five, .binary => inferInstanceAs (Module ℚ K4Coordinates.Space)
instance : (p : SmallOddPrime) → (s : PrimaryShape) → Module.Finite ℚ (primaryModelSpace p s)
  | .three, .zero => inferInstanceAs (Module.Finite ℚ (Fin 0 → ℚ))
  | .three, .two => inferInstanceAs (Module.Finite ℚ E6Coordinates.Space)
  | .three, .four => inferInstanceAs (Module.Finite ℚ (Fin 2 → ℚ))
  | .three, .binary => inferInstanceAs (Module.Finite ℚ A2SquareCoordinates.Space)
  | .five, .zero => inferInstanceAs (Module.Finite ℚ (Fin 0 → ℚ))
  | .five, .two => inferInstanceAs (Module.Finite ℚ K8Coordinates.Space)
  | .five, .four => inferInstanceAs (Module.Finite ℚ (Fin 4 → ℚ))
  | .five, .binary => inferInstanceAs (Module.Finite ℚ K4Coordinates.Space)

def primaryModelForm : (p : SmallOddPrime) → (s : PrimaryShape) →
    LinearMap.BilinForm ℚ (primaryModelSpace p s)
  | .three, .zero => standardRatForm 0
  | .three, .two => E6Coordinates.form
  | .three, .four => simplexRatForm 2
  | .three, .binary => A2SquareCoordinates.form
  | .five, .zero => standardRatForm 0
  | .five, .two => K8Coordinates.form
  | .five, .four => simplexRatForm 4
  | .five, .binary => K4Coordinates.form

def primaryModelLattice : (p : SmallOddPrime) → (s : PrimaryShape) →
    Submodule ℤ (primaryModelSpace p s)
  | .three, .zero => coordinateIntegerLattice 0
  | .three, .two => E6Coordinates.lattice
  | .three, .four => coordinateIntegerLattice 2
  | .three, .binary => A2SquareCoordinates.lattice
  | .five, .zero => coordinateIntegerLattice 0
  | .five, .two => K8Coordinates.lattice
  | .five, .four => coordinateIntegerLattice 4
  | .five, .binary => K4Coordinates.lattice

def primaryModelVector : (p : SmallOddPrime) → (s : PrimaryShape) →
    Fin s.arity → primaryModelSpace p s
  | .three, .zero => Fin.elim0
  | .three, .two => fun _ => E6Coordinates.dualVector
  | .three, .four => fun _ => simplexWeight 2
  | .three, .binary => A2SquareCoordinates.matchingVector
  | .five, .zero => Fin.elim0
  | .five, .two => fun _ => (2 : ℤ) • K8Coordinates.dualVector
  | .five, .four => fun _ => (2 : ℤ) • simplexWeight 4
  | .five, .binary => K4Coordinates.matchingVector

def primaryModelRank : SmallOddPrime → PrimaryShape → ℕ
  | .three, .zero => 0 | .three, .two => 6 | .three, .four => 2 | .three, .binary => 4
  | .five, .zero => 0 | .five, .two => 8 | .five, .four => 4 | .five, .binary => 4

theorem primaryModel_isSymm (p : SmallOddPrime) (s : PrimaryShape) :
    (primaryModelForm p s).IsSymm := by
  cases p <;> cases s
  · exact standardRatForm_isSymm 0
  · exact E6Coordinates.form_isSymm
  · exact simplexRatForm_isSymm 2
  · exact A2SquareCoordinates.form_isSymm
  · exact standardRatForm_isSymm 0
  · exact K8Coordinates.form_isSymm
  · exact simplexRatForm_isSymm 4
  · exact K4Coordinates.form_isSymm

theorem primaryModel_posDef (p : SmallOddPrime) (s : PrimaryShape) :
    ∀ z : primaryModelSpace p s, z ≠ 0 → 0 < primaryModelForm p s z z := by
  cases p <;> cases s
  · exact standardRatForm_posDef 0
  · exact E6Coordinates.form_posDef
  · exact simplexRatForm_posDef 2
  · exact A2SquareCoordinates.form_posDef
  · exact standardRatForm_posDef 0
  · exact K8Coordinates.form_posDef
  · exact simplexRatForm_posDef 4
  · exact K4Coordinates.form_posDef

theorem primaryModel_isLattice (p : SmallOddPrime) (s : PrimaryShape) :
    IsLattice ℚ (primaryModelLattice p s) := by
  cases p <;> cases s
  · exact coordinateIntegerLattice_isLattice 0
  · exact E6Coordinates.lattice_isLattice
  · exact coordinateIntegerLattice_isLattice 2
  · exact A2SquareCoordinates.lattice_isLattice
  · exact coordinateIntegerLattice_isLattice 0
  · exact K8Coordinates.lattice_isLattice
  · exact coordinateIntegerLattice_isLattice 4
  · exact K4Coordinates.lattice_isLattice

private theorem zero_integral : IsIntegral (standardRatForm 0) (coordinateIntegerLattice 0) := by
  rw [IsIntegral, standardRatForm_dual_coordinateIntegerLattice]
private theorem zero_even : IsEven (standardRatForm 0) (coordinateIntegerLattice 0) := by
  intro z _
  exact ⟨0, by simp [standardRatForm_apply]⟩

theorem primaryModel_isIntegral (p : SmallOddPrime) (s : PrimaryShape) :
    IsIntegral (primaryModelForm p s) (primaryModelLattice p s) := by
  cases p <;> cases s
  · exact zero_integral
  · exact E6Coordinates.lattice_isIntegral
  · exact simplexRatForm_isIntegral 2
  · exact A2SquareCoordinates.lattice_isIntegral
  · exact zero_integral
  · exact K8Coordinates.lattice_isIntegral
  · exact simplexRatForm_isIntegral 4
  · exact K4Coordinates.lattice_isIntegral

theorem primaryModel_isEven (p : SmallOddPrime) (s : PrimaryShape) :
    IsEven (primaryModelForm p s) (primaryModelLattice p s) := by
  cases p <;> cases s
  · exact zero_even
  · exact E6Coordinates.lattice_isEven
  · exact simplexRatForm_isEven 2
  · exact A2SquareCoordinates.lattice_isEven
  · exact zero_even
  · exact K8Coordinates.lattice_isEven
  · exact simplexRatForm_isEven 4
  · exact K4Coordinates.lattice_isEven

theorem primaryModel_finrank (p : SmallOddPrime) (s : PrimaryShape) :
    Module.finrank ℚ (primaryModelSpace p s) = primaryModelRank p s := by
  cases p <;> cases s
  · simp [primaryModelSpace, primaryModelRank]
  · exact E6Coordinates.finrank_space
  · simp [primaryModelSpace, primaryModelRank]
  · exact A2SquareCoordinates.finrank_space
  · simp [primaryModelSpace, primaryModelRank]
  · exact K8Coordinates.finrank_space
  · simp [primaryModelSpace, primaryModelRank]
  · exact K4Coordinates.finrank_space

theorem primaryModel_dual (p : SmallOddPrime) (s : PrimaryShape) :
    (primaryModelForm p s).dualSubmodule (primaryModelLattice p s) =
      primaryModelLattice p s ⊔ Submodule.span ℤ (Set.range (primaryModelVector p s)) := by
  cases p <;> cases s
  · change (standardRatForm 0).dualSubmodule (coordinateIntegerLattice 0) =
      coordinateIntegerLattice 0 ⊔ Submodule.span ℤ (Set.range (Fin.elim0 : Fin 0 → (Fin 0 → ℚ)))
    simp [standardRatForm_dual_coordinateIntegerLattice]
  · change E6Coordinates.form.dualSubmodule E6Coordinates.lattice =
      E6Coordinates.lattice ⊔ Submodule.span ℤ (Set.range (fun _ : Fin 1 => E6Coordinates.dualVector))
    rw [Set.range_const]
    exact E6Coordinates.lattice_dual
  · change (simplexRatForm 2).dualSubmodule (coordinateIntegerLattice 2) =
      coordinateIntegerLattice 2 ⊔ Submodule.span ℤ (Set.range (fun _ : Fin 1 => simplexWeight 2))
    rw [Set.range_const]
    exact simplexRatForm_dual 2
  · exact A2SquareCoordinates.matchingVector_dual
  · change (standardRatForm 0).dualSubmodule (coordinateIntegerLattice 0) =
      coordinateIntegerLattice 0 ⊔ Submodule.span ℤ (Set.range (Fin.elim0 : Fin 0 → (Fin 0 → ℚ)))
    simp [standardRatForm_dual_coordinateIntegerLattice]
  · change K8Coordinates.form.dualSubmodule K8Coordinates.lattice =
      K8Coordinates.lattice ⊔ Submodule.span ℤ
        (Set.range (fun _ : Fin 1 => (2 : ℤ) • K8Coordinates.dualVector))
    rw [Set.range_const]
    exact k8_twice_dualVector_dual
  · change (simplexRatForm 4).dualSubmodule (coordinateIntegerLattice 4) =
      coordinateIntegerLattice 4 ⊔ Submodule.span ℤ
        (Set.range (fun _ : Fin 1 => (2 : ℤ) • simplexWeight 4))
    rw [Set.range_const]
    exact a4_twice_weight_dual
  · exact K4Coordinates.matchingVector_dual

theorem primaryModel_period (p : SmallOddPrime) (s : PrimaryShape) (i : Fin s.arity) :
    (p.modulus : ℤ) • primaryModelVector p s i ∈ primaryModelLattice p s := by
  cases p <;> cases s
  · exact Fin.elim0 i
  · exact E6Coordinates.three_smul_dualVector_mem
  · change (3 : ℤ) • simplexWeight 2 ∈ coordinateIntegerLattice 2
    simpa using succ_smul_simplexWeight_mem 2
  · exact A2SquareCoordinates.matchingVector_three_smul_mem i
  · exact Fin.elim0 i
  · change (5 : ℤ) • ((2 : ℤ) • K8Coordinates.dualVector) ∈ K8Coordinates.lattice
    rw [show (5 : ℤ) • ((2 : ℤ) • K8Coordinates.dualVector) =
      (2 : ℤ) • ((5 : ℤ) • K8Coordinates.dualVector) by module]
    exact Submodule.smul_mem _ (2 : ℤ) K8Coordinates.five_smul_dualVector_mem
  · change (5 : ℤ) • ((2 : ℤ) • simplexWeight 4) ∈ coordinateIntegerLattice 4
    rw [show (5 : ℤ) • ((2 : ℤ) • simplexWeight 4) =
      (2 : ℤ) • ((5 : ℤ) • simplexWeight 4) by module]
    exact Submodule.smul_mem _ (2 : ℤ) (by simpa using succ_smul_simplexWeight_mem 4)
  · exact K4Coordinates.matchingVector_five_smul_mem i

theorem primaryModel_cross (p : SmallOddPrime) (s : PrimaryShape) (i j : Fin s.arity) (hij : i ≠ j) :
    primaryModelForm p s (primaryModelVector p s i) (primaryModelVector p s j) ∈
      (1 : Submodule ℤ ℚ) := by
  cases p <;> cases s
  · exact Fin.elim0 i
  · exact (hij (Subsingleton.elim i j)).elim
  · exact (hij (Subsingleton.elim i j)).elim
  · change A2SquareCoordinates.form (A2SquareCoordinates.matchingVector i)
      (A2SquareCoordinates.matchingVector j) ∈ (1 : Submodule ℤ ℚ)
    rw [A2SquareCoordinates.matchingVector_cross i j hij]
    exact zero_mem _
  · exact Fin.elim0 i
  · exact (hij (Subsingleton.elim i j)).elim
  · exact (hij (Subsingleton.elim i j)).elim
  · change K4Coordinates.form (K4Coordinates.matchingVector i)
      (K4Coordinates.matchingVector j) ∈ (1 : Submodule ℤ ℚ)
    rw [K4Coordinates.matchingVector_cross i j hij]
    exact zero_mem _

theorem primaryModel_matched_norm (p : SmallOddPrime) (s : PrimaryShape) (i : Fin s.arity) :
    ∃ k : ℤ, primaryFraction p s i +
      primaryModelForm p s (primaryModelVector p s i) (primaryModelVector p s i) = 2 * (k : ℚ) := by
  cases p <;> cases s
  · exact Fin.elim0 i
  · refine ⟨2, ?_⟩
    change 2 / 3 + E6Coordinates.form E6Coordinates.dualVector E6Coordinates.dualVector = 2 * (2 : ℚ)
    rw [E6Coordinates.dualVector_norm]
    norm_num
  · refine ⟨1, ?_⟩
    change 4 / 3 + simplexRatForm 2 (simplexWeight 2) (simplexWeight 2) = 2 * (1 : ℚ)
    rw [simplexWeight_norm]
    norm_num
  · refine ⟨1, ?_⟩
    change 2 / 3 + A2SquareCoordinates.form (A2SquareCoordinates.matchingVector i)
      (A2SquareCoordinates.matchingVector i) = 2 * (1 : ℚ)
    rw [A2SquareCoordinates.matchingVector_norm]
    norm_num
  · exact Fin.elim0 i
  · refine ⟨1, ?_⟩
    change 2 / 5 + K8Coordinates.form ((2 : ℤ) • K8Coordinates.dualVector)
      ((2 : ℤ) • K8Coordinates.dualVector) = 2 * (1 : ℚ)
    rw [k8_twice_dualVector_norm]
    norm_num
  · refine ⟨2, ?_⟩
    change 4 / 5 + simplexRatForm 4 ((2 : ℤ) • simplexWeight 4)
      ((2 : ℤ) • simplexWeight 4) = 2 * (2 : ℚ)
    rw [a4_twice_weight_norm]
    norm_num
  · fin_cases i
    · refine ⟨1, ?_⟩
      change 2 / 5 + K4Coordinates.form (K4Coordinates.matchingVector 0)
        (K4Coordinates.matchingVector 0) = 2 * (1 : ℚ)
      rw [K4Coordinates.matchingVector_norm]
      norm_num
    · refine ⟨10, ?_⟩
      change 4 / 5 + K4Coordinates.form (K4Coordinates.matchingVector 1)
        (K4Coordinates.matchingVector 1) = 2 * (10 : ℚ)
      rw [K4Coordinates.matchingVector_norm]
      norm_num

end SRG266.Lattice
