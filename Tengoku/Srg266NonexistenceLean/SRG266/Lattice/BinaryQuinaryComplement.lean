/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.K4Coordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CyclicSelfDual
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.EvenGlue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

namespace K4Coordinates

def matchingVector (i : Fin 2) : Space := (2 : ℤ) • (if i = 0 then dualA else dualB)

theorem matchingVector_five_smul_mem (i : Fin 2) : (5 : ℤ) • matchingVector i ∈ lattice := by
  have h : (5 : ℤ) • (if i = 0 then dualA else dualB) ∈ lattice := by
    split_ifs <;> first | exact five_smul_dualA_mem | exact five_smul_dualB_mem
  have heq : (5 : ℤ) • matchingVector i =
      (2 : ℤ) • ((5 : ℤ) • (if i = 0 then dualA else dualB)) := by
    dsimp [matchingVector]
    module
  rw [heq]
  exact lattice.smul_mem _ h

theorem matchingVector_norm (i : Fin 2) :
    form (matchingVector i) (matchingVector i) = if i = 0 then 8 / 5 else 96 / 5 := by
  have heq : matchingVector i = (2 : ℚ) • (if i = 0 then dualA else dualB) := by
    dsimp [matchingVector]
    module
  rw [heq]
  split_ifs <;> norm_num [dualA_norm, dualB_norm]

theorem matchingVector_cross (i j : Fin 2) (hij : i ≠ j) :
    form (matchingVector i) (matchingVector j) = 0 := by
  have heq (k : Fin 2) : matchingVector k = (2 : ℚ) • (if k = 0 then dualA else dualB) := by
    dsimp [matchingVector]
    module
  have hba : form dualB dualA = 0 := by rw [form_isSymm.eq, dualA_pair_dualB]
  fin_cases i <;> fin_cases j <;> simp_all [dualA_pair_dualB]

theorem matchingVector_dual : form.dualSubmodule lattice =
    lattice ⊔ Submodule.span ℤ (Set.range matchingVector) := by
  have hr : Set.range matchingVector = {(2 : ℤ) • dualA, (2 : ℤ) • dualB} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [matchingVector]
    · intro hz
      rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz :
        z = (2 : ℤ) • dualA ∨ z = (2 : ℤ) • dualB) with rfl | rfl
      · exact ⟨0, by simp [matchingVector]⟩
      · exact ⟨1, by simp [matchingVector]⟩
  rw [hr, lattice_dual]
  have ha := sup_span_smul_eq_of_bezout (p := 5) (a := 2) (b := 3) (k := -1)
    five_smul_dualA_mem (by norm_num)
  have hb := sup_span_smul_eq_of_bezout (p := 5) (a := 2) (b := 3) (k := -1)
    five_smul_dualB_mem (by norm_num)
  have hpair (a b : Space) : lattice ⊔ Submodule.span ℤ {a, b} =
      (lattice ⊔ Submodule.span ℤ {a}) ⊔ (lattice ⊔ Submodule.span ℤ {b}) := by
    rw [show ({a, b} : Set Space) = {a} ∪ {b} by ext; simp [or_comm], Submodule.span_union]
    exact sup_sup_distrib_left _ _ _
  rw [hpair, hpair, ha, hb]

end K4Coordinates

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {N : Submodule ℤ W}

def quinaryBinaryLattice (N : Submodule ℤ W) (u : Fin 2 → W) :
    Submodule ℤ (W × K4Coordinates.Space) :=
  glueLattice N K4Coordinates.lattice (fun i => (u i, K4Coordinates.matchingVector i))

theorem complete_quinary_binary (u : Fin 2 → W)
    (hsB : B.IsSymm) (hlN : IsLattice ℚ N) (hiN : IsIntegral B N) (heN : IsEven B N)
    (hdN : B.dualSubmodule N = N ⊔ Submodule.span ℤ (Set.range u))
    (hcross : ∀ i j, i ≠ j → B (u i) (u j) ∈ (1 : Submodule ℤ ℚ))
    (hnorm : ∀ i, ∃ k : ℤ, B (u i) (u i) =
      (if i = 0 then 2 / 5 else 4 / 5) + 2 * (k : ℚ)) :
    IsLattice ℚ (quinaryBinaryLattice N u) ∧
      IsEven (prodForm B K4Coordinates.form) (quinaryBinaryLattice N u) ∧
      (prodForm B K4Coordinates.form).dualSubmodule (quinaryBinaryLattice N u) =
        quinaryBinaryLattice N u := by
  have hdiag (i : Fin 2) : ∃ k : ℤ,
      B (u i) (u i) + K4Coordinates.form (K4Coordinates.matchingVector i)
        (K4Coordinates.matchingVector i) = 2 * (k : ℚ) := by
    obtain ⟨k, hk⟩ := hnorm i
    rw [hk, K4Coordinates.matchingVector_norm]
    split_ifs
    · refine ⟨k + 1, ?_⟩
      push_cast
      ring
    · refine ⟨k + 10, ?_⟩
      push_cast
      ring
  refine complete_even_glue u K4Coordinates.matchingVector (fun _ => 5)
    hsB K4Coordinates.form_isSymm hlN K4Coordinates.lattice_isLattice
    hiN K4Coordinates.lattice_isIntegral heN K4Coordinates.lattice_isEven
    hdN K4Coordinates.matchingVector_dual K4Coordinates.matchingVector_five_smul_mem
    hcross ?_ hdiag ?_
  · intro i j hij
    rw [K4Coordinates.matchingVector_cross i j hij]
    exact zero_mem _
  · intro i
    obtain ⟨k, hk⟩ := hnorm i
    split_ifs at hk
    · exact norm_denominator_unit (p := 5) (r := 2) (by norm_num) ⟨1, -2, by norm_num⟩ hk
    · exact norm_denominator_unit (p := 5) (r := 4) (by norm_num) ⟨1, -1, by norm_num⟩ hk

end SRG266.Lattice
