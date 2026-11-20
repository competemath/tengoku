/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Q15Coordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.MixedPrimaryCompletion
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.SimplexRootChain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice.A4Q15Coordinates

abbrev Space := (Fin 4 → ℚ) × Q15Coordinates.Space
def form : LinearMap.BilinForm ℚ Space := prodForm (simplexRatForm 4) Q15Coordinates.form
def lattice : Submodule ℤ Space := (coordinateIntegerLattice 4).prod Q15Coordinates.lattice

def matchingVector : Fin 1 ⊕ Fin 2 → Space :=
  Sum.elim (fun _ => (0, Q15Coordinates.dualThree))
    (fun i => if i = 0 then (0, (2 : ℤ) • Q15Coordinates.dualFive)
      else ((2 : ℤ) • simplexWeight 4, 0))

theorem form_isSymm : form.IsSymm :=
  prodForm_isSymm (simplexRatForm_isSymm 4) Q15Coordinates.form_isSymm

theorem form_posDef : ∀ x : Space, x ≠ 0 → 0 < form x x :=
  prodForm_posDef (simplexRatForm_posDef 4) Q15Coordinates.form_posDef

theorem lattice_isLattice : IsLattice ℚ lattice :=
  isLattice_prod (coordinateIntegerLattice_isLattice 4) Q15Coordinates.lattice_isLattice

theorem lattice_isIntegral : IsIntegral form lattice :=
  isIntegral_prod (simplexRatForm_isIntegral 4) Q15Coordinates.lattice_isIntegral

theorem lattice_isEven : IsEven form lattice :=
  isEven_prod (simplexRatForm_isEven 4) Q15Coordinates.lattice_isEven

theorem space_finrank : Module.finrank ℚ Space = 6 := by
  rw [Module.finrank_prod]
  norm_num [Space, Q15Coordinates.Space]

theorem matchingVector_dual : form.dualSubmodule lattice =
    lattice ⊔ Submodule.span ℤ (Set.range matchingVector) := by
  let u : Fin 1 → (Fin 4 → ℚ) := fun _ => (2 : ℤ) • simplexWeight 4
  let v : Fin 2 → Q15Coordinates.Space := ![Q15Coordinates.dualThree,
    (2 : ℤ) • Q15Coordinates.dualFive]
  have hu : (simplexRatForm 4).dualSubmodule (coordinateIntegerLattice 4) =
      coordinateIntegerLattice 4 ⊔ Submodule.span ℤ (Set.range u) := by
    rw [range_fin_one_eq_singleton]
    exact a4_twice_weight_dual
  have hv : Q15Coordinates.form.dualSubmodule Q15Coordinates.lattice =
      Q15Coordinates.lattice ⊔ Submodule.span ℤ (Set.range v) := by
    rw [range_fin_two_eq_pair]
    change Q15Coordinates.form.dualSubmodule Q15Coordinates.lattice =
      Q15Coordinates.lattice ⊔ Submodule.span ℤ
        {Q15Coordinates.dualThree, (2 : ℤ) • Q15Coordinates.dualFive}
    rw [Q15Coordinates.lattice_dual, sup_span_pair, sup_span_pair,
      sup_span_smul_eq_of_bezout (b := 3) (k := -1)
        Q15Coordinates.five_smul_dualFive_mem (by norm_num)]
  have hr : Set.range (Sum.elim (fun i => (u i, (0 : Q15Coordinates.Space)))
      (fun j => ((0 : Fin 4 → ℚ), v j))) = Set.range matchingVector := by
    simp only [matchingVector, Set.Sum.elim_range, range_fin_one_eq_singleton,
      range_fin_two_eq_pair]
    ext z
    simp [u, v, or_left_comm, or_comm]
  rw [form, lattice, dualSubmodule_prodForm, hu, hv, prod_sup_span_ranges, hr]

theorem matchingVector_period (i : Fin 1 ⊕ Fin 2) :
    mixedPrimaryPeriod .four .binary i • matchingVector i ∈ lattice := by
  have hQ : (5 : ℤ) • ((2 : ℤ) • Q15Coordinates.dualFive) ∈ Q15Coordinates.lattice := by
    rw [show (5 : ℤ) • ((2 : ℤ) • Q15Coordinates.dualFive) =
      (2 : ℤ) • ((5 : ℤ) • Q15Coordinates.dualFive) by module]
    exact Submodule.smul_mem _ 2 Q15Coordinates.five_smul_dualFive_mem
  have hA : (5 : ℤ) • ((2 : ℤ) • simplexWeight 4) ∈ coordinateIntegerLattice 4 := by
    rw [show (5 : ℤ) • ((2 : ℤ) • simplexWeight 4) =
      (2 : ℤ) • ((5 : ℤ) • simplexWeight 4) by module]
    exact Submodule.smul_mem _ 2 (by simpa using succ_smul_simplexWeight_mem 4)
  rcases i with i | i
  · exact ⟨by simp [matchingVector, mixedPrimaryPeriod], Q15Coordinates.three_smul_dualThree_mem⟩
  · fin_cases i
    · exact ⟨by simp [matchingVector, mixedPrimaryPeriod], hQ⟩
    · exact ⟨hA, by simp [matchingVector, mixedPrimaryPeriod]⟩

theorem matchingVector_norm_three (i : Fin 1) :
    form (matchingVector (.inl i)) (matchingVector (.inl i)) = 2/3 := by
  simpa [matchingVector, form, prodForm_apply] using Q15Coordinates.dualThree_norm

theorem matchingVector_norm_five (i : Fin 2) :
    form (matchingVector (.inr i)) (matchingVector (.inr i)) =
      if i = 0 then 8/5 else 16/5 := by
  have hQ : Q15Coordinates.form ((2 : ℤ) • Q15Coordinates.dualFive)
      ((2 : ℤ) • Q15Coordinates.dualFive) = 8/5 := by
    rw [show (2 : ℤ) • Q15Coordinates.dualFive = (2 : ℚ) • Q15Coordinates.dualFive by module]
    norm_num [Q15Coordinates.dualFive_norm]
  fin_cases i
  · simpa [matchingVector, form, prodForm_apply] using hQ
  · simpa [matchingVector, form, prodForm_apply] using a4_twice_weight_norm

theorem matchingVector_cross (i j : Fin 1 ⊕ Fin 2) (hij : i ≠ j) :
    form (matchingVector i) (matchingVector j) ∈ (1 : Submodule ℤ ℚ) := by
  rcases i with i | i <;> rcases j with j | j
  · exact (hij (congrArg Sum.inl (Subsingleton.elim i j))).elim
  · fin_cases j <;> norm_num [matchingVector, form, prodForm_apply,
      Q15Coordinates.form_apply, Q15Coordinates.dualThree, Q15Coordinates.dualFive]
  · fin_cases i <;> norm_num [matchingVector, form, prodForm_apply,
      Q15Coordinates.form_apply, Q15Coordinates.dualThree, Q15Coordinates.dualFive]
  · fin_cases i <;> fin_cases j <;>
      simp_all [matchingVector, form, prodForm_apply]

theorem has_A4_chain : ∃ r : Fin 4 → Space,
    (∀ i, r i ∈ lattice) ∧
    (∀ i j, form (r i) (r j) = (gramA 4 i j : ℚ)) := by
  refine ⟨fun i => (simplexSimpleRoot 4 i, 0), ?_, ?_⟩
  · intro i
    exact ⟨simplexSimpleRoot_mem 4 i, zero_mem _⟩
  · intro i j
    simpa [form, prodForm_apply] using simplexSimpleRoot_gram 4 i j

end SRG266.Lattice.A4Q15Coordinates

namespace SRG266.Lattice

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {N : Submodule ℤ W}

def a4Q15CompletionLattice (S : PrimaryFamily B N .three .four)
    (T : PrimaryFamily B N .five .binary) : Submodule ℤ (W × A4Q15Coordinates.Space) :=
  glueLattice N A4Q15Coordinates.lattice
    (fun i => (mixedPrimarySource S T i, A4Q15Coordinates.matchingVector i))

theorem complete_a4Q15 (S : PrimaryFamily B N .three .four)
    (T : PrimaryFamily B N .five .binary)
    (hs : B.IsSymm) (hl : IsLattice ℚ N) (hi : IsIntegral B N) (he : IsEven B N)
    (hd : B.dualSubmodule N = torsionPart B N 3 ⊔ torsionPart B N 5) :
    IsLattice ℚ (a4Q15CompletionLattice S T) ∧
      IsEven (prodForm B A4Q15Coordinates.form) (a4Q15CompletionLattice S T) ∧
      (prodForm B A4Q15Coordinates.form).dualSubmodule (a4Q15CompletionLattice S T) =
        a4Q15CompletionLattice S T := by
  refine complete_even_glue (mixedPrimarySource S T) A4Q15Coordinates.matchingVector
    (mixedPrimaryPeriod .four .binary) hs A4Q15Coordinates.form_isSymm
    hl A4Q15Coordinates.lattice_isLattice hi A4Q15Coordinates.lattice_isIntegral
    he A4Q15Coordinates.lattice_isEven (mixedPrimarySource_dual S T hd)
    A4Q15Coordinates.matchingVector_dual A4Q15Coordinates.matchingVector_period
    (mixedPrimarySource_cross S T hs) A4Q15Coordinates.matchingVector_cross ?_ ?_
  · rintro (i | i)
    · obtain ⟨k, hk⟩ := S.norm i
      refine ⟨k+1, ?_⟩
      change B (S.vec i) (S.vec i) +
        A4Q15Coordinates.form (A4Q15Coordinates.matchingVector (.inl i))
          (A4Q15Coordinates.matchingVector (.inl i)) = _
      rw [hk, A4Q15Coordinates.matchingVector_norm_three]
      norm_num [primaryFraction, primaryNumerator, SmallOddPrime.modulus]
      ring
    · obtain ⟨k, hk⟩ := T.norm i
      change ∃ n : ℤ, B (T.vec i) (T.vec i) +
        A4Q15Coordinates.form (A4Q15Coordinates.matchingVector (.inr i))
          (A4Q15Coordinates.matchingVector (.inr i)) = 2*(n : ℚ)
      rw [hk, A4Q15Coordinates.matchingVector_norm_five]
      fin_cases i
      · refine ⟨k+1, ?_⟩
        norm_num [primaryFraction, primaryNumerator, SmallOddPrime.modulus,
          SmallOddPrime.binaryNumerator]
        ring
      · refine ⟨k+2, ?_⟩
        norm_num [primaryFraction, primaryNumerator, SmallOddPrime.modulus,
          SmallOddPrime.binaryNumerator]
        ring
  · rintro (i | i) a ha
    · exact S.unit i a ha
    · exact T.unit i a ha

end SRG266.Lattice
