/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.H6Coordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.MixedPrimaryCompletion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice.H6Coordinates

def matchingVector : Fin 1 ⊕ Fin 1 → Space :=
  Sum.elim (fun _ => dualThree) (fun _ => (2 : ℤ) • dualFive)

/--
@isnad1 id=eq.0h0v.s10.27055207b2a5 from=translated src=- shape=d3074da7 vocab=031cd6d9
-/
theorem twice_dualFive_norm : form ((2 : ℤ) • dualFive) ((2 : ℤ) • dualFive) = 8 / 5 := by
  have h : (2 : ℤ) • dualFive = (2 : ℚ) • dualFive := by module
  rw [h]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, dualFive_norm]
  norm_num

/--
@isnad1 id=eq.0h0v.s10.3cf3fd05253c from=translated src=- shape=9cfe1072 vocab=2244d6f8
-/
theorem matchingVector_dual : form.dualSubmodule lattice =
    lattice ⊔ Submodule.span ℤ (Set.range matchingVector) := by
  have hr : Set.range matchingVector = {dualThree, (2 : ℤ) • dualFive} := by
    ext z
    simp [matchingVector, Set.Sum.elim_range, or_comm]
  rw [hr, lattice_dual, sup_span_pair, sup_span_pair]
  rw [sup_span_smul_eq_of_bezout (b := 3) (k := -1) five_smul_dualFive_mem (by norm_num)]

/--
@isnad1 id=mem.0h1v.s8.92204ef96fe1 from=translated src=- shape=7559990f vocab=225e0d8e
-/
theorem matchingVector_period (i : Fin 1 ⊕ Fin 1) :
    mixedPrimaryPeriod .two .two i • matchingVector i ∈ lattice := by
  rcases i with i | i
  · exact three_smul_dualThree_mem
  · change (5 : ℤ) • ((2 : ℤ) • dualFive) ∈ lattice
    rw [show (5 : ℤ) • ((2 : ℤ) • dualFive) = (2 : ℤ) • ((5 : ℤ) • dualFive) by module]
    exact lattice.smul_mem 2 five_smul_dualFive_mem

/--
@isnad1 id=mem.1h2v.s10.56a2faa6215d from=translated src=- shape=296d1342 vocab=3d28865f
-/
theorem matchingVector_cross (i j : Fin 1 ⊕ Fin 1) (hij : i ≠ j) :
    form (matchingVector i) (matchingVector j) ∈ (1 : Submodule ℤ ℚ) := by
  rcases i with i | i <;> rcases j with j | j
  · exact (hij (congrArg Sum.inl (Subsingleton.elim i j))).elim
  · change form dualThree ((2 : ℤ) • dualFive) ∈ (1 : Submodule ℤ ℚ)
    rw [map_zsmul, dualThree_pair_dualFive, smul_zero]
    exact zero_mem _
  · change form ((2 : ℤ) • dualFive) dualThree ∈ (1 : Submodule ℤ ℚ)
    rw [form_isSymm.eq, map_zsmul, dualThree_pair_dualFive, smul_zero]
    exact zero_mem _
  · exact (hij (congrArg Sum.inr (Subsingleton.elim i j))).elim

end SRG266.Lattice.H6Coordinates

namespace SRG266.Lattice

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {N : Submodule ℤ W}

def h6CompletionLattice (S : PrimaryFamily B N .three .two) (T : PrimaryFamily B N .five .two) :
    Submodule ℤ (W × H6Coordinates.Space) :=
  glueLattice N H6Coordinates.lattice (fun i => (mixedPrimarySource S T i, H6Coordinates.matchingVector i))

/--
@isnad1 id=and.5h5v.s10.0d2000fb5fc6 from=translated src=- shape=a0cff625 vocab=fa14efbe
-/
theorem complete_h6 (S : PrimaryFamily B N .three .two) (T : PrimaryFamily B N .five .two)
    (hs : B.IsSymm) (hl : IsLattice ℚ N) (hi : IsIntegral B N) (he : IsEven B N)
    (hd : B.dualSubmodule N = torsionPart B N 3 ⊔ torsionPart B N 5) :
    IsLattice ℚ (h6CompletionLattice S T) ∧
      IsEven (prodForm B H6Coordinates.form) (h6CompletionLattice S T) ∧
      (prodForm B H6Coordinates.form).dualSubmodule (h6CompletionLattice S T) =
        h6CompletionLattice S T := by
  refine complete_even_glue (mixedPrimarySource S T) H6Coordinates.matchingVector
    (mixedPrimaryPeriod .two .two) hs H6Coordinates.form_isSymm hl H6Coordinates.lattice_isLattice
    hi H6Coordinates.lattice_isIntegral he H6Coordinates.lattice_isEven
    (mixedPrimarySource_dual S T hd) H6Coordinates.matchingVector_dual
    H6Coordinates.matchingVector_period (mixedPrimarySource_cross S T hs)
    H6Coordinates.matchingVector_cross ?_ ?_
  · rintro (i | i)
    · obtain ⟨k, hk⟩ := S.norm i
      refine ⟨k + 2, ?_⟩
      change B (S.vec i) (S.vec i) + H6Coordinates.form H6Coordinates.dualThree H6Coordinates.dualThree = _
      rw [hk, H6Coordinates.dualThree_norm]
      norm_num [primaryFraction, primaryNumerator, SmallOddPrime.modulus]
      ring
    · obtain ⟨k, hk⟩ := T.norm i
      refine ⟨k + 1, ?_⟩
      change B (T.vec i) (T.vec i) + H6Coordinates.form ((2 : ℤ) • H6Coordinates.dualFive)
        ((2 : ℤ) • H6Coordinates.dualFive) = _
      rw [hk, H6Coordinates.twice_dualFive_norm]
      norm_num [primaryFraction, primaryNumerator, SmallOddPrime.modulus]
      ring
  · rintro (i | i) a ha
    · exact S.unit i a ha
    · exact T.unit i a ha

end SRG266.Lattice
