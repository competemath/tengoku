/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.SmallPrimaryModels
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.PrimaryNormalForms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {N : Submodule ℤ W}

structure PrimaryFamily (B : LinearMap.BilinForm ℚ W) (N : Submodule ℤ W)
    (p : SmallOddPrime) (s : PrimaryShape) where
  vec : Fin s.arity → W
  spans : torsionPart B N p.modulus = N ⊔ Submodule.span ℤ (Set.range vec)
  mem : ∀ i, vec i ∈ torsionPart B N p.modulus
  cross : ∀ i j, i ≠ j → B (vec i) (vec j) ∈ (1 : Submodule ℤ ℚ)
  norm : ∀ i, ∃ k : ℤ, B (vec i) (vec i) = primaryFraction p s i + 2 * (k : ℚ)

theorem HasPrimaryNormalForm.exists_family {p : SmallOddPrime}
    (hs : B.IsSymm) (h : HasPrimaryNormalForm B N p.modulus p.binaryNumerator) :
    ∃ s : PrimaryShape, Nonempty (PrimaryFamily B N p s) := by
  rcases h with h | ⟨u, r, k, hr, hsp, hn⟩ | ⟨u, v, hsp, hc, hu, hv⟩
  · refine ⟨.zero, ⟨{
      vec := Fin.elim0
      mem := fun i => Fin.elim0 i
      spans := ?_
      cross := fun i => Fin.elim0 i
      norm := fun i => Fin.elim0 i }⟩⟩
    simpa using h
  · rcases hr with rfl | rfl
    · refine ⟨.two, ⟨{
        vec := fun _ => u
        spans := ?_
        mem := ?_
        cross := ?_
        norm := ?_ }⟩⟩
      · simpa only [Set.range_const] using hsp
      · intro i
        rw [hsp]
        exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
      · intro i j hij
        exact (hij (Subsingleton.elim i j)).elim
      · intro i
        exact ⟨k, hn⟩
    · refine ⟨.four, ⟨{
        vec := fun _ => u
        spans := ?_
        mem := ?_
        cross := ?_
        norm := ?_ }⟩⟩
      · simpa only [Set.range_const] using hsp
      · intro i
        rw [hsp]
        exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
      · intro i j hij
        exact (hij (Subsingleton.elim i j)).elim
      · intro i
        exact ⟨k, hn⟩
  · let w : Fin 2 → W := fun i => if i = 0 then u else v
    have hw : Set.range w = {u, v} := by
      rw [range_fin_two_eq_pair]
      simp [w]
    refine ⟨.binary, ⟨{ vec := w, spans := ?_, mem := ?_, cross := ?_, norm := ?_ }⟩⟩
    · rw [hw]
      exact hsp
    · intro i
      rw [hsp, ← hw]
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · simpa [w] using hc
      · simpa [w, hs.eq v u] using hc
      · exact (hij rfl).elim
    · intro i
      fin_cases i
      · obtain ⟨k, hk⟩ := hu
        refine ⟨k, ?_⟩
        cases p <;> simpa [w, primaryFraction, primaryNumerator] using hk
      · obtain ⟨k, hk⟩ := hv
        refine ⟨k, ?_⟩
        cases p <;> simpa [w, primaryFraction, primaryNumerator,
          SmallOddPrime.binaryNumerator] using hk

omit [AddCommGroup W] [Module ℚ W] in
theorem primaryFraction_unit (p : SmallOddPrime) (s : PrimaryShape) (i : Fin s.arity)
    (k a : ℤ) (h : (a : ℚ) * (primaryFraction p s i + 2 * (k : ℚ)) ∈
      (1 : Submodule ℤ ℚ)) : (p.modulus : ℤ) ∣ a := by
  have hcop : IsCoprime (p.modulus : ℤ) (primaryNumerator p s i) := by
    cases p <;> cases s
    · exact Fin.elim0 i
    · exact ⟨1, -1, by norm_num [SmallOddPrime.modulus, primaryNumerator]⟩
    · exact ⟨-1, 1, by norm_num [SmallOddPrime.modulus, primaryNumerator]⟩
    · exact ⟨1, -1, by norm_num [SmallOddPrime.modulus, primaryNumerator]⟩
    · exact Fin.elim0 i
    · exact ⟨1, -2, by norm_num [SmallOddPrime.modulus, primaryNumerator]⟩
    · exact ⟨1, -1, by norm_num [SmallOddPrime.modulus, primaryNumerator]⟩
    · fin_cases i
      · exact ⟨1, -2, by norm_num [SmallOddPrime.modulus, primaryNumerator]⟩
      · exact ⟨1, -1, by norm_num [SmallOddPrime.modulus, primaryNumerator]⟩
  refine norm_denominator_unit (k := k)
    (by cases p <;> norm_num [SmallOddPrime.modulus]) hcop ?_ a h
  simp only [primaryFraction, Int.cast_natCast]

theorem PrimaryFamily.unit {p : SmallOddPrime} {s : PrimaryShape}
    (S : PrimaryFamily B N p s) (i : Fin s.arity) (a : ℤ)
    (h : (a : ℚ) * B (S.vec i) (S.vec i) ∈ (1 : Submodule ℤ ℚ)) : (p.modulus : ℤ) ∣ a := by
  obtain ⟨k, hk⟩ := S.norm i
  rw [hk] at h
  exact primaryFraction_unit p s i k a h

end SRG266.Lattice
