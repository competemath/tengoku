/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import Tengoku.Compply.CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Combinations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Mulders-Storjohann Correctness Reduction Invariants

Shape, well-formedness, row-span, and weak-Popov correctness for the reducer.
-/

@[expose] public section

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/--
@isnad1 id=eq.1h5v.s6.775250590d26 from=translated src=- shape=a1f3560d vocab=f12de1fc
-/
theorem muldersStorjohannStep_shape_preserved
    {M : PolynomialMatrix F} (shift : Array Nat) {i j : Nat} (hM : WellFormed M) :
    MatrixShape (muldersStorjohannStep M shift i j) = MatrixShape M := by
  simp only [muldersStorjohannStep, Array.getD_eq_getD_getElem?]
  cases hI : rowShiftedDegree? (M[i]?.getD #[]) shift with
  | none =>
      simp
  | some degI =>
      cases hJ : rowShiftedDegree? (M[j]?.getD #[]) shift with
      | none =>
          simp
      | some degJ =>
          simp only
          have hi : i < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hI
          have hj : j < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hJ
          split
          · apply replaceRow_shape
            simpa [Array.getD_eq_getD_getElem?] using
              cancelShiftedLeadingTerm_size_of_wellFormed hM hj hi shift
          · apply replaceRow_shape
            simpa [Array.getD_eq_getD_getElem?] using
              cancelShiftedLeadingTerm_size_of_wellFormed hM hi hj shift

/--
@isnad1 id=le.1h5v.s6.a9f242933d65 from=translated src=- shape=0b59dff5 vocab=b7e4e878
-/
theorem muldersStorjohannStep_rowSpan_subset
    {M : PolynomialMatrix F} (shift : Array Nat) {i j : Nat} (hM : WellFormed M) :
    RowSpan (muldersStorjohannStep M shift i j) ⊆ RowSpan M := by
  apply rowSpan_subset_of_rows_mem hM
  · exact congrArg PolynomialMatrixShape.width
      (muldersStorjohannStep_shape_preserved shift hM)
  · intro row hrow
    simp only [muldersStorjohannStep, Array.getD_eq_getD_getElem?] at hrow
    cases hI : rowShiftedDegree? (M[i]?.getD #[]) shift with
    | none =>
        exact matrix_row_mem_rowSpan hM (by simpa [hI] using hrow)
    | some degI =>
        cases hJ : rowShiftedDegree? (M[j]?.getD #[]) shift with
        | none =>
            exact matrix_row_mem_rowSpan hM (by simpa [hI, hJ] using hrow)
        | some degJ =>
            have hi : i < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hI
            have hj : j < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hJ
            have hrowI : (M[i]?.getD #[]) ∈ RowSpan M := by
              have hget : M[i]?.getD #[] = M[i] := by
                simp [Array.getElem?_eq_getElem hi]
              rw [hget]
              exact matrix_row_mem_rowSpan hM
                (by simp [MatrixRows, Array.getElem_mem_toList hi])
            have hrowJ : (M[j]?.getD #[]) ∈ RowSpan M := by
              have hget : M[j]?.getD #[] = M[j] := by
                simp [Array.getElem?_eq_getElem hj]
              rw [hget]
              exact matrix_row_mem_rowSpan hM
                (by simp [MatrixRows, Array.getElem_mem_toList hj])
            simp [hI, hJ] at hrow
            split at hrow
            · exact replaceRow_rows_mem_rowSpan hM
                (cancelShiftedLeadingTerm_mem_rowSpan hrowJ hrowI) hrow
            · exact replaceRow_rows_mem_rowSpan hM
                (cancelShiftedLeadingTerm_mem_rowSpan hrowI hrowJ) hrow

/--
@isnad1 id=le.4h5v.s7.a9fc757f5ca0 from=translated src=- shape=c9c623a5 vocab=a1ccced2
-/
theorem muldersStorjohannStep_rowSpan_superset
    {M : PolynomialMatrix F} (shift : Array Nat) {i j : Nat}
    (hM : WellFormed M) (hi : i < M.size) (hj : j < M.size) (hne : i ≠ j) :
    RowSpan M ⊆ RowSpan (muldersStorjohannStep M shift i j) := by
  apply rowSpan_subset_of_rows_mem
  · simp only [muldersStorjohannStep, Array.getD_eq_getD_getElem?]
    cases hI : rowShiftedDegree? (M[i]?.getD #[]) shift with
    | none =>
        simpa [hI] using hM
    | some degI =>
        cases hJ : rowShiftedDegree? (M[j]?.getD #[]) shift with
        | none =>
            simpa [hI, hJ] using hM
        | some degJ =>
            simp only
            split
            · apply replaceRow_wellFormed hM
              simpa [Array.getD_eq_getD_getElem?] using
                cancelShiftedLeadingTerm_size_of_wellFormed hM hj hi shift
            · apply replaceRow_wellFormed hM
              simpa [Array.getD_eq_getD_getElem?] using
                cancelShiftedLeadingTerm_size_of_wellFormed hM hi hj shift
  · exact (congrArg PolynomialMatrixShape.width
      (muldersStorjohannStep_shape_preserved shift hM)).symm
  · intro row hrow
    rcases List.getElem_of_mem hrow with ⟨k, hk, hget⟩
    have hkM : k < M.size := by
      simpa [MatrixRows] using hk
    have hrow_eq : M[k] = row := by
      simpa [MatrixRows, Array.getElem_toList] using hget
    rw [← hrow_eq]
    simp only [muldersStorjohannStep, Array.getD_eq_getD_getElem?]
    cases hI : rowShiftedDegree? (M[i]?.getD #[]) shift with
    | none =>
        exact matrix_row_mem_rowSpan hM
          (by simp [MatrixRows, Array.getElem_mem_toList hkM])
    | some degI =>
        cases hJ : rowShiftedDegree? (M[j]?.getD #[]) shift with
        | none =>
            exact matrix_row_mem_rowSpan hM
              (by simp [MatrixRows, Array.getElem_mem_toList hkM])
        | some degJ =>
            have hcancelJ_size :
                (cancelShiftedLeadingTerm (M[j]?.getD #[]) (M[i]?.getD #[]) shift).size =
                  MatrixWidth M := by
              simpa [Array.getD_eq_getD_getElem?] using
                cancelShiftedLeadingTerm_size_of_wellFormed hM hj hi shift
            have hreplaceJ_wf :
                WellFormed
                  (replaceRow M j
                    (cancelShiftedLeadingTerm (M[j]?.getD #[]) (M[i]?.getD #[]) shift)) :=
              replaceRow_wellFormed hM hcancelJ_size
            have hcancelI_size :
                (cancelShiftedLeadingTerm (M[i]?.getD #[]) (M[j]?.getD #[]) shift).size =
                  MatrixWidth M := by
              simpa [Array.getD_eq_getD_getElem?] using
                cancelShiftedLeadingTerm_size_of_wellFormed hM hi hj shift
            have hreplaceI_wf :
                WellFormed
                  (replaceRow M i
                    (cancelShiftedLeadingTerm (M[i]?.getD #[]) (M[j]?.getD #[]) shift)) :=
              replaceRow_wellFormed hM hcancelI_size
            have hrowI : (M[i]?.getD #[]) ∈
                RowSpan
                  (replaceRow M j
                    (cancelShiftedLeadingTerm (M[j]?.getD #[]) (M[i]?.getD #[]) shift)) := by
              have hgetI : M[i]?.getD #[] = M[i] := by
                simp [Array.getElem?_eq_getElem hi]
              exact matrix_row_mem_rowSpan hreplaceJ_wf
                (by simpa [hgetI] using replaceRow_oldRow_mem hi (by exact hne.symm))
            have hrowJ : (M[j]?.getD #[]) ∈
                RowSpan
                  (replaceRow M i
                    (cancelShiftedLeadingTerm (M[i]?.getD #[]) (M[j]?.getD #[]) shift)) := by
              have hgetJ : M[j]?.getD #[] = M[j] := by
                simp [Array.getElem?_eq_getElem hj]
              exact matrix_row_mem_rowSpan hreplaceI_wf
                (by simpa [hgetJ] using replaceRow_oldRow_mem hj hne)
            by_cases hdeg : degI ≤ degJ
            · simp only [hdeg, ite_true]
              by_cases hkj : k = j
              · subst k
                have hcancel : cancelShiftedLeadingTerm (M[j]?.getD #[])
                    (M[i]?.getD #[]) shift ∈
                    RowSpan
                      (replaceRow M j
                        (cancelShiftedLeadingTerm (M[j]?.getD #[]) (M[i]?.getD #[]) shift)) := by
                  exact matrix_row_mem_rowSpan hreplaceJ_wf (replaceRow_newRow_mem hj)
                have hsize : (M[i]?.getD #[]).size = (M[j]?.getD #[]).size := by
                  rw [matrix_getElem?_getD_size_of_wellFormed hM hi,
                    matrix_getElem?_getD_size_of_wellFormed hM hj]
                have htarget : (M[j]?.getD #[]) ∈
                    RowSpan
                      (replaceRow M j
                        (cancelShiftedLeadingTerm (M[j]?.getD #[]) (M[i]?.getD #[]) shift)) :=
                  cancelShiftedLeadingTerm_target_mem_rowSpan hcancel hrowI hsize
                simpa [Array.getElem?_eq_getElem hj] using htarget
              · have hne' : j ≠ k := fun h ↦ hkj h.symm
                exact matrix_row_mem_rowSpan hreplaceJ_wf (replaceRow_oldRow_mem hkM hne')
            · simp only [hdeg, ite_false]
              by_cases hki : k = i
              · subst k
                have hcancel : cancelShiftedLeadingTerm (M[i]?.getD #[])
                    (M[j]?.getD #[]) shift ∈
                    RowSpan
                      (replaceRow M i
                        (cancelShiftedLeadingTerm (M[i]?.getD #[]) (M[j]?.getD #[]) shift)) := by
                  exact matrix_row_mem_rowSpan hreplaceI_wf (replaceRow_newRow_mem hi)
                have hsize : (M[j]?.getD #[]).size = (M[i]?.getD #[]).size := by
                  rw [matrix_getElem?_getD_size_of_wellFormed hM hj,
                    matrix_getElem?_getD_size_of_wellFormed hM hi]
                have htarget : (M[i]?.getD #[]) ∈
                    RowSpan
                      (replaceRow M i
                        (cancelShiftedLeadingTerm (M[i]?.getD #[]) (M[j]?.getD #[]) shift)) :=
                  cancelShiftedLeadingTerm_target_mem_rowSpan hcancel hrowJ hsize
                simpa [Array.getElem?_eq_getElem hi] using htarget
              · have hne' : i ≠ k := fun h ↦ hki h.symm
                exact matrix_row_mem_rowSpan hreplaceI_wf (replaceRow_oldRow_mem hkM hne')

/--
@isnad1 id=wellform.1h5v.s6.53e0d9548c1f from=translated src=- shape=362f4afb vocab=a089398f
-/
theorem muldersStorjohannStep_wellFormed
    {M : PolynomialMatrix F} (shift : Array Nat) {i j : Nat} (hM : WellFormed M) :
    WellFormed (muldersStorjohannStep M shift i j) := by
  simp only [muldersStorjohannStep, Array.getD_eq_getD_getElem?]
  cases hI : rowShiftedDegree? (M[i]?.getD #[]) shift with
  | none =>
      simpa [hI] using hM
  | some degI =>
      cases hJ : rowShiftedDegree? (M[j]?.getD #[]) shift with
      | none =>
          simpa [hI, hJ] using hM
      | some degJ =>
          simp only
          have hi : i < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hI
          have hj : j < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hJ
          split
          · apply replaceRow_wellFormed hM
            simpa [Array.getD_eq_getD_getElem?] using
              cancelShiftedLeadingTerm_size_of_wellFormed hM hj hi shift
          · apply replaceRow_wellFormed hM
            simpa [Array.getD_eq_getD_getElem?] using
              cancelShiftedLeadingTerm_size_of_wellFormed hM hi hj shift

/--
@isnad1 id=eq.1h4v.s6.e3fdff7986ac from=translated src=- shape=83e1704d vocab=63cf7148
-/
theorem muldersStorjohannReduceWithFuel_shape_preserved
    (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    MatrixShape (muldersStorjohannReduceWithFuel fuel M shift) = MatrixShape M := by
  induction fuel generalizing M with
  | zero =>
      simp [muldersStorjohannReduceWithFuel]
  | succ fuel ih =>
      rw [muldersStorjohannReduceWithFuel]
      split
      · rfl
      · rename_i _ i j hconf
        exact (ih (muldersStorjohannStep M shift i j)
          (muldersStorjohannStep_wellFormed shift hM)).trans
          (muldersStorjohannStep_shape_preserved shift hM)

/--
@isnad1 id=wellform.1h4v.s6.c354e5b5c726 from=translated src=- shape=d9b46cf3 vocab=ee15c29b
-/
theorem muldersStorjohannReduceWithFuel_wellFormed
    (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    WellFormed (muldersStorjohannReduceWithFuel fuel M shift) := by
  induction fuel generalizing M with
  | zero =>
      simpa [muldersStorjohannReduceWithFuel] using hM
  | succ fuel ih =>
      rw [muldersStorjohannReduceWithFuel]
      split
      · exact hM
      · rename_i _ i j hconf
        exact ih (muldersStorjohannStep M shift i j)
          (muldersStorjohannStep_wellFormed shift hM)

/--
@isnad1 id=wellform.1h3v.s6.ea4192b11284 from=translated src=- shape=88c93f56 vocab=0b25ead4
-/
theorem muldersStorjohannReduce_wellFormed
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    WellFormed (muldersStorjohannReduce M shift) := by
  exact muldersStorjohannReduceWithFuel_wellFormed
    (muldersStorjohannFuel M shift) M shift hM

/--
@isnad1 id=eq.2h4v.s6.3fdcd3dc7de8 from=translated src=- shape=8515c3a9 vocab=fdf14ec8
-/
theorem muldersStorjohannReduceWithFuel_no_conflict_of_measure_lt
    (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat)
    (hM : WellFormed M)
    (hfuel : shiftedMatrixMeasure M shift < fuel) :
    shiftedLeadingConflict? (muldersStorjohannReduceWithFuel fuel M shift) shift = none := by
  induction fuel generalizing M with
  | zero =>
      omega
  | succ fuel ih =>
      rw [muldersStorjohannReduceWithFuel]
      cases hconf : shiftedLeadingConflict? M shift with
      | none =>
          simp [hconf]
      | some pair =>
          rcases pair with ⟨i, j⟩
          have hstepLt :=
            muldersStorjohannStep_shiftedMatrixMeasure_lt hM hconf
          have hstepFuel :
              shiftedMatrixMeasure (muldersStorjohannStep M shift i j) shift < fuel := by
            omega
          exact ih (muldersStorjohannStep M shift i j)
            (muldersStorjohannStep_wellFormed shift hM) hstepFuel

/--
@isnad1 id=eq.1h3v.s6.c349f6caea3b from=translated src=- shape=e1c77a7c vocab=a5b31523
-/
theorem muldersStorjohannReduce_no_conflict
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    shiftedLeadingConflict? (muldersStorjohannReduce M shift) shift = none := by
  exact muldersStorjohannReduceWithFuel_no_conflict_of_measure_lt
    (muldersStorjohannFuel M shift) M shift hM
    (shiftedMatrixMeasure_lt_muldersStorjohannFuel hM)

/-- The fueled reducer is deterministic: two runs that both end without a
shifted leading conflict stopped at the same (first conflict-free) matrix of
the common step orbit, regardless of their fuel.
@isnad1 id=eq.2h5v.s6.43f469beac36 from=translated src=- shape=cd509531 vocab=029b43c5
-/
theorem muldersStorjohannReduceWithFuel_eq_of_no_conflict :
    ∀ (f g : Nat) (M : PolynomialMatrix F) (shift : Array Nat),
      shiftedLeadingConflict? (muldersStorjohannReduceWithFuel f M shift) shift =
        none →
      shiftedLeadingConflict? (muldersStorjohannReduceWithFuel g M shift) shift =
        none →
      muldersStorjohannReduceWithFuel f M shift =
        muldersStorjohannReduceWithFuel g M shift := by
  intro f
  induction f with
  | zero =>
      intro g M shift hf hg
      simp only [muldersStorjohannReduceWithFuel] at hf
      cases g with
      | zero => rfl
      | succ g => simp only [muldersStorjohannReduceWithFuel, hf]
  | succ f ih =>
      intro g M shift hf hg
      cases hconf : shiftedLeadingConflict? M shift with
      | none =>
          cases g with
          | zero => simp only [muldersStorjohannReduceWithFuel, hconf]
          | succ g => simp only [muldersStorjohannReduceWithFuel, hconf]
      | some pair =>
          rcases pair with ⟨i, j⟩
          simp only [muldersStorjohannReduceWithFuel, hconf] at hf ⊢
          cases g with
          | zero =>
              simp only [muldersStorjohannReduceWithFuel, hconf] at hg
              cases hg
          | succ g =>
              simp only [muldersStorjohannReduceWithFuel, hconf] at hg ⊢
              exact ih g (muldersStorjohannStep M shift i j) shift hf hg

/--
@isnad1 id=le.1h4v.s6.f93126c03397 from=translated src=- shape=00845ed6 vocab=2ffea085
-/
theorem muldersStorjohannReduceWithFuel_rowSpan_subset
    (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    RowSpan (muldersStorjohannReduceWithFuel fuel M shift) ⊆ RowSpan M := by
  induction fuel generalizing M with
  | zero =>
      intro row hrow
      simpa [muldersStorjohannReduceWithFuel] using hrow
  | succ fuel ih =>
      rw [muldersStorjohannReduceWithFuel]
      split
      · intro row hrow
        exact hrow
      · rename_i _ i j hconf
        exact Set.Subset.trans
          (ih (muldersStorjohannStep M shift i j)
            (muldersStorjohannStep_wellFormed shift hM))
          (muldersStorjohannStep_rowSpan_subset shift hM)

/--
@isnad1 id=le.1h3v.s6.7c42b0fab5f2 from=translated src=- shape=a04522da vocab=6def1f3e
-/
theorem muldersStorjohannReduce_rowSpan_subset
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    RowSpan (muldersStorjohannReduce M shift) ⊆ RowSpan M := by
  exact muldersStorjohannReduceWithFuel_rowSpan_subset
    (muldersStorjohannFuel M shift) M shift hM

/--
@isnad1 id=le.1h4v.s6.10c8d213293f from=translated src=- shape=cb58210e vocab=2ffea085
-/
theorem muldersStorjohannReduceWithFuel_rowSpan_superset
    (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    RowSpan M ⊆ RowSpan (muldersStorjohannReduceWithFuel fuel M shift) := by
  induction fuel generalizing M with
  | zero =>
      intro row hrow
      simpa [muldersStorjohannReduceWithFuel] using hrow
  | succ fuel ih =>
      rw [muldersStorjohannReduceWithFuel]
      split
      · intro row hrow
        exact hrow
      · rename_i _ i j hconf
        rcases shiftedLeadingConflict?_some_bounds hconf with ⟨hi, hj, hij⟩
        have hne : i ≠ j := by omega
        exact Set.Subset.trans
          (muldersStorjohannStep_rowSpan_superset shift hM hi hj hne)
          (ih (muldersStorjohannStep M shift i j)
            (muldersStorjohannStep_wellFormed shift hM))

/--
@isnad1 id=le.1h3v.s6.b00ad0273597 from=translated src=- shape=fc7a4cf0 vocab=6def1f3e
-/
theorem muldersStorjohannReduce_rowSpan_superset
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    RowSpan M ⊆ RowSpan (muldersStorjohannReduce M shift) := by
  exact muldersStorjohannReduceWithFuel_rowSpan_superset
    (muldersStorjohannFuel M shift) M shift hM

/--
@isnad1 id=eq.1h3v.s6.ae2d00be1017 from=translated src=- shape=adb94c50 vocab=d05f9b61
-/
theorem muldersStorjohannReduce_shape_preserved
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    MatrixShape (muldersStorjohannReduce M shift) = MatrixShape M := by
  exact muldersStorjohannReduceWithFuel_shape_preserved
    (muldersStorjohannFuel M shift) M shift hM

/--
@isnad1 id=eq.1h3v.s6.47929b81de02 from=translated src=- shape=a04522da vocab=df295f40
-/
theorem muldersStorjohannReduce_rowSpan_eq
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    RowSpan (muldersStorjohannReduce M shift) = RowSpan M := by
  apply Set.Subset.antisymm
  · exact muldersStorjohannReduce_rowSpan_subset M shift hM
  · exact muldersStorjohannReduce_rowSpan_superset M shift hM

/--
@isnad1 id=shiftedw.2h3v.s6.956f9fa3b331 from=translated src=- shape=01df60ea vocab=22d0ac9f
-/
theorem muldersStorjohannReduce_weakPopov
    (M : PolynomialMatrix F) (shift : Array Nat)
    (hM : WellFormed M) (_hshift : shift.size = MatrixWidth M) :
    ShiftedWeakPopov (muldersStorjohannReduce M shift) shift := by
  exact shiftedLeadingConflict?_none_weakPopov
    (muldersStorjohannReduce_no_conflict M shift hM)

end PolynomialMatrix

end CompPoly
