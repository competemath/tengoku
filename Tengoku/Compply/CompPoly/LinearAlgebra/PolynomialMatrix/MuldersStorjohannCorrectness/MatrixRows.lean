/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import Tengoku.Compply.CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.RowOps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Mulders-Storjohann Correctness Matrix Row Helpers

Replacement-row, matrix-shape, and row-span transport lemmas.
-/

@[expose] public section

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=eq.0h4v.s6.bec8621b40a9 from=translated src=- shape=c023b832 vocab=1dfedc1c
-/
theorem replaceRow_size (M : PolynomialMatrix F) (idx : Nat) (row : PolynomialRow F) :
    (replaceRow M idx row).size = M.size := by
  simp [replaceRow, Array.size_setIfInBounds]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=eq.1h4v.s6.186f6b365423 from=translated src=- shape=48ecad64 vocab=8e9189c0
-/
theorem replaceRow_matrixWidth
    {M : PolynomialMatrix F} {idx : Nat} {row : PolynomialRow F}
    (hrow : row.size = MatrixWidth M) :
    MatrixWidth (replaceRow M idx row) = MatrixWidth M := by
  unfold MatrixWidth replaceRow
  by_cases hM0 : 0 < M.size
  · rw [Array.getElem?_setIfInBounds]
    by_cases hidx : idx = 0
    · subst idx
      simpa [hM0, MatrixWidth] using hrow
    · simp [hidx]
  · have hsize : M.size = 0 := Nat.eq_zero_of_not_pos hM0
    simp [hsize]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=eq.1h4v.s6.e06aa6424afc from=translated src=- shape=0010aecc vocab=e9225200
-/
theorem replaceRow_shape
    {M : PolynomialMatrix F} {idx : Nat} {row : PolynomialRow F}
    (hrow : row.size = MatrixWidth M) :
    MatrixShape (replaceRow M idx row) = MatrixShape M := by
  simp [MatrixShape, replaceRow_size, replaceRow_matrixWidth hrow]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=wellform.2h4v.s6.710033636f68 from=translated src=- shape=1d52afa6 vocab=1b8ed49f
-/
theorem replaceRow_wellFormed
    {M : PolynomialMatrix F} {idx : Nat} {row : PolynomialRow F}
    (hM : WellFormed M) (hrow : row.size = MatrixWidth M) :
    WellFormed (replaceRow M idx row) := by
  intro stored hstored
  have hwidth : MatrixWidth (replaceRow M idx row) = MatrixWidth M :=
    replaceRow_matrixWidth hrow
  rw [hwidth]
  rcases List.getElem_of_mem hstored with ⟨k, hk, hget⟩
  have hkReplace : k < (replaceRow M idx row).size := by
    simpa [MatrixRows] using hk
  have hkM : k < M.size := by
    simpa [replaceRow_size] using hkReplace
  have hstored_eq : (replaceRow M idx row)[k] = stored := by
    simpa [MatrixRows, Array.getElem_toList] using hget
  rw [← hstored_eq]
  by_cases hidx : k = idx
  · subst idx
    simpa [replaceRow, Array.getElem_setIfInBounds, hkM] using hrow
  · have hmem : M[k] ∈ MatrixRows M := by
      simp [MatrixRows, Array.getElem_mem_toList hkM]
    have hstoredM : M[k].size = MatrixWidth M := hM M[k] hmem
    have hidx' : idx ≠ k := fun h ↦ hidx h.symm
    simpa [replaceRow, Array.getElem_setIfInBounds, hidx', hkM] using hstoredM

/--
@isnad1 id=mem.3h5v.s8.bd42c854b202 from=translated src=- shape=e02b1480 vocab=6c31ac60
-/
theorem replaceRow_rows_mem_rowSpan
    {M : PolynomialMatrix F} (hM : WellFormed M) {idx : Nat} {newRow row : PolynomialRow F}
    (hnew : newRow ∈ RowSpan M)
    (hrow : row ∈ MatrixRows (replaceRow M idx newRow)) :
    row ∈ RowSpan M := by
  rcases List.getElem_of_mem hrow with ⟨k, hk, hget⟩
  have hkReplace : k < (replaceRow M idx newRow).size := by
    simpa [MatrixRows] using hk
  have hkM : k < M.size := by
    simpa [replaceRow_size] using hkReplace
  have hstored_eq : (replaceRow M idx newRow)[k] = row := by
    simpa [MatrixRows, Array.getElem_toList] using hget
  rw [← hstored_eq]
  by_cases hidx : idx = k
  · subst idx
    simpa [replaceRow, Array.getElem_setIfInBounds, hkM] using hnew
  · have hstoredM : (replaceRow M idx newRow)[k] = M[k] := by
      simp [replaceRow, hidx, hkM]
    rw [hstoredM]
    exact matrix_row_mem_rowSpan hM
      (by simp [MatrixRows, Array.getElem_mem_toList hkM])

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=mem.1h4v.s6.cdee39dc01f0 from=translated src=- shape=66f4d41c vocab=73868a05
-/
theorem replaceRow_newRow_mem
    {M : PolynomialMatrix F} {idx : Nat} {newRow : PolynomialRow F}
    (hidx : idx < M.size) :
    newRow ∈ MatrixRows (replaceRow M idx newRow) := by
  have hidxReplace : idx < (replaceRow M idx newRow).size := by
    simpa [replaceRow_size] using hidx
  have hget : (replaceRow M idx newRow)[idx] = newRow := by
    simp [replaceRow]
  have hmem : (replaceRow M idx newRow)[idx] ∈ MatrixRows (replaceRow M idx newRow) := by
    exact Array.getElem_mem_toList hidxReplace
  simpa [hget] using hmem

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=mem.2h5v.s7.060c9321a028 from=translated src=- shape=b8a3ad4e vocab=227f7287
-/
theorem replaceRow_oldRow_mem
    {M : PolynomialMatrix F} {idx k : Nat} {newRow : PolynomialRow F}
    (hk : k < M.size) (hne : idx ≠ k) :
    M[k] ∈ MatrixRows (replaceRow M idx newRow) := by
  have hkReplace : k < (replaceRow M idx newRow).size := by
    simpa [replaceRow_size] using hk
  have hget : (replaceRow M idx newRow)[k] = M[k] := by
    simp [replaceRow, hne, hk]
  rw [← hget]
  simp [MatrixRows, Array.getElem_mem_toList hkReplace]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=eq.2h3v.s7.c2676901de9a from=translated src=- shape=9823989f vocab=fb054fc4
-/
theorem matrix_getD_size_of_wellFormed
    {M : PolynomialMatrix F} (hM : WellFormed M) {i : Nat} (hi : i < M.size) :
    (M.getD i #[]).size = MatrixWidth M := by
  have hget : M.getD i #[] = M[i] := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rw [hget]
  exact hM M[i] (by simp [MatrixRows, Array.getElem_mem_toList hi])

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=eq.2h3v.s7.cd33a4804218 from=translated src=- shape=000bd32c vocab=1779d599
-/
theorem matrix_getElem?_getD_size_of_wellFormed
    {M : PolynomialMatrix F} (hM : WellFormed M) {i : Nat} (hi : i < M.size) :
    (M[i]?.getD #[]).size = MatrixWidth M := by
  simpa [Array.getElem?_eq_getElem hi] using matrix_getD_size_of_wellFormed hM hi

/--
@isnad1 id=mem.2h3v.s7.497d8c3dda92 from=translated src=- shape=69f03482 vocab=71f8939e
-/
theorem matrix_getD_mem_rowSpan
    {M : PolynomialMatrix F} (hM : WellFormed M) {i : Nat} (hi : i < M.size) :
    M.getD i #[] ∈ RowSpan M := by
  have hget : M.getD i #[] = M[i] := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rw [hget]
  exact matrix_row_mem_rowSpan hM
    (by simp [MatrixRows, Array.getElem_mem_toList hi])

omit [DecidableEq F] in
/--
@isnad1 id=mem.1h2v.s6.8bc0d3968635 from=translated src=- shape=47a8a61a vocab=eb51d38b
-/
theorem zeroRow_mem_rowSpan
    {M : PolynomialMatrix F} (hM : WellFormed M) :
    zeroRow (F := F) (MatrixWidth M) ∈ RowSpan M := by
  let coeffs := Array.replicate M.size (0 : CPolynomial F)
  refine ⟨coeffs, by simp [coeffs], ?_⟩
  unfold rowLinearCombination
  have hfold :
      ∀ n, n ≤ M.size →
        ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffs.getD i 0) (M.getD i #[])))
          (zeroRow (MatrixWidth M))) = zeroRow (F := F) (MatrixWidth M) := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        have hnM : n < M.size := by omega
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ih (by omega)]
        have hcoeff : coeffs.getD n 0 = 0 := by
          simp [coeffs, hnM]
        rw [hcoeff, rowScalePolynomial_zero]
        rw [matrix_getD_size_of_wellFormed hM hnM]
        exact rowAdd_zeroRow_zeroRow (MatrixWidth M)
  exact (hfold M.size (Nat.le_refl M.size)).symm

omit [DecidableEq F] in
/--
@isnad1 id=mem.3h4v.s8.e82d0de79fec from=translated src=- shape=09b724d3 vocab=eed85c51
-/
theorem rowLinearCombination_mem_rowSpan_of_rows_mem
    {A B : PolynomialMatrix F} (hB : WellFormed B)
    (hwidth : MatrixWidth A = MatrixWidth B)
    (hrows : ∀ row, row ∈ MatrixRows A → row ∈ RowSpan B)
    (coeffs : Array (CPolynomial F)) :
    rowLinearCombination coeffs A ∈ RowSpan B := by
  unfold rowLinearCombination
  have hfold :
      ∀ n, n ≤ A.size →
        ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffs.getD i 0) (A.getD i #[])))
          (zeroRow (MatrixWidth A))) ∈ RowSpan B := by
    intro n
    induction n with
    | zero =>
        intro _
        rw [hwidth]
        exact zeroRow_mem_rowSpan hB
    | succ n ih =>
        intro hn
        have hnA : n < A.size := by omega
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        apply rowAdd_mem_rowSpan
        · exact ih (by omega)
        · apply rowScalePolynomial_mem_rowSpan
          have hget : A.getD n #[] = A[n] := by
            simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hnA]
          rw [hget]
          exact hrows A[n] (by simp [MatrixRows, Array.getElem_mem_toList hnA])
  exact hfold A.size (Nat.le_refl A.size)

omit [DecidableEq F] in
/--
@isnad1 id=le.3h3v.s8.d57877c66edf from=translated src=- shape=563563ce vocab=dcd7bb1d
-/
theorem rowSpan_subset_of_rows_mem
    {A B : PolynomialMatrix F} (hB : WellFormed B)
    (hwidth : MatrixWidth A = MatrixWidth B)
    (hrows : ∀ row, row ∈ MatrixRows A → row ∈ RowSpan B) :
    RowSpan A ⊆ RowSpan B := by
  intro row hrow
  rcases hrow with ⟨coeffs, _hsize, rfl⟩
  exact rowLinearCombination_mem_rowSpan_of_rows_mem hB hwidth hrows coeffs

/--
@isnad1 id=eq.3h5v.s7.5e15161129b5 from=translated src=- shape=e377d7c1 vocab=1dad6962
-/
theorem cancelShiftedLeadingTerm_size_of_wellFormed
    {M : PolynomialMatrix F} (hM : WellFormed M) {i j : Nat}
    (hi : i < M.size) (hj : j < M.size) (shift : Array Nat) :
    (cancelShiftedLeadingTerm (M.getD i #[]) (M.getD j #[]) shift).size =
      MatrixWidth M := by
  rw [cancelShiftedLeadingTerm_size
      (hsize := (matrix_getD_size_of_wellFormed hM hj).trans
        (matrix_getD_size_of_wellFormed hM hi).symm)]
  exact matrix_getD_size_of_wellFormed hM hi

end PolynomialMatrix

end CompPoly
