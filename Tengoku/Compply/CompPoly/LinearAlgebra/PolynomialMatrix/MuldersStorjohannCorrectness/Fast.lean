/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import Tengoku.Compply.CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Minimal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fast Mulders-Storjohann Reduction Agrees With the Direct Definition

The fast reducer caches shifted leading positions once per conflict scan and
cancels leading terms through the fused `rowSubScaledShift` update. This file
proves it extensionally equal to `muldersStorjohannReduce`, so every
correctness result transfers, and packages it as a certified
`ShiftedRowReducerContext`.
-/

@[expose] public section

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-! ### Row-level cancellation -/

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h5v.s6.1cd2e1f59da6 from=translated src=- shape=f876f0c2 vocab=5c690884
-/
theorem rowSubScaledShift_size (a : PolynomialRow F) (c : F) (d : Nat)
    (b : PolynomialRow F) :
    (rowSubScaledShift a c d b).size = max a.size b.size := by
  simp [rowSubScaledShift]

/--
@isnad1 id=eq.0h6v.s7.45f502d2c5b9 from=translated src=- shape=c08e3f45 vocab=2551a2cf
-/
theorem rowGet_rowSubScaledShift (a : PolynomialRow F) (c : F) (d : Nat)
    (b : PolynomialRow F) (j : Nat) :
    rowGet (rowSubScaledShift a c d b) j =
      CPolynomial.subMulMonomial (rowGet a j) c d (rowGet b j) := by
  by_cases hj : j < (rowSubScaledShift a c d b).size
  · rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    simp [rowSubScaledShift]
  · have hle : (rowSubScaledShift a c d b).size ≤ j := Nat.le_of_not_gt hj
    rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]
    rw [rowSubScaledShift_size] at hle
    have hja : a.size ≤ j := by omega
    have hjb : b.size ≤ j := by omega
    rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hja,
      Option.getD_none, rowGet, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none hjb, Option.getD_none,
      CPolynomial.subMulMonomial_eq]
    simp

/--
@isnad1 id=eq.0h5v.s6.8478dc49a782 from=translated src=- shape=440b3072 vocab=48b8103d
-/
theorem rowSubScaledShift_eq (a : PolynomialRow F) (c : F) (d : Nat)
    (b : PolynomialRow F) :
    rowSubScaledShift a c d b = rowSub a (rowScaleMonomial c d b) := by
  apply Array.ext
  · rw [rowSubScaledShift_size, rowSub_size, rowScaleMonomial_size]
  · intro j hj hj'
    have hlhs : (rowSubScaledShift a c d b)[j] =
        rowGet (rowSubScaledShift a c d b) j := by
      rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj,
        Option.getD_some]
    have hrhs : (rowSub a (rowScaleMonomial c d b))[j] =
        rowGet (rowSub a (rowScaleMonomial c d b)) j := by
      rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj',
        Option.getD_some]
    rw [hlhs, hrhs, rowGet_rowSubScaledShift, rowGet_rowSub,
      rowGet_rowScaleMonomial, CPolynomial.subMulMonomial_eq]

/--
@isnad1 id=eq.0h4v.s6.36eb35534fd6 from=translated src=- shape=8bf588ba vocab=528ac30e
-/
theorem cancelShiftedLeadingTermFast_eq (target reducer : PolynomialRow F)
    (shift : Array Nat) :
    cancelShiftedLeadingTermFast target reducer shift =
      cancelShiftedLeadingTerm target reducer shift := by
  unfold cancelShiftedLeadingTermFast cancelShiftedLeadingTerm
  simp only [rowSubScaledShift_eq]

/-! ### Cached conflict scan -/

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=eq.0h3v.s5.83bd7953889d from=translated src=- shape=e4f3c0da vocab=3610bba2
-/
theorem rowLeadingPositions_size (M : PolynomialMatrix F)
    (shift : Array Nat) :
    (rowLeadingPositions M shift).size = M.size := by
  simp [rowLeadingPositions]

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=eq.1h4v.s6.c9c83a6c0900 from=translated src=- shape=70d0ecdf vocab=a42638db
-/
theorem rowLeadingPositions_getD (M : PolynomialMatrix F) (shift : Array Nat)
    {i : Nat} (hi : i < M.size) :
    (rowLeadingPositions M shift).getD i none =
      rowShiftedLeadingPosition? (M.getD i #[]) shift := by
  have hM : M.getD i #[] = M[i] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
      Option.getD_some]
  have hpos : i < (rowLeadingPositions M shift).size := by
    rw [rowLeadingPositions_size]; exact hi
  rw [hM, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hpos]
  simp [rowLeadingPositions]

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=eq.2h6v.s6.4ff396c822cc from=translated src=- shape=2b3e6c6f vocab=8d79bd18
-/
theorem cachedLeadingConflictInRowStep?_eq (M : PolynomialMatrix F)
    (shift : Array Nat) {i j : Nat} (hi : i < M.size) (hj : j < M.size)
    (found : Option (Nat × Nat)) :
    cachedLeadingConflictInRowStep? (rowLeadingPositions M shift) i found j =
      shiftedLeadingConflictInRowStep? M shift i found j := by
  unfold cachedLeadingConflictInRowStep? shiftedLeadingConflictInRowStep?
  rw [rowLeadingPositions_getD M shift hi, rowLeadingPositions_getD M shift hj]

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=eq.1h5v.s6.0af740629c62 from=translated src=- shape=fc7fa255 vocab=c0ff2929
-/
theorem cachedLeadingConflictInRow?_eq (M : PolynomialMatrix F)
    (shift : Array Nat) {i : Nat} (hi : i < M.size)
    (found : Option (Nat × Nat)) :
    cachedLeadingConflictInRow? (rowLeadingPositions M shift) i found =
      shiftedLeadingConflictInRow? M shift i found := by
  unfold cachedLeadingConflictInRow? shiftedLeadingConflictInRow?
  rw [rowLeadingPositions_size]
  apply List.foldl_ext
  intro acc j hjmem
  have hjlt : j < M.size := by
    have hj := List.mem_range'_1.mp hjmem
    omega
  exact cachedLeadingConflictInRowStep?_eq M shift hi hjlt acc

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=eq.0h3v.s5.18f60672c061 from=translated src=- shape=00bad3ee vocab=ef59b526
-/
theorem cachedLeadingConflict?_eq (M : PolynomialMatrix F) (shift : Array Nat) :
    cachedLeadingConflict? (rowLeadingPositions M shift) =
      shiftedLeadingConflict? M shift := by
  unfold cachedLeadingConflict? shiftedLeadingConflict?
    shiftedLeadingConflictFrom? shiftedLeadingConflictFromStep?
  rw [rowLeadingPositions_size]
  apply List.foldl_ext
  intro acc i himem
  have hilt : i < M.size := by
    have hi := List.mem_range'_1.mp himem
    omega
  exact cachedLeadingConflictInRow?_eq M shift hilt acc

/-! ### Step, loop, and reducer -/

/--
@isnad1 id=eq.0h5v.s6.b9dca7b0deda from=translated src=- shape=77ed39cb vocab=7abf5f74
-/
theorem muldersStorjohannStepFast_eq (M : PolynomialMatrix F)
    (shift : Array Nat) (i j : Nat) :
    muldersStorjohannStepFast M shift i j = muldersStorjohannStep M shift i j := by
  unfold muldersStorjohannStepFast muldersStorjohannStep
  simp only [cancelShiftedLeadingTermFast_eq]

/--
@isnad1 id=eq.0h4v.s6.97af02b8b4ad from=translated src=- shape=08022cc7 vocab=d8019c21
-/
theorem muldersStorjohannReduceWithFuelFast_eq :
    ∀ (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat),
      muldersStorjohannReduceWithFuelFast fuel M shift =
        muldersStorjohannReduceWithFuel fuel M shift := by
  intro fuel
  induction fuel with
  | zero =>
      intro M shift
      rfl
  | succ fuel ih =>
      intro M shift
      unfold muldersStorjohannReduceWithFuelFast muldersStorjohannReduceWithFuel
      rw [cachedLeadingConflict?_eq]
      cases shiftedLeadingConflict? M shift with
      | none => rfl
      | some pair =>
          simp only [muldersStorjohannStepFast_eq, ih]

/--
@isnad1 id=eq.0h3v.s5.3ca4bda0d4bb from=translated src=- shape=5a1acd4b vocab=b600f830
-/
theorem muldersStorjohannReduceFast_eq (M : PolynomialMatrix F)
    (shift : Array Nat) :
    muldersStorjohannReduceFast M shift = muldersStorjohannReduce M shift := by
  unfold muldersStorjohannReduceFast muldersStorjohannReduce
  exact muldersStorjohannReduceWithFuelFast_eq _ M shift

/-! ### Certified context -/

/-- Certified fast Mulders-Storjohann shifted row-reducer context. The
implementation caches leading positions per scan and uses fused row
cancellation; correctness transfers along `muldersStorjohannReduceFast_eq`.-/
def muldersStorjohannFastReducerContext (F : Type*) [Field F] [BEq F]
    [LawfulBEq F] [DecidableEq F] : ShiftedRowReducerContext F where
  reduce := muldersStorjohannReduceFast
  shape_preserved := by
    intro M shift hM
    rw [muldersStorjohannReduceFast_eq]
    exact muldersStorjohannReduce_shape_preserved M shift hM
  rowSpan_eq := by
    intro M shift hM
    rw [muldersStorjohannReduceFast_eq]
    exact muldersStorjohannReduce_rowSpan_eq M shift hM
  weakPopov := by
    intro M shift hM hshift
    rw [muldersStorjohannReduceFast_eq]
    exact muldersStorjohannReduce_weakPopov M shift hM hshift
  least_row_minimal := by
    intro M shift row hM hshift hrow hdeg
    simp only [muldersStorjohannReduceFast_eq]
    exact muldersStorjohannReduce_least_row_minimal M shift row hM hshift hrow hdeg

end PolynomialMatrix

end CompPoly
