/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import Tengoku.Compply.CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.MatrixRows

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Mulders-Storjohann Correctness Shifted Leading Conflict Helpers

Bounds and validity lemmas for shifted-leading-position conflict detection.
-/

@[expose] public section

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=lt.1h5v.s7.2ce645774e5b from=translated src=- shape=3af0ec5d vocab=76321830
-/
theorem index_lt_of_rowShiftedDegree?_getElem?_eq_some
    {M : PolynomialMatrix F} {shift : Array Nat} {i d : Nat}
    (hdeg : rowShiftedDegree? (M[i]?.getD #[]) shift = some d) :
    i < M.size := by
  by_contra hnot
  have hle : M.size ≤ i := Nat.le_of_not_gt hnot
  have hnone : rowShiftedDegree? (M[i]?.getD #[]) shift = none := by
    rw [Array.getElem?_eq_none hle]
    simp [rowShiftedDegree?]
  rw [hnone] at hdeg
  contradiction

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
def ConflictBounds (M : PolynomialMatrix F) : Option (Nat × Nat) → Prop
  | none => True
  | some (i, j) => i < M.size ∧ j < M.size ∧ i < j

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=conflict.2h6v.s8.b5ee0a4e5526 from=translated src=- shape=c412a365 vocab=9e1e0050
-/
theorem shiftedLeadingConflictInRowFold_bounds
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat) (xs : List Nat)
    (found : Option (Nat × Nat))
    (hxs : ∀ j, j ∈ xs → i < j ∧ j < M.size)
    (hfound : ConflictBounds M found) :
    ConflictBounds M
      (xs.foldl
        (fun found j ↦
          match found with
          | some _ => found
          | none =>
              match rowShiftedLeadingPosition? (M.getD i #[]) shift,
                  rowShiftedLeadingPosition? (M.getD j #[]) shift with
              | some pi, some pj =>
                  if pi == pj then some (i, j) else none
              | _, _ => none)
        found) := by
  induction xs generalizing found with
  | nil =>
      simpa using hfound
  | cons j xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro k hk
        exact hxs k (by simp [hk])
      · cases found with
        | none =>
            cases rowShiftedLeadingPosition? (M.getD i #[]) shift <;>
              cases rowShiftedLeadingPosition? (M.getD j #[]) shift
            · simp [ConflictBounds]
            · simp [ConflictBounds]
            · simp [ConflictBounds]
            · rename_i pi pj
              by_cases hpos : pi == pj
              · have hjBounds := hxs j (by simp)
                have hiM : i < M.size := by omega
                simp [hpos, ConflictBounds, hjBounds, hiM]
              · simp [hpos, ConflictBounds]
        | some pair =>
            rcases pair with ⟨a, b⟩
            simpa [ConflictBounds] using hfound

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=conflict.2h5v.s6.71578727137f from=translated src=- shape=2dc0468d vocab=83757b5e
-/
theorem shiftedLeadingConflictInRow?_bounds
    (M : PolynomialMatrix F) (shift : Array Nat) {i : Nat} {found : Option (Nat × Nat)}
    (hi : i < M.size) (hfound : ConflictBounds M found) :
    ConflictBounds M (shiftedLeadingConflictInRow? M shift i found) := by
  unfold shiftedLeadingConflictInRow?
  apply shiftedLeadingConflictInRowFold_bounds
  · intro j hj
    have hj' := (List.mem_range'.1 hj)
    omega
  · exact hfound

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=conflict.2h5v.s6.1ecec0164360 from=translated src=- shape=d1c3ad7b vocab=539aa1ad
-/
theorem shiftedLeadingConflictFromFold_bounds
    (M : PolynomialMatrix F) (shift : Array Nat) (xs : List Nat)
    (found : Option (Nat × Nat))
    (hxs : ∀ i, i ∈ xs → i < M.size)
    (hfound : ConflictBounds M found) :
    ConflictBounds M
      (xs.foldl
        (fun found i ↦ shiftedLeadingConflictInRow? M shift i found)
        found) := by
  induction xs generalizing found with
  | nil =>
      simpa using hfound
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro k hk
        exact hxs k (by simp [hk])
      · exact shiftedLeadingConflictInRow?_bounds M shift (hxs i (by simp)) hfound

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=conflict.1h4v.s5.9ecc98e6942c from=translated src=- shape=19b2f823 vocab=de4d70d1
-/
theorem shiftedLeadingConflictFrom?_bounds
    (M : PolynomialMatrix F) (shift : Array Nat) {found : Option (Nat × Nat)}
    (hfound : ConflictBounds M found) :
    ConflictBounds M (shiftedLeadingConflictFrom? M shift found) := by
  unfold shiftedLeadingConflictFrom?
  apply shiftedLeadingConflictFromFold_bounds
  · intro i hi
    have hi' := (List.mem_range'.1 hi)
    omega
  · exact hfound

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=and.1h5v.s6.22f86bee4e34 from=translated src=- shape=c5e0b070 vocab=78121918
-/
theorem shiftedLeadingConflict?_some_bounds
    {M : PolynomialMatrix F} {shift : Array Nat} {i j : Nat}
    (hconf : shiftedLeadingConflict? M shift = some (i, j)) :
    i < M.size ∧ j < M.size ∧ i < j := by
  have hbounds : ConflictBounds M (shiftedLeadingConflict? M shift) := by
    unfold shiftedLeadingConflict?
    exact shiftedLeadingConflictFrom?_bounds M shift trivial
  rw [hconf] at hbounds
  exact hbounds

def ConflictValid (M : PolynomialMatrix F) (shift : Array Nat) :
    Option (Nat × Nat) → Prop
  | none => True
  | some (i, j) =>
      ∃ p,
        rowShiftedLeadingPosition? (M.getD i #[]) shift = some p ∧
        rowShiftedLeadingPosition? (M.getD j #[]) shift = some p

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=conflict.1h6v.s5.edd35cbc57fb from=translated src=- shape=8d81a89e vocab=2300d6b5
-/
theorem shiftedLeadingConflictInRowStep?_valid
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat)
    {found : Option (Nat × Nat)} (j : Nat)
    (hfound : ConflictValid M shift found) :
    ConflictValid M shift (shiftedLeadingConflictInRowStep? M shift i found j) := by
  unfold shiftedLeadingConflictInRowStep?
  cases found with
  | none =>
      cases hposI : rowShiftedLeadingPosition? (M.getD i #[]) shift with
      | none =>
          simp [ConflictValid]
      | some pi =>
          cases hposJ : rowShiftedLeadingPosition? (M.getD j #[]) shift with
          | none =>
              simp [ConflictValid]
          | some pj =>
              by_cases hsame : pi == pj
              · have hpj : pj = pi := (LawfulBEq.eq_of_beq hsame).symm
                subst pj
                change ConflictValid M shift
                  (if (pi == pi) = true then some (i, j) else none)
                rw [hsame]
                refine ⟨pi, ?_, ?_⟩
                · simpa [Array.getD_eq_getD_getElem?] using hposI
                · simpa [Array.getD_eq_getD_getElem?] using hposJ
              · simp [hsame, ConflictValid]
  | some pair =>
      simpa [ConflictValid] using hfound

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=conflict.1h6v.s6.fce957cb8f6e from=translated src=- shape=77d4d1dc vocab=dcc99057
-/
theorem shiftedLeadingConflictInRowFold_valid
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat)
    (xs : List Nat) {found : Option (Nat × Nat)}
    (hfound : ConflictValid M shift found) :
    ConflictValid M shift
      (xs.foldl (shiftedLeadingConflictInRowStep? M shift i) found) := by
  induction xs generalizing found with
  | nil =>
      exact hfound
  | cons j xs ih =>
      simp only [List.foldl_cons]
      exact ih (shiftedLeadingConflictInRowStep?_valid M shift i j hfound)

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=conflict.1h5v.s5.b5b82e44fbda from=translated src=- shape=a70abf1e vocab=52d7bdea
-/
theorem shiftedLeadingConflictInRow?_valid
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat)
    {found : Option (Nat × Nat)}
    (hfound : ConflictValid M shift found) :
    ConflictValid M shift (shiftedLeadingConflictInRow? M shift i found) := by
  unfold shiftedLeadingConflictInRow?
  exact shiftedLeadingConflictInRowFold_valid M shift i _ hfound

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=conflict.1h5v.s5.2afdc8c757a9 from=translated src=- shape=f748f85e vocab=e4889af5
-/
theorem shiftedLeadingConflictFromFold_valid
    (M : PolynomialMatrix F) (shift : Array Nat) (xs : List Nat)
    {found : Option (Nat × Nat)}
    (hfound : ConflictValid M shift found) :
    ConflictValid M shift
      (xs.foldl (shiftedLeadingConflictFromStep? M shift) found) := by
  induction xs generalizing found with
  | nil =>
      exact hfound
  | cons i xs ih =>
      simp only [List.foldl_cons]
      exact ih (shiftedLeadingConflictInRow?_valid M shift i hfound)

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=conflict.1h4v.s5.1f6f7cd8a243 from=translated src=- shape=bebdd445 vocab=8ea38b35
-/
theorem shiftedLeadingConflictFrom?_valid
    (M : PolynomialMatrix F) (shift : Array Nat) {found : Option (Nat × Nat)}
    (hfound : ConflictValid M shift found) :
    ConflictValid M shift (shiftedLeadingConflictFrom? M shift found) := by
  unfold shiftedLeadingConflictFrom?
  exact shiftedLeadingConflictFromFold_valid M shift _ hfound

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=ex.1h5v.s7.d3fc168510e2 from=translated src=- shape=4943942f vocab=3dc62227
-/
theorem shiftedLeadingConflict?_some_valid
    {M : PolynomialMatrix F} {shift : Array Nat} {i j : Nat}
    (hconf : shiftedLeadingConflict? M shift = some (i, j)) :
    ∃ p,
      rowShiftedLeadingPosition? (M.getD i #[]) shift = some p ∧
      rowShiftedLeadingPosition? (M.getD j #[]) shift = some p := by
  have hvalid : ConflictValid M shift (shiftedLeadingConflict? M shift) := by
    unfold shiftedLeadingConflict?
    exact shiftedLeadingConflictFrom?_valid M shift trivial
  rw [hconf] at hvalid
  exact hvalid

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=eq.0h6v.s5.f512c4c11552 from=translated src=- shape=468814b6 vocab=6dbb27da
-/
theorem shiftedLeadingConflictInRowFold_some
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat)
    (xs : List Nat) (pair : Nat × Nat) :
    xs.foldl (shiftedLeadingConflictInRowStep? M shift i) (some pair) = some pair := by
  induction xs with
  | nil =>
      rfl
  | cons j xs ih =>
      simp [shiftedLeadingConflictInRowStep?, ih]

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=eq.0h5v.s5.56074b386924 from=translated src=- shape=ad1f9082 vocab=288f6957
-/
theorem shiftedLeadingConflictInRow?_some
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat) (pair : Nat × Nat) :
    shiftedLeadingConflictInRow? M shift i (some pair) = some pair := by
  unfold shiftedLeadingConflictInRow?
  exact shiftedLeadingConflictInRowFold_some M shift i _ pair

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=eq.0h5v.s5.1ed96719ad3d from=translated src=- shape=303cf4b2 vocab=d0d7d3a8
-/
theorem shiftedLeadingConflictFromFold_some
    (M : PolynomialMatrix F) (shift : Array Nat) (xs : List Nat) (pair : Nat × Nat) :
    xs.foldl (shiftedLeadingConflictFromStep? M shift) (some pair) = some pair := by
  induction xs with
  | nil =>
      rfl
  | cons i xs ih =>
      simp [shiftedLeadingConflictFromStep?, shiftedLeadingConflictInRow?_some, ih]

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=false.4h7v.s7.2aa6fb26704c from=translated src=- shape=267d3d10 vocab=b8bfafcf
-/
theorem shiftedLeadingConflictInRowFold_none_no_conflict
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat) (xs : List Nat)
    (hfold : xs.foldl (shiftedLeadingConflictInRowStep? M shift i) none = none)
    {j p : Nat} (hj : j ∈ xs)
    (hposI : rowShiftedLeadingPosition? (M.getD i #[]) shift = some p)
    (hposJ : rowShiftedLeadingPosition? (M.getD j #[]) shift = some p) :
    False := by
  induction xs with
  | nil =>
      cases hj
  | cons x xs ih =>
      simp only [List.foldl_cons] at hfold
      rw [List.mem_cons] at hj
      cases hstep : shiftedLeadingConflictInRowStep? M shift i none x with
      | none =>
          have htail : xs.foldl (shiftedLeadingConflictInRowStep? M shift i) none = none := by
            simpa [hstep] using hfold
          rcases hj with rfl | hj
          · rw [Array.getD_eq_getD_getElem?] at hposI hposJ
            simp [shiftedLeadingConflictInRowStep?, hposI, hposJ] at hstep
          · exact ih htail hj
      | some pair =>
          have hsome := shiftedLeadingConflictInRowFold_some M shift i xs pair
          rw [hstep, hsome] at hfold
          contradiction

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=false.5h6v.s7.795893c2735f from=translated src=- shape=ce1cf5da vocab=a1beaefc
-/
theorem shiftedLeadingConflictInRow?_none_no_conflict
    {M : PolynomialMatrix F} {shift : Array Nat} {i j p : Nat}
    (hfold : shiftedLeadingConflictInRow? M shift i none = none)
    (hij : i < j) (hj : j < M.size)
    (hposI : rowShiftedLeadingPosition? (M.getD i #[]) shift = some p)
    (hposJ : rowShiftedLeadingPosition? (M.getD j #[]) shift = some p) :
    False := by
  unfold shiftedLeadingConflictInRow? at hfold
  apply shiftedLeadingConflictInRowFold_none_no_conflict (j := j) (p := p) M shift i
    (List.range' (i + 1) (M.size - (i + 1))) hfold
  · rw [List.mem_range']
    refine ⟨j - (i + 1), ?_, ?_⟩ <;> omega
  · exact hposI
  · exact hposJ

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=eq.2h5v.s6.ef39cb62307a from=translated src=- shape=0d89e550 vocab=9a9e4199
-/
theorem shiftedLeadingConflictFromFold_none_inner_none
    (M : PolynomialMatrix F) (shift : Array Nat) (xs : List Nat)
    (hfold : xs.foldl (shiftedLeadingConflictFromStep? M shift) none = none)
    {i : Nat} (hi : i ∈ xs) :
    shiftedLeadingConflictInRow? M shift i none = none := by
  induction xs with
  | nil =>
      cases hi
  | cons x xs ih =>
      simp only [List.foldl_cons] at hfold
      rw [List.mem_cons] at hi
      cases hstep : shiftedLeadingConflictFromStep? M shift none x with
      | none =>
          have htail : xs.foldl (shiftedLeadingConflictFromStep? M shift) none = none := by
            simpa [hstep] using hfold
          rcases hi with rfl | hi
          · simpa [shiftedLeadingConflictFromStep?] using hstep
          · exact ih htail hi
      | some pair =>
          have hsome := shiftedLeadingConflictFromFold_some M shift xs pair
          rw [hstep, hsome] at hfold
          contradiction

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=false.6h6v.s7.fe492d046487 from=translated src=- shape=7bbb74ea vocab=3f522c5d
-/
theorem shiftedLeadingConflict?_none_no_conflict
    {M : PolynomialMatrix F} {shift : Array Nat} {i j p : Nat}
    (hconf : shiftedLeadingConflict? M shift = none)
    (hi : i < M.size) (hj : j < M.size) (hij : i < j)
    (hposI : rowShiftedLeadingPosition? (M.getD i #[]) shift = some p)
    (hposJ : rowShiftedLeadingPosition? (M.getD j #[]) shift = some p) :
    False := by
  unfold shiftedLeadingConflict? shiftedLeadingConflictFrom? at hconf
  have hinner :
      shiftedLeadingConflictInRow? M shift i none = none := by
    apply shiftedLeadingConflictFromFold_none_inner_none M shift (List.range' 0 M.size) hconf
    rw [List.mem_range']
    exact ⟨i, hi, by omega⟩
  exact shiftedLeadingConflictInRow?_none_no_conflict hinner hij hj hposI hposJ

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=shiftedw.1h3v.s5.85d7d5380118 from=translated src=- shape=1f5b2435 vocab=c5921e77
-/
theorem shiftedLeadingConflict?_none_weakPopov
    {M : PolynomialMatrix F} {shift : Array Nat}
    (hconf : shiftedLeadingConflict? M shift = none) :
    ShiftedWeakPopov M shift := by
  intro i j hi hj hne hposI_ne hposJ_ne hsame
  cases hposI : rowShiftedLeadingPosition? (M.getD i #[]) shift with
  | none =>
      exact False.elim (hposI_ne hposI)
  | some p =>
      cases hposJ : rowShiftedLeadingPosition? (M.getD j #[]) shift with
      | none =>
          exact False.elim (hposJ_ne hposJ)
      | some q =>
          have hpq : p = q := by
            have hpqOption : some p = some q := by
              rw [← hposI, ← hposJ]
              exact hsame
            exact Option.some.inj hpqOption
          subst q
          rcases Nat.lt_or_gt_of_ne hne with hij | hji
          · exact False.elim
              (shiftedLeadingConflict?_none_no_conflict hconf hi hj hij hposI hposJ)
          · exact False.elim
              (shiftedLeadingConflict?_none_no_conflict hconf hj hi hji hposJ hposI)

end PolynomialMatrix

end CompPoly
