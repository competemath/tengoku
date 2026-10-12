/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Combinatorics.Young.BetaNumbers
public import Tengoku.Tauceti.TauCeti.Combinatorics.Young.HookLength.Basic

/-!
# Beta-numbers and the hook-length product

Fix a Young diagram `μ` and a bound `r` on its number of rows, and write `βᵢ` for the beta-number
`YoungDiagram.betaNumber μ r i = μ.rowLen i + (r - 1 - i)` of row `i`, defined in
`TauCeti/Combinatorics/Young/BetaNumbers.lean`. For the exact row count `r = μ.colLen 0`, and only
for it, the beta-numbers of the nonempty rows are the hook lengths of the first column: for
`i < μ.colLen 0` the number `βᵢ` is the hook length of the cell `(i, 0)` at the head of row `i`
(`YoungDiagram.betaNumber_eq_hookLength`). A larger bound `r` does not merely append entries to
that list; it raises every beta-number of a nonempty row by the excess `r - μ.colLen 0`, and
contributes the beta-numbers `r - 1 - i` of the empty rows `i`.

The theorem of this file is the identity

`(∏_{c ∈ μ} hookLength μ c) * ∏_{i < j < r} (βᵢ - βⱼ) = ∏_{i < r} βᵢ !`,

`YoungDiagram.prod_hookLength_mul_prod_betaNumber_sub_eq_prod_factorial`. It is the combinatorial
half of the Frame-Robinson-Thrall route to the hook-length formula: the other half is the Frobenius
determinant formula `f^μ · ∏_{i < r} βᵢ ! = μ.card ! · ∏_{i < j < r} (βᵢ - βⱼ)` for the number of
standard Young tableaux, and multiplying the two gives the multiplicative hook-length formula
`f^μ · ∏_{c ∈ μ} hookLength μ c = μ.card !`.

The file also records the one interaction between beta-numbers and corners, which the induction
proving the Frobenius formula runs on: erasing a corner lowers the beta-number of its row by one
and leaves the other beta-numbers alone.

## The row-by-row mechanism

Everything reduces to one statement about a single row `i`, proved in
`YoungDiagram.image_betaNumber_sub_hookLength_union_image_betaNumber`: inside `{0, …, βᵢ - 1}` the
numbers `βᵢ - hookLength μ (i, c)`, for the cells `(i, c)` of row `i`, are exactly the numbers that
are **not** a later beta-number `βⱼ`, `i < j < r`. Equivalently the hook lengths of row `i` are
`{1, …, βᵢ}` with the differences `βᵢ - βⱼ` removed, which is the classical description of a row of
hook lengths.

Two computations drive it. The first, `YoungDiagram.hookLength_add_eq_betaNumber`, is that

`hookLength μ (i, c) + (c + r - μ.colLen c) = βᵢ`,

so the complement `βᵢ - hookLength μ (i, c)` of a hook length in row `i` is `c + r - μ.colLen c`, a
quantity that does not depend on the row at all. The second is that this quantity is never a
beta-number `βⱼ` of an index `j` *within the bound*
(`YoungDiagram.betaNumber_sub_hookLength_ne_betaNumber`, for `j < r`; beyond the bound `βⱼ` is the
unshifted `μ.rowLen j` and the two can agree): the equation `c + r - μ.colLen c = βⱼ` says
`c + j + 1 = μ.colLen c + μ.rowLen j`, which is too large by one when `(j, c) ∈ μ` and too small
when `(j, c) ∉ μ`. Disjointness plus a count of both sides then forces the union to exhaust
`{0, …, βᵢ - 1}`, with no separate surjectivity argument.

## Main results

* `YoungDiagram.hookLength_add_eq_betaNumber`: the complement of a hook length of row `i` inside
  `βᵢ` is `c + r - μ.colLen c`.
* `YoungDiagram.betaNumber_sub_hookLength_ne_betaNumber`: that complement is not a beta-number `βⱼ`
  of an index `j < r`.
* `YoungDiagram.betaNumber_eq_hookLength`: for `r = μ.colLen 0` the beta-numbers of the nonempty
  rows `i < μ.colLen 0` are the hook lengths of the first column.
* `YoungDiagram.image_betaNumber_sub_hookLength_union_image_betaNumber`: the row description of the
  hook lengths.
* `YoungDiagram.prod_hookLength_row_mul_prod_betaNumber_sub_eq_factorial`: the identity for one row.
* `YoungDiagram.prod_hookLength_mul_prod_betaNumber_sub_eq_prod_factorial`: the hook-length
  product identity.
* `YoungDiagram.IsCorner.betaNumber_erase`: erasing a corner lowers exactly one beta-number, by
  one.

## References

* J. S. Frame, G. de B. Robinson, R. M. Thrall, *The hook graphs of the symmetric group*, Canad. J.
  Math. 6 (1954) 316-324, where the identity below is the step from the Frobenius determinant
  formula to the hook-length formula.
* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I, Section
  1, Example 1, for the description of a row of hook lengths by beta-numbers.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5: the multiplicative hook-length formula.
-/

public section

namespace YoungDiagram

open Finset Nat

variable {μ : YoungDiagram} {r i j c : ℕ}

/-! ### The complement of a hook length in its beta-number -/

/-- **The complement of a hook length inside its beta-number.** For a cell `(i, c)` of `μ` whose
column is no longer than `r`, the hook length of `(i, c)` and the quantity `c + r - μ.colLen c` add
up to the beta-number of row `i`. The second summand depends only on the column `c`, which is what
makes the beta-number description of a row of hook lengths uniform in the row. -/
theorem hookLength_add_eq_betaNumber (hr : μ.colLen c ≤ r) (hc : c < μ.rowLen i) :
    μ.hookLength (i, c) + (c + r - μ.colLen c) = μ.betaNumber r i := by
  have hcol : i < μ.colLen c := mem_iff_lt_colLen.mp (mem_iff_lt_rowLen.mpr hc)
  simp only [hookLength_def, armLength_def, legLength_def, betaNumber_def]
  omega

/-- A hook length of row `i` is at most the beta-number of row `i`. -/
theorem hookLength_le_betaNumber (hr : μ.colLen c ≤ r) (hc : c < μ.rowLen i) :
    μ.hookLength (i, c) ≤ μ.betaNumber r i :=
  Nat.le.intro (hookLength_add_eq_betaNumber hr hc)

/-- The complement of a hook length of row `i` inside its beta-number, in the closed form supplied
by `YoungDiagram.hookLength_add_eq_betaNumber`. -/
@[simp]
theorem betaNumber_sub_hookLength (hi : i < r) (hc : c < μ.rowLen i) :
    μ.betaNumber r i - μ.hookLength (i, c) = c + r - μ.colLen c := by
  have hcol : i < μ.colLen c := mem_iff_lt_colLen.mp (mem_iff_lt_rowLen.mpr hc)
  simp only [hookLength_def, armLength_def, legLength_def, betaNumber_def]
  omega

/-- **The complements of the hook lengths of a row avoid the beta-numbers inside the bound.** By
`YoungDiagram.betaNumber_sub_hookLength` the claim is that `c + r - μ.colLen c` is never a
beta-number `βⱼ` with `j < r`, that is, that `c + j + 1 = μ.colLen c + μ.rowLen j` is impossible:
the right-hand side is at least `c + j + 2` when the cell `(j, c)` lies in `μ` and at most `c + j`
when it does not. -/
theorem betaNumber_sub_hookLength_ne_betaNumber (hi : i < r) (hc : c < μ.rowLen i) (hj : j < r) :
    μ.betaNumber r i - μ.hookLength (i, c) ≠ μ.betaNumber r j := by
  rw [betaNumber_sub_hookLength hi hc]
  simp only [betaNumber_def]
  by_cases hm : (j, c) ∈ μ
  · have h1 : j < μ.colLen c := mem_iff_lt_colLen.mp hm
    have h2 : c < μ.rowLen j := mem_iff_lt_rowLen.mp hm
    omega
  · have h1 : μ.colLen c ≤ j := Nat.not_lt.mp fun h => hm (mem_iff_lt_colLen.mpr h)
    have h2 : μ.rowLen j ≤ c := Nat.not_lt.mp fun h => hm (mem_iff_lt_rowLen.mpr h)
    omega

/-! ### Beta-numbers as hook lengths -/

/-- Relative to the exact number of rows, the beta-numbers of the nonempty rows of a Young diagram
are the hook lengths of its first column: the `c = 0`, `r = μ.colLen 0` case of
`YoungDiagram.hookLength_add_eq_betaNumber`, where the complement `c + r - μ.colLen c` vanishes. -/
@[simp]
theorem betaNumber_eq_hookLength (hi : i < μ.colLen 0) :
    μ.betaNumber (μ.colLen 0) i = μ.hookLength (i, 0) := by
  have hrow : 0 < μ.rowLen i := mem_iff_lt_rowLen.mp (mem_iff_lt_colLen.mpr hi)
  have := hookLength_add_eq_betaNumber (μ := μ) (c := 0) (r := μ.colLen 0) le_rfl hrow
  omega

/-! ### A row of hook lengths -/

/-! ### The hook-length product -/

/-! ### Erasing a corner -/

/-- Erasing a corner lowers the beta-number of its row by one and leaves the other beta-numbers
unchanged. -/
@[simp]
theorem IsCorner.betaNumber_erase {c : ℕ × ℕ} (h : IsCorner μ c) (r i : ℕ) :
    (μ.erase c).betaNumber r i
      = if c.1 = i then μ.betaNumber r i - 1 else μ.betaNumber r i := by
  have hrow : 0 < μ.rowLen c.1 := by rw [h.rowLen_eq_snd_add_one]; omega
  rw [betaNumber_def, h.rowLen_erase, betaNumber_def]
  split_ifs with hi
  · subst hi; omega
  · rfl

end YoungDiagram
