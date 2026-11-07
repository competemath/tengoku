/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import Tengoku.Compply.CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohann
public import Tengoku.Compply.CompPoly.Univariate.ToPoly.Impl

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Mulders-Storjohann Correctness Row and Row-Span Helpers

Row operation and row-span lemmas used by the Mulders-Storjohann correctness proof.
-/

@[expose] public section

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h3v.s6.2859502c3889 from=translated src=- shape=0f49a507 vocab=a1d0088b
-/
theorem rowScalePolynomial_size (c : CPolynomial F) (row : PolynomialRow F) :
    (rowScalePolynomial c row).size = row.size := by
  simp [rowScalePolynomial]

/--
@isnad1 id=eq.0h4v.s6.be3e993241ae from=translated src=- shape=edf512b3 vocab=f17b35a3
-/
theorem rowScaleMonomial_size (c : F) (d : Nat) (row : PolynomialRow F) :
    (rowScaleMonomial c d row).size = row.size := by
  simp [rowScaleMonomial, rowScalePolynomial_size]

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h2v.s6.d0bc3066d0ba from=translated src=- shape=1e65daae vocab=ea46ee12
-/
theorem rowNeg_size (row : PolynomialRow F) :
    (rowNeg row).size = row.size := by
  simp [rowNeg]

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h3v.s6.c5108a31ec5f from=translated src=- shape=30580531 vocab=8bc58b32
-/
theorem rowAdd_size (a b : PolynomialRow F) :
    (rowAdd a b).size = max a.size b.size := by
  simp [rowAdd]

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h3v.s6.6b93652181f4 from=translated src=- shape=30580531 vocab=c64a0df0
-/
theorem rowSub_size (a b : PolynomialRow F) :
    (rowSub a b).size = max a.size b.size := by
  simp [rowSub, rowAdd_size, rowNeg_size]

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h4v.s7.9fca788eb7c7 from=translated src=- shape=5a033672 vocab=d5bb1a32
-/
theorem rowGet_rowAdd (a b : PolynomialRow F) (j : Nat) :
    rowGet (rowAdd a b) j = rowGet a j + rowGet b j := by
  by_cases hj : j < (rowAdd a b).size
  · rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    simp [rowAdd, rowGet] at hj ⊢
  · have hle : (rowAdd a b).size ≤ j := Nat.le_of_not_gt hj
    rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]
    simp [rowAdd] at hle
    have hja : a.size ≤ j := by omega
    have hjb : b.size ≤ j := by omega
    simp [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hja,
      Array.getElem?_eq_none hjb]

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h4v.s7.65ba34ea74d5 from=translated src=- shape=8a5a7203 vocab=267dcc84
-/
theorem rowGet_rowScalePolynomial
    (c : CPolynomial F) (row : PolynomialRow F) (j : Nat) :
    rowGet (rowScalePolynomial c row) j = c * rowGet row j := by
  by_cases hj : j < (rowScalePolynomial c row).size
  · rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    simp [rowScalePolynomial, rowGet] at hj ⊢
    simp [Array.getElem?_eq_getElem hj]
  · have hle : (rowScalePolynomial c row).size ≤ j := Nat.le_of_not_gt hj
    rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]
    simp [rowScalePolynomial] at hle
    simp [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h3v.s6.a29b2c12b347 from=translated src=- shape=e63c17ea vocab=3ca6122c
-/
theorem rowGet_rowNeg (row : PolynomialRow F) (j : Nat) :
    rowGet (rowNeg row) j = -rowGet row j := by
  by_cases hj : j < (rowNeg row).size
  · rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    simp [rowNeg, rowGet] at hj ⊢
    simp [Array.getElem?_eq_getElem hj]
  · have hle : (rowNeg row).size ≤ j := Nat.le_of_not_gt hj
    rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]
    simp [rowNeg] at hle
    simp [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h4v.s7.64c2c4d7a959 from=translated src=- shape=5a033672 vocab=3c04a4d6
-/
theorem rowGet_rowSub (a b : PolynomialRow F) (j : Nat) :
    rowGet (rowSub a b) j = rowGet a j - rowGet b j := by
  simp [rowSub, rowGet_rowAdd, rowGet_rowNeg, sub_eq_add_neg]

/--
@isnad1 id=eq.0h5v.s7.aab74b2cd547 from=translated src=- shape=06bf7425 vocab=67cd1905
-/
theorem rowGet_rowScaleMonomial
    (c : F) (d : Nat) (row : PolynomialRow F) (j : Nat) :
    rowGet (rowScaleMonomial c d row) j =
      CPolynomial.monomial d c * rowGet row j := by
  simp [rowScaleMonomial, rowGet_rowScalePolynomial]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=eq.0h3v.s6.e2aff5d2a912 from=translated src=- shape=93373762 vocab=69e8b353
-/
theorem rowGet_zeroRow (width j : Nat) :
    rowGet (zeroRow (F := F) width) j = 0 := by
  unfold rowGet zeroRow
  by_cases hj : j < (Array.replicate width (0 : CPolynomial F)).size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    simp
  · have hle : (Array.replicate width (0 : CPolynomial F)).size ≤ j :=
      Nat.le_of_not_gt hj
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]
    simp

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h3v.s6.3ff82de44691 from=translated src=- shape=5a14254d vocab=758bbb85
-/
theorem rowScalePolynomial_zeroRow (c : CPolynomial F) (width : Nat) :
    rowScalePolynomial c (zeroRow (F := F) width) = zeroRow width := by
  apply Array.ext
  · simp [rowScalePolynomial, zeroRow]
  · intro j hj₁ hj₂
    simp [rowScalePolynomial, zeroRow]

omit [DecidableEq F] in
/--
@isnad1 id=eq.1h3v.s6.8311f645e8b8 from=translated src=- shape=4ab412f6 vocab=ccef97c5
-/
theorem rowScalePolynomial_eq_zeroRow_of_rowIsZero
    (c : CPolynomial F) {row : PolynomialRow F} (hrow : RowIsZero row) :
    rowScalePolynomial c row = zeroRow row.size := by
  apply Array.ext
  · simp [rowScalePolynomial, zeroRow]
  · intro j hj₁ hj₂
    have hjRow : j < row.size := by
      simpa [rowScalePolynomial] using hj₁
    have hzero : row[j] = 0 := by
      exact hrow row[j] (by
        simpa only [Array.mem_def] using Array.getElem_mem_toList hjRow)
    simp [rowScalePolynomial, zeroRow, hzero]

omit [LawfulBEq F] [DecidableEq F] in
/--
@isnad1 id=rowiszer.0h2v.s5.5431efe93fb5 from=translated src=- shape=652f8bf5 vocab=139a5e56
-/
theorem zeroRow_rowIsZero (width : Nat) :
    RowIsZero (zeroRow (F := F) width) := by
  intro p hp
  rw [zeroRow] at hp
  simpa using (List.mem_replicate.mp (by simpa [Array.mem_def] using hp)).2

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h2v.s6.00e55dbfb4ad from=translated src=- shape=d3a0df6e vocab=33722407
-/
theorem rowScalePolynomial_zero (row : PolynomialRow F) :
    rowScalePolynomial (0 : CPolynomial F) row = zeroRow row.size := by
  apply Array.ext
  · simp [rowScalePolynomial, zeroRow]
  · intro j hj₁ hj₂
    have hget :
        rowGet (rowScalePolynomial (0 : CPolynomial F) row) j =
          rowGet (zeroRow (F := F) row.size) j := by
      simp [rowGet_zeroRow]
      by_cases hj : j < row.size
      · simp [rowGet, rowScalePolynomial, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_getElem hj]
      · have hle : row.size ≤ j := Nat.le_of_not_gt hj
        simp [rowGet, rowScalePolynomial, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none hle]
    simpa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj₁,
      Array.getElem?_eq_getElem hj₂] using hget

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h2v.s6.48a271ca0a05 from=translated src=- shape=2d106ad6 vocab=91141e8c
-/
theorem rowAdd_zeroRow_zeroRow (width : Nat) :
    rowAdd (zeroRow (F := F) width) (zeroRow width) = zeroRow width := by
  apply Array.ext
  · simp [rowAdd, zeroRow]
  · intro j hj₁ hj₂
    have hget :
        rowGet (rowAdd (zeroRow (F := F) width) (zeroRow width)) j =
          rowGet (zeroRow (F := F) width) j := by
      simp [rowGet_rowAdd, rowGet_zeroRow]
    simpa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj₁,
      Array.getElem?_eq_getElem hj₂] using hget

omit [DecidableEq F] in
/--
@isnad1 id=eq.1h3v.s6.36f75157737e from=translated src=- shape=0127b255 vocab=1c54b7c6
-/
theorem rowAdd_zeroRow_right
    {width : Nat} (row : PolynomialRow F) (hsize : row.size = width) :
    rowAdd row (zeroRow (F := F) width) = row := by
  apply Array.ext
  · simp [rowAdd, zeroRow, hsize]
  · intro j hj₁ hj₂
    have hget :
        rowGet (rowAdd row (zeroRow (F := F) width)) j = rowGet row j := by
      simp [rowGet_rowAdd, rowGet_zeroRow]
    simpa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj₁,
      Array.getElem?_eq_getElem hj₂] using hget

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h4v.s7.312827d91205 from=translated src=- shape=34d3127f vocab=bdc3c80e
-/
theorem rowScalePolynomial_rowAdd
    (c : CPolynomial F) (a b : PolynomialRow F) :
    rowScalePolynomial c (rowAdd a b) =
      rowAdd (rowScalePolynomial c a) (rowScalePolynomial c b) := by
  apply Array.ext
  · simp [rowScalePolynomial, rowAdd]
  · intro j hj₁ hj₂
    simp [rowScalePolynomial, rowAdd, rowGet]
    cases a[j]? <;> cases b[j]? <;> simp [mul_add]

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h4v.s6.73c66007f350 from=translated src=- shape=dc54a78a vocab=992f4ca9
-/
theorem rowAdd_assoc (a b c : PolynomialRow F) :
    rowAdd (rowAdd a b) c = rowAdd a (rowAdd b c) := by
  apply Array.ext
  · simp [rowAdd, max_assoc]
  · intro j hj₁ hj₂
    have hget :
        rowGet (rowAdd (rowAdd a b) c) j =
          rowGet (rowAdd a (rowAdd b c)) j := by
      simp [rowGet_rowAdd, add_assoc]
    simpa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj₁,
      Array.getElem?_eq_getElem hj₂] using hget

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h2v.s6.3dcc8d61496c from=translated src=- shape=1f377d30 vocab=191459d9
-/
theorem rowAdd_rowNeg_left (row : PolynomialRow F) :
    rowAdd (rowNeg row) row = zeroRow row.size := by
  apply Array.ext
  · simp [rowAdd, rowNeg, zeroRow]
  · intro j hj₁ hj₂
    have hget :
        rowGet (rowAdd (rowNeg row) row) j =
          rowGet (zeroRow (F := F) row.size) j := by
      simp [rowGet_rowAdd, rowGet_rowNeg, rowGet_zeroRow]
    simpa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj₁,
      Array.getElem?_eq_getElem hj₂] using hget

omit [DecidableEq F] in
/--
@isnad1 id=eq.1h3v.s6.4b121a4136af from=translated src=- shape=60ab36e0 vocab=0ca46f51
-/
theorem rowSub_add_cancel
    {a b : PolynomialRow F} (hsize : b.size = a.size) :
    rowAdd (rowSub a b) b = a := by
  unfold rowSub
  rw [rowAdd_assoc, rowAdd_rowNeg_left]
  exact rowAdd_zeroRow_right a hsize.symm

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h5v.s7.3cc22af3a31f from=translated src=- shape=fae0010a vocab=992f4ca9
-/
theorem rowAdd_medial (a b c d : PolynomialRow F) :
    rowAdd (rowAdd a b) (rowAdd c d) =
      rowAdd (rowAdd a c) (rowAdd b d) := by
  apply Array.ext
  · simp [rowAdd]
    omega
  · intro j hj₁ hj₂
    have hget :
        rowGet (rowAdd (rowAdd a b) (rowAdd c d)) j =
          rowGet (rowAdd (rowAdd a c) (rowAdd b d)) j := by
      simp [rowGet_rowAdd]
      abel
    simpa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj₁,
      Array.getElem?_eq_getElem hj₂] using hget

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h4v.s7.cf75d9a5a6ca from=translated src=- shape=f02fa69a vocab=dbe8f2b1
-/
theorem rowScalePolynomial_add
    (c d : CPolynomial F) (row : PolynomialRow F) :
    rowAdd (rowScalePolynomial c row) (rowScalePolynomial d row) =
      rowScalePolynomial (c + d) row := by
  apply Array.ext
  · simp [rowScalePolynomial, rowAdd]
  · intro j hj₁ hj₂
    have hget :
        rowGet (rowAdd (rowScalePolynomial c row) (rowScalePolynomial d row)) j =
          rowGet (rowScalePolynomial (c + d) row) j := by
      simp [rowGet_rowAdd, rowGet_rowScalePolynomial, add_mul]
    simpa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj₁,
      Array.getElem?_eq_getElem hj₂] using hget

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h4v.s7.bdc5d9c341e1 from=translated src=- shape=347c885d vocab=b5e7ac5c
-/
theorem rowScalePolynomial_assoc
    (c d : CPolynomial F) (row : PolynomialRow F) :
    rowScalePolynomial c (rowScalePolynomial d row) =
      rowScalePolynomial (c * d) row := by
  apply Array.ext
  · simp [rowScalePolynomial]
  · intro j hj₁ hj₂
    simp [rowScalePolynomial, mul_assoc]

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h4v.s8.c24932e25be8 from=translated src=- shape=b410fbdb vocab=1dc78f75
-/
theorem getD_map_mul
    (coeffs : Array (CPolynomial F)) (c : CPolynomial F) (i : Nat) :
    (coeffs.map (fun q ↦ c * q)).getD i 0 = c * coeffs.getD i 0 := by
  by_cases hi : i < coeffs.size
  · simp [Array.getD_eq_getD_getElem?, hi]
  · have hle : coeffs.size ≤ i := Nat.le_of_not_gt hi
    have hleMap : (coeffs.map (fun q ↦ c * q)).size ≤ i := by
      simpa using hle
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle,
      Array.getElem?_eq_none hleMap]

omit [DecidableEq F] in
/--
@isnad1 id=eq.1h5v.s8.8930a64b8c82 from=translated src=- shape=14fb1c25 vocab=4b74f585
-/
theorem getD_ofFn_add
    (n : Nat) (coeffsA coeffsB : Array (CPolynomial F)) {i : Nat} (hi : i < n) :
    (Array.ofFn
        (fun k : Fin n ↦ coeffsA.getD k.1 0 + coeffsB.getD k.1 0)).getD i 0 =
      coeffsA.getD i 0 + coeffsB.getD i 0 := by
  rw [Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_getElem]
  · simp
  · simp [hi]

omit [DecidableEq F] in
/--
@isnad1 id=eq.1h5v.s9.11bae80906bb from=translated src=- shape=255f1af2 vocab=bf1f9c91
-/
theorem rowAdd_rowLinearCombination_range
    {M : PolynomialMatrix F} (coeffsA coeffsB : Array (CPolynomial F)) :
    ∀ n, n ≤ M.size →
      rowAdd
        ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffsA.getD i 0) (M.getD i #[])))
          (zeroRow (MatrixWidth M)))
        ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffsB.getD i 0) (M.getD i #[])))
          (zeroRow (MatrixWidth M))) =
      ((List.range n).foldl
        (fun acc i ↦
          rowAdd acc
            (rowScalePolynomial
              ((Array.ofFn
                (fun k : Fin M.size ↦ coeffsA.getD k.1 0 + coeffsB.getD k.1 0)).getD i 0)
              (M.getD i #[])))
        (zeroRow (MatrixWidth M))) := by
  intro n hn
  induction n with
  | zero =>
      simp [rowAdd_zeroRow_zeroRow]
  | succ n ih =>
      have hnM : n < M.size := by omega
      rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [rowAdd_medial, ih (by omega),
        getD_ofFn_add M.size coeffsA coeffsB hnM, rowScalePolynomial_add]

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h4v.s8.037908c14803 from=translated src=- shape=a4f89ad6 vocab=e4214284
-/
theorem rowAdd_rowLinearCombination
    {M : PolynomialMatrix F} (coeffsA coeffsB : Array (CPolynomial F)) :
    rowAdd (rowLinearCombination coeffsA M) (rowLinearCombination coeffsB M) =
      rowLinearCombination
        (Array.ofFn
          (fun k : Fin M.size ↦ coeffsA.getD k.1 0 + coeffsB.getD k.1 0)) M := by
  simpa [rowLinearCombination] using
    rowAdd_rowLinearCombination_range (M := M) coeffsA coeffsB M.size
      (Nat.le_refl M.size)

omit [DecidableEq F] in
/--
@isnad1 id=mem.2h4v.s7.e7b5524b0f8a from=translated src=- shape=09146846 vocab=b8cfa12a
-/
theorem rowAdd_mem_rowSpan
    {M : PolynomialMatrix F} {a b : PolynomialRow F}
    (ha : a ∈ RowSpan M) (hb : b ∈ RowSpan M) :
    rowAdd a b ∈ RowSpan M := by
  rcases ha with ⟨coeffsA, hsizeA, rfl⟩
  rcases hb with ⟨coeffsB, hsizeB, rfl⟩
  refine ⟨Array.ofFn
    (fun k : Fin M.size ↦ coeffsA.getD k.1 0 + coeffsB.getD k.1 0), ?_, ?_⟩
  · simp
  · rw [rowAdd_rowLinearCombination]

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h2v.s7.a3ad72bd393b from=translated src=- shape=22beb199 vocab=73dd71c5
-/
theorem C_neg_one_mul (p : CPolynomial F) :
    CPolynomial.C (-1 : F) * p = -p := by
  apply (CPolynomial.eq_iff_coeff).2
  intro i
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly]
  rw [CPolynomial.toPoly_neg]
  have hpoly := congrArg (fun P : Polynomial F ↦ P.coeff i)
    (CPolynomial.toPoly_mul (CPolynomial.C (-1 : F)) p)
  rw [CPolynomial.C_toPoly] at hpoly
  simpa using hpoly

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h2v.s6.dc4f6d0a25cb from=translated src=- shape=a98194f6 vocab=adb627a3
-/
theorem rowNeg_eq_rowScalePolynomial (row : PolynomialRow F) :
    rowNeg row = rowScalePolynomial (CPolynomial.C (-1 : F)) row := by
  apply Array.ext
  · simp [rowNeg, rowScalePolynomial]
  · intro j hj₁ hj₂
    simp [rowNeg, rowScalePolynomial, C_neg_one_mul]

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h5v.s9.7c66938854ca from=translated src=- shape=52f13fc6 vocab=6071be91
-/
theorem rowScalePolynomial_rowLinearCombination_range
    {M : PolynomialMatrix F} (c : CPolynomial F) (coeffs : Array (CPolynomial F)) :
    ∀ n,
      rowScalePolynomial c
        ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffs.getD i 0) (M.getD i #[])))
          (zeroRow (MatrixWidth M))) =
      ((List.range n).foldl
        (fun acc i ↦
          rowAdd acc
            (rowScalePolynomial ((coeffs.map fun q ↦ c * q).getD i 0)
              (M.getD i #[])))
        (zeroRow (MatrixWidth M))) := by
  intro n
  induction n with
  | zero =>
      simp [rowScalePolynomial_zeroRow]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [rowScalePolynomial_rowAdd, ih, getD_map_mul,
        rowScalePolynomial_assoc]

omit [DecidableEq F] in
/--
@isnad1 id=eq.0h4v.s7.c8ccf386e970 from=translated src=- shape=41726b8e vocab=f794b94b
-/
theorem rowScalePolynomial_rowLinearCombination
    {M : PolynomialMatrix F} (c : CPolynomial F) (coeffs : Array (CPolynomial F)) :
    rowScalePolynomial c (rowLinearCombination coeffs M) =
      rowLinearCombination (coeffs.map fun q ↦ c * q) M := by
  simpa [rowLinearCombination] using
    rowScalePolynomial_rowLinearCombination_range (M := M) c coeffs M.size

omit [DecidableEq F] in
/--
@isnad1 id=mem.1h4v.s7.030f3299153b from=translated src=- shape=1fc320a7 vocab=a319c698
-/
theorem rowScalePolynomial_mem_rowSpan
    {M : PolynomialMatrix F} {row : PolynomialRow F}
  (c : CPolynomial F) (hrow : row ∈ RowSpan M) :
    rowScalePolynomial c row ∈ RowSpan M := by
  rcases hrow with ⟨coeffs, hsize, rfl⟩
  refine ⟨coeffs.map fun q ↦ c * q, by simp [hsize], ?_⟩
  rw [rowScalePolynomial_rowLinearCombination]

/--
@isnad1 id=mem.1h5v.s7.9ecd991be3c7 from=translated src=- shape=0028ccd9 vocab=b66c3871
-/
theorem rowScaleMonomial_mem_rowSpan
    {M : PolynomialMatrix F} {row : PolynomialRow F}
    (c : F) (d : Nat) (hrow : row ∈ RowSpan M) :
    rowScaleMonomial c d row ∈ RowSpan M := by
  unfold rowScaleMonomial
  exact rowScalePolynomial_mem_rowSpan (CPolynomial.monomial d c) hrow

omit [DecidableEq F] in
/--
@isnad1 id=mem.1h3v.s7.785e4d25afd9 from=translated src=- shape=ce26d852 vocab=9ef74668
-/
theorem rowNeg_mem_rowSpan
    {M : PolynomialMatrix F} {row : PolynomialRow F}
    (hrow : row ∈ RowSpan M) :
    rowNeg row ∈ RowSpan M := by
  rw [rowNeg_eq_rowScalePolynomial]
  exact rowScalePolynomial_mem_rowSpan (CPolynomial.C (-1 : F)) hrow

omit [DecidableEq F] in
/--
@isnad1 id=mem.2h4v.s7.5ead55675d5a from=translated src=- shape=09146846 vocab=cc96ac01
-/
theorem rowSub_mem_rowSpan
    {M : PolynomialMatrix F} {a b : PolynomialRow F}
    (ha : a ∈ RowSpan M) (hb : b ∈ RowSpan M) :
    rowSub a b ∈ RowSpan M := by
  unfold rowSub
  exact rowAdd_mem_rowSpan ha (rowNeg_mem_rowSpan hb)

/--
@isnad1 id=mem.2h5v.s7.8ed48f24c75d from=translated src=- shape=1f444f31 vocab=90ec3415
-/
theorem cancelShiftedLeadingTerm_mem_rowSpan
    {M : PolynomialMatrix F} {target reducer : PolynomialRow F} {shift : Array Nat}
    (htarget : target ∈ RowSpan M) (hreducer : reducer ∈ RowSpan M) :
    cancelShiftedLeadingTerm target reducer shift ∈ RowSpan M := by
  unfold cancelShiftedLeadingTerm
  split <;> try assumption
  split <;> try assumption
  split <;> try assumption
  apply rowSub_mem_rowSpan htarget
  exact rowScaleMonomial_mem_rowSpan _ _ hreducer

/--
@isnad1 id=mem.3h5v.s8.c812ac625a5b from=translated src=- shape=3ddda87e vocab=3b0d8fbe
-/
theorem cancelShiftedLeadingTerm_target_mem_rowSpan
    {M : PolynomialMatrix F} {target reducer : PolynomialRow F} {shift : Array Nat}
    (hcancel : cancelShiftedLeadingTerm target reducer shift ∈ RowSpan M)
    (hreducer : reducer ∈ RowSpan M)
    (hsize : reducer.size = target.size) :
    target ∈ RowSpan M := by
  unfold cancelShiftedLeadingTerm at hcancel
  split at hcancel
  · split at hcancel
    · split at hcancel
      · exact hcancel
      · rename_i _ _ t r _ _ _ _
        let scaled := rowScaleMonomial (t.coeff / r.coeff) (t.degree - r.degree) reducer
        have hscaled : scaled ∈ RowSpan M := by
          exact rowScaleMonomial_mem_rowSpan (t.coeff / r.coeff) (t.degree - r.degree) hreducer
        have hrecovered :
            rowAdd (rowSub target scaled) scaled ∈ RowSpan M :=
          rowAdd_mem_rowSpan hcancel hscaled
        have hscaled_size : scaled.size = target.size := by
          simp [scaled, rowScaleMonomial_size, hsize]
        simpa using
          (show rowAdd (rowSub target scaled) scaled = target from
            rowSub_add_cancel hscaled_size)
            ▸ hrecovered
    · exact hcancel
  · exact hcancel

/--
@isnad1 id=eq.1h4v.s6.2a09f69b190b from=translated src=- shape=7d389e2c vocab=633d9c69
-/
theorem cancelShiftedLeadingTerm_size
    {target reducer : PolynomialRow F} {shift : Array Nat}
    (hsize : reducer.size = target.size) :
    (cancelShiftedLeadingTerm target reducer shift).size = target.size := by
  unfold cancelShiftedLeadingTerm
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  rw [rowSub_size, rowScaleMonomial_size, hsize, max_self]

end PolynomialMatrix

end CompPoly
