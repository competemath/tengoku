/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.LinearAlgebra.Matrix.Echelon.Decomposition
import Tengoku.Seed.LinearAlgebra.Matrix.Swap
import Tengoku.Seed.LinearAlgebra.Matrix.Transvection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/FurinaManifold/sandrones-library@6bce6404b264, `SandronesLibrary/LinearAlgebra/MatrixElimination.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# 初等行变换与高斯消元

> **Entry**: linear-algebra.elimination.row-reduction
-/

namespace SandronesLibrary.LinearAlgebra.MatrixElimination

open Matrix
open scoped Finset

variable {K m n : Type*} [Field K]
variable [Fintype m] [DecidableEq m]

/-- 交换第 `i,j` 行。-/
def swapRows (A : Matrix m n K) (i j : m) : Matrix m n K := Matrix.swap K i j * A

/-- 将第 `j` 行的 `c` 倍加到第 `i` 行；要求 `i ≠ j` 时这是初等行变换。-/
def addRowMultiple (A : Matrix m n K) (i j : m) (c : K) : Matrix m n K :=
  Matrix.transvection i j c * A

/-- 将第 `i` 行乘以标量 `c`。-/
def scaleRow (A : Matrix m n K) (i : m) (c : K) : Matrix m n K :=
  ((1 : Matrix m m K).updateRow i (c • (1 : Matrix m m K) i)) * A

/-- 教材中的行阶梯形。-/
def IsRowEchelon [LT m] [LT n] (A : Matrix m n K) : Prop := Matrix.IsRowEchelon A

/--
@isnad1 id=eq.0h7v.s5.05d936158fb9 from=translated src=- shape=dbfccb33 vocab=2bc9c864
-/
@[simp] theorem swapRows_apply_left (A : Matrix m n K) (i j : m) (k : n) :
    swapRows A i j i k = A j k := Matrix.swap_mul_apply_left i j k A

/--
@isnad1 id=eq.0h7v.s5.c7b233c02ef6 from=translated src=- shape=fb775457 vocab=2bc9c864
-/
@[simp] theorem swapRows_apply_right (A : Matrix m n K) (i j : m) (k : n) :
    swapRows A i j j k = A i k := Matrix.swap_mul_apply_right i j k A

/--
@isnad1 id=eq.2h8v.s5.75fba540e4c0 from=translated src=- shape=177ba3bf vocab=2bc9c864
-/
theorem swapRows_apply_of_ne (A : Matrix m n K) {i j r : m} (hri : r ≠ i) (hrj : r ≠ j)
    (k : n) : swapRows A i j r k = A r k :=
  Matrix.swap_mul_of_ne hri hrj A

/--
@isnad1 id=eq.0h8v.s6.8ff5ab9017a3 from=translated src=- shape=11eeaa4f vocab=036a5dca
-/
@[simp] theorem addRowMultiple_apply_target (A : Matrix m n K) (i j : m) (c : K) (k : n) :
    addRowMultiple A i j c i k = A i k + c * A j k :=
  Matrix.transvection_mul_apply_same i j k c A

/--
@isnad1 id=eq.1h9v.s5.bc727815df0b from=translated src=- shape=f50131f9 vocab=65adce51
-/
theorem addRowMultiple_apply_of_ne (A : Matrix m n K) {i j r : m} (hri : r ≠ i)
    (c : K) (k : n) : addRowMultiple A i j c r k = A r k :=
  Matrix.transvection_mul_apply_of_ne i j r k hri c A

/--
@isnad1 id=eq.0h7v.s5.20e664590911 from=translated src=- shape=9cd9f3f2 vocab=ec5a0d05
-/
@[simp] theorem scaleRow_apply_target (A : Matrix m n K) (i : m) (c : K) (j : n) :
    scaleRow A i c i j = c * A i j := by
  rw [scaleRow, Matrix.updateRow_mul]
  simp only [Matrix.one_mul, Matrix.updateRow_self, Matrix.smul_vecMul, Pi.smul_apply,
    smul_eq_mul]
  have h := congrArg (fun M : Matrix m n K => M i j) (Matrix.one_mul A)
  have hrow : ((1 : Matrix m m K) i ᵥ* A) j = A i j := by
    change (∑ k : m, (1 : Matrix m m K) i k * A k j) = A i j
    simpa [Matrix.mul_apply] using h
  rw [hrow]

/--
@isnad1 id=eq.1h8v.s5.7ed62c959a3d from=translated src=- shape=75ced998 vocab=8e964048
-/
theorem scaleRow_apply_of_ne (A : Matrix m n K) {i r : m} (hri : r ≠ i) (c : K) (j : n) :
    scaleRow A i c r j = A r j := by
  simp [scaleRow, Matrix.updateRow_mul, hri]

/-- 交换同一对行两次恢复原矩阵。
@isnad1 id=eq.0h6v.s5.613f0f5369f7 from=translated src=- shape=64485688 vocab=2bc9c864
-/
@[simp] theorem swapRows_swapRows (A : Matrix m n K) (i j : m) :
    swapRows (swapRows A i j) i j = A := by
  simp [swapRows, ← Matrix.mul_assoc, Matrix.swap_mul_self]

/-- 加行倍数的逆操作是加相反倍数。
@isnad1 id=eq.1h7v.s6.c972dea66396 from=translated src=- shape=dba14703 vocab=97c0dca7
-/
@[simp] theorem addRowMultiple_neg (A : Matrix m n K) {i j : m} (hij : i ≠ j) (c : K) :
    addRowMultiple (addRowMultiple A i j c) i j (-c) = A := by
  simp [addRowMultiple, ← Matrix.mul_assoc,
    Matrix.transvection_mul_transvection_same i j hij]

/-- 初等加行倍数不改变矩阵的秩。
@isnad1 id=eq.1h7v.s6.53d154a0fd94 from=translated src=- shape=0657a58e vocab=b386c2c8
-/
theorem rank_addRowMultiple [Fintype n] (A : Matrix m n K) {i j : m} (hij : i ≠ j) (c : K) :
    (addRowMultiple A i j c).rank = A.rank := by
  apply Matrix.rank_mul_eq_right_of_det_ne_zero
  rw [Matrix.det_transvection_of_ne i j hij c]
  exact one_ne_zero

/-- 交换两行不改变矩阵的秩。
@isnad1 id=eq.0h6v.s5.d291d49b48c4 from=translated src=- shape=cc078e07 vocab=c511ff45
-/
theorem rank_swapRows [Fintype n] (A : Matrix m n K) (i j : m) :
    (swapRows A i j).rank = A.rank := by
  apply Matrix.rank_mul_eq_right_of_det_ne_zero
  simp [Matrix.swap]
  split <;> norm_num

/-- 以非零标量缩放一行不改变矩阵的秩。
@isnad1 id=eq.1h6v.s6.ce139e12dc02 from=translated src=- shape=07133922 vocab=e87d1487
-/
theorem rank_scaleRow [Fintype n] (A : Matrix m n K) (i : m) {c : K} (hc : c ≠ 0) :
    (scaleRow A i c).rank = A.rank := by
  apply Matrix.rank_mul_eq_right_of_det_ne_zero
  rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, Matrix.det_one, mul_one]
  exact hc

/-- 两个矩阵行等价，若它们可由有限次初等行变换互相得到。-/
inductive RowEquivalent : Matrix m n K → Matrix m n K → Prop
  | refl (A) : RowEquivalent A A
  | swap (A) (i j : m) : RowEquivalent A (swapRows A i j)
  | add (A) {i j : m} (hij : i ≠ j) (c : K) :
      RowEquivalent A (addRowMultiple A i j c)
  | scale (A) (i : m) {c : K} (hc : c ≠ 0) : RowEquivalent A (scaleRow A i c)
  | symm {A B} : RowEquivalent A B → RowEquivalent B A
  | trans {A B C} : RowEquivalent A B → RowEquivalent B C → RowEquivalent A C

/-- 行等价是等价关系。-/
instance rowEquivalentSetoid : Setoid (Matrix m n K) where
  r := RowEquivalent
  iseqv := ⟨RowEquivalent.refl, RowEquivalent.symm, RowEquivalent.trans⟩

/-- 行等价矩阵具有相同的秩。
@isnad1 id=eq.1h5v.s5.a9ea2417b167 from=translated src=- shape=ebe69a53 vocab=bf51577b
-/
theorem RowEquivalent.rank_eq [Fintype n] {A B : Matrix m n K} (h : RowEquivalent A B) :
    A.rank = B.rank := by
  induction h with
  | refl => rfl
  | swap A i j => exact (rank_swapRows A i j).symm
  | add A hij c => exact (rank_addRowMultiple A hij c).symm
  | scale A i hc => exact (rank_scaleRow A i hc).symm
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit [Fintype m] [DecidableEq m] in
/-- 零矩阵是没有主元的行阶梯形。
@isnad1 id=ispivote.0h3v.s6.3c1750ef8ec6 from=translated src=- shape=7b6038db vocab=2d734b4d
-/
theorem zero_isPivotedBy_top [LinearOrder m] [LinearOrder n] :
    (0 : Matrix m n K).IsPivotedBy (fun _ => ⊤) := by
  constructor
  · intro i₁ i₂ hi j₂ hz
    rfl
  · intro i
    constructor
    · intro j hj
      rfl
    · intro c hc
      exact (WithTop.coe_ne_top (a := c) hc.symm).elim

/-- 零矩阵情形的高斯消元立即成立。
@isnad1 id=ex.1h4v.s7.b118185e2cf2 from=translated src=- shape=55822bf6 vocab=002d5977
-/
theorem exists_rowEchelon_of_eq_zero [LinearOrder m] [LinearOrder n]
    (A : Matrix m n K) (hA : A = 0) :
    ∃ (R : Matrix m n K) (pivot : m → WithTop n),
      RowEquivalent A R ∧ R.IsPivotedBy pivot := by
  subst A
  exact ⟨0, fun _ => ⊤, RowEquivalent.refl 0, zero_isPivotedBy_top⟩

/-- 把任意非零矩阵元换到指定行，并将其规范化为主元 `1`。
@isnad1 id=ex.1h7v.s6.b994e703e550 from=translated src=- shape=7b86e014 vocab=006a9cc6
-/
theorem normalize_pivot (A : Matrix m n K) {i r : m} {j : n} (hij : A i j ≠ 0) :
    ∃ B : Matrix m n K, RowEquivalent A B ∧ B r j = 1 := by
  let S := swapRows A r i
  let B := scaleRow S r (A i j)⁻¹
  have hinv : (A i j)⁻¹ ≠ 0 := inv_ne_zero hij
  refine ⟨B, RowEquivalent.trans (RowEquivalent.swap A r i)
    (RowEquivalent.scale S r hinv), ?_⟩
  simp [B, S, hij]

/-- 利用已经规范化为 `1` 的主元，消去同一列中的另一个矩阵元。
@isnad1 id=ex.2h7v.s6.827efbcf215c from=translated src=- shape=45c6c5de vocab=006a9cc6
-/
theorem clear_entry_using_pivot (A : Matrix m n K) {r i : m} (hri : i ≠ r) {j : n}
    (hpivot : A r j = 1) :
    ∃ B : Matrix m n K, RowEquivalent A B ∧ B r j = 1 ∧ B i j = 0 := by
  let B := addRowMultiple A i r (-A i j)
  refine ⟨B, RowEquivalent.add A hri (-A i j), ?_, ?_⟩
  · exact (addRowMultiple_apply_of_ne A hri.symm (-A i j) j).trans hpivot
  · simp [B, hpivot]

/-- 依次使用第 `r` 行，消去列表中各行在第 `j` 列的元素。-/
def clearRows (A : Matrix m n K) (r : m) (j : n) : List m → Matrix m n K
  | [] => A
  | i :: rows => clearRows (addRowMultiple A i r (-A i j)) r j rows

/-- 整列消元由有限次初等行变换组成。
@isnad1 id=rowequiv.1h7v.s5.0beccd0ce45f from=translated src=- shape=0b7682de vocab=cf172ea0
-/
theorem clearRows_rowEquivalent (A : Matrix m n K) (r : m) (j : n)
    {rows : List m} (hr : r ∉ rows) : RowEquivalent A (clearRows A r j rows) := by
  induction rows generalizing A with
  | nil => exact RowEquivalent.refl A
  | cons i rows ih =>
      simp only [List.mem_cons, not_or] at hr
      exact RowEquivalent.trans (RowEquivalent.add A (fun h => hr.1 h.symm) (-A i j))
        (ih (A := addRowMultiple A i r (-A i j)) hr.2)

/-- 整列消元过程中，规范主元保持为 `1`。
@isnad1 id=eq.2h7v.s6.0a024bbda119 from=translated src=- shape=80538447 vocab=5fc0635b
-/
theorem clearRows_preserves_pivot (A : Matrix m n K) (r : m) (j : n)
    {rows : List m} (hr : r ∉ rows) (hpivot : A r j = 1) :
    clearRows A r j rows r j = 1 := by
  induction rows generalizing A with
  | nil => exact hpivot
  | cons i rows ih =>
      simp only [List.mem_cons, not_or] at hr
      apply ih (A := addRowMultiple A i r (-A i j)) hr.2
      exact (addRowMultiple_apply_of_ne A hr.1 (-A i j) j).trans hpivot

/-- 未列入消元列表的行不会被整列消元改变。
@isnad1 id=eq.1h8v.s5.fe2b6e560ab4 from=translated src=- shape=d05b9a1e vocab=5fc0635b
-/
theorem clearRows_preserves_row_of_not_mem (A : Matrix m n K) (r k : m) (j : n)
    {rows : List m} (hk : k ∉ rows) : clearRows A r j rows k = A k := by
  induction rows generalizing A with
  | nil => rfl
  | cons i rows ih =>
      simp only [List.mem_cons, not_or] at hk
      simp only [clearRows]
      rw [ih (A := addRowMultiple A i r (-A i j)) hk.2]
      funext c
      exact addRowMultiple_apply_of_ne A hk.1 (-A i j) c

/-- 若目标行列表无重复且不含主元行，则整列消元后列表中每一行的目标列均为零。
@isnad1 id=eq.4h8v.s6.5e05d4e6de3b from=translated src=- shape=6641ff33 vocab=d54c337d
-/
theorem clearRows_eq_zero_of_mem (A : Matrix m n K) (r : m) (j : n)
    {rows : List m} (hnodup : rows.Nodup) (hr : r ∉ rows) (hpivot : A r j = 1)
    {i : m} (hi : i ∈ rows) : clearRows A r j rows i j = 0 := by
  induction rows generalizing A i with
  | nil => simp at hi
  | cons k rows ih =>
      simp only [List.nodup_cons, List.mem_cons, not_or] at hnodup hr hi
      rcases hi with hi | hi
      · subst i
        simp only [clearRows]
        rw [clearRows_preserves_row_of_not_mem
          (A := addRowMultiple A k r (-A k j)) (r := r) (k := k) (j := j) hnodup.1]
        simp [hpivot]
      · simp only [clearRows]
        apply ih (A := addRowMultiple A k r (-A k j)) hnodup.2 hr.2
          ((addRowMultiple_apply_of_ne A hr.1 (-A k j) j).trans hpivot) hi

/-- 使用规范主元消去目标列中除主元外的所有元素。-/
noncomputable def clearColumn (A : Matrix m n K) (r : m) (j : n) : Matrix m n K :=
  clearRows A r j (Finset.univ.erase r).toList

/-- 整列消元保持行等价。
@isnad1 id=rowequiv.0h6v.s5.4954980849b3 from=translated src=- shape=09372d38 vocab=810292db
-/
theorem rowEquivalent_clearColumn (A : Matrix m n K) (r : m) (j : n) :
    RowEquivalent A (clearColumn A r j) := by
  apply clearRows_rowEquivalent
  simp

/-- 整列消元保持规范主元。
@isnad1 id=eq.1h6v.s6.6c44ee7a4410 from=translated src=- shape=96c75857 vocab=0320455f
-/
theorem clearColumn_pivot (A : Matrix m n K) (r : m) (j : n) (hp : A r j = 1) :
    clearColumn A r j r j = 1 := by
  apply clearRows_preserves_pivot <;> simp_all

/-- 整列消元后，目标列中除主元外的元素全部为零。
@isnad1 id=eq.2h7v.s6.24ca5391cdeb from=translated src=- shape=62cae8bc vocab=0320455f
-/
theorem clearColumn_eq_zero (A : Matrix m n K) (r : m) (j : n) (hp : A r j = 1)
    {i : m} (hir : i ≠ r) : clearColumn A r j i j = 0 := by
  apply clearRows_eq_zero_of_mem (A := A) (r := r) (j := j)
  · exact Finset.nodup_toList _
  · simp
  · exact hp
  · simp [hir]

/-- 完整主元准备：选择非零元、换到指定行、规范化为 `1`，并清空该列其余元素。
@isnad1 id=ex.1h7v.s6.117fa2e9f953 from=translated src=- shape=8809ab31 vocab=006a9cc6
-/
theorem prepare_pivot (A : Matrix m n K) {i r : m} {j : n} (hij : A i j ≠ 0) :
    ∃ B : Matrix m n K, RowEquivalent A B ∧ B r j = 1 ∧ ∀ k ≠ r, B k j = 0 := by
  obtain ⟨S, hAS, hS⟩ := normalize_pivot A (r := r) hij
  let B := clearColumn S r j
  refine ⟨B, hAS.trans (rowEquivalent_clearColumn S r j),
    clearColumn_pivot S r j hS, ?_⟩
  intro k hk
  exact clearColumn_eq_zero S r j hS hk

section FiniteBlocks

variable {r c : ℕ}

/-- 删除首行，得到后续行组成的子矩阵。-/
def dropFirstRow (A : Matrix (Fin (r + 1)) (Fin c) K) : Matrix (Fin r) (Fin c) K :=
  A.submatrix Fin.succ id

/-- 删除首列，得到后续列组成的子矩阵。-/
def dropFirstColumn (A : Matrix (Fin r) (Fin (c + 1)) K) : Matrix (Fin r) (Fin c) K :=
  A.submatrix id Fin.succ

/-- 在矩阵左侧补一列零。-/
def prependZeroColumn (A : Matrix (Fin r) (Fin c) K) : Matrix (Fin r) (Fin (c + 1)) K :=
  fun i => Fin.cases 0 (A i)

/-- 由主元行右侧部分 `v` 与右下子矩阵 `A` 拼回规范主元块。-/
def adjoinPivot (v : Fin c → K) (A : Matrix (Fin r) (Fin c) K) :
    Matrix (Fin (r + 1)) (Fin (c + 1)) K :=
  fun i => Fin.cases (Fin.cases 1 v) (fun k => Fin.cases 0 (A k)) i

/--
@isnad1 id=eq.0h5v.s6.e2f77c825111 from=translated src=- shape=5cf53da8 vocab=e0365e92
-/
@[simp] theorem prependZeroColumn_zero (A : Matrix (Fin r) (Fin c) K) (i : Fin r) :
    prependZeroColumn A i 0 = 0 := rfl

/--
@isnad1 id=eq.0h6v.s5.ee52ff4cfb1d from=translated src=- shape=94ad8ec9 vocab=60ddfdf7
-/
@[simp] theorem prependZeroColumn_succ (A : Matrix (Fin r) (Fin c) K)
    (i : Fin r) (j : Fin c) : prependZeroColumn A i j.succ = A i j := rfl

/--
@isnad1 id=eq.0h5v.s6.499945d0ee53 from=translated src=- shape=e3fd6269 vocab=8be03d7f
-/
@[simp] theorem adjoinPivot_zero_zero (v : Fin c → K) (A : Matrix (Fin r) (Fin c) K) :
    adjoinPivot v A 0 0 = 1 := rfl

/--
@isnad1 id=eq.0h6v.s6.5ba55a42325a from=translated src=- shape=45e58f1a vocab=1e908c8e
-/
@[simp] theorem adjoinPivot_zero_succ (v : Fin c → K) (A : Matrix (Fin r) (Fin c) K)
    (j : Fin c) : adjoinPivot v A 0 j.succ = v j := rfl

/--
@isnad1 id=eq.0h6v.s6.9de46d0e2276 from=translated src=- shape=39ddaa99 vocab=1e908c8e
-/
@[simp] theorem adjoinPivot_succ_zero (v : Fin c → K) (A : Matrix (Fin r) (Fin c) K)
    (i : Fin r) : adjoinPivot v A i.succ 0 = 0 := rfl

/--
@isnad1 id=eq.0h7v.s5.fdf7fed106b7 from=translated src=- shape=6e55c2f7 vocab=6cd9e60b
-/
@[simp] theorem adjoinPivot_succ_succ (v : Fin c → K) (A : Matrix (Fin r) (Fin c) K)
    (i : Fin r) (j : Fin c) : adjoinPivot v A i.succ j.succ = A i j := rfl

/--
@isnad1 id=eq.0h4v.s5.72f844dd5b1a from=translated src=- shape=841a2fbe vocab=71c22b12
-/
@[simp] theorem dropFirstColumn_prependZeroColumn (A : Matrix (Fin r) (Fin c) K) :
    dropFirstColumn (prependZeroColumn A) = A := by
  ext i j
  rfl

/--
@isnad1 id=eq.0h5v.s6.2ef82cec16af from=translated src=- shape=4c3bf875 vocab=8d7a4d76
-/
@[simp] theorem dropFirstRow_adjoinPivot (v : Fin c → K) (A : Matrix (Fin r) (Fin c) K) :
    dropFirstRow (adjoinPivot v A) = prependZeroColumn A := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) j <;> rfl

/-- 删除首列后，旧主元在回填零首列时整体右移一列。-/
def shiftPivot (p : Fin r → WithTop (Fin c)) : Fin r → WithTop (Fin (c + 1)) :=
  fun i => WithTop.map Fin.succ (p i)

/-- 在主元表前加入左上角的新主元。-/
def consPivot (p : Fin r → WithTop (Fin c)) : Fin (r + 1) → WithTop (Fin (c + 1)) :=
  Fin.cases (0 : Fin (c + 1)) (shiftPivot p)

/-- 在阶梯形矩阵左侧补零列后仍为阶梯形，主元位置统一右移。
@isnad1 id=ispivote.1h5v.s6.50787b20e826 from=translated src=- shape=f40a912a vocab=cb90d699
-/
theorem prependZeroColumn_isPivotedBy {A : Matrix (Fin r) (Fin c) K}
    {p : Fin r → WithTop (Fin c)} (hp : A.IsPivotedBy p) :
    (prependZeroColumn A).IsPivotedBy (shiftPivot p) := by
  constructor
  · intro i₁ i₂ hi j₂ hz
    cases j₂ using Fin.cases with
    | zero => rfl
    | succ k =>
        exact hp.isRowEchelon hi (fun l hl => hz l.succ (Fin.succ_lt_succ_iff.mpr hl))
  · intro i
    constructor
    · intro j hj
      cases j using Fin.cases with
      | zero => rfl
      | succ k =>
          cases hpi : p i with
          | top =>
              apply (hp.isPivotEntry i).1 k
              rw [hpi]
              exact WithTop.coe_lt_top (a := k)
          | coe a =>
              apply (hp.isPivotEntry i).1 k
              rw [hpi]
              rw [shiftPivot, hpi, WithTop.map_coe] at hj
              exact_mod_cast Fin.succ_lt_succ_iff.mp (WithTop.coe_lt_coe.mp hj)
    · intro d hd
      cases hpi : p i with
      | top =>
          simp [shiftPivot, hpi] at hd
      | coe a =>
          have hda : d = a.succ := by
            simpa [shiftPivot, hpi] using hd.symm
          subst d
          exact (hp.isPivotEntry i).2 a hpi

/-- 在阶梯形右下块左上方加入规范主元后，所得完整矩阵仍为阶梯形。
@isnad1 id=ispivote.1h6v.s7.678bd2e36351 from=translated src=- shape=905752ed vocab=49a1b288
-/
theorem adjoinPivot_isPivotedBy {A : Matrix (Fin r) (Fin c) K}
    {p : Fin r → WithTop (Fin c)} (hp : A.IsPivotedBy p) (v : Fin c → K) :
    (adjoinPivot v A).IsPivotedBy (consPivot p) := by
  constructor
  · intro i₁ i₂ hi j₂ hz
    cases i₁ using Fin.cases with
    | zero =>
        cases i₂ using Fin.cases with
        | zero => simp at hi
        | succ k =>
            cases j₂ using Fin.cases with
            | zero => rfl
            | succ q =>
                have hzero : (0 : Fin (c + 1)) < q.succ :=
                  Fin.pos_iff_ne_zero.mpr (Fin.succ_ne_zero q)
                exact ((one_ne_zero : (1 : K) ≠ 0) (hz 0 hzero)).elim
    | succ a =>
        cases i₂ using Fin.cases with
        | zero => simp at hi
        | succ b =>
            cases j₂ using Fin.cases with
            | zero => rfl
            | succ q =>
                apply hp.isRowEchelon (Fin.succ_lt_succ_iff.mp hi)
                intro l hl
                exact hz l.succ (Fin.succ_lt_succ_iff.mpr hl)
  · intro i
    cases i using Fin.cases with
    | zero =>
        constructor
        · intro j hj
          exact (not_lt_of_ge (bot_le : (0 : WithTop (Fin (c + 1))) ≤ j) hj).elim
        · intro d hd
          simp [consPivot] at hd
          have hd0 : d = 0 := hd
          subst d
          exact one_ne_zero
    | succ i =>
        have ht := (prependZeroColumn_isPivotedBy hp).isPivotEntry i
        have hrow : adjoinPivot v A i.succ = prependZeroColumn A i := by
          funext j
          cases j using Fin.cases <;> rfl
        simpa [consPivot, hrow] using ht

/--
@isnad1 id=eq.0h6v.s6.8526501eaf93 from=translated src=- shape=240c6764 vocab=eabd8f83
-/
theorem prependZeroColumn_swapRows (A : Matrix (Fin r) (Fin c) K) (i j : Fin r) :
    prependZeroColumn (swapRows A i j) = swapRows (prependZeroColumn A) i j := by
  ext k l
  cases l using Fin.cases with
  | zero => simp [swapRows, Matrix.mul_apply, prependZeroColumn]
  | succ q => simp [prependZeroColumn, swapRows, Matrix.mul_apply]

/--
@isnad1 id=eq.0h7v.s6.c1a959e0c1ce from=translated src=- shape=d179177c vocab=a4e4d411
-/
theorem prependZeroColumn_addRowMultiple (A : Matrix (Fin r) (Fin c) K)
    (i j : Fin r) (a : K) :
    prependZeroColumn (addRowMultiple A i j a) =
      addRowMultiple (prependZeroColumn A) i j a := by
  ext k l
  cases l using Fin.cases with
  | zero => simp [addRowMultiple, Matrix.mul_apply, prependZeroColumn]
  | succ q => simp [prependZeroColumn, addRowMultiple, Matrix.mul_apply]

/--
@isnad1 id=eq.0h6v.s6.a86a2f8539a5 from=translated src=- shape=519fac3c vocab=7289f624
-/
theorem prependZeroColumn_scaleRow (A : Matrix (Fin r) (Fin c) K) (i : Fin r) (a : K) :
    prependZeroColumn (scaleRow A i a) = scaleRow (prependZeroColumn A) i a := by
  ext k l
  cases l using Fin.cases with
  | zero => simp [scaleRow, Matrix.mul_apply, prependZeroColumn]
  | succ q => simp [prependZeroColumn, scaleRow, Matrix.mul_apply]

/-- 行等价在左侧补零列后仍成立。
@isnad1 id=rowequiv.1h5v.s6.dc60d320d596 from=translated src=- shape=cfa1ede0 vocab=f3b0a652
-/
theorem rowEquivalent_prependZeroColumn {A B : Matrix (Fin r) (Fin c) K}
    (h : RowEquivalent A B) : RowEquivalent (prependZeroColumn A) (prependZeroColumn B) := by
  induction h with
  | refl A => exact RowEquivalent.refl _
  | swap A i j => simpa [prependZeroColumn_swapRows] using
      RowEquivalent.swap (prependZeroColumn A) i j
  | add A hij a => simpa [prependZeroColumn_addRowMultiple] using
      RowEquivalent.add (prependZeroColumn A) hij a
  | scale A i ha => simpa [prependZeroColumn_scaleRow] using
      RowEquivalent.scale (prependZeroColumn A) i ha
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/--
@isnad1 id=eq.0h7v.s7.d504ac9f1922 from=translated src=- shape=2d9213c8 vocab=abcff707
-/
theorem adjoinPivot_swapRows (v : Fin c → K) (A : Matrix (Fin r) (Fin c) K)
    (i j : Fin r) :
    adjoinPivot v (swapRows A i j) = swapRows (adjoinPivot v A) i.succ j.succ := by
  ext k l
  cases k using Fin.cases with
  | zero =>
      rw [swapRows_apply_of_ne]
      · rfl
      · exact (Fin.succ_ne_zero i).symm
      · exact (Fin.succ_ne_zero j).symm
  | succ q =>
      by_cases hqi : q = i
      · subst q
        cases l using Fin.cases <;> simp
      · by_cases hqj : q = j
        · subst q
          cases l using Fin.cases <;> simp
        · rw [swapRows_apply_of_ne _ (fun h => hqi (Fin.succ_inj.mp h))
            (fun h => hqj (Fin.succ_inj.mp h))]
          cases l using Fin.cases <;> simp [swapRows_apply_of_ne A hqi hqj]

/--
@isnad1 id=eq.0h8v.s7.26d56d918257 from=translated src=- shape=681dcf9f vocab=563a0349
-/
theorem adjoinPivot_addRowMultiple (v : Fin c → K) (A : Matrix (Fin r) (Fin c) K)
    (i j : Fin r) (a : K) :
    adjoinPivot v (addRowMultiple A i j a) =
      addRowMultiple (adjoinPivot v A) i.succ j.succ a := by
  ext k l
  cases k using Fin.cases with
  | zero =>
      rw [addRowMultiple_apply_of_ne]
      · rfl
      · exact (Fin.succ_ne_zero i).symm
  | succ q =>
      by_cases hqi : q = i
      · subst q
        cases l using Fin.cases <;> simp
      · rw [addRowMultiple_apply_of_ne _ (fun h => hqi (Fin.succ_inj.mp h))]
        cases l using Fin.cases <;> simp [addRowMultiple_apply_of_ne A hqi]

/--
@isnad1 id=eq.0h7v.s7.f669eb490b37 from=translated src=- shape=29ef9da5 vocab=19b42d91
-/
theorem adjoinPivot_scaleRow (v : Fin c → K) (A : Matrix (Fin r) (Fin c) K)
    (i : Fin r) (a : K) :
    adjoinPivot v (scaleRow A i a) = scaleRow (adjoinPivot v A) i.succ a := by
  ext k l
  cases k using Fin.cases with
  | zero =>
      rw [scaleRow_apply_of_ne]
      · rfl
      · exact (Fin.succ_ne_zero i).symm
  | succ q =>
      by_cases hqi : q = i
      · subst q
        cases l using Fin.cases <;> simp
      · rw [scaleRow_apply_of_ne _ (fun h => hqi (Fin.succ_inj.mp h))]
        cases l using Fin.cases <;> simp [scaleRow_apply_of_ne A hqi]

/-- 右下子矩阵的行等价可提升为完整主元块的行等价。
@isnad1 id=rowequiv.1h6v.s6.098c904b9f8d from=translated src=- shape=e3ab71f8 vocab=cb210393
-/
theorem rowEquivalent_adjoinPivot (v : Fin c → K) {A B : Matrix (Fin r) (Fin c) K}
    (h : RowEquivalent A B) : RowEquivalent (adjoinPivot v A) (adjoinPivot v B) := by
  induction h with
  | refl A => exact RowEquivalent.refl _
  | swap A i j => simpa [adjoinPivot_swapRows] using
      RowEquivalent.swap (adjoinPivot v A) i.succ j.succ
  | add A hij a => simpa [adjoinPivot_addRowMultiple] using
      RowEquivalent.add (adjoinPivot v A) (fun h => hij (Fin.succ_inj.mp h)) a
  | scale A i ha => simpa [adjoinPivot_scaleRow] using
      RowEquivalent.scale (adjoinPivot v A) i.succ ha
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- 若有限矩阵的首列为零，删去首列再补回零列便得到原矩阵。-/
theorem eq_prependZeroColumn_dropFirstColumn {r c : ℕ}
    (A : Matrix (Fin r) (Fin (c + 1)) K) (hzero : ∀ i, A i 0 = 0) :
    prependZeroColumn (dropFirstColumn A) = A := by
  ext i j
  cases j using Fin.cases with
  | zero => simpa using (hzero i).symm
  | succ q => rfl

/-- 首个主元已经归一化且首列其余项为零时，矩阵可由首行和右下子矩阵重建。-/
theorem eq_adjoinPivot_drop {r c : ℕ} (A : Matrix (Fin (r + 1)) (Fin (c + 1)) K)
    (hp : A 0 0 = 1) (hz : ∀ i : Fin r, A i.succ 0 = 0) :
    adjoinPivot (fun j => A 0 j.succ) (dropFirstColumn (dropFirstRow A)) = A := by
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => exact hp.symm
      | succ q => rfl
  | succ k =>
      cases j using Fin.cases with
      | zero => exact (hz k).symm
      | succ q => rfl

/-- 有限矩阵的高斯消元定理：存在与原矩阵行等价的行阶梯形矩阵。

证明对行数与列数之和作强归纳。首列为零时删去它递归；否则交换并归一化
一个非零元、消去首列其余项，再对右下子矩阵递归。
@isnad1 id=ex.0h4v.s6.6acb429ccda9 from=translated src=- shape=49f7fdff vocab=858aa307
-/
theorem fin_exists_rowEchelon (rows cols : ℕ) (A : Matrix (Fin rows) (Fin cols) K) :
    ∃ (R : Matrix (Fin rows) (Fin cols) K) (pivot : Fin rows → WithTop (Fin cols)),
      RowEquivalent A R ∧ R.IsPivotedBy pivot := by
  generalize hd : rows + cols = d
  induction d using Nat.strong_induction_on generalizing rows cols with
  | h d ih =>
      cases rows with
      | zero =>
          apply exists_rowEchelon_of_eq_zero
          ext i
          exact Fin.elim0 i
      | succ r =>
          cases cols with
          | zero =>
              apply exists_rowEchelon_of_eq_zero
              ext i j
              exact Fin.elim0 j
          | succ c =>
              by_cases hcol : ∀ i, A i 0 = 0
              · let A' : Matrix (Fin (r + 1)) (Fin c) K := dropFirstColumn A
                have hlt : (r + 1) + c < d := by omega
                obtain ⟨R', p, hAR, hp⟩ := ih _ hlt (r + 1) c A' rfl
                refine ⟨prependZeroColumn R', shiftPivot p, ?_,
                  prependZeroColumn_isPivotedBy hp⟩
                rw [← eq_prependZeroColumn_dropFirstColumn A hcol]
                exact rowEquivalent_prependZeroColumn hAR
              · push Not at hcol
                obtain ⟨i, hi⟩ := hcol
                obtain ⟨S, hAS, hS00, hScol⟩ := prepare_pivot A (r := 0) hi
                let T : Matrix (Fin r) (Fin c) K := dropFirstColumn (dropFirstRow S)
                have hlt : r + c < d := by omega
                obtain ⟨R', p, hTR, hp⟩ := ih _ hlt r c T rfl
                let v : Fin c → K := fun j => S 0 j.succ
                refine ⟨adjoinPivot v R', consPivot p, ?_, adjoinPivot_isPivotedBy hp v⟩
                have hrec : adjoinPivot v T = S := by
                  apply eq_adjoinPivot_drop S hS00
                  intro k
                  exact hScol k.succ (Fin.succ_ne_zero k)
                have hSR : RowEquivalent S (adjoinPivot v R') := by
                  rw [← hrec]
                  exact rowEquivalent_adjoinPivot v hTR
                exact hAS.trans hSR

/-- 教材版高斯消元：有限矩阵经过有限次初等行变换后成为行阶梯形。
@isnad1 id=ex.0h4v.s6.6acb429ccda9 from=translated src=- shape=49f7fdff vocab=858aa307
-/
theorem exists_rowEchelon {rows cols : ℕ} (A : Matrix (Fin rows) (Fin cols) K) :
    ∃ (R : Matrix (Fin rows) (Fin cols) K) (pivot : Fin rows → WithTop (Fin cols)),
      RowEquivalent A R ∧ R.IsPivotedBy pivot :=
  fin_exists_rowEchelon rows cols A

/-- 高斯消元同时给出秩公式：原矩阵的秩等于阶梯形矩阵的主元数。
@isnad1 id=ex.0h4v.s7.cea4821316cd from=translated src=- shape=faab856c vocab=8653520c
-/
theorem exists_rowEchelon_with_rank {rows cols : ℕ}
    (A : Matrix (Fin rows) (Fin cols) K) :
    ∃ (R : Matrix (Fin rows) (Fin cols) K) (pivot : Fin rows → WithTop (Fin cols)),
      RowEquivalent A R ∧ R.IsPivotedBy pivot ∧
      A.rank = #{i | pivot i ≠ ⊤} := by
  obtain ⟨R, pivot, hAR, hpivot⟩ := exists_rowEchelon A
  exact ⟨R, pivot, hAR, hpivot, hAR.rank_eq.trans hpivot.rank_eq⟩

end FiniteBlocks

/-- 方阵可通过有限次加行倍数与加列倍数化为对角矩阵；这是高斯主元消去的
双边版本，也是后续 LU/PLU 构造的代数前置。
@isnad1 id=ex.0h3v.s8.183c782db43f from=translated src=- shape=499276a3 vocab=ae2d233d
-/
theorem exists_diagonal_reduction [Fintype n] [DecidableEq n] (A : Matrix n n K) :
    ∃ (L L' : List (Matrix.TransvectionStruct n K)) (d : n → K),
      (L.map Matrix.TransvectionStruct.toMatrix).prod * A *
        (L'.map Matrix.TransvectionStruct.toMatrix).prod = Matrix.diagonal d :=
  Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal A

omit [DecidableEq m] in
/-- 已给出阶梯分解证书时，矩阵秩等于主元个数。
@isnad1 id=eq.0h5v.s7.cbca11e5354a from=translated src=- shape=a1bf295d vocab=00550b3b
-/
theorem rank_eq_pivot_count [Fintype n] [LinearOrder m] [LinearOrder n]
    {A : Matrix m n K} (cert : Echelon.Decomposition A) :
    A.rank = #{i | cert.pivot i ≠ ⊤} := cert.rank_eq

end SandronesLibrary.LinearAlgebra.MatrixElimination
