/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenLetterWord

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `Path.concat` 的 dyadic 分段

本文件刻画 Mathlib 左结合 `Path.concat` 的 dyadic 断点，把相邻断点间的子道路与原输入道路作端点
相对同伦，并把二开集方格细分的步数约束为 dyadic scale 的倍数。

当前条目：

* `topology.homotopy.path-concat-dyadic-subdivision`。

本文件继续直接复用 Mathlib `Path`、`Path.concat` 与 `Path.subpath`，不建立另一套道路或等长分段
承载；aligned block grid、kernel 与 van Kampen 单射属于后续批次。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 任给正整数 `m` 与正实数 `δ`，可选择一个也是 `m` 的倍数的一致网格步数，且网格宽度
仍严格小于 `δ`。这是让 Lebesgue 网格包含全部 `m` 等分断点的数论核心。-/
private theorem exists_nat_pos_multiple_inv_lt (m : ℕ) (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ m ∣ N ∧ (N : ℝ)⁻¹ < δ := by
  obtain ⟨k, hk, hkmesh⟩ := Real.exists_nat_pos_inv_lt hδ
  refine ⟨m * k, Nat.mul_pos hm hk, ⟨k, rfl⟩, ?_⟩
  have hk_le : k ≤ m * k := by
    exact Nat.le_mul_of_pos_left k hm
  calc
    ((m * k : ℕ) : ℝ)⁻¹ ≤ (k : ℝ)⁻¹ :=
      inv_anti₀ (by exact_mod_cast hk) (by exact_mod_cast hk_le)
    _ < δ := hkmesh

private theorem dist_convexComb_left_le_for_multiple_grid (a b u : unitInterval) :
    dist (Set.Icc.convexComb a b u) a ≤ dist b a := by
  rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
  change
    |((1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ)) - (a : ℝ)| ≤
      |(b : ℝ) - (a : ℝ)|
  rw [show ((1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ)) - (a : ℝ) =
      (u : ℝ) * ((b : ℝ) - (a : ℝ)) by ring, abs_mul,
    abs_of_nonneg u.2.1]
  exact mul_le_of_le_one_left (abs_nonneg _) u.2.2

/-- 带指定纵向等分约束的二开集方形细分：网格步数是给定正整数 `m` 的倍数。

> **Entry**: topology.homotopy.path-concat-dyadic-subdivision-/
theorem exists_binaryOpenCoverSquareSubdivision_steps_multiple
    (H : C(unitInterval × unitInterval, X)) {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V)
    (hH : ∀ z, H z ∈ U ∨ H z ∈ V)
    (m : ℕ) (hm : 0 < m) :
    ∃ D : BinaryOpenCoverSquareSubdivision H U V, m ∣ D.steps := by
  let C : Bool → Set (unitInterval × unitInterval)
    | false => H ⁻¹' U
    | true => H ⁻¹' V
  have hCopen : ∀ b, IsOpen (C b) := by
    intro b
    cases b
    · exact hU.preimage H.continuous
    · exact hV.preimage H.continuous
  have hCcover : (Set.univ : Set (unitInterval × unitInterval)) ⊆ ⋃ b, C b := by
    intro z _
    rcases hH z with hz | hz
    · exact Set.mem_iUnion.mpr ⟨false, hz⟩
    · exact Set.mem_iUnion.mpr ⟨true, hz⟩
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric
      (s := (Set.univ : Set (unitInterval × unitInterval)))
      isCompact_univ hCopen hCcover
  obtain ⟨N, hN, hmN, hmesh⟩ :=
    exists_nat_pos_multiple_inv_lt m hm hδ
  have hchoice : ∀ i j : Fin N, ∃ b : Bool,
      Metric.ball
        (unitIntervalMeshPoint N hN i.castSucc,
          unitIntervalMeshPoint N hN j.castSucc) δ ⊆ C b := by
    intro i j
    exact hball _ (Set.mem_univ _)
  let label : Fin N → Fin N → Bool := fun i j => Classical.choose (hchoice i j)
  let D : BinaryOpenCoverSquareSubdivision H U V := {
    steps := N
    steps_pos := hN
    label := label
    cell_mem := by
      intro i j u v
      have hx : dist
          (Set.Icc.convexComb (unitIntervalMeshPoint N hN i.castSucc)
            (unitIntervalMeshPoint N hN i.succ) u)
          (unitIntervalMeshPoint N hN i.castSucc) < δ := by
        calc
          _ ≤ dist (unitIntervalMeshPoint N hN i.succ)
              (unitIntervalMeshPoint N hN i.castSucc) :=
            dist_convexComb_left_le_for_multiple_grid _ _ _
          _ = (N : ℝ)⁻¹ := by
            rw [dist_comm, dist_unitIntervalMeshPoint_castSucc_succ]
          _ < δ := hmesh
      have hy : dist
          (Set.Icc.convexComb (unitIntervalMeshPoint N hN j.castSucc)
            (unitIntervalMeshPoint N hN j.succ) v)
          (unitIntervalMeshPoint N hN j.castSucc) < δ := by
        calc
          _ ≤ dist (unitIntervalMeshPoint N hN j.succ)
              (unitIntervalMeshPoint N hN j.castSucc) :=
            dist_convexComb_left_le_for_multiple_grid _ _ _
          _ = (N : ℝ)⁻¹ := by
            rw [dist_comm, dist_unitIntervalMeshPoint_castSucc_succ]
          _ < δ := hmesh
      have hdist : dist
          (unitSquareCellPoint N hN i j u v)
          (unitIntervalMeshPoint N hN i.castSucc,
            unitIntervalMeshPoint N hN j.castSucc) < δ := by
        simpa [unitSquareCellPoint, Prod.dist_eq, max_lt_iff] using And.intro hx hy
      have hmem := Classical.choose_spec (hchoice i j)
        (Metric.mem_ball.mpr hdist)
      cases hlabel : label i j <;>
        simpa [label, C, binaryOpenCoverPiece, hlabel] using hmem }
  exact ⟨D, hmN⟩

/-- `n` 次有限 `Path.concat` 所有递归二分断点的公共分母。-/
def pathConcatDyadicScale (n : ℕ) : ℕ := 2 ^ n

@[simp] theorem pathConcatDyadicScale_pos (n : ℕ) :
    0 < pathConcatDyadicScale n := by
  simp [pathConcatDyadicScale]

/-- 可选择网格步数为 `2^n` 的倍数，从而为后续对齐 `n` 段 `Path.concat` 的全部 dyadic
断点提供统一分母。-/
theorem exists_binaryOpenCoverSquareSubdivision_concat_multiple
    (H : C(unitInterval × unitInterval, X)) {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V)
    (hH : ∀ z, H z ∈ U ∨ H z ∈ V) (n : ℕ) :
    ∃ D : BinaryOpenCoverSquareSubdivision H U V,
      pathConcatDyadicScale n ∣ D.steps :=
  exists_binaryOpenCoverSquareSubdivision_steps_multiple H hU hV hH
    (pathConcatDyadicScale n) (pathConcatDyadicScale_pos n)

/-- 左结合 `Path.concat` 的 dyadic 断点分子；所有分母统一取 `2^n`。递增一步时，旧 concat
压入左半区，所以旧分子保持不变，新终点分子取新分母。-/
def pathConcatBreakpointNumerator : (n : ℕ) → Fin (n + 1) → ℕ
  | 0, _ => 0
  | n + 1, i => Fin.lastCases (pathConcatDyadicScale (n + 1))
      (fun j => pathConcatBreakpointNumerator n j) i

@[simp] private theorem pathConcatBreakpointNumerator_zero (n : ℕ) :
    pathConcatBreakpointNumerator n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold pathConcatBreakpointNumerator
      rw [show (0 : Fin (n + 1 + 1)) = (0 : Fin (n + 1)).castSucc by rfl]
      rw [Fin.lastCases_castSucc]
      exact ih

@[simp] theorem pathConcatBreakpointNumerator_last (n : ℕ) :
    pathConcatBreakpointNumerator (n + 1) (Fin.last (n + 1)) =
      pathConcatDyadicScale (n + 1) := by
  simp [pathConcatBreakpointNumerator]

@[simp] private theorem pathConcatBreakpointNumerator_castSucc
    (n : ℕ) (i : Fin (n + 1)) :
    pathConcatBreakpointNumerator (n + 1) i.castSucc =
      pathConcatBreakpointNumerator n i := by
  simp [pathConcatBreakpointNumerator]

theorem pathConcatBreakpointNumerator_le_scale :
    ∀ (n : ℕ) (i : Fin (n + 1)),
      pathConcatBreakpointNumerator n i ≤ pathConcatDyadicScale n
  | 0, i => by simp [pathConcatBreakpointNumerator, pathConcatDyadicScale]
  | n + 1, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · rw [pathConcatBreakpointNumerator_castSucc]
        calc
          pathConcatBreakpointNumerator n j ≤ pathConcatDyadicScale n :=
            pathConcatBreakpointNumerator_le_scale n j
          _ ≤ pathConcatDyadicScale (n + 1) := by
            simp [pathConcatDyadicScale, pow_succ]

/-- 相邻 concat 断点的整数分子严格递增。各段长度可以不同，但都非退化。-/
theorem pathConcatBreakpointNumerator_strictMonoAdjacent :
    ∀ (n : ℕ) (i : Fin n),
      pathConcatBreakpointNumerator n i.castSucc <
        pathConcatBreakpointNumerator n i.succ
  | 0, i => Fin.elim0 i
  | n + 1, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [pathConcatBreakpointNumerator_castSucc, Fin.succ_last,
          pathConcatBreakpointNumerator_last]
        calc
          pathConcatBreakpointNumerator n (Fin.last n) ≤ pathConcatDyadicScale n :=
            pathConcatBreakpointNumerator_le_scale n (Fin.last n)
          _ < pathConcatDyadicScale (n + 1) := by
            simp [pathConcatDyadicScale, pow_succ]
      · rw [Fin.succ_castSucc, pathConcatBreakpointNumerator_castSucc,
          pathConcatBreakpointNumerator_castSucc]
        exact pathConcatBreakpointNumerator_strictMonoAdjacent n j

/-- 左结合 `Path.concat` 的第 `r` 个 dyadic 断点。-/
def pathConcatBreakpoint (n : ℕ) (r : Fin (n + 1)) : unitInterval :=
  ⟨(pathConcatBreakpointNumerator n r : ℝ) /
      (pathConcatDyadicScale n : ℝ), by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast pathConcatDyadicScale_pos n)).2
      exact_mod_cast pathConcatBreakpointNumerator_le_scale n r⟩

@[simp] private theorem pathConcatBreakpoint_zero :
    pathConcatBreakpoint 0 (0 : Fin 1) = 0 := by
  ext
  simp [pathConcatBreakpoint, pathConcatBreakpointNumerator,
    pathConcatDyadicScale]

@[simp] theorem pathConcatBreakpoint_last (n : ℕ) :
    pathConcatBreakpoint (n + 1) (Fin.last (n + 1)) = 1 := by
  ext
  simp [pathConcatBreakpoint, ne_of_gt (pathConcatDyadicScale_pos (n + 1))]

/-- 单位区间点压缩到左半区。-/
private def unitIntervalHalf (t : unitInterval) : unitInterval :=
  ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

/-- `concat_succ` 中旧 concat 的全部断点严格压缩为原断点的一半。-/
@[simp] private theorem pathConcatBreakpoint_castSucc (n : ℕ) (i : Fin (n + 1)) :
    pathConcatBreakpoint (n + 1) i.castSucc =
      unitIntervalHalf (pathConcatBreakpoint n i) := by
  apply Subtype.ext
  simp only [pathConcatBreakpoint, pathConcatBreakpointNumerator_castSucc,
    unitIntervalHalf]
  change (pathConcatBreakpointNumerator n i : ℝ) /
      (pathConcatDyadicScale (n + 1) : ℝ) =
    ((pathConcatBreakpointNumerator n i : ℝ) /
      (pathConcatDyadicScale n : ℝ)) / 2
  rw [show pathConcatDyadicScale (n + 1) = 2 * pathConcatDyadicScale n by
    simp [pathConcatDyadicScale, pow_succ, Nat.mul_comm]]
  have hs0 : (pathConcatDyadicScale n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (pathConcatDyadicScale_pos n))
  field_simp
  push_cast
  ring

/-- 单位区间中点。-/
private def unitIntervalMidpoint : unitInterval := ⟨1 / 2, by norm_num⟩

/-- `Path.trans` 右半区重参数化回第二条道路。-/
private theorem Path.trans_subpath_midpoint_one_apply
    {Y : Type*} [TopologicalSpace Y] {a b c : Y}
    (p : Path a b) (q : Path b c) (t : unitInterval) :
    (p.trans q).subpath unitIntervalMidpoint 1 t = q t := by
  change (p.trans q) (Set.Icc.convexComb unitIntervalMidpoint 1 t) = q t
  rw [Path.trans_apply]
  split_ifs with h
  · have ht : (t : ℝ) = 0 := by
      simp [Set.Icc.convexComb, unitIntervalMidpoint] at h
      linarith [t.2.1]
    have ht' : t = 0 := Subtype.ext ht
    subst t
    simp [unitIntervalMidpoint, p.target, q.source]
  · congr 1
    apply Subtype.ext
    simp [unitIntervalMidpoint]
    ring

/-- `Path.trans` 左半区中任意两个已减半参数之间的子道路，逐点就是第一条道路在原参数间的
子道路。-/
private theorem Path.trans_subpath_half_apply
    {Y : Type*} [TopologicalSpace Y] {a b c : Y}
    (p : Path a b) (q : Path b c) (s t u : unitInterval) :
    (p.trans q).subpath (unitIntervalHalf s) (unitIntervalHalf t) u =
      p.subpath s t u := by
  change (p.trans q)
      (Set.Icc.convexComb (unitIntervalHalf s) (unitIntervalHalf t) u) =
    p (Set.Icc.convexComb s t u)
  rw [Path.trans_apply, dite_eq_left]
  · congr 1
    apply Subtype.ext
    simp [unitIntervalHalf]
    ring
  · change ((1 - (u : ℝ)) * ((s : ℝ) / 2) +
      (u : ℝ) * ((t : ℝ) / 2)) ≤ 1 / 2
    nlinarith [s.2.1, s.2.2, t.2.1, t.2.2, u.2.1, u.2.2]

/-- `Path.trans` 在左半区参数 `t/2` 的取值严格等于第一条道路在 `t` 的取值。-/
private theorem Path.trans_half_apply
    {Y : Type*} [TopologicalSpace Y] {a b c : Y}
    (p : Path a b) (q : Path b c) (t : unitInterval) :
    (p.trans q) (unitIntervalHalf t) = p t := by
  rw [Path.trans_apply, dite_eq_left]
  · congr 1
    apply Subtype.ext
    simp [unitIntervalHalf]
    ring
  · change (t : ℝ) / 2 ≤ 1 / 2
    linarith [t.2.2]

/-- `Path.concat` 在每个 dyadic 断点的值严格等于原顶点 family 的对应值。-/
theorem Path.concat_breakpoint_apply
    {Y : Type*} [TopologicalSpace Y] :
    ∀ {n : ℕ} (p : Fin (n + 1) → Y)
      (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
      (r : Fin (n + 1)),
      Path.concat p F (pathConcatBreakpoint n r) = p r
  | 0, p, F, r => by
      have hr : r = 0 := by apply Fin.ext; omega
      subst r
      simp [Path.concat_zero, pathConcatBreakpoint_zero]
  | n + 1, p, F, r => by
      rw [Path.concat_succ]
      refine Fin.lastCases ?_ (fun j => ?_) r
      · rw [pathConcatBreakpoint_last]
        simp
      · rw [pathConcatBreakpoint_castSucc]
        exact (SandronesLibrary.Topology.Path.trans_half_apply
          (Path.concat (p ∘ Fin.castSucc) (fun i => F i.castSucc))
          (F (Fin.last n)) (pathConcatBreakpoint n j)).trans
            (Path.concat_breakpoint_apply
              (p ∘ Fin.castSucc) (fun i => F i.castSucc) j)

/-- `Path.concat` 在第 `i` 对 dyadic 断点之间的子道路，transport 回输入 family 的规范端点。-/
def Path.concatDyadicSegment
    {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (p : Fin (n + 1) → Y)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (i : Fin n) : Path (p i.castSucc) (p i.succ) :=
  ((Path.concat p F).subpath
      (pathConcatBreakpoint n i.castSucc)
      (pathConcatBreakpoint n i.succ)).cast
    (Path.concat_breakpoint_apply p F i.castSucc).symm
    (Path.concat_breakpoint_apply p F i.succ).symm

/-- 单输入道路时，唯一 dyadic segment 严格等于整个 `Path.concat`；后者仍是
`(Path.refl _).trans (F 0)`，并不严格等于 `F 0`。-/
private theorem Path.concatDyadicSegment_one_eq_concat
    {Y : Type*} [TopologicalSpace Y]
    (p : Fin 2 → Y) (F : (i : Fin 1) → Path (p i.castSucc) (p i.succ)) :
    Path.concatDyadicSegment p F 0 = Path.concat p F := by
  have hzero : pathConcatBreakpoint 1 (0 : Fin 2) = 0 := by
    rw [show (0 : Fin 2) = (0 : Fin 1).castSucc by rfl,
      pathConcatBreakpoint_castSucc, pathConcatBreakpoint_zero]
    apply Subtype.ext
    simp [unitIntervalHalf]
  have hone : pathConcatBreakpoint 1 (1 : Fin 2) = 1 :=
    pathConcatBreakpoint_last 0
  have hzero' : pathConcatBreakpoint 1 (Fin.castSucc (0 : Fin 1)) = 0 := by
    simpa using hzero
  have hone' : pathConcatBreakpoint 1 (Fin.succ (0 : Fin 1)) = 1 := by
    simpa using hone
  apply Path.ext
  funext t
  unfold Path.concatDyadicSegment
  rw [Path.cast_coe]
  change Path.concat p F
    (Set.Icc.convexComb
      (pathConcatBreakpoint 1 (Fin.castSucc (0 : Fin 1)))
      (pathConcatBreakpoint 1 (Fin.succ (0 : Fin 1))) t) = _
  rw [hzero', hone']
  simp

/-- 单输入道路时，唯一 dyadic segment 与该输入道路同伦。-/
private theorem Path.concatDyadicSegment_one_homotopic
    {Y : Type*} [TopologicalSpace Y]
    (p : Fin 2 → Y) (F : (i : Fin 1) → Path (p i.castSucc) (p i.succ)) :
    (Path.concatDyadicSegment p F 0).Homotopic (F 0) := by
  rw [Path.concatDyadicSegment_one_eq_concat]
  exact Path.Homotopic.concat_one p F

/-- 至少有两条输入道路时，最后一个 dyadic segment transport 后严格等于最后输入道路。-/
private theorem Path.concatDyadicSegment_last_eq
    {Y : Type*} [TopologicalSpace Y] (n : ℕ)
    (p : Fin (n + 2 + 1) → Y)
    (F : (i : Fin (n + 2)) → Path (p i.castSucc) (p i.succ)) :
    Path.concatDyadicSegment p F (Fin.last (n + 1)) = F (Fin.last (n + 1)) := by
  apply Path.ext
  funext t
  unfold Path.concatDyadicSegment
  rw [Path.cast_coe, Path.concat_succ]
  have hleft : pathConcatBreakpoint (n + 2) (Fin.last (n + 1)).castSucc =
      unitIntervalMidpoint := by
    rw [pathConcatBreakpoint_castSucc,
      pathConcatBreakpoint_last n]
    apply Subtype.ext
    simp [unitIntervalHalf, unitIntervalMidpoint]
  have hright : pathConcatBreakpoint (n + 2) (Fin.last (n + 1)).succ = 1 := by
    rw [show (Fin.last (n + 1)).succ = Fin.last (n + 2) by apply Fin.ext; rfl]
    exact pathConcatBreakpoint_last (n + 1)
  change ((Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc)).trans
      (F (Fin.last (n + 1)))).subpath
        (pathConcatBreakpoint (n + 2) (Fin.last (n + 1)).castSucc)
        (pathConcatBreakpoint (n + 2) (Fin.last (n + 1)).succ) t = _
  rw [hleft, hright]
  exact SandronesLibrary.Topology.Path.trans_subpath_midpoint_one_apply
    (Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc))
    (F (Fin.last (n + 1))) t

/-- 后继 concat 中所有旧 segment 严格等于旧 concat 的对应 dyadic segment。-/
private theorem Path.concatDyadicSegment_castSucc_eq
    {Y : Type*} [TopologicalSpace Y] (n : ℕ)
    (p : Fin (n + 2 + 1) → Y)
    (F : (i : Fin (n + 2)) → Path (p i.castSucc) (p i.succ))
    (i : Fin (n + 1)) :
    Path.concatDyadicSegment p F i.castSucc =
      Path.concatDyadicSegment (p ∘ Fin.castSucc) (fun k => F k.castSucc) i := by
  apply Path.ext
  funext t
  unfold Path.concatDyadicSegment
  rw [Path.cast_coe, Path.cast_coe, Path.concat_succ]
  have hleft : pathConcatBreakpoint (n + 2) i.castSucc.castSucc =
      unitIntervalHalf (pathConcatBreakpoint (n + 1) i.castSucc) := by
    rw [pathConcatBreakpoint_castSucc]
  have hright : pathConcatBreakpoint (n + 2) i.castSucc.succ =
      unitIntervalHalf (pathConcatBreakpoint (n + 1) i.succ) := by
    rw [show i.castSucc.succ = i.succ.castSucc by apply Fin.ext; rfl,
      pathConcatBreakpoint_castSucc]
  change ((Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc)).trans
      (F (Fin.last (n + 1)))).subpath
        (pathConcatBreakpoint (n + 2) i.castSucc.castSucc)
        (pathConcatBreakpoint (n + 2) i.castSucc.succ) t = _
  rw [hleft, hright]
  exact SandronesLibrary.Topology.Path.trans_subpath_half_apply
    (Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc))
    (F (Fin.last (n + 1)))
    (pathConcatBreakpoint (n + 1) i.castSucc)
    (pathConcatBreakpoint (n + 1) i.succ) t

/-- `Path.concat` 的每个规范 dyadic segment 都与相应输入道路端点相对同伦。-/
theorem Path.concatDyadicSegment_homotopic
    {Y : Type*} [TopologicalSpace Y] :
    ∀ {n : ℕ} (p : Fin (n + 1) → Y)
      (F : (i : Fin n) → Path (p i.castSucc) (p i.succ)) (i : Fin n),
      (Path.concatDyadicSegment p F i).Homotopic (F i)
  | 0, p, F, i => Fin.elim0 i
  | 1, p, F, i => by
      have hi : i = 0 := by apply Fin.ext; omega
      subst i
      exact Path.concatDyadicSegment_one_homotopic p F
  | n + 2, p, F, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Path.concatDyadicSegment_last_eq]
      · rw [Path.concatDyadicSegment_castSucc_eq]
        exact Path.concatDyadicSegment_homotopic
          (p ∘ Fin.castSucc) (fun k => F k.castSucc) j

/-- 左结合 `Path.concat` 中，除第一个输入 segment 外，每个 dyadic segment 经规范端点 transport
后都严格等于原输入道路；唯一非严格基例是第一个 segment 前面的常值道路。-/
private theorem Path.concatDyadicSegment_eq_of_ne_zero :
    ∀ {Y : Type*} [TopologicalSpace Y] {n : ℕ}
      (p : Fin (n + 2) → Y)
      (F : (i : Fin (n + 1)) → Path (p i.castSucc) (p i.succ))
      (i : Fin (n + 1)), i ≠ 0 → Path.concatDyadicSegment p F i = F i
  | Y, _, 0, p, F, i, hi => by
      have hizero : i = 0 := by apply Fin.ext; omega
      exact (hi hizero).elim
  | Y, _, n + 1, p, F, i, hi => by
      revert hi
      refine Fin.lastCases (fun _ => ?_) (fun j hi => ?_) i
      · exact Path.concatDyadicSegment_last_eq n p F
      · rw [Path.concatDyadicSegment_castSucc_eq]
        apply Path.concatDyadicSegment_eq_of_ne_zero
        intro hj
        apply hi
        apply Fin.ext
        simp [hj]

/-- 无需在签名中为 `Fin n` 合成 `0` 的版本：索引的自然数值非零时 dyadic segment 严格等于输入。-/
private theorem Path.concatDyadicSegment_eq_of_val_ne_zero
    {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (p : Fin (n + 1) → Y)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (i : Fin n) (hi : i.val ≠ 0) : Path.concatDyadicSegment p F i = F i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      apply Path.concatDyadicSegment_eq_of_ne_zero
      intro hizero
      apply hi
      simp [hizero]

/-- 任意非空左结合 concat 的第一个 dyadic segment，严格等于第一条输入道路前接起点常值道路。-/
private theorem Path.concatDyadicSegment_zero_eq_refl_trans :
    ∀ {Y : Type*} [TopologicalSpace Y] {n : ℕ}
      (p : Fin (n + 2) → Y)
      (F : (i : Fin (n + 1)) → Path (p i.castSucc) (p i.succ)),
      Path.concatDyadicSegment p F (0 : Fin (n + 1)) =
        (Path.refl (p (Fin.castSucc (0 : Fin (n + 1))))).trans (F 0)
  | Y, _, 0, p, F => by
      rw [Path.concatDyadicSegment_one_eq_concat, Path.concat_succ,
        Path.concat_zero]
      rfl
  | Y, _, n + 1, p, F => by
      rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc by rfl,
        Path.concatDyadicSegment_castSucc_eq]
      exact Path.concatDyadicSegment_zero_eq_refl_trans
        (p ∘ Fin.castSucc) (fun i => F i.castSucc)

/-- 以显式正性证明构造首索引的非空版本。-/
private theorem Path.concatDyadicSegment_zero_eq_refl_trans_of_pos
    {Y : Type*} [TopologicalSpace Y] {n : ℕ} (hn : 0 < n)
    (p : Fin (n + 1) → Y)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ)) :
    Path.concatDyadicSegment p F ⟨0, hn⟩ =
      (Path.refl (p (Fin.castSucc ⟨0, hn⟩))).trans (F ⟨0, hn⟩) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact Path.concatDyadicSegment_zero_eq_refl_trans p F

/-- 单输入 `Path.concat` 的全部取值仍落在唯一输入道路取值所在的任意集合中；左半常值段取该道路
的起点。-/
private theorem Path.concat_one_mem
    {Y : Type*} [TopologicalSpace Y]
    (p : Fin 2 → Y) (F : (i : Fin 1) → Path (p i.castSucc) (p i.succ))
    (S : Set Y) (hF : ∀ t, F 0 t ∈ S) (t : unitInterval) :
    Path.concat p F t ∈ S := by
  rw [Path.concat_succ, Path.trans_apply]
  split_ifs
  · simpa [Path.concat_zero] using hF 0
  · exact hF _

/-- 每个 concat dyadic segment 的全部取值仍落在对应输入 segment 全部取值所在的任意集合中。
这比同伦结论更强，后续可据此把真实左边界细网格边提升到输入字母指定的覆盖成员。-/
theorem Path.concatDyadicSegment_mem :
    ∀ {Y : Type*} [TopologicalSpace Y] {n : ℕ}
      (p : Fin (n + 1) → Y)
      (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
      (i : Fin n) (S : Set Y),
      (∀ t, F i t ∈ S) → ∀ t, Path.concatDyadicSegment p F i t ∈ S
  | Y, _, 0, p, F, i, S, hF => Fin.elim0 i
  | Y, _, 1, p, F, i, S, hF => by
      have hi : i = 0 := by apply Fin.ext; omega
      subst i
      rw [Path.concatDyadicSegment_one_eq_concat]
      exact Path.concat_one_mem p F S hF
  | Y, _, n + 2, p, F, i, S, hF => by
      revert hF
      refine Fin.lastCases (fun hF => ?_) (fun j hF => ?_) i
      · rw [Path.concatDyadicSegment_last_eq]
        exact hF
      · rw [Path.concatDyadicSegment_castSucc_eq]
        exact Path.concatDyadicSegment_mem
          (p ∘ Fin.castSucc) (fun k => F k.castSucc) j S hF

/-- `Path.concat` 的第 `i` 个 dyadic segment（包括一段基例中的常值重参数化部分）逐点仍位于
反序输入列表第 `i` 个字母指定的覆盖成员中。-/
theorem binaryVanKampenLetterConcatLoop_dyadicSegment_mem_piece
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (i : Fin letters.reverse.length) (t : unitInterval) :
    Path.concatDyadicSegment
        (fun _ : Fin (letters.reverse.length + 1) => x₀)
        (fun j : Fin letters.reverse.length =>
          (letters.reverse.get j).ambientLoop hxU hxV) i t ∈
      binaryOpenCoverPiece U V (letters.reverse.get i).1 := by
  exact Path.concatDyadicSegment_mem
    (fun _ : Fin (letters.reverse.length + 1) => x₀)
    (fun j : Fin letters.reverse.length =>
      (letters.reverse.get j).ambientLoop hxU hxV)
    i (binaryOpenCoverPiece U V (letters.reverse.get i).1)
    (binaryVanKampenLetterConcatLoop_segment_mem hxU hxV letters i) t

omit [TopologicalSpace X] in
@[simp] theorem coe_binaryOpenCoverBasepoint
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (b : Bool) :
    ((binaryOpenCoverBasepoint hxU hxV b : binaryOpenCoverPiece U V b) : X) = x₀ := by
  cases b <;> rfl

/-- 第 `i` 个 dyadic segment 直接提升到该输入字母指定的覆盖成员。-/
def binaryVanKampenLetterDyadicSegmentInPiece
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (i : Fin letters.reverse.length) :
    Path (binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1)
      (binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1) where
  toFun t := ⟨Path.concatDyadicSegment
      (fun _ : Fin (letters.reverse.length + 1) => x₀)
      (fun j : Fin letters.reverse.length =>
        (letters.reverse.get j).ambientLoop hxU hxV) i t,
      binaryVanKampenLetterConcatLoop_dyadicSegment_mem_piece
        hxU hxV letters i t⟩
  continuous_toFun := by fun_prop
  source' := by
    apply Subtype.ext
    simp
  target' := by
    apply Subtype.ext
    simp

/-- 字母成员中的 dyadic segment 提升，与该字母所选基本群道路代表在同一 subtype 中同伦。-/
theorem binaryVanKampenLetterDyadicSegmentInPiece_homotopic_representative
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (i : Fin letters.reverse.length) :
    (binaryVanKampenLetterDyadicSegmentInPiece hxU hxV letters i).Homotopic
      (fundamentalGroupPathRepresentative
        (binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1)
        (letters.reverse.get i).2) := by
  let p : Fin (letters.reverse.length + 1) → X := fun _ => x₀
  let F : (j : Fin letters.reverse.length) → Path (p j.castSucc) (p j.succ) :=
    fun j => (letters.reverse.get j).ambientLoop hxU hxV
  by_cases hi : i.val = 0
  · have hn : 0 < letters.reverse.length := Nat.pos_of_ne_zero (by
      intro hzero
      have : i.val < 0 := by simpa [hzero] using i.isLt
      omega)
    have hizero : i = ⟨0, hn⟩ := by apply Fin.ext; exact hi
    have hpath : binaryVanKampenLetterDyadicSegmentInPiece hxU hxV letters i =
        (Path.refl (binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1)).trans
          (fundamentalGroupPathRepresentative
            (binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1)
            (letters.reverse.get i).2) := by
      apply Path.ext
      funext t
      apply Subtype.ext
      simp only [binaryVanKampenLetterDyadicSegmentInPiece]
      calc
        Path.concatDyadicSegment p F i t =
            ((Path.refl x₀).trans ((letters.reverse.get i).ambientLoop hxU hxV)) t := by
          rw [hizero, Path.concatDyadicSegment_zero_eq_refl_trans_of_pos hn p F]
        _ = (fun z : binaryOpenCoverPiece U V (letters.reverse.get i).1 => (z : X))
              (((Path.refl (binaryOpenCoverBasepoint hxU hxV
                (letters.reverse.get i).1)).trans
                (fundamentalGroupPathRepresentative
                  (binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1)
                  (letters.reverse.get i).2)) t) := by
          rw [Path.trans_apply, Path.trans_apply]
          split_ifs
          · simp
          · exact BinaryVanKampenLetter.ambientLoop_apply
              hxU hxV (letters.reverse.get i) _
    rw [hpath]
    exact ⟨Path.Homotopy.reflTrans _⟩
  · have hpath : binaryVanKampenLetterDyadicSegmentInPiece hxU hxV letters i =
        fundamentalGroupPathRepresentative
          (binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1)
          (letters.reverse.get i).2 := by
      apply Path.ext
      funext t
      apply Subtype.ext
      simp only [binaryVanKampenLetterDyadicSegmentInPiece]
      calc
        Path.concatDyadicSegment p F i t =
            (letters.reverse.get i).ambientLoop hxU hxV t := by
          rw [Path.concatDyadicSegment_eq_of_val_ne_zero p F i hi]
        _ = (fun z : binaryOpenCoverPiece U V (letters.reverse.get i).1 => (z : X))
              (fundamentalGroupPathRepresentative
                (binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1)
                (letters.reverse.get i).2 t) :=
          BinaryVanKampenLetter.ambientLoop_apply
            hxU hxV (letters.reverse.get i) t
    rw [hpath]

end SandronesLibrary.Topology
