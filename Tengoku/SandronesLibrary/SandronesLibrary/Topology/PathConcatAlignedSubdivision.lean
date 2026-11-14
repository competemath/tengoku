/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PathConcatDyadicSubdivision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `Path.concat` 与方格细边的 dyadic 对齐

本文件把 10a 的 dyadic breakpoint 嵌入实际方格网格，建立 block-local 到全局边索引的 flatten 定理，
并以 `PathConcatAlignedSquareSubdivision` 记录方格细分和正 refinement factor 的精确对齐。

当前条目：

* `topology.fundamental-group.van-kampen-concat-aligned-subdivision`。

道路、subpath、同伦和方格细分继续复用既有承载；本层只增加二者间必要的对齐证书，不比较 cell
标签与字母标签，也不进入 kernel 或 van Kampen 单射。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- `m` 等分网格在 `m*k` 等分加细中的同一断点索引。-/
private def repeatedMeshBreakpoint (m k : ℕ) (r : Fin (m + 1)) : Fin (m * k + 1) :=
  ⟨r.val * k, Nat.lt_succ_of_le (Nat.mul_le_mul_right k (Nat.le_of_lt_succ r.isLt))⟩

/-- 正倍数一致网格严格保留原 `m` 等分的全部断点。-/
private theorem unitIntervalMeshPoint_repeatedMeshBreakpoint
    (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (r : Fin (m + 1)) :
    unitIntervalMeshPoint (m * k) (Nat.mul_pos hm hk)
        (repeatedMeshBreakpoint m k r) =
      unitIntervalMeshPoint m hm r := by
  apply Subtype.ext
  change (((r.val * k : ℕ) : ℝ) / ((m * k : ℕ) : ℝ)) =
    (r.val : ℝ) / (m : ℝ)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  push_cast
  field_simp

/-- 将 `Path.concat` 的第 `r` 个 dyadic 断点放入 `2^n*k` 网格。

> **Entry**: topology.fundamental-group.van-kampen-concat-aligned-subdivision-/
def pathConcatBreakpointGridIndex (n k : ℕ) (r : Fin (n + 1)) :
    Fin (pathConcatDyadicScale n * k + 1) :=
  repeatedMeshBreakpoint (pathConcatDyadicScale n) k
    ⟨pathConcatBreakpointNumerator n r,
      Nat.lt_succ_of_le (pathConcatBreakpointNumerator_le_scale n r)⟩

/-- `2^n*k` 一致网格中上述索引的网格点严格等于相应 concat dyadic 断点。-/
theorem unitIntervalMeshPoint_pathConcatBreakpointGridIndex
    (n k : ℕ) (hk : 0 < k) (r : Fin (n + 1)) :
    unitIntervalMeshPoint (pathConcatDyadicScale n * k)
        (Nat.mul_pos (pathConcatDyadicScale_pos n) hk)
        (pathConcatBreakpointGridIndex n k r) =
      pathConcatBreakpoint n r := by
  rw [pathConcatBreakpointGridIndex,
    unitIntervalMeshPoint_repeatedMeshBreakpoint
      (pathConcatDyadicScale n) k (pathConcatDyadicScale_pos n) hk]
  rfl

/-- 第 `i` 个 concat segment 在 `2^n*k` 对齐网格中实际跨越的细网格边数。这个数通常不是
简单的 `k`，因为左结合 `Path.concat` 的相邻 dyadic 断点间距并不一致。-/
def pathConcatSegmentGridLength (n k : ℕ) (i : Fin n) : ℕ :=
  (pathConcatBreakpointNumerator n i.succ -
      pathConcatBreakpointNumerator n i.castSucc) * k

@[simp] theorem pathConcatSegmentGridLength_pos
    (n k : ℕ) (hk : 0 < k) (i : Fin n) :
    0 < pathConcatSegmentGridLength n k i := by
  exact Nat.mul_pos
    (Nat.sub_pos_of_lt (pathConcatBreakpointNumerator_strictMonoAdjacent n i)) hk

/-- 第 `i` 个 concat segment 内第 `s` 个细网格点的全局索引。-/
def pathConcatSegmentGridIndex
    (n k : ℕ) (i : Fin n)
    (s : Fin (pathConcatSegmentGridLength n k i + 1)) :
    Fin (pathConcatDyadicScale n * k + 1) := by
  let a := pathConcatBreakpointNumerator n i.castSucc
  let b := pathConcatBreakpointNumerator n i.succ
  refine ⟨a * k + s, Nat.lt_succ_of_le ?_⟩
  have hab : a ≤ b := Nat.le_of_lt
    (pathConcatBreakpointNumerator_strictMonoAdjacent n i)
  calc
    a * k + s ≤ a * k + pathConcatSegmentGridLength n k i :=
      Nat.add_le_add_left (Nat.le_of_lt_succ s.isLt) _
    _ = b * k := by
      rw [pathConcatSegmentGridLength, ← Nat.add_mul, Nat.add_sub_of_le hab]
    _ ≤ pathConcatDyadicScale n * k := Nat.mul_le_mul_right k
      (pathConcatBreakpointNumerator_le_scale n i.succ)

/-- 第 `i` 个 concat segment 内第 `s` 条细网格边的全局边索引。-/
def pathConcatSegmentGridEdgeIndex
    (n k : ℕ) (i : Fin n) (s : Fin (pathConcatSegmentGridLength n k i)) :
    Fin (pathConcatDyadicScale n * k) := by
  let a := pathConcatBreakpointNumerator n i.castSucc
  let b := pathConcatBreakpointNumerator n i.succ
  refine ⟨a * k + s, ?_⟩
  have hab : a ≤ b := Nat.le_of_lt
    (pathConcatBreakpointNumerator_strictMonoAdjacent n i)
  calc
    a * k + s < a * k + pathConcatSegmentGridLength n k i :=
      Nat.add_lt_add_left s.isLt _
    _ = b * k := by
      rw [pathConcatSegmentGridLength, ← Nat.add_mul, Nat.add_sub_of_le hab]
    _ ≤ pathConcatDyadicScale n * k := Nat.mul_le_mul_right k
      (pathConcatBreakpointNumerator_le_scale n i.succ)

/-- Consecutive half-open natural-number intervals determined by a monotone
finite breakpoint family flatten to the single interval from the first to the
last breakpoint.-/
private theorem contiguousRanges_ofFn
    (n : ℕ) (a : Fin (n + 1) → ℕ) (ha : Monotone a) :
    (List.ofFn fun i : Fin n =>
      List.range' (a i.castSucc) (a i.succ - a i.castSucc)).flatten =
      List.range' (a 0) (a (Fin.last n) - a 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ']
      rw [List.concat_eq_append, List.flatten_concat]
      let a' : Fin (n + 1) → ℕ := fun r => a r.castSucc
      have ha' : Monotone a' := fun _ _ h =>
        ha (Fin.castSucc_le_castSucc_iff.mpr h)
      have hih := ih a' ha'
      rw [show (List.ofFn fun i : Fin n =>
          List.range' (a i.castSucc.castSucc)
            (a i.castSucc.succ - a i.castSucc.castSucc)).flatten =
          List.range' (a 0) (a (Fin.last n).castSucc - a 0) by
        simpa only [a', ← Fin.castSucc_succ, Fin.castSucc_zero] using hih]
      let start := a 0
      let middle := a (Fin.last n).castSucc
      let finish := a (Fin.last (n + 1))
      have hstart : start ≤ middle := by
        apply ha
        exact Fin.zero_le _
      have hmiddle : middle ≤ finish := by
        apply ha
        exact Fin.le_last _
      change List.range' start (middle - start) ++
          List.range' middle (finish - middle) =
        List.range' start (finish - start)
      have hadd : start + (middle - start) = middle :=
        Nat.add_sub_of_le hstart
      have hlen : (middle - start) + (finish - middle) = finish - start := by
        omega
      calc
        List.range' start (middle - start) ++
            List.range' middle (finish - middle) =
          List.range' start (middle - start) ++
            List.range' (start + 1 * (middle - start))
              (finish - middle) := by rw [one_mul, hadd]
        _ = List.range' start
            ((middle - start) + (finish - middle)) := List.range'_append
        _ = List.range' start (finish - start) := by rw [hlen]

/-- The dyadic concat blocks, each internally listed in increasing fine-grid
edge order, flatten to every global fine-grid edge index exactly once and in
order.-/
theorem pathConcatSegmentGridEdgeIndices_flatten
    (n k : ℕ) (hn : 0 < n) :
    (List.ofFn fun i : Fin n =>
      List.ofFn fun s : Fin (pathConcatSegmentGridLength n k i) =>
        pathConcatSegmentGridEdgeIndex n k i s).flatten =
      List.ofFn (fun r : Fin (pathConcatDyadicScale n * k) => r) := by
  apply (List.map_injective_iff.mpr Fin.val_injective)
  rw [List.map_flatten]
  rw [show (List.ofFn fun i : Fin n =>
      List.ofFn fun s : Fin (pathConcatSegmentGridLength n k i) =>
        pathConcatSegmentGridEdgeIndex n k i s).map (List.map Fin.val) =
      List.ofFn (fun i : Fin n =>
        List.ofFn fun s : Fin (pathConcatSegmentGridLength n k i) =>
          (pathConcatSegmentGridEdgeIndex n k i s).val) by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    dsimp only [Function.comp_apply]
    rw [List.map_ofFn]
    rfl]
  rw [show (List.ofFn (fun r : Fin (pathConcatDyadicScale n * k) => r)).map
      Fin.val = List.ofFn (fun r : Fin (pathConcatDyadicScale n * k) => r.val) by
    rw [List.map_ofFn]
    rfl]
  let a : Fin (n + 1) → ℕ := fun r =>
    pathConcatBreakpointNumerator n r * k
  have ha : Monotone a := Fin.monotone_iff_le_succ.mpr fun i =>
    Nat.mul_le_mul_right k
      (Nat.le_of_lt (pathConcatBreakpointNumerator_strictMonoAdjacent n i))
  have hinner : ∀ i : Fin n,
      List.ofFn (fun s : Fin (pathConcatSegmentGridLength n k i) =>
        (pathConcatSegmentGridEdgeIndex n k i s).val) =
      List.range' (a i.castSucc) (a i.succ - a i.castSucc) := by
    intro i
    apply List.ext_getElem
    · simp [pathConcatSegmentGridLength, a, Nat.sub_mul]
    · intro m hm₁ hm₂
      rw [List.getElem_ofFn, List.getElem_range'_1]
      rfl
  rw [show List.ofFn (fun i : Fin n =>
      List.ofFn (fun s : Fin (pathConcatSegmentGridLength n k i) =>
        (pathConcatSegmentGridEdgeIndex n k i s).val)) =
      List.ofFn (fun i : Fin n =>
        List.range' (a i.castSucc) (a i.succ - a i.castSucc)) by
    apply congrArg List.ofFn
    funext i
    exact hinner i]
  rw [contiguousRanges_ofFn n a ha]
  have ha0 : a 0 = 0 := by
    simp [a]
  have halast : a (Fin.last n) = pathConcatDyadicScale n * k := by
    cases n with
    | zero => omega
    | succ n => simp [a]
  rw [ha0, halast]
  simp only [Nat.sub_zero]
  apply List.ext_getElem
  · simp
  · intro m hm₁ hm₂
    rw [List.getElem_range'_1, List.getElem_ofFn]
    simp

@[simp] theorem pathConcatSegmentGridEdgeIndex_castSucc
    (n k : ℕ) (i : Fin n) (s : Fin (pathConcatSegmentGridLength n k i)) :
    (pathConcatSegmentGridEdgeIndex n k i s).castSucc =
      pathConcatSegmentGridIndex n k i s.castSucc := by
  apply Fin.ext
  rfl

@[simp] theorem pathConcatSegmentGridEdgeIndex_succ
    (n k : ℕ) (i : Fin n) (s : Fin (pathConcatSegmentGridLength n k i)) :
    (pathConcatSegmentGridEdgeIndex n k i s).succ =
      pathConcatSegmentGridIndex n k i s.succ := by
  apply Fin.ext
  rfl

@[simp] theorem pathConcatSegmentGridIndex_zero
    (n k : ℕ) (i : Fin n) :
    pathConcatSegmentGridIndex n k i 0 =
      pathConcatBreakpointGridIndex n k i.castSucc := by
  apply Fin.ext
  rfl

@[simp] theorem pathConcatSegmentGridIndex_last
    (n k : ℕ) (i : Fin n) :
    pathConcatSegmentGridIndex n k i
        (Fin.last (pathConcatSegmentGridLength n k i)) =
      pathConcatBreakpointGridIndex n k i.succ := by
  apply Fin.ext
  simp only [pathConcatSegmentGridIndex,
    pathConcatSegmentGridLength, pathConcatBreakpointGridIndex,
    repeatedMeshBreakpoint]
  change pathConcatBreakpointNumerator n i.castSucc * k +
      (pathConcatBreakpointNumerator n i.succ -
        pathConcatBreakpointNumerator n i.castSucc) * k =
    pathConcatBreakpointNumerator n i.succ * k
  rw [← Nat.add_mul, Nat.add_sub_of_le
    (Nat.le_of_lt (pathConcatBreakpointNumerator_strictMonoAdjacent n i))]

/-- 第 `i` 个 concat segment 内的细网格点，作为单位区间中的真实参数。-/
def pathConcatSegmentMeshPoint
    (n k : ℕ) (hk : 0 < k) (i : Fin n)
    (s : Fin (pathConcatSegmentGridLength n k i + 1)) : unitInterval :=
  unitIntervalMeshPoint (pathConcatDyadicScale n * k)
    (Nat.mul_pos (pathConcatDyadicScale_pos n) hk)
    (pathConcatSegmentGridIndex n k i s)

@[simp] theorem pathConcatSegmentMeshPoint_zero
    (n k : ℕ) (hk : 0 < k) (i : Fin n) :
    pathConcatSegmentMeshPoint n k hk i 0 =
      pathConcatBreakpoint n i.castSucc := by
  rw [pathConcatSegmentMeshPoint, pathConcatSegmentGridIndex_zero,
    unitIntervalMeshPoint_pathConcatBreakpointGridIndex n k hk i.castSucc]

@[simp] theorem pathConcatSegmentMeshPoint_last
    (n k : ℕ) (hk : 0 < k) (i : Fin n) :
    pathConcatSegmentMeshPoint n k hk i
        (Fin.last (pathConcatSegmentGridLength n k i)) =
      pathConcatBreakpoint n i.succ := by
  rw [pathConcatSegmentMeshPoint, pathConcatSegmentGridIndex_last,
    unitIntervalMeshPoint_pathConcatBreakpointGridIndex n k hk i.succ]

/-- block 内的全局细网格点，严格等于整个 dyadic segment 在相应局部一致网格参数处的仿射点。-/
theorem pathConcatSegmentMeshPoint_eq_convexComb
    (n k : ℕ) (hk : 0 < k) (i : Fin n)
    (s : Fin (pathConcatSegmentGridLength n k i + 1)) :
    pathConcatSegmentMeshPoint n k hk i s =
      Set.Icc.convexComb
        (pathConcatBreakpoint n i.castSucc)
        (pathConcatBreakpoint n i.succ)
        (unitIntervalMeshPoint (pathConcatSegmentGridLength n k i)
          (pathConcatSegmentGridLength_pos n k hk i) s) := by
  let a := pathConcatBreakpointNumerator n i.castSucc
  let b := pathConcatBreakpointNumerator n i.succ
  let scale := pathConcatDyadicScale n
  have hab : a < b := pathConcatBreakpointNumerator_strictMonoAdjacent n i
  have hd : 0 < b - a := Nat.sub_pos_of_lt hab
  have hscale : 0 < scale := pathConcatDyadicScale_pos n
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hd0 : ((b - a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hs0 : (scale : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hscale)
  apply Subtype.ext
  dsimp [pathConcatSegmentMeshPoint, pathConcatSegmentGridIndex,
    pathConcatBreakpoint, unitIntervalMeshPoint, pathConcatSegmentGridLength,
    Set.Icc.convexComb, a, b, scale]
  push_cast
  have hab_sub : (a : ℝ) + ((b - a : ℕ) : ℝ) = (b : ℝ) := by
    exact_mod_cast Nat.add_sub_of_le (Nat.le_of_lt hab)
  field_simp [hk0, hd0, hs0, a, b, scale]
  dsimp [a, b] at hab_sub
  nlinarith

/-- 一个 block 内相邻两个细网格点之间的仿射参数，等于先在该 dyadic segment 的局部网格中取
相邻参数、再映回全局 dyadic 区间。-/
theorem pathConcatSegmentFineInterval_eq_convexComb
    (n k : ℕ) (hk : 0 < k) (i : Fin n)
    (s : Fin (pathConcatSegmentGridLength n k i)) (t : unitInterval) :
    Set.Icc.convexComb
        (pathConcatSegmentMeshPoint n k hk i s.castSucc)
        (pathConcatSegmentMeshPoint n k hk i s.succ) t =
      Set.Icc.convexComb
        (pathConcatBreakpoint n i.castSucc)
        (pathConcatBreakpoint n i.succ)
        (Set.Icc.convexComb
          (unitIntervalMeshPoint (pathConcatSegmentGridLength n k i)
            (pathConcatSegmentGridLength_pos n k hk i) s.castSucc)
          (unitIntervalMeshPoint (pathConcatSegmentGridLength n k i)
            (pathConcatSegmentGridLength_pos n k hk i) s.succ) t) := by
  rw [pathConcatSegmentMeshPoint_eq_convexComb,
    pathConcatSegmentMeshPoint_eq_convexComb]
  apply Subtype.ext
  simp only [Set.Icc.convexComb, Subtype.coe_mk]
  ring

/-- 对齐网格中位于第 `i` 个 dyadic block 的每条细子区间，`Path.concat` 的取值仍落在输入
`F i` 所在的任意集合中。-/
private theorem Path.concatSegmentFineInterval_mem
    {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (p : Fin (n + 1) → Y)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (k : ℕ) (hk : 0 < k) (i : Fin n)
    (S : Set Y) (hF : ∀ t, F i t ∈ S)
    (s : Fin (pathConcatSegmentGridLength n k i)) (t : unitInterval) :
    Path.concat p F
        (Set.Icc.convexComb
          (pathConcatSegmentMeshPoint n k hk i s.castSucc)
          (pathConcatSegmentMeshPoint n k hk i s.succ) t) ∈ S := by
  let uLocal := Set.Icc.convexComb
    (unitIntervalMeshPoint (pathConcatSegmentGridLength n k i)
      (pathConcatSegmentGridLength_pos n k hk i) s.castSucc)
    (unitIntervalMeshPoint (pathConcatSegmentGridLength n k i)
      (pathConcatSegmentGridLength_pos n k hk i) s.succ) t
  have hmem := Path.concatDyadicSegment_mem p F i S hF uLocal
  unfold Path.concatDyadicSegment at hmem
  rw [Path.cast_coe] at hmem
  rw [pathConcatSegmentFineInterval_eq_convexComb n k hk i s t]
  exact hmem

/-- 一个 concat segment 覆盖的全部连续细网格子道路，按顺序拼接后同伦于该网格块的整段子道路。-/
theorem Path.concatSegmentMeshSubpaths_homotopic
    {Y : Type*} [TopologicalSpace Y] {a b : Y} (p : Path a b)
    (n k : ℕ) (hk : 0 < k) (i : Fin n) :
    Path.Homotopic
      (Path.concat
        (p ∘ pathConcatSegmentMeshPoint n k hk i)
        (fun s => p.subpath
          (pathConcatSegmentMeshPoint n k hk i s.castSucc)
          (pathConcatSegmentMeshPoint n k hk i s.succ)))
      (p.subpath
        (pathConcatSegmentMeshPoint n k hk i 0)
        (pathConcatSegmentMeshPoint n k hk i
          (Fin.last (pathConcatSegmentGridLength n k i)))) := by
  exact Path.Homotopic.concat_subpath p
    (pathConcatSegmentMeshPoint n k hk i)

/-- 第 `i` 个 concat segment 覆盖的全部细网格子道路拼接，并 transport 回原输入 family 的端点。-/
def Path.concatDyadicGridSegment
    {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (p : Fin (n + 1) → Y)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (k : ℕ) (hk : 0 < k) (i : Fin n) : Path (p i.castSucc) (p i.succ) :=
  let γ := Path.concat p F
  (Path.concat
      (γ ∘ pathConcatSegmentMeshPoint n k hk i)
      (fun s => γ.subpath
        (pathConcatSegmentMeshPoint n k hk i s.castSucc)
        (pathConcatSegmentMeshPoint n k hk i s.succ))).cast
    (by
      change p i.castSucc = γ (pathConcatSegmentMeshPoint n k hk i 0)
      rw [pathConcatSegmentMeshPoint_zero,
      Path.concat_breakpoint_apply p F i.castSucc])
    (by
      change p i.succ = γ (pathConcatSegmentMeshPoint n k hk i
        (Fin.last (pathConcatSegmentGridLength n k i)))
      rw [pathConcatSegmentMeshPoint_last,
      Path.concat_breakpoint_apply p F i.succ])

/-- 一个 dyadic block 中所有细网格子道路的拼接，同伦于该输入 concat segment。-/
theorem Path.concatDyadicGridSegment_homotopic
    {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (p : Fin (n + 1) → Y)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (k : ℕ) (hk : 0 < k) (i : Fin n) :
    (Path.concatDyadicGridSegment p F k hk i).Homotopic (F i) := by
  let γ := Path.concat p F
  have hblock := Path.concatSegmentMeshSubpaths_homotopic γ n k hk i
  have hsource : p i.castSucc = γ (pathConcatSegmentMeshPoint n k hk i 0) := by
    rw [pathConcatSegmentMeshPoint_zero,
      Path.concat_breakpoint_apply p F i.castSucc]
  have htarget : p i.succ = γ
      (pathConcatSegmentMeshPoint n k hk i
        (Fin.last (pathConcatSegmentGridLength n k i))) := by
    rw [pathConcatSegmentMeshPoint_last,
      Path.concat_breakpoint_apply p F i.succ]
  have hcast := hblock.pathCast hsource htarget
  have hright :
      ((γ.subpath
        (pathConcatSegmentMeshPoint n k hk i 0)
        (pathConcatSegmentMeshPoint n k hk i
          (Fin.last (pathConcatSegmentGridLength n k i)))).cast hsource htarget) =
        Path.concatDyadicSegment p F i := by
    apply Path.ext
    funext t
    change γ (Set.Icc.convexComb
      (pathConcatSegmentMeshPoint n k hk i 0)
      (pathConcatSegmentMeshPoint n k hk i
        (Fin.last (pathConcatSegmentGridLength n k i))) t) =
      γ (Set.Icc.convexComb
        (pathConcatBreakpoint n i.castSucc)
        (pathConcatBreakpoint n i.succ) t)
    rw [pathConcatSegmentMeshPoint_zero, pathConcatSegmentMeshPoint_last]
  have hgrid : Path.concatDyadicGridSegment p F k hk i =
      (Path.concat
        (γ ∘ pathConcatSegmentMeshPoint n k hk i)
        (fun s => γ.subpath
          (pathConcatSegmentMeshPoint n k hk i s.castSucc)
          (pathConcatSegmentMeshPoint n k hk i s.succ))).cast hsource htarget := by
    apply Path.ext
    funext t
    rfl
  rw [hgrid]
  exact hcast.trans (by
    rw [hright]
    exact Path.concatDyadicSegment_homotopic p F i)

/-- 一份与 `n` 段 `Path.concat` 的全部 dyadic 断点对齐的方形细分证书。除保存原细分外，
还显式保存正加细因子，避免后续每次从整除证书重新排除零因子。-/
structure PathConcatAlignedSquareSubdivision
    (H : C(unitInterval × unitInterval, X)) (U V : Set X) (n : ℕ) where
  subdivision : BinaryOpenCoverSquareSubdivision H U V
  factor : ℕ
  factor_pos : 0 < factor
  steps_eq : subdivision.steps = pathConcatDyadicScale n * factor

/-- 受约束 Lebesgue 方格细分总能提升为带正加细因子的 concat 对齐证书。-/
theorem exists_pathConcatAlignedSquareSubdivision
    (H : C(unitInterval × unitInterval, X)) {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V)
    (hH : ∀ z, H z ∈ U ∨ H z ∈ V) (n : ℕ) :
    Nonempty (PathConcatAlignedSquareSubdivision H U V n) := by
  rcases exists_binaryOpenCoverSquareSubdivision_concat_multiple H hU hV hH n with
    ⟨D, k, hsteps⟩
  have hk : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    exact (Nat.ne_of_gt D.steps_pos) (by
      simpa only [Nat.mul_zero] using hsteps)
  exact ⟨D, k, hk, hsteps⟩

namespace PathConcatAlignedSquareSubdivision

/-- 对齐证书把每个 concat dyadic 断点给出为原细分中的真实网格索引。-/
def breakpointGridIndex
    {H : C(unitInterval × unitInterval, X)} {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision H U V n) (r : Fin (n + 1)) :
    Fin (A.subdivision.steps + 1) :=
  Fin.cast (congrArg (· + 1) A.steps_eq.symm)
    (pathConcatBreakpointGridIndex n A.factor r)

/-- 对齐证书中的真实网格点严格就是相应 concat dyadic 断点。-/
theorem unitIntervalMeshPoint_breakpointGridIndex
    {H : C(unitInterval × unitInterval, X)} {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision H U V n) (r : Fin (n + 1)) :
    unitIntervalMeshPoint A.subdivision.steps A.subdivision.steps_pos
        (A.breakpointGridIndex r) = pathConcatBreakpoint n r := by
  rcases A with ⟨D, k, hk, hsteps⟩
  rcases D with ⟨steps, hsteps_pos, label, cell_mem⟩
  dsimp at hsteps ⊢
  subst steps
  simpa [breakpointGridIndex] using
    (unitIntervalMeshPoint_pathConcatBreakpointGridIndex n k hk r)

/-- 对齐证书中第 `i` 个 concat segment 的第 `s` 条真实细网格边。-/
def segmentGridEdgeIndex
    {H : C(unitInterval × unitInterval, X)} {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision H U V n) (i : Fin n)
    (s : Fin (pathConcatSegmentGridLength n A.factor i)) :
    Fin A.subdivision.steps :=
  Fin.cast A.steps_eq.symm
    (pathConcatSegmentGridEdgeIndex n A.factor i s)

/-- The aligned subdivision's block-local edge indices flatten to the complete
global row index list.-/
theorem segmentGridEdgeIndices_flatten
    {H : C(unitInterval × unitInterval, X)} {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision H U V n) (hn : 0 < n) :
    (List.ofFn fun i : Fin n =>
      List.ofFn fun s : Fin (pathConcatSegmentGridLength n A.factor i) =>
        A.segmentGridEdgeIndex i s).flatten =
      List.ofFn (fun r : Fin A.subdivision.steps => r) := by
  rcases A with ⟨D, k, hk, hsteps⟩
  rcases D with ⟨steps, hsteps_pos, label, cell_mem⟩
  dsimp at hsteps ⊢
  subst steps
  simpa [segmentGridEdgeIndex] using
    pathConcatSegmentGridEdgeIndices_flatten n k hn

/-- The first fine edge of the first concat block is the first global grid
edge.-/
theorem segmentGridEdgeIndex_first
    {H : C(unitInterval × unitInterval, X)} {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision H U V n) (hn : 0 < n) :
    A.segmentGridEdgeIndex ⟨0, hn⟩
        ⟨0, pathConcatSegmentGridLength_pos n A.factor A.factor_pos ⟨0, hn⟩⟩ =
      ⟨0, A.subdivision.steps_pos⟩ := by
  apply Fin.ext
  unfold segmentGridEdgeIndex pathConcatSegmentGridEdgeIndex
  simp

/-- The last fine edge of the last concat block is the last global grid edge.-/
theorem segmentGridEdgeIndex_last
    {H : C(unitInterval × unitInterval, X)} {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision H U V n) (hn : 0 < n) :
    let i : Fin n := ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩
    let L := pathConcatSegmentGridLength n A.factor i
    let hL := pathConcatSegmentGridLength_pos n A.factor A.factor_pos i
    A.segmentGridEdgeIndex i (finLastOfPos L hL) =
      ⟨A.subdivision.steps - 1,
        Nat.sub_lt A.subdivision.steps_pos Nat.zero_lt_one⟩ := by
  dsimp only
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  apply Fin.ext
  unfold segmentGridEdgeIndex pathConcatSegmentGridEdgeIndex finLastOfPos
  simp only [Fin.val_cast]
  have hi : (⟨m + 1 - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ : Fin (m + 1)).succ =
      Fin.last (m + 1) := by
    apply Fin.ext
    simp
  unfold pathConcatSegmentGridLength
  rw [hi, pathConcatBreakpointNumerator_last]
  have ha := pathConcatBreakpointNumerator_strictMonoAdjacent (m + 1)
    (⟨m + 1 - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ : Fin (m + 1))
  rw [hi, pathConcatBreakpointNumerator_last] at ha
  have hsum : pathConcatBreakpointNumerator (m + 1)
        (⟨m + 1 - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ : Fin (m + 1)).castSucc *
          A.factor +
        (pathConcatDyadicScale (m + 1) -
          pathConcatBreakpointNumerator (m + 1)
            (⟨m + 1 - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ : Fin (m + 1)).castSucc) *
          A.factor =
      pathConcatDyadicScale (m + 1) * A.factor := by
    rw [← Nat.add_mul, Nat.add_sub_of_le (Nat.le_of_lt ha)]
  have hpositive : 0 <
      (pathConcatDyadicScale (m + 1) -
        pathConcatBreakpointNumerator (m + 1)
          (⟨m + 1 - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ : Fin (m + 1)).castSucc) *
        A.factor :=
    Nat.mul_pos (Nat.sub_pos_of_lt ha) A.factor_pos
  rw [A.steps_eq, ← hsum]
  exact (Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt hpositive)) _).symm

/-- 同一 concat segment 中相邻的局部细边，对应原方形细分中的相邻全局行。-/
theorem segmentGridEdgeIndex_succ_eq_castSucc
    {H : C(unitInterval × unitInterval, X)} {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision H U V n) (i : Fin n)
    (s t : Fin (pathConcatSegmentGridLength n A.factor i))
    (hshared : s.succ = t.castSucc) :
    (A.segmentGridEdgeIndex i s).succ =
      (A.segmentGridEdgeIndex i t).castSucc := by
  apply Fin.ext
  simp only [Fin.val_succ, Fin.val_castSucc]
  unfold segmentGridEdgeIndex pathConcatSegmentGridEdgeIndex
  simp only [Fin.val_cast]
  have hs := congrArg Fin.val hshared
  simp only [Fin.val_succ, Fin.val_castSucc] at hs
  omega

/-- 上述相邻索引桥在同伦方形最左边界给出同一个真实网格顶点。-/
theorem leftBoundary_segmentGridEdgeIndex_shared_vertex
    {H : C(unitInterval × unitInterval, X)} {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision H U V n) (i : Fin n)
    (s t : Fin (pathConcatSegmentGridLength n A.factor i))
    (hshared : s.succ = t.castSucc) :
    squareGridVertex H A.subdivision.steps A.subdivision.steps_pos 0
        (A.segmentGridEdgeIndex i s).succ =
      squareGridVertex H A.subdivision.steps A.subdivision.steps_pos 0
        (A.segmentGridEdgeIndex i t).castSucc := by
  rw [A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared]

@[simp] theorem unitIntervalMeshPoint_segmentGridEdgeIndex_castSucc
    {H : C(unitInterval × unitInterval, X)} {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision H U V n) (i : Fin n)
    (s : Fin (pathConcatSegmentGridLength n A.factor i)) :
    unitIntervalMeshPoint A.subdivision.steps A.subdivision.steps_pos
        (A.segmentGridEdgeIndex i s).castSucc =
      pathConcatSegmentMeshPoint n A.factor A.factor_pos i s.castSucc := by
  rcases A with ⟨D, k, hk, hsteps⟩
  rcases D with ⟨steps, hsteps_pos, label, cell_mem⟩
  dsimp at hsteps ⊢
  subst steps
  simp [segmentGridEdgeIndex, pathConcatSegmentMeshPoint]

@[simp] theorem unitIntervalMeshPoint_segmentGridEdgeIndex_succ
    {H : C(unitInterval × unitInterval, X)} {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision H U V n) (i : Fin n)
    (s : Fin (pathConcatSegmentGridLength n A.factor i)) :
    unitIntervalMeshPoint A.subdivision.steps A.subdivision.steps_pos
        (A.segmentGridEdgeIndex i s).succ =
      pathConcatSegmentMeshPoint n A.factor A.factor_pos i s.succ := by
  rcases A with ⟨D, k, hk, hsteps⟩
  rcases D with ⟨steps, hsteps_pos, label, cell_mem⟩
  dsimp at hsteps ⊢
  subst steps
  simp [segmentGridEdgeIndex, pathConcatSegmentMeshPoint]

end PathConcatAlignedSquareSubdivision

/-- 对齐同伦方形中一个 concat block 的每条真实左边界竖边，逐点就是输入环路在对应细网格
子区间上的限制。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundarySegmentGridEdge_apply
    {x₀ x₁ : X} {p q : Path x₀ x₁} (Fhom : Path.Homotopy p q)
    {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V n)
    (i : Fin n) (s : Fin (pathConcatSegmentGridLength n A.factor i))
    (t : unitInterval) :
    squareGridVerticalEdge (pathHomotopySquare Fhom)
        A.subdivision.steps A.subdivision.steps_pos 0
        (A.segmentGridEdgeIndex i s) t =
      p (Set.Icc.convexComb
        (pathConcatSegmentMeshPoint n A.factor A.factor_pos i s.castSucc)
        (pathConcatSegmentMeshPoint n A.factor A.factor_pos i s.succ) t) := by
  rw [squareGridVerticalEdge_pathHomotopySquare_left]
  rw [A.unitIntervalMeshPoint_segmentGridEdgeIndex_castSucc,
    A.unitIntervalMeshPoint_segmentGridEdgeIndex_succ]

/-- 对 kernel 字母 concat loop 的对齐同伦方形，每个 dyadic block 内的真实最左网格边逐点位于该
输入字母指定的覆盖成员中，无论方格细分给该行选择了哪个标签。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundarySegmentGridEdge_mem_letterPiece
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i))
    (t : unitInterval) :
    squareGridVerticalEdge (pathHomotopySquare Fhom)
        A.subdivision.steps A.subdivision.steps_pos 0
        (A.segmentGridEdgeIndex i s) t ∈
      binaryOpenCoverPiece U V (letters.reverse.get i).1 := by
  rw [A.leftBoundarySegmentGridEdge_apply Fhom i s t]
  unfold binaryVanKampenLetterConcatLoop
  exact Path.concatSegmentFineInterval_mem
    (fun _ : Fin (letters.reverse.length + 1) => x₀)
    (fun j : Fin letters.reverse.length =>
      (letters.reverse.get j).ambientLoop hxU hxV)
    A.factor A.factor_pos i
    (binaryOpenCoverPiece U V (letters.reverse.get i).1)
    (binaryVanKampenLetterConcatLoop_segment_mem hxU hxV letters i) s t

/-- 同一结论按 VK2 `Path.BinaryOpenCoverSubdivision` 的标准 `Path.subpath` 表示：block 内对应全局
行索引的 segment 除了属于 cell 标签成员，也属于输入字母标签成员。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundarySubdivision_subpath_mem_letterPiece
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i))
    (t : unitInterval) :
    (binaryVanKampenLetterConcatLoop hxU hxV letters).subpath
        (unitIntervalMeshPoint A.subdivision.steps A.subdivision.steps_pos
          (A.segmentGridEdgeIndex i s).castSucc)
        (unitIntervalMeshPoint A.subdivision.steps A.subdivision.steps_pos
          (A.segmentGridEdgeIndex i s).succ) t ∈
      binaryOpenCoverPiece U V (letters.reverse.get i).1 := by
  unfold Path.subpath
  rw [A.unitIntervalMeshPoint_segmentGridEdgeIndex_castSucc,
    A.unitIntervalMeshPoint_segmentGridEdgeIndex_succ]
  unfold binaryVanKampenLetterConcatLoop
  exact Path.concatSegmentFineInterval_mem
    (fun _ : Fin (letters.reverse.length + 1) => x₀)
    (fun j : Fin letters.reverse.length =>
      (letters.reverse.get j).ambientLoop hxU hxV)
    A.factor A.factor_pos i
    (binaryOpenCoverPiece U V (letters.reverse.get i).1)
    (binaryVanKampenLetterConcatLoop_segment_mem hxU hxV letters i) s t

end SandronesLibrary.Topology
