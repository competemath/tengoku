/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PathPolygonalApproximation
import Tengoku.Seed.Analysis.Calculus.ContDiff.Operations
import Tengoku.Seed.Analysis.Calculus.AddTorsor.AffineMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 分段 C1 道路

本文件在 Mathlib `Path` 上定义归纳命题 `Path.PiecewiseC1`：整体 C1 道路属于该类，且该类对
`Path.trans` 和端点 `Path.cast` 闭合。这个承载保留道路的实际参数化，不另造道路类型或统一断点
约定。

当前条目：

* `topology.homotopy.piecewise-c1-path`。

本文件证明常道路、线段、反向和有限拼接的闭合性，并把 R3a 的开集内折线替换升级为分段 C1
替换。它不定义曲线积分，也不宣称任意连续同伦可以正则化为分片 C2 方形。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 道路是分段 C1 的，如果它整体 C1，或由两条分段 C1 道路拼接而成，或由一条分段 C1 道路作
端点类型转换而成。

> **Entry**: topology.homotopy.piecewise-c1-path-/
inductive Path.PiecewiseC1 : {x y : E} → Path x y → Prop
  | of_contDiffOn {x y : E} (gamma : Path x y)
      (regular : ContDiffOn ℝ 1 gamma.extend (Icc 0 1)) : Path.PiecewiseC1 gamma
  | trans {x y z : E} (gamma : Path x y) (delta : Path y z)
      (hgamma : Path.PiecewiseC1 gamma) (hdelta : Path.PiecewiseC1 delta) :
      Path.PiecewiseC1 (gamma.trans delta)
  | cast {x y x' y' : E} (gamma : Path x y) (hgamma : Path.PiecewiseC1 gamma)
      (hx : x' = x) (hy : y' = y) : Path.PiecewiseC1 (gamma.cast hx hy)

/-- 整体 C1 道路是分段 C1 道路。
@isnad1 id=piecewis.1h4v.s7.87fb04f12453 from=translated src=- shape=797911ea vocab=36be452a
-/
theorem Path.piecewiseC1_of_contDiffOn {x y : E} (gamma : Path x y)
    (regular : ContDiffOn ℝ 1 gamma.extend (Icc 0 1)) : Path.PiecewiseC1 gamma :=
  .of_contDiffOn gamma regular

/-- 常道路是分段 C1 道路。
@isnad1 id=piecewis.0h2v.s5.7f540463f689 from=translated src=- shape=f9399930 vocab=b8793be1
-/
theorem Path.piecewiseC1_refl (x : E) : Path.PiecewiseC1 (Path.refl x) := by
  apply Path.piecewiseC1_of_contDiffOn
  apply contDiffOn_const

/-- 赋范实线性空间中的线段是分段 C1 道路。
@isnad1 id=piecewis.0h3v.s5.fc612929efa5 from=translated src=- shape=57aa64b1 vocab=6e93ef7e
-/
theorem Path.piecewiseC1_segment (a b : E) :
    Path.PiecewiseC1 (Path.segment a b) := by
  apply Path.piecewiseC1_of_contDiffOn
  apply (AffineMap.contDiff_lineMap a b).contDiffOn.congr
  intro t ht
  rw [Path.extend_apply _ ht]
  rfl

/-- 有限条整体 C1 道路的规范拼接是分段 C1 道路。
@isnad1 id=piecewis.1h4v.s7.8c5b4afdf3de from=translated src=- shape=ee9bd01d vocab=fecf08d4
-/
theorem Path.piecewiseC1_concat
    {n : ℕ} (vertices : Fin (n + 1) → E)
    (pieces : (i : Fin n) → Path (vertices i.castSucc) (vertices i.succ))
    (regular : ∀ i, ContDiffOn ℝ 1 (pieces i).extend (Icc 0 1)) :
    Path.PiecewiseC1 (Path.concat vertices pieces) := by
  induction n with
  | zero =>
      rw [Path.concat_zero]
      exact Path.piecewiseC1_refl (vertices 0)
  | succ n ih =>
      rw [Path.concat_succ]
      exact .trans _ _
        (ih (vertices ∘ Fin.castSucc) (fun i => pieces i.castSucc)
          (fun i => regular i.castSucc))
        (.of_contDiffOn _ (regular (Fin.last n)))

/-- 反向保持道路的分段 C1 性。
@isnad1 id=piecewis.1h4v.s5.8d155add26eb from=translated src=- shape=a1e398fd vocab=2c948752
-/
theorem Path.PiecewiseC1.symm
    {x y : E} {gamma : Path x y} (hgamma : Path.PiecewiseC1 gamma) :
    Path.PiecewiseC1 gamma.symm := by
  induction hgamma with
  | of_contDiffOn gamma regular =>
      apply Path.piecewiseC1_of_contDiffOn
      rw [Path.extend_symm]
      exact regular.comp
        ((contDiff_const.sub contDiff_id).contDiffOn)
        (fun t ht => by
          constructor <;> linarith [ht.1, ht.2])
  | trans gamma delta _ _ ihgamma ihdelta =>
      rw [Path.trans_symm]
      exact .trans _ _ ihdelta ihgamma
  | cast gamma _ hx hy ih =>
      simpa using Path.PiecewiseC1.cast gamma.symm ih hy hx

/-- R3a 的规范网格折线路径是分段 C1 道路。
@isnad1 id=piecewis.1h5v.s5.df29a3b0ae53 from=translated src=- shape=b866015c vocab=678ea843
-/
theorem Path.meshPolygonal_piecewiseC1
    {x y : E} (p : Path x y) (N : ℕ) (hN : 0 < N) :
    Path.PiecewiseC1 (Path.meshPolygonal p N hN) := by
  unfold Path.meshPolygonal
  apply Path.PiecewiseC1.cast
  apply Path.piecewiseC1_concat
  intro i
  apply (AffineMap.contDiff_lineMap
    (p (unitIntervalMeshPoint N hN i.castSucc))
    (p (unitIntervalMeshPoint N hN i.succ))).contDiffOn.congr
  intro t ht
  rw [Path.extend_apply _ ht]
  rfl

/-- 任意落在开集内的道路，都能在该开集内相对端点同伦到一条分段 C1 道路；结论保留替换道路
及整个同伦的像集控制。
@isnad1 id=ex.2h5v.s9.f23197a649db from=translated src=- shape=eee9357b vocab=b18ed88b
-/
theorem Path.exists_piecewiseC1_range_subset_open_and_homotopyWithin
    {x y : E} (p : Path x y) {U : Set E}
    (hU : IsOpen U) (hpU : ∀ t, p t ∈ U) :
    ∃ q : Path x y,
      Set.range q ⊆ U ∧ Path.PiecewiseC1 q ∧
        ∃ K : p.Homotopy q, ∀ t s : unitInterval, K (t, s) ∈ U := by
  obtain ⟨N, hN, hrange, K, hK⟩ :=
    Path.exists_meshPolygonal_range_subset_open_and_homotopyWithin p hU hpU
  exact ⟨Path.meshPolygonal p N hN, hrange,
    Path.meshPolygonal_piecewiseC1 p N hN, K, hK⟩

end SandronesLibrary.Topology
