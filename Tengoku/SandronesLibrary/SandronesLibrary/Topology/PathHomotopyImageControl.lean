/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Topology.Subpath
import Tengoku.Seed.Topology.Homotopy.Affine
import Tengoku.Seed.Analysis.Normed.Module.Basic
import Tengoku.Seed.Analysis.Normed.Module.Convex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 道路同伦的像集控制与有限拼接

本文件为道路同伦补充逐点像集不变量：证明水平、竖直复合、重参数化、子道路结合以及有限依赖拼接
不会离开指定集合。通用复合与有限拼接部分只要求拓扑空间；仿射同伦及凸集、球控制部分才要求实
赋范线性空间。公开同伦承载仍是 Mathlib `Path.Homotopy`，本库不另造同伦结构。

当前条目：

* `topology.homotopy.path-homotopy-image-control`。
-/

open Set
open scoped unitInterval Convex

noncomputable section

namespace SandronesLibrary.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X : Type*} [TopologicalSpace X]

/-- 两条同端点道路之间的逐点仿射同伦，使用标准端点相对 `Path.Homotopy` 承载。

> **Entry**: topology.homotopy.path-homotopy-image-control-/
def Path.affineHomotopy {x y : E} (p q : Path x y) : p.Homotopy q where
  toHomotopy := ContinuousMap.Homotopy.affine p.toContinuousMap q.toContinuousMap
  prop' := by
    intro t z hz
    rcases hz with rfl | rfl
    · simp
    · simp

@[simp] theorem Path.affineHomotopy_apply {x y : E} (p q : Path x y)
    (t s : unitInterval) :
    SandronesLibrary.Topology.Path.affineHomotopy p q (t, s) =
      Path.segment (p s) (q s) t :=
  rfl

/-- 若凸集逐点包含两条道路，则端点相对仿射同伦中的每条中间道路也位于该凸集内。-/
theorem Path.affineHomotopy_mapsTo_convex {x y : E} (p q : Path x y)
    {S : Set E} (hS : Convex ℝ S) (hp : ∀ s, p s ∈ S) (hq : ∀ s, q s ∈ S) :
    ∀ t s : unitInterval,
      SandronesLibrary.Topology.Path.affineHomotopy p q (t, s) ∈ S := by
  intro t s
  exact hS.lineMap_mem (hp s) (hq s) t.2

/-- 若两条道路都位于同一开球内，则它们之间的仿射同伦全部位于该球内。-/
theorem Path.affineHomotopy_mapsTo_ball {x y : E} (p q : Path x y)
    (c : E) (r : ℝ) (hp : ∀ s, p s ∈ Metric.ball c r)
    (hq : ∀ s, q s ∈ Metric.ball c r) :
    ∀ t s : unitInterval,
      SandronesLibrary.Topology.Path.affineHomotopy p q (t, s) ∈ Metric.ball c r :=
  SandronesLibrary.Topology.Path.affineHomotopy_mapsTo_convex
    p q (convex_ball c r) hp hq

/- 若两个端点相对道路同伦都不离开集合 `S`，则它们的水平复合也不离开 `S`。 -/
theorem Path.Homotopy.hcomp_mapsTo
    {x₀ x₁ x₂ : X}
    {p₀ q₀ : Path x₀ x₁} {p₁ q₁ : Path x₁ x₂}
    (F : p₀.Homotopy q₀) (G : p₁.Homotopy q₁) {S : Set X}
    (hF : ∀ t s : unitInterval, F (t, s) ∈ S)
    (hG : ∀ t s : unitInterval, G (t, s) ∈ S) :
    ∀ t s : unitInterval, F.hcomp G (t, s) ∈ S := by
  intro t s
  rw [Path.Homotopy.hcomp_apply]
  split_ifs
  · apply hF
  · apply hG

/- 道路同伦的竖直复合保持任意给定的像集界。 -/
theorem Path.Homotopy.trans_mapsTo
    {x y : X} {p q r : Path x y}
    (F : p.Homotopy q) (G : q.Homotopy r) {S : Set X}
    (hF : ∀ t s : unitInterval, F (t, s) ∈ S)
    (hG : ∀ t s : unitInterval, G (t, s) ∈ S) :
    ∀ t s : unitInterval, F.trans G (t, s) ∈ S := by
  intro t s
  rw [Path.Homotopy.trans_apply]
  split_ifs
  · apply hF
  · apply hG

/- Mathlib 的道路重参数化同伦的所有取值都来自原道路。 -/
theorem Path.Homotopy.reparam_mapsTo
    {x y : X} (p : Path x y) (f : unitInterval → unitInterval)
    (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1)
    {S : Set X} (hp : ∀ s, p s ∈ S) :
    ∀ t s : unitInterval,
      Path.Homotopy.reparam p f hf hf₀ hf₁ (t, s) ∈ S := by
  intro t s
  exact hp _

/- 删去末尾常值道路只是重参数化，因而不会离开原道路的像。 -/
theorem Path.Homotopy.transRefl_mapsTo
    {x y : X} (p : Path x y) {S : Set X} (hp : ∀ s, p s ∈ S) :
    ∀ t s : unitInterval, Path.Homotopy.transRefl p (t, s) ∈ S := by
  intro t s
  unfold Path.Homotopy.transRefl
  rw [Path.Homotopy.symm_apply]
  rw [Path.Homotopy.cast_apply]
  apply Path.Homotopy.reparam_mapsTo
  exact hp

/- 两条相邻子道路的结合同伦只在不同区间参数处计算原道路。 -/
theorem Path.Homotopy.subpathTransSubpathRefl_mapsTo
    {x y : X} (p : Path x y) (t₀ t₁ t₂ : unitInterval)
    {S : Set X} (hp : ∀ s, p s ∈ S) :
    ∀ t s : unitInterval,
      Path.Homotopy.subpathTransSubpathRefl p t₀ t₁ t₂ (t, s) ∈ S := by
  intro t s
  unfold Path.Homotopy.subpathTransSubpathRefl
  change ((p.subpath t₀ (Set.Icc.convexComb t₁ t₂ t)).trans
    (p.subpath (Set.Icc.convexComb t₁ t₂ t) t₂)) s ∈ S
  rw [Path.trans_apply]
  split_ifs
  · apply hp
  · apply hp

/- 删去多余的末尾常值子道路保持同一像集界，因此公开的 `subpathTransSubpath` 同伦始终位于 `p` 的像上。 -/
theorem Path.Homotopy.subpathTransSubpath_mapsTo
    {x y : X} (p : Path x y) (t₀ t₁ t₂ : unitInterval)
    {S : Set X} (hp : ∀ s, p s ∈ S) :
    ∀ t s : unitInterval,
      Path.Homotopy.subpathTransSubpath p t₀ t₁ t₂ (t, s) ∈ S := by
  intro t s
  unfold Path.Homotopy.subpathTransSubpath
  apply Path.Homotopy.trans_mapsTo
    (Path.Homotopy.subpathTransSubpathRefl p t₀ t₁ t₂)
    (Path.Homotopy.transRefl (p.subpath t₀ t₂))
  · exact Path.Homotopy.subpathTransSubpathRefl_mapsTo p t₀ t₁ t₂ hp
  · exact Path.Homotopy.transRefl_mapsTo (p.subpath t₀ t₂) (fun _ ↦ hp _)

/- 道路上的常值同伦保持任何包含该道路像的集合。 -/
theorem Path.Homotopy.refl_mapsTo
    {x y : X} (p : Path x y) {S : Set X} (hp : ∀ s, p s ∈ S) :
    ∀ t s : unitInterval, Path.Homotopy.refl p (t, s) ∈ S := by
  intro t s
  exact hp s

/- 在 Mathlib 的有限子道路拼接上附加“每个中间点仍位于原道路像上”的不变量。 -/
def Path.Homotopy.concatSubpathWithMapsTo
    {x y : X} {n : ℕ} (p : Path x y)
    (mesh : Fin (n + 1) → unitInterval) {S : Set X}
    (hp : ∀ s, p s ∈ S) :
    {K : (Path.concat (p ∘ mesh)
          (fun i ↦ p.subpath (mesh i.castSucc) (mesh i.succ))).Homotopy
        (p.subpath (mesh 0) (mesh (Fin.last n))) //
      ∀ t s : unitInterval, K (t, s) ∈ S} := by
  induction n with
  | zero =>
      let K₀ := Path.Homotopy.refl (Path.refl (p (mesh 0)))
      let K := K₀.cast
        (Path.concat_zero (p ∘ mesh)
          (fun i ↦ p.subpath (mesh i.castSucc) (mesh i.succ))).symm
        (Path.subpath_self p (mesh 0)).symm
      refine ⟨K, ?_⟩
      intro t s
      rw [Path.Homotopy.cast_apply]
      exact hp (mesh 0)
  | succ n ih =>
      let previous := ih (mesh ∘ Fin.castSucc)
      let lastPiece := p.subpath
        (mesh (Fin.last n).castSucc) (mesh (Fin.last n).succ)
      let joined := previous.1.hcomp (Path.Homotopy.refl lastPiece)
      let reassoc := Path.Homotopy.subpathTransSubpath p
        (mesh 0) (mesh (Fin.last n).castSucc) (mesh (Fin.last n).succ)
      let raw := joined.trans reassoc
      let K := raw.cast
        (Path.concat_succ (p ∘ mesh)
          (fun i ↦ p.subpath (mesh i.castSucc) (mesh i.succ))).symm
        rfl
      refine ⟨K, ?_⟩
      intro t s
      have hprevious := previous.2
      have hlast := Path.Homotopy.refl_mapsTo lastPiece (fun _ ↦ hp _)
      have hjoined := Path.Homotopy.hcomp_mapsTo
        previous.1 (Path.Homotopy.refl lastPiece) hprevious hlast
      have hreassoc := Path.Homotopy.subpathTransSubpath_mapsTo p
        (mesh 0) (mesh (Fin.last n).castSucc) (mesh (Fin.last n).succ) hp
      have hraw := Path.Homotopy.trans_mapsTo joined reassoc hjoined hreassoc
      have hK : K (t, s) = raw (t, s) := by
        unfold K
        exact Path.Homotopy.cast_apply _ _ _ _
      rw [hK]
      exact hraw t s

/- 有限水平拼接及其像集证书。它对应 Mathlib `Path.Homotopy.concat`，但会让集合成员不变量
穿过依赖道路类型引入的端点转换。 -/
def Path.Homotopy.concatWithMapsTo
    {n : ℕ} (vertices : Fin (n + 1) → X)
    (P Q : (i : Fin n) → Path (vertices i.castSucc) (vertices i.succ))
    (H : (i : Fin n) → (P i).Homotopy (Q i)) {S : Set X}
    (hvertices : ∀ i, vertices i ∈ S)
    (hH : ∀ i t s, H i (t, s) ∈ S) :
    {K : (Path.concat vertices P).Homotopy (Path.concat vertices Q) //
      ∀ t s : unitInterval, K (t, s) ∈ S} := by
  induction n with
  | zero =>
      let K₀ := Path.Homotopy.refl (Path.refl (vertices 0))
      let K := K₀.cast
        (Path.concat_zero vertices P).symm
        (Path.concat_zero vertices Q).symm
      refine ⟨K, ?_⟩
      intro t s
      rw [Path.Homotopy.cast_apply]
      exact hvertices 0
  | succ n ih =>
      let previous := ih
        (vertices ∘ Fin.castSucc)
        (fun i ↦ P i.castSucc) (fun i ↦ Q i.castSucc)
        (fun i ↦ H i.castSucc)
        (fun i ↦ hvertices i.castSucc)
        (fun i ↦ hH i.castSucc)
      let raw := previous.1.hcomp (H (Fin.last n))
      let K := raw.cast
        (Path.concat_succ vertices P).symm
        (Path.concat_succ vertices Q).symm
      refine ⟨K, ?_⟩
      intro t s
      have hK : K (t, s) = raw (t, s) := by
        unfold K
        exact Path.Homotopy.cast_apply _ _ _ _
      rw [hK]
      exact Path.Homotopy.hcomp_mapsTo previous.1 (H (Fin.last n))
        previous.2 (hH (Fin.last n)) t s

/- 若所有顶点和组成道路都位于 `S`，则有限拼接的整个像也位于 `S`。Mathlib 已提供二元的
`Path.trans_range`；本定理是它对有限 `Path.concat` 的对应版本。 -/
set_option backward.isDefEq.respectTransparency false in
theorem Path.concat_range_subset
    {n : ℕ} (vertices : Fin (n + 1) → X)
    (pieces : (i : Fin n) → Path (vertices i.castSucc) (vertices i.succ))
    {S : Set X} (hvertices : ∀ i, vertices i ∈ S)
    (hpieces : ∀ i, Set.range (pieces i) ⊆ S) :
    Set.range (Path.concat vertices pieces) ⊆ S := by
  induction n with
  | zero =>
      simpa using hvertices 0
  | succ n ih =>
      rw [Path.concat_succ]
      have hu := Set.union_subset
        (ih (vertices ∘ Fin.castSucc) (fun i ↦ pieces i.castSucc)
          (fun i ↦ hvertices i.castSucc) (fun i ↦ hpieces i.castSucc))
        (hpieces (Fin.last n))
      simpa only [Path.trans_range] using hu

end SandronesLibrary.Topology
