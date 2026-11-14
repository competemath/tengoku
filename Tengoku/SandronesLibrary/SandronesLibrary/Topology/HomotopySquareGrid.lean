/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PathHomotopyStandard
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.UnitIntervalMesh

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 道路同伦方形与一致网格边

本文件把端点相对道路同伦表示成连续参数方形，并在单位方形的一致网格上定义顶点、小格参数点和
统一定向的横竖边。它是方格细分、van Kampen 单格关系与连续同伦下道路积分不变性的共享基础层。

当前条目：

* `topology.homotopy.homotopy-square-grid`。

本文件只固定坐标、参数化和边界计算规则；不包含覆盖标签、基本群、Pushout、道路正则性或积分。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 把 Mathlib 的端点相对道路同伦按其真实坐标次序看作连续方形：第一坐标是同伦参数，
第二坐标是道路参数。

> **Entry**: topology.homotopy.homotopy-square-grid-/
def pathHomotopySquare {x₀ x₁ : X} {p q : Path x₀ x₁}
    (F : Path.Homotopy p q) : C(unitInterval × unitInterval, X) :=
  F.toHomotopy.toContinuousMap

@[simp] theorem pathHomotopySquare_zero_left
    {x₀ x₁ : X} {p q : Path x₀ x₁} (F : Path.Homotopy p q)
    (t : unitInterval) :
    pathHomotopySquare F (0, t) = p t := by
  simp [pathHomotopySquare]

@[simp] theorem pathHomotopySquare_one_left
    {x₀ x₁ : X} {p q : Path x₀ x₁} (F : Path.Homotopy p q)
    (t : unitInterval) :
    pathHomotopySquare F (1, t) = q t := by
  simp [pathHomotopySquare]

@[simp] theorem pathHomotopySquare_bottom
    {x₀ x₁ : X} {p q : Path x₀ x₁} (F : Path.Homotopy p q)
    (s : unitInterval) :
    pathHomotopySquare F (s, 0) = x₀ := by
  simp [pathHomotopySquare]

@[simp] theorem pathHomotopySquare_top
    {x₀ x₁ : X} {p q : Path x₀ x₁} (F : Path.Homotopy p q)
    (s : unitInterval) :
    pathHomotopySquare F (s, 1) = x₁ := by
  simp [pathHomotopySquare]

/-- 连续方形在一致网格的全局顶点值。-/
def squareGridVertex (H : C(unitInterval × unitInterval, X))
    (N : ℕ) (hN : 0 < N) (i j : Fin (N + 1)) : X :=
  H (unitIntervalMeshPoint N hN i, unitIntervalMeshPoint N hN j)

/-- 第 `(i,j)` 个一致方格中的点；两个局部参数分别沿横、纵方向线性变化。-/
def unitSquareCellPoint (N : ℕ) (hN : 0 < N) (i j : Fin N)
    (u v : unitInterval) : unitInterval × unitInterval :=
  (Set.Icc.convexComb (unitIntervalMeshPoint N hN i.castSucc)
      (unitIntervalMeshPoint N hN i.succ) u,
    Set.Icc.convexComb (unitIntervalMeshPoint N hN j.castSucc)
      (unitIntervalMeshPoint N hN j.succ) v)

/-- 全网格统一取从左到右方向的横边。-/
def squareGridHorizontalEdge (H : C(unitInterval × unitInterval, X))
    (N : ℕ) (hN : 0 < N) (i : Fin N) (j : Fin (N + 1)) :
    Path (squareGridVertex H N hN i.castSucc j)
      (squareGridVertex H N hN i.succ j) where
  toFun u := H
    (Set.Icc.convexComb (unitIntervalMeshPoint N hN i.castSucc)
      (unitIntervalMeshPoint N hN i.succ) u,
      unitIntervalMeshPoint N hN j)
  continuous_toFun := by fun_prop
  source' := by simp [squareGridVertex]
  target' := by simp [squareGridVertex]

/-- 全网格统一取从下到上方向的竖边。-/
def squareGridVerticalEdge (H : C(unitInterval × unitInterval, X))
    (N : ℕ) (hN : 0 < N) (i : Fin (N + 1)) (j : Fin N) :
    Path (squareGridVertex H N hN i j.castSucc)
      (squareGridVertex H N hN i j.succ) where
  toFun v := H
    (unitIntervalMeshPoint N hN i,
      Set.Icc.convexComb (unitIntervalMeshPoint N hN j.castSucc)
        (unitIntervalMeshPoint N hN j.succ) v)
  continuous_toFun := by fun_prop
  source' := by simp [squareGridVertex]
  target' := by simp [squareGridVertex]

/-- 道路同伦方形最左列的竖边正是原道路的相应网格子段。-/
theorem squareGridVerticalEdge_pathHomotopySquare_left
    {x₀ x₁ : X} {p q : Path x₀ x₁} (F : Path.Homotopy p q)
    (N : ℕ) (hN : 0 < N) (j : Fin N) (t : unitInterval) :
    squareGridVerticalEdge (pathHomotopySquare F) N hN 0 j t =
      p (Set.Icc.convexComb (unitIntervalMeshPoint N hN j.castSucc)
        (unitIntervalMeshPoint N hN j.succ) t) := by
  simp [squareGridVerticalEdge, pathHomotopySquare]
  rfl

/-- 道路同伦方形最右列的竖边正是终道路的相应网格子段。-/
theorem squareGridVerticalEdge_pathHomotopySquare_right
    {x₀ x₁ : X} {p q : Path x₀ x₁} (F : Path.Homotopy p q)
    (N : ℕ) (hN : 0 < N) (j : Fin N) (t : unitInterval) :
    squareGridVerticalEdge (pathHomotopySquare F) N hN (Fin.last N) j t =
      q (Set.Icc.convexComb (unitIntervalMeshPoint N hN j.castSucc)
        (unitIntervalMeshPoint N hN j.succ) t) := by
  simp [squareGridVerticalEdge, pathHomotopySquare]
  rfl

/-- 道路同伦方形最下行的每条横边都是起点处常值道路。-/
theorem squareGridHorizontalEdge_pathHomotopySquare_bottom
    {x₀ x₁ : X} {p q : Path x₀ x₁} (F : Path.Homotopy p q)
    (N : ℕ) (hN : 0 < N) (i : Fin N) (t : unitInterval) :
    squareGridHorizontalEdge (pathHomotopySquare F) N hN i 0 t = x₀ := by
  simp [squareGridHorizontalEdge, pathHomotopySquare]
  rfl

/-- 道路同伦方形最上行的每条横边都是终点处常值道路。-/
theorem squareGridHorizontalEdge_pathHomotopySquare_top
    {x₀ x₁ : X} {p q : Path x₀ x₁} (F : Path.Homotopy p q)
    (N : ℕ) (hN : 0 < N) (i : Fin N) (t : unitInterval) :
    squareGridHorizontalEdge (pathHomotopySquare F) N hN i (Fin.last N) t = x₁ := by
  simp [squareGridHorizontalEdge, pathHomotopySquare]
  rfl

end SandronesLibrary.Topology
