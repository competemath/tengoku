/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Tengoku.Seed.Topology.Subpath

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 道路段的基点修正环路

本文件用从公共基点到道路段两端的连接道路，把该道路段闭合为基点环路，并证明相邻修正环路及其
有限乘积的望远镜公式。这些构造只依赖道路、有限拼接和基本群，不属于 van Kampen 专用理论。

当前条目：

* `topology.fundamental-group.path-corrected-loop`。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

namespace Path

/-- 用从基点到道路段两端的连接道路，把该道路段闭合为基点环路。

> **Entry**: topology.fundamental-group.path-corrected-loop-/
def correctedLoop {x₀ z w : X}
    (left : Path x₀ z) (segment : Path z w) (right : Path x₀ w) :
    Path x₀ x₀ :=
  left.trans (segment.trans right.symm)

/-- 相邻修正环路在基本群中的乘积消去公共连接道路。
@isnad1 id=eq.0h10v.s7.de6453574026 from=translated src=- shape=7fe6b8b2 vocab=68c0dc9d
-/
theorem correctedLoop_product {x₀ z w v : X}
    (left : Path x₀ z) (first : Path z w) (middle : Path x₀ w)
    (second : Path w v) (right : Path x₀ v) :
    FundamentalGroup.fromPath ⟦correctedLoop middle second right⟧ *
        FundamentalGroup.fromPath ⟦correctedLoop left first middle⟧ =
      FundamentalGroup.fromPath
        ⟦correctedLoop left (first.trans second) right⟧ := by
  rw [FundamentalGroup.mul_def]
  unfold FundamentalGroup.fromPath FundamentalGroup.fromArrow
  change Path.Homotopic.Quotient.trans
      (Path.Homotopic.Quotient.mk (correctedLoop left first middle))
      (Path.Homotopic.Quotient.mk (correctedLoop middle second right)) =
    Path.Homotopic.Quotient.mk
      (correctedLoop left (first.trans second) right)
  unfold correctedLoop
  simp only [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  simp only [Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc
    (Path.Homotopic.Quotient.mk middle).symm
    (Path.Homotopic.Quotient.mk middle)]
  simp

/-- 有限道路段链对应的修正环路按反向依赖折叠形成的基本群元素。-/
def correctedLoopWord {x₀ : X} {n : ℕ} (q : Fin (n + 1) → X)
    (F : (i : Fin n) → Path (q i.castSucc) (q i.succ))
    (connector : (i : Fin (n + 1)) → Path x₀ (q i)) :
    FundamentalGroup X x₀ :=
  Fin.dfoldl n (fun _ => FundamentalGroup X x₀)
    (fun i acc => FundamentalGroup.fromPath
      ⟦correctedLoop (connector i.castSucc) (F i) (connector i.succ)⟧ * acc) 1

/-- 有限修正环路词望远镜化为整条拼接道路的修正环路。
@isnad1 id=eq.0h6v.s7.bdfd17751089 from=translated src=- shape=0c53690c vocab=5c2fb8f0
-/
theorem correctedLoopWord_eq_concat {x₀ : X} {n : ℕ}
    (q : Fin (n + 1) → X)
    (F : (i : Fin n) → Path (q i.castSucc) (q i.succ))
    (connector : (i : Fin (n + 1)) → Path x₀ (q i)) :
    correctedLoopWord q F connector =
      FundamentalGroup.fromPath
        ⟦correctedLoop (connector 0) (Path.concat q F)
          (connector (Fin.last n))⟧ := by
  induction n with
  | zero =>
      simp only [correctedLoopWord, Fin.dfoldl_zero, Path.concat_zero]
      rw [FundamentalGroup.one_def]
      unfold correctedLoop FundamentalGroup.fromPath FundamentalGroup.fromArrow
      simp
  | succ n ih =>
      rw [correctedLoopWord, Fin.dfoldl_succ_last]
      rw [Path.concat_succ]
      change FundamentalGroup.fromPath
          ⟦correctedLoop (connector (Fin.last n).castSucc) (F (Fin.last n))
            (connector (Fin.last (n + 1)))⟧ *
          correctedLoopWord (q ∘ Fin.castSucc) (fun i => F i.castSucc)
            (fun i => connector i.castSucc) = _
      rw [ih]
      exact correctedLoop_product (connector 0)
        (Path.concat (q ∘ Fin.castSucc) (fun i => F i.castSucc))
        (connector (Fin.last n).castSucc) (F (Fin.last n))
        (connector (Fin.last (n + 1)))

end Path

end SandronesLibrary.Topology
