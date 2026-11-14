/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.Space
import Tengoku.Seed.Topology.ClusterPt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 内部、闭包与边界

本模块补齐点集拓扑中集合的三个基本构造。内部是集合所含的最大开集，闭包是包含
集合的最小闭集，边界则是闭包中不属于内部的部分。除极值刻画外，还给出补集对偶、
邻域刻画以及有限并等后续分析最常使用的性质。
-/

namespace SandronesLibrary.Topology.Closure

open Set

variable {X : Type*} [TopologicalSpace X] {s t : Set X} {x : X}

section Interior

/-- 内部是 `s` 所含全部开集的并。

> **Entry**: topology.space.closure
@isnad1 id=eq.0h2v.s5.26fd8446738f from=translated src=- shape=2dbdc793 vocab=21765a89
-/
theorem interior_eq_sUnion_open_subsets (s : Set X) :
    interior s = ⋃₀ {u : Set X | IsOpen u ∧ u ⊆ s} := rfl

/-- 集合的内部是开集。
@isnad1 id=isopen.0h2v.s3.a06ed55e5356 from=translated src=- shape=ed10201d vocab=3528a4e0
-/
theorem isOpen_interior' (s : Set X) : IsOpen (interior s) := isOpen_interior

/-- 内部包含于原集合。
@isnad1 id=le.0h2v.s4.e6b2c32a02dd from=translated src=- shape=0d06f2ab vocab=efe6aae7
-/
theorem interior_subset_self (s : Set X) : interior s ⊆ s := interior_subset

/-- 内部的最大性：原集合内的每个开集都包含于其内部。
@isnad1 id=le.2h3v.s5.4a6171c52ff3 from=translated src=- shape=a2f2c7dc vocab=26af7d09
-/
theorem subset_interior_of_isOpen (ht : IsOpen t) (h : t ⊆ s) : t ⊆ interior s :=
  interior_maximal h ht

/-- 点属于内部，当且仅当它拥有一个包含于原集合的开邻域。
@isnad1 id=iff.0h3v.s5.c3d35284fecd from=translated src=- shape=ceeba18e vocab=347dd934
-/
theorem mem_interior_iff_open_neighborhood :
    x ∈ interior s ↔ ∃ u : Set X, IsOpen u ∧ x ∈ u ∧ u ⊆ s := by
  simpa [and_comm, and_left_comm, and_assoc] using (mem_interior (s := s) (x := x))

/-- 开集等于自己的内部。
@isnad1 id=iff.0h2v.s4.a328f1399d15 from=translated src=- shape=abce628b vocab=3528a4e0
-/
theorem interior_eq_self_iff_isOpen : interior s = s ↔ IsOpen s := by
  exact interior_eq_iff_isOpen

/-- 内部关于集合包含关系单调。
@isnad1 id=le.1h3v.s5.17924c8514fe from=translated src=- shape=edd1c803 vocab=efe6aae7
-/
theorem interior_mono' (h : s ⊆ t) : interior s ⊆ interior t := interior_mono h

end Interior

section Closure

/-- 闭包是所有包含 `s` 的闭集之交。

> **Entry**: topology.space.closure
@isnad1 id=eq.0h2v.s5.210f145f4de5 from=translated src=- shape=f9028830 vocab=b171ff3e
-/
theorem closure_eq_sInter_closed_supersets (s : Set X) :
    closure s = ⋂₀ {u : Set X | IsClosed u ∧ s ⊆ u} := rfl

/-- 原集合包含于其闭包。
@isnad1 id=le.0h2v.s4.66ad99020284 from=translated src=- shape=1b31f6ab vocab=8f4eada7
-/
theorem subset_closure_self (s : Set X) : s ⊆ closure s := subset_closure

/-- 集合的闭包是闭集。
@isnad1 id=isclosed.0h2v.s3.d53b5a420e4b from=translated src=- shape=ed10201d vocab=a29f75fa
-/
theorem isClosed_closure' (s : Set X) : IsClosed (closure s) := isClosed_closure

/-- 闭包的最小性：任何包含原集合的闭集都包含其闭包。
@isnad1 id=le.2h3v.s5.0ac386e71afb from=translated src=- shape=61d27377 vocab=33e2ab2c
-/
theorem closure_subset_of_isClosed (h : s ⊆ t) (ht : IsClosed t) : closure s ⊆ t :=
  closure_minimal h ht

/-- 集合闭，当且仅当它等于自己的闭包。
@isnad1 id=iff.0h2v.s4.d9c695422871 from=translated src=- shape=abce628b vocab=a29f75fa
-/
theorem closure_eq_self_iff_isClosed : closure s = s ↔ IsClosed s := closure_eq_iff_isClosed

/-- 闭包关于集合包含关系单调。
@isnad1 id=le.1h3v.s5.08457ff3e06c from=translated src=- shape=edd1c803 vocab=8f4eada7
-/
theorem closure_mono' (h : s ⊆ t) : closure s ⊆ closure t := closure_mono h

/-- 有限并的闭包等于闭包的并。
@isnad1 id=eq.0h3v.s5.229ede10e35d from=translated src=- shape=398b1dff vocab=b1a82716
-/
theorem closure_union' (s t : Set X) : closure (s ∪ t) = closure s ∪ closure t := closure_union

/-- 点属于闭包，当且仅当它的每个开邻域都与原集合相交。
@isnad1 id=iff.0h3v.s5.989ed288b1fb from=translated src=- shape=ee32d398 vocab=13727dc7
-/
theorem mem_closure_iff_open_neighborhood_meets :
    x ∈ closure s ↔ ∀ u : Set X, IsOpen u → x ∈ u → (u ∩ s).Nonempty :=
  mem_closure_iff

end Closure

section Duality

/-- 闭包与内部通过补集对偶。

> **Entry**: topology.space.closure
@isnad1 id=eq.0h2v.s4.c20e9fa14f02 from=translated src=- shape=16afebe7 vocab=ba0aeba7
-/
theorem closure_eq_compl_interior_compl' (s : Set X) :
    closure s = (interior sᶜ)ᶜ := closure_eq_compl_interior_compl

/-- 内部与闭包通过补集对偶。
@isnad1 id=eq.0h2v.s4.64ebdb30ceb8 from=translated src=- shape=db085028 vocab=ba0aeba7
-/
theorem interior_compl' (s : Set X) : interior sᶜ = (closure s)ᶜ := interior_compl

end Duality

section Frontier

/-- 边界的教材定义：闭包减去内部。

> **Entry**: topology.space.closure
@isnad1 id=eq.0h2v.s4.62595665a3b0 from=translated src=- shape=04d1a947 vocab=c8e5889c
-/
theorem frontier_eq_closure_sdiff_interior (s : Set X) :
    frontier s = closure s \ interior s := rfl

/-- 边界也等于集合闭包与其补集闭包之交。
@isnad1 id=eq.0h2v.s5.963fce7d6e8b from=translated src=- shape=6bc29433 vocab=f5f4fca0
-/
theorem frontier_eq_two_closures (s : Set X) :
    frontier s = closure s ∩ closure sᶜ := frontier_eq_closure_inter_closure

/-- 集合的边界是闭集。
@isnad1 id=isclosed.0h2v.s3.9730095d8027 from=translated src=- shape=ed10201d vocab=87eb045b
-/
theorem isClosed_frontier' (s : Set X) : IsClosed (frontier s) := isClosed_frontier

/-- 集合与其补集具有相同边界。
@isnad1 id=eq.0h2v.s4.d287242bbda0 from=translated src=- shape=c2f7b7a0 vocab=272705b1
-/
theorem frontier_compl' (s : Set X) : frontier sᶜ = frontier s := frontier_compl s

/-- 闭包由内部与边界组成。
@isnad1 id=eq.0h2v.s4.244e524beb34 from=translated src=- shape=04d1a947 vocab=26ab0f88
-/
theorem closure_eq_interior_union_frontier' (s : Set X) :
    closure s = interior s ∪ frontier s := closure_eq_interior_union_frontier s

/-- 闭包也由原集合与边界组成。
@isnad1 id=eq.0h2v.s4.d067db873092 from=translated src=- shape=81cfa3bf vocab=2ad14050
-/
theorem closure_eq_self_union_frontier' (s : Set X) :
    closure s = s ∪ frontier s := closure_eq_self_union_frontier s

end Frontier

end SandronesLibrary.Topology.Closure
