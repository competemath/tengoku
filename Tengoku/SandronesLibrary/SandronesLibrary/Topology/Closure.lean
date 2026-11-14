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

> **Entry**: topology.space.closure-/
theorem interior_eq_sUnion_open_subsets (s : Set X) :
    interior s = ⋃₀ {u : Set X | IsOpen u ∧ u ⊆ s} := rfl

/-- 集合的内部是开集。-/
theorem isOpen_interior' (s : Set X) : IsOpen (interior s) := isOpen_interior

/-- 内部包含于原集合。-/
theorem interior_subset_self (s : Set X) : interior s ⊆ s := interior_subset

/-- 内部的最大性：原集合内的每个开集都包含于其内部。-/
theorem subset_interior_of_isOpen (ht : IsOpen t) (h : t ⊆ s) : t ⊆ interior s :=
  interior_maximal h ht

/-- 点属于内部，当且仅当它拥有一个包含于原集合的开邻域。-/
theorem mem_interior_iff_open_neighborhood :
    x ∈ interior s ↔ ∃ u : Set X, IsOpen u ∧ x ∈ u ∧ u ⊆ s := by
  simpa [and_comm, and_left_comm, and_assoc] using (mem_interior (s := s) (x := x))

/-- 开集等于自己的内部。-/
theorem interior_eq_self_iff_isOpen : interior s = s ↔ IsOpen s := by
  exact interior_eq_iff_isOpen

/-- 内部关于集合包含关系单调。-/
theorem interior_mono' (h : s ⊆ t) : interior s ⊆ interior t := interior_mono h

end Interior

section Closure

/-- 闭包是所有包含 `s` 的闭集之交。

> **Entry**: topology.space.closure-/
theorem closure_eq_sInter_closed_supersets (s : Set X) :
    closure s = ⋂₀ {u : Set X | IsClosed u ∧ s ⊆ u} := rfl

/-- 原集合包含于其闭包。-/
theorem subset_closure_self (s : Set X) : s ⊆ closure s := subset_closure

/-- 集合的闭包是闭集。-/
theorem isClosed_closure' (s : Set X) : IsClosed (closure s) := isClosed_closure

/-- 闭包的最小性：任何包含原集合的闭集都包含其闭包。-/
theorem closure_subset_of_isClosed (h : s ⊆ t) (ht : IsClosed t) : closure s ⊆ t :=
  closure_minimal h ht

/-- 集合闭，当且仅当它等于自己的闭包。-/
theorem closure_eq_self_iff_isClosed : closure s = s ↔ IsClosed s := closure_eq_iff_isClosed

/-- 闭包关于集合包含关系单调。-/
theorem closure_mono' (h : s ⊆ t) : closure s ⊆ closure t := closure_mono h

/-- 有限并的闭包等于闭包的并。-/
theorem closure_union' (s t : Set X) : closure (s ∪ t) = closure s ∪ closure t := closure_union

/-- 点属于闭包，当且仅当它的每个开邻域都与原集合相交。-/
theorem mem_closure_iff_open_neighborhood_meets :
    x ∈ closure s ↔ ∀ u : Set X, IsOpen u → x ∈ u → (u ∩ s).Nonempty :=
  mem_closure_iff

end Closure

section Duality

/-- 闭包与内部通过补集对偶。

> **Entry**: topology.space.closure-/
theorem closure_eq_compl_interior_compl' (s : Set X) :
    closure s = (interior sᶜ)ᶜ := closure_eq_compl_interior_compl

/-- 内部与闭包通过补集对偶。-/
theorem interior_compl' (s : Set X) : interior sᶜ = (closure s)ᶜ := interior_compl

end Duality

section Frontier

/-- 边界的教材定义：闭包减去内部。

> **Entry**: topology.space.closure-/
theorem frontier_eq_closure_sdiff_interior (s : Set X) :
    frontier s = closure s \ interior s := rfl

/-- 边界也等于集合闭包与其补集闭包之交。-/
theorem frontier_eq_two_closures (s : Set X) :
    frontier s = closure s ∩ closure sᶜ := frontier_eq_closure_inter_closure

/-- 集合的边界是闭集。-/
theorem isClosed_frontier' (s : Set X) : IsClosed (frontier s) := isClosed_frontier

/-- 集合与其补集具有相同边界。-/
theorem frontier_compl' (s : Set X) : frontier sᶜ = frontier s := frontier_compl s

/-- 闭包由内部与边界组成。-/
theorem closure_eq_interior_union_frontier' (s : Set X) :
    closure s = interior s ∪ frontier s := closure_eq_interior_union_frontier s

/-- 闭包也由原集合与边界组成。-/
theorem closure_eq_self_union_frontier' (s : Set X) :
    closure s = s ∪ frontier s := closure_eq_self_union_frontier s

end Frontier

end SandronesLibrary.Topology.Closure
