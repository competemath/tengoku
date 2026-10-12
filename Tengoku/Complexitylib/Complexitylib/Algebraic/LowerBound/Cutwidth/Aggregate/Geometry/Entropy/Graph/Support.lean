/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku

/-!
# Supports of finite families of edges

Adding an edge introduces zero, one, or two new endpoints. These exact cardinality
increments are the combinatorial accounting used by the joint-message entropy bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph

open scoped Classical

variable {V E : Type*} [DecidableEq V]

/-- The vertices occurring among a finite family of edges. -/
def support (left right : E → V) (edges : Finset E) : Finset V :=
  edges.biUnion fun e => {left e, right e}

/-- Membership in the support gives an incident edge in the selected family.
@isnad1 id=iff.0h6v.s6.d76cabe6933f from=translated src=- shape=38159503 vocab=94934b87
-/
@[simp] theorem mem_support (left right : E → V) (edges : Finset E) (v : V) :
    v ∈ support left right edges ↔ ∃ e ∈ edges, v = left e ∨ v = right e := by
  simp [support]

/-- The empty edge family has empty support.
@isnad1 id=eq.0h4v.s5.52cfec3f1ab9 from=translated src=- shape=e5e372a4 vocab=a3be1ab4
-/
@[simp] theorem support_empty (left right : E → V) : support left right ∅ = ∅ := by
  simp [support]

/-- Inserting an edge adds precisely its two endpoints to the support.
@isnad1 id=eq.0h6v.s6.ea375736685a from=translated src=- shape=96dbf5f7 vocab=473bb857
-/
theorem support_insert [DecidableEq E] (left right : E → V) (edges : Finset E) (e : E) :
    support left right (insert e edges) = insert (left e) (insert (right e)
      (support left right edges)) := by
  ext v
  simp [or_assoc]

/-- No support vertex is added when both endpoints already occur.
@isnad1 id=eq.2h6v.s6.bc3cb3257ff8 from=translated src=- shape=6d5fff5d vocab=ff4cca97
-/
theorem card_support_insert_of_mem_mem [DecidableEq E]
    (left right : E → V) (edges : Finset E) (e : E)
    (hl : left e ∈ support left right edges) (hr : right e ∈ support left right edges) :
    (support left right (insert e edges)).card = (support left right edges).card := by
  rw [support_insert, Finset.insert_eq_of_mem hr, Finset.insert_eq_of_mem hl]

/-- Exactly one support vertex is added when only the right endpoint is new.
@isnad1 id=eq.2h6v.s6.bd54670fc570 from=translated src=- shape=38053249 vocab=d95ec8a2
-/
theorem card_support_insert_of_mem_notMem [DecidableEq E]
    (left right : E → V) (edges : Finset E) (e : E)
    (hl : left e ∈ support left right edges) (hr : right e ∉ support left right edges) :
    (support left right (insert e edges)).card = (support left right edges).card + 1 := by
  rw [support_insert, Finset.insert_eq_of_mem (Finset.mem_insert_of_mem hl),
    Finset.card_insert_of_notMem hr]

/-- Exactly one support vertex is added when only the left endpoint is new.
@isnad1 id=eq.2h6v.s6.91b2af24f84a from=translated src=- shape=c41e231d vocab=d95ec8a2
-/
theorem card_support_insert_of_notMem_mem [DecidableEq E]
    (left right : E → V) (edges : Finset E) (e : E)
    (hl : left e ∉ support left right edges) (hr : right e ∈ support left right edges) :
    (support left right (insert e edges)).card = (support left right edges).card + 1 := by
  rw [support_insert, Finset.insert_eq_of_mem hr, Finset.card_insert_of_notMem hl]

/-- Two support vertices are added when the distinct endpoints are both new.
@isnad1 id=eq.3h6v.s6.fe3624923565 from=translated src=- shape=a4afe858 vocab=d95ec8a2
-/
theorem card_support_insert_of_notMem_notMem [DecidableEq E]
    (left right : E → V) (edges : Finset E) (e : E) (hne : left e ≠ right e)
    (hl : left e ∉ support left right edges) (hr : right e ∉ support left right edges) :
    (support left right (insert e edges)).card = (support left right edges).card + 2 := by
  rw [support_insert, Finset.card_insert_of_notMem (by simp [hne, hl]),
    Finset.card_insert_of_notMem hr]

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph
