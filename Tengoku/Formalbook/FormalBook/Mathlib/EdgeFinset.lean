import Tengoku

-- https://github.com/leanprover-community/mathlib4/pull/17587

section Mathlib.Data.Sym.Sym2

namespace Sym2

variable {α : Type*}

/--
@isnad1 id=ex.0h2v.s4.c87545339f92 from=translated src=- shape=55a7df0b vocab=5c8c580b
-/
theorem exists_eq (z : Sym2 α) : ∃ x y, z = s(x, y) :=
  z.ind fun x y => ⟨x, y, rfl⟩

/--
@isnad1 id=eq.0h2v.s4.d70eb46c71f2 from=translated src=- shape=beeffd28 vocab=d95c5c77
-/
@[simp] theorem setOf_mem_eq {z : Sym2 α} : {v | v ∈ z} = z := rfl

/--
@isnad1 id=eq.0h3v.s5.4313fddffc99 from=translated src=- shape=f702f88a vocab=b75ecd5d
-/
theorem coe_mk_eq {x y : α} : (s(x, y) : Set α) = {x, y} := by
  ext; simp

/--
@isnad1 id=iff.0h2v.s4.73ce85e68e89 from=translated src=- shape=9f7f4681 vocab=540932a9
-/
theorem isDiag_iff_exists {z : Sym2 α} : z.IsDiag ↔ ∃ x, z = s(x, x) := by
  induction z; rw [mk_isDiag_iff]; simp [eq_comm]

/--
@isnad1 id=iff.0h2v.s4.7686d7cf9729 from=translated src=- shape=577b9742 vocab=540932a9
-/
theorem not_isDiag_iff_exists {z : Sym2 α} : ¬ z.IsDiag ↔ ∃ x y, x ≠ y ∧ z = s(x, y) := by
  induction z with | _ x y =>
  rw [mk_isDiag_iff, not_iff_comm]
  push Not
  constructor
  · intro h; simpa using h x y
  · aesop

instance instCoeMultiset : Coe (Sym2 α) (Multiset α) := ⟨Sym2.toMultiset⟩

/--
@isnad1 id=eq.0h3v.s4.799e2e148f30 from=translated src=- shape=1ad0e8e9 vocab=9dd8ccbb
-/
@[simp] lemma toMultiset_mk {x y : α} : (s(x, y) : Multiset α) = {x, y} := rfl

variable [DecidableEq α]

local instance instCoeFinset : Coe (Sym2 α) (Finset α) := ⟨Sym2.toFinset⟩

/--
@isnad1 id=eq.0h3v.s5.b0ec5474a3b1 from=translated src=- shape=b4d86735 vocab=b670d944
-/
@[local simp] lemma toFinset_mk {x y : α} : (s(x, y) : Finset α) = {x, y} := by
  ext; rw [Sym2.toFinset, Sym2.toMultiset]; simp

/--
@isnad1 id=eq.0h2v.s4.5d8cd194afa6 from=translated src=- shape=7c2a7128 vocab=fb71a526
-/
@[local simp] lemma toFinset_toMultiset {s : Sym2 α} : (s : Multiset α).toFinset = (s : Finset α) := rfl

/--
@isnad1 id=eq.0h2v.s4.f50d02747c20 from=translated src=- shape=33410fb1 vocab=f3fa958b
-/
@[simp] lemma coe_toFinset {z : Sym2 α} : ((z : Finset α) : Set α) = z := by
  ext; simp

/--
@isnad1 id=eq.0h2v.s6.c0b1e7a16e0f from=translated src=- shape=c714861c vocab=a75a34fa
-/
lemma toFinset_eq [Fintype α] {e : Sym2 α} : (e : Finset α) = {v | v ∈ e}.toFinset := by
  ext; simp

/--
@isnad1 id=eq.1h3v.s4.3d223103ccc5 from=translated src=- shape=f3d67da8 vocab=0a1467fc
-/
lemma card_toFinset_mk_of_ne {x y : α} (h : x ≠ y) : s(x, y).toFinset.card = 2 := by
  rw [Finset.card_eq_two]
  use x, y, h
  simp

/--
@isnad1 id=le.0h2v.s4.38c29505d4b9 from=translated src=- shape=e1606677 vocab=24ad19df
-/
lemma one_le_card_toFinset {z : Sym2 α} : 1 ≤ z.toFinset.card := by
  induction z; simp

/--
@isnad1 id=le.0h2v.s4.1499fa29ccbc from=translated src=- shape=5bd2d9aa vocab=24ad19df
-/
lemma card_toFinset_le_two {z : Sym2 α} : z.toFinset.card ≤ 2 := by
  by_cases z.IsDiag <;> simp [*, card_toFinset_of_isDiag, card_toFinset_of_not_isDiag]

end Sym2
attribute [local instance] Sym2.instCoeMultiset
attribute [local simp] Sym2.toFinset_mk Sym2.toMultiset_mk

end Mathlib.Data.Sym.Sym2
attribute [local instance] Sym2.instCoeMultiset
attribute [local simp] Sym2.toFinset_mk Sym2.toMultiset_mk

section Mathlib.Combinatorics.SimpleGraph.Basic

namespace SimpleGraph

variable {α : Type*} {G : SimpleGraph α} [DecidableEq α]

-- lemma card_toFinset_of_mem_edgeSet (e : Sym2 α) (he : e ∈ G.edgeSet) :
--     (e : Finset α).card = 2 := by
--   refine Sym2.card_toFinset_of_not_isDiag ?_

--   have := (not_isDiag_of_mem_edgeSet _ he)

--   sorry

-- lemma card_filter_mem_of_mem_edgeSet [Fintype α] (e : Sym2 α) (he : e ∈ G.edgeSet) :
--     Finset.card {v | v ∈ e} = 2 := by
--   rw [← SimpleGraph.card_toFinset_of_mem_edgeSet _ he]
--   congr; ext; simp

end SimpleGraph

end Mathlib.Combinatorics.SimpleGraph.Basic

section Mathlib.Combinatorics.SimpleGraph.Finite

namespace SimpleGraph

variable {α : Type*} [Fintype α] {G : SimpleGraph α} [DecidableRel G.Adj] [DecidableEq α]

-- lemma card_toFinset_of_mem_edgeFinset (e : Sym2 α) (he : e ∈ G.edgeFinset) :
--     (e : Finset α).card = 2 :=
--   Sym2.card_toFinset_of_not_isDiag (not_isDiag_of_mem_edgeSet _ (mem_edgeFinset.mp he))

-- lemma card_filter_mem_of_mem_edgeFinset (e : Sym2 α) (he : e ∈ G.edgeFinset) :
--     Finset.card {v | v ∈ e} = 2 := by
--   rw [← SimpleGraph.card_toFinset_of_mem_edgeFinset _ he]
--   congr; ext; simp

end SimpleGraph

end Mathlib.Combinatorics.SimpleGraph.Finite
-- Tengoku: 3 registration(s) of this module made local so they do not change other libraries (generated)
