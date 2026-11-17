/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.TreeCode.Validity
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.Rank
import Tengoku.Seed.MeasureTheory.MeasurableSpace.Card

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rank of valid coded Borel trees

The syntax rank is exactly the existing well-founded-tree rank of the decoded natural-number tree.
No second ordinal recursion is introduced.  Validity is an explicit argument, and countability is
inherited from the countability theorem for well-founded trees on `ℕ`.
-/

open Cardinal Ordinal

namespace DescriptiveSetTheory.BorelTreeCode

/-- The ordinal syntax rank of a valid raw code.-/
noncomputable def rank (c : Raw) (h : IsValid c) : Ordinal.{0} :=
  Tree.rank c.tree h.wellFounded

/-- The syntax rank is independent of the supplied validity proof.
@isnad1 id=eq.2h1v.s4.ebd0d0b09374 from=translated src=- shape=a583252e vocab=42025456
-/
theorem rank_proof_irrel (c : Raw) (h k : IsValid c) : rank c h = rank c k :=
  rfl

private theorem accRank_lt_omega_one {c : Raw} {s : c.tree}
    (h : Acc (Tree.Child c.tree) s) : h.rank < (ω₁ : Ordinal.{0}) := by
  induction h with
  | intro s hbelow ih =>
      rw [Acc.rank_eq]
      apply Ordinal.iSup_lt_omega_one
      intro child
      exact (isSuccLimit_omega 1).succ_lt (ih child.1 child.2)

private theorem nodeRank_lt_omega_one {c : Raw} (h : IsValid c) (s : c.tree) :
    Tree.nodeRank h.wellFounded s < (ω₁ : Ordinal.{0}) := by
  letI : _root_.IsWellFounded c.tree (Tree.Child c.tree) := ⟨h.wellFounded⟩
  unfold Tree.nodeRank _root_.IsWellFounded.rank
  exact accRank_lt_omega_one (_root_.IsWellFounded.apply (Tree.Child c.tree) s)

/-- Every valid coded Borel syntax tree has countable rank.
@isnad1 id=lt.1h1v.s5.f096e0aad877 from=translated src=- shape=c72c6de0 vocab=2dc5ce55
-/
theorem rank_lt_omega_one (c : Raw) (h : IsValid c) : rank c h < ω₁ := by
  rw [rank, Tree.rank_eq_nodeRank h.wellFounded h.root_mem]
  exact nodeRank_lt_omega_one h ⟨[], h.root_mem⟩

/-- The rank is the node rank at the required root.
@isnad1 id=eq.1h1v.s7.dece7ab880cb from=translated src=- shape=f46cb330 vocab=857fdefb
-/
theorem rank_eq_root_nodeRank (c : Raw) (h : IsValid c) :
    rank c h = Tree.nodeRank h.wellFounded ⟨[], h.root_mem⟩ :=
  Tree.rank_eq_nodeRank h.wellFounded h.root_mem

/-- Node rank strictly decreases along every immediate syntax-tree edge.
@isnad1 id=lt.2h3v.s8.61349b5028d2 from=translated src=- shape=6f8765c1 vocab=d55260e2
-/
theorem nodeRank_lt_of_child {c : Raw} (h : IsValid c) {s t : c.tree}
    (hst : Tree.Child c.tree s t) :
    Tree.nodeRank h.wellFounded s < Tree.nodeRank h.wellFounded t :=
  Tree.nodeRank_lt_of_child h.wellFounded hst

end DescriptiveSetTheory.BorelTreeCode
