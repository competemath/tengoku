/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import Tengoku.Jsp000907Lean.JSP907.Degen
import Tengoku.Jsp000907Lean.JSP907.Parity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local analysis of a cycle in `G m`

Every non-hub vertex has exactly three neighbours, and a cycle through it uses exactly
two of them.  Consequently a vertex lies on at most one chord, and if that chord is a
pentagon edge then the vertex's inter-block edge is used by the cycle.
-/

namespace JSP907

open SimpleGraph

variable {m : ℕ}

/-- The inter-block neighbour lies in a different block.
@isnad1 id=ne.1h3v.s5.2cf9d6df6d15 from=translated src=- shape=bc937bf6 vocab=9127f034
-/
lemma ext_block_ne {p q : Blk m × Pos} (h : ext p = some q) : q.1 ≠ p.1 := by
  obtain ⟨B, y⟩ := p
  cases B with
  | inr L =>
      rw [ext_inr, extL] at h
      split_ifs at h with hy
      · obtain rfl : q = (Sum.inl (⟨L.1.1, L.2.1⟩ : SIdx m), L.1.2) := (Option.some.inj h).symm
        exact fun hc => Sum.inl_ne_inr hc
  | inl S =>
      rw [ext_inl, extS] at h
      split_ifs at h with hL hy
      · obtain rfl : q = (Sum.inr (⟨(S.1, y), ⟨S.2, hL⟩⟩ : LIdx m), y) := (Option.some.inj h).symm
        exact fun hc => Sum.inr_ne_inl hc
      · obtain rfl : q = (Sum.inl (⟨S.1 - 1, (Nat.sub_le _ _).trans S.2⟩ : SIdx m), 2) :=
          (Option.some.inj h).symm
        obtain ⟨-, hne⟩ | ⟨hy2, -⟩ := not_leafOK_cases hL
        · intro hc
          have : S.1 - 1 = S.1 := congrArg Subtype.val (Sum.inl_injective hc)
          omega
        · exact absurd hy2 (by rw [hy]; decide)
      · obtain rfl : q = (Sum.inl (⟨min (S.1 + 1) m, min_le_right _ _⟩ : SIdx m), 0) :=
          (Option.some.inj h).symm
        obtain ⟨hy0, -⟩ | ⟨rfl, hne⟩ := not_leafOK_cases hL
        · exact absurd hy0 hy
        · intro hc
          have hlt : S.1 < m := lt_of_le_of_ne S.2 hne
          have : min (S.1 + 1) m = S.1 := congrArg Subtype.val (Sum.inl_injective hc)
          omega

/--
@isnad1 id=ne.0h1v.s6.09e17fd53bd5 from=translated src=- shape=6e7d942a vocab=c21ac8e2
-/
lemma pos_ne_shift (y : Pos) : y + 1 ≠ y + 1 + 1 + 1 + 1 := by
  revert y
  decide

/--
@isnad1 id=ne.0h2v.s7.28457034c376 from=translated src=- shape=5203ec97 vocab=8267e0d5
-/
lemma pentNbr_ne (p : Blk m × Pos) :
    (some (p.1, p.2 + 1) : Vtx m) ≠ some (p.1, p.2 + 1 + 1 + 1 + 1) := by
  intro h
  exact pos_ne_shift p.2 (congrArg Prod.snd (Option.some.inj h))

/--
@isnad1 id=ne.0h2v.s5.0b6e684ebdc3 from=translated src=- shape=989134aa vocab=d9636115
-/
lemma ext_ne_pentNbr₁ (p : Blk m × Pos) : (ext p : Vtx m) ≠ some (p.1, p.2 + 1) := by
  intro h
  exact ext_block_ne h rfl

/--
@isnad1 id=ne.0h2v.s6.719040641726 from=translated src=- shape=38744802 vocab=d9636115
-/
lemma ext_ne_pentNbr₂ (p : Blk m × Pos) :
    (ext p : Vtx m) ≠ some (p.1, p.2 + 1 + 1 + 1 + 1) := by
  intro h
  exact ext_block_ne h rfl

/-- The neighbour set of a non-hub vertex, as a `Set`.
@isnad1 id=eq.0h2v.s7.1eb1d72334ae from=translated src=- shape=3220a695 vocab=634ed336
-/
lemma neighborSet_some (p : Blk m × Pos) :
    (G m).neighborSet (some p) =
      ({some (p.1, p.2 + 1), some (p.1, p.2 + 1 + 1 + 1 + 1), ext p} : Set (Vtx m)) := by
  ext x
  simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact adj_some_iff p x

end JSP907
