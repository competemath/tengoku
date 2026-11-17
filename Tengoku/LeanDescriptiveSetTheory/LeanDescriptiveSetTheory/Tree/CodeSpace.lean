/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Spaces.ListCoding
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A Polish code space for trees on natural numbers

A Boolean function on finite natural-number lists codes membership in a tree. The valid codes are
exactly those satisfying the one-step prefix condition. This locus is closed in the product
topology, hence its subtype is Polish and standard Borel.

The encode/decode equivalence is extensional and exact. No topology is installed on mathlib's
existing `Descriptive.tree ℕ`, so this file deliberately makes no homeomorphism or continuity claim
about that type.
-/

open Set

namespace DescriptiveSetTheory.Tree

/-- The closed locus of Boolean membership codes satisfying one-step prefix closure.-/
def treeCodeSet : Set (List ℕ → Bool) :=
  {c | ∀ (x : List ℕ) (a : ℕ), c (x ++ [a]) = true → c x = true}

/--
@isnad1 id=iff.0h1v.s5.3e1160016536 from=translated src=- shape=6db34a51 vocab=46c91f12
-/
@[simp]
theorem mem_treeCodeSet {c : List ℕ → Bool} :
    c ∈ treeCodeSet ↔ ∀ (x : List ℕ) (a : ℕ), c (x ++ [a]) = true → c x = true :=
  Iff.rfl

/-- Prefix-closed Boolean membership codes form a closed subset of the ambient product space.
@isnad1 id=isclosed.0h0v.s4.d207bfad1c1c from=translated src=- shape=4fbb056c vocab=74ba304c
-/
theorem isClosed_treeCodeSet : IsClosed treeCodeSet := by
  rw [show treeCodeSet = ⋂ (x : List ℕ) (a : ℕ),
      {c : List ℕ → Bool | c (x ++ [a]) = true → c x = true} by
    ext c
    simp [treeCodeSet]]
  exact isClosed_iInter fun x => isClosed_iInter fun a => by
    have hcontinuous : Continuous (fun c : List ℕ → Bool =>
        (c (x ++ [a]), c x)) :=
      (continuous_listNatBoolCoordinate (x ++ [a])).prodMk
        (continuous_listNatBoolCoordinate x)
    have hclosed : IsClosed {p : Bool × Bool | p.1 = true → p.2 = true} :=
      (isClopen_discrete _).isClosed
    simpa only [Set.preimage_ofPred_eq] using hclosed.preimage hcontinuous

/-- The subtype of valid Boolean tree codes.-/
abbrev TreeCode : Type := treeCodeSet

/-- The inherited topology makes `TreeCode` Polish because its carrier is closed.
@isnad1 id=polishsp.0h0v.s5.8f10d3759b78 from=translated src=- shape=49959d42 vocab=17f5d4e0
-/
noncomputable instance treeCodePolishSpace : PolishSpace TreeCode :=
  isClosed_treeCodeSet.polishSpace

/-- The inherited Borel structure on `TreeCode` is standard Borel.
@isnad1 id=standard.0h0v.s5.063832e6bf48 from=translated src=- shape=49959d42 vocab=4ec1c50e
-/
instance treeCodeStandardBorelSpace : StandardBorelSpace TreeCode := by
  infer_instance

/-- Encode a tree by the Boolean characteristic function of its node set.-/
noncomputable def encodeTree (T : Descriptive.tree ℕ) : TreeCode := by
  classical
  refine ⟨fun s => decide (s ∈ T), ?_⟩
  intro x a hx
  simp only [decide_eq_true_eq] at hx ⊢
  exact T.property hx

/-- Decode a prefix-closed Boolean membership code as a mathlib tree.-/
def decodeTree (c : TreeCode) : Descriptive.tree ℕ where
  val := {s | c.1 s = true}
  property := by
    intro x a hx
    exact c.2 x a hx

/--
@isnad1 id=iff.0h2v.s7.f3a8548de93f from=translated src=- shape=87b3d407 vocab=791e21c1
-/
@[simp]
theorem mem_decodeTree {c : TreeCode} {s : List ℕ} :
    s ∈ decodeTree c ↔ c.1 s = true :=
  Iff.rfl

/--
@isnad1 id=iff.0h2v.s7.19ed96c738db from=translated src=- shape=11f67146 vocab=c0833340
-/
@[simp]
theorem encodeTree_apply_eq_true (T : Descriptive.tree ℕ) (s : List ℕ) :
    (encodeTree T).1 s = true ↔ s ∈ T := by
  classical
  simp [encodeTree]

/-- Decoding an encoded tree recovers the original tree extensionally.
@isnad1 id=eq.0h1v.s7.831a6dcc2cb4 from=translated src=- shape=122ec9d9 vocab=fc647c3d
-/
@[simp]
theorem decodeTree_encodeTree (T : Descriptive.tree ℕ) :
    decodeTree (encodeTree T) = T := by
  ext s
  simp

end DescriptiveSetTheory.Tree
