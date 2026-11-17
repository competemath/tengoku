/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.ConstructionRank
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.CountableBasis
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.TreeCode.Rank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Semantics of valid coded Borel trees

Evaluation is defined only with an explicit `IsValid` proof.  Well-founded recursion decodes a
valid labelled tree into the existing `GeneratedCode` syntax over a natural-number-indexed basis.
The resulting semantics therefore reuses the established generated-code evaluator and does not
give malformed or ill-founded raw codes an arbitrary denotation.
-/

open Set

universe u

namespace DescriptiveSetTheory.BorelTreeCode

variable {X : Type u}

/-- The required root node of a valid raw code.-/
def root {c : Raw} (h : IsValid c) : c.tree :=
  ⟨[], h.root_mem⟩

/-- The unique child of a valid complement node.-/
def complChild {c : Raw} (h : IsValid c) (s : c.tree)
    (hkind : c.kindAt? s.1 = some .compl) : c.tree :=
  ⟨s.1 ++ [0], h.child_zero_mem_of_kindAt?_eq_compl s.2 hkind⟩

/-- The `n`th child of a valid countable-union node.-/
def iUnionChild {c : Raw} (h : IsValid c) (s : c.tree)
    (hkind : c.kindAt? s.1 = some .iUnion) (n : ℕ) : c.tree :=
  ⟨s.1 ++ [n], h.child_mem_of_kindAt?_eq_iUnion s.2 hkind n⟩

/-- A complement child is an immediate child in the decoded syntax tree.-/
theorem child_complChild {c : Raw} (h : IsValid c) (s : c.tree)
    (hkind : c.kindAt? s.1 = some .compl) :
    Tree.Child c.tree (complChild h s hkind) s :=
  ⟨0, rfl⟩

/-- A union child is an immediate child in the decoded syntax tree.-/
theorem child_iUnionChild {c : Raw} (h : IsValid c) (s : c.tree)
    (hkind : c.kindAt? s.1 = some .iUnion) (n : ℕ) :
    Tree.Child c.tree (iUnionChild h s hkind n) s :=
  ⟨n, rfl⟩

/-- Decode the valid subtree rooted at `s` into the established generated-code syntax.-/
noncomputable def decodeAt (b : ℕ → Set X) (c : Raw) (h : IsValid c) :
    (s : c.tree) → GeneratedCode b :=
  h.wellFounded.fix fun s below =>
    match hkind : c.kindAt? s.1 with
    | some .empty => .empty
    | some .basic => .basic (c.payloadAt s.1)
    | some .compl =>
        .compl (below (complChild h s hkind) (child_complChild h s hkind))
    | some .iUnion =>
        .iUnion fun n => below (iUnionChild h s hkind n) (child_iUnionChild h s hkind n)
    | none => .empty

/-- Decode a valid raw code at its root.-/
noncomputable def decode (b : ℕ → Set X) (c : Raw) (h : IsValid c) : GeneratedCode b :=
  decodeAt b c h (root h)

/-- Evaluate the valid subtree rooted at `s`.-/
noncomputable def evalAt (b : ℕ → Set X) (c : Raw) (h : IsValid c)
    (s : c.tree) : Set X :=
  (decodeAt b c h s).eval

/-- Evaluate a valid raw code. There is deliberately no evaluator on `Raw` without validity.-/
noncomputable def eval (b : ℕ → Set X) (c : Raw) (h : IsValid c) : Set X :=
  (decode b c h).eval

/-- Decoding is independent of the supplied validity proof.-/
theorem decode_proof_irrel (b : ℕ → Set X) (c : Raw) (h k : IsValid c) :
    decode b c h = decode b c k := by
  have hk : h = k := Subsingleton.elim _ _
  subst k
  rfl

/-- Evaluation is independent of the supplied validity proof.-/
theorem eval_proof_irrel (b : ℕ → Set X) (c : Raw) (h k : IsValid c) :
    eval b c h = eval b c k := by
  change (decode b c h).eval = (decode b c k).eval
  rw [decode_proof_irrel b c h k]

/-- A valid code over a topological basis denotes a Borel set.-/
theorem measurableSet_eval [TopologicalSpace X] {b : ℕ → Set X}
    (hb : TopologicalSpace.IsTopologicalBasis (range b)) (c : Raw) (h : IsValid c) :
    @MeasurableSet X (borel X) (eval b c h) :=
  CountableBasisCode.measurableSet_eval hb (decode b c h)

/-- A valid standard tree code can be transported back to the unrestricted `BorelCode` API.-/
theorem exists_borelCode_eval [TopologicalSpace X] {b : ℕ → Set X}
    (hb : TopologicalSpace.IsTopologicalBasis (range b)) (c : Raw) (h : IsValid c) :
    ∃ d : BorelCode X, d.eval = eval b c h :=
  BorelCode.borelMeasurableSet_iff_exists_code.mp (measurableSet_eval hb c h)

section Encode

variable {b : ℕ → Set X}

private def subcodeAt (d : GeneratedCode b) : List ℕ → Option (GeneratedCode b)
  | [] => some d
  | n :: s =>
      match d with
      | .basic _ => none
      | .empty => none
      | .compl e => if n = 0 then subcodeAt e s else none
      | .iUnion e => subcodeAt (e n) s

private theorem subcodeAt_append (d : GeneratedCode b) (s t : List ℕ) :
    subcodeAt d (s ++ t) = (subcodeAt d s).bind fun e => subcodeAt e t := by
  induction s generalizing d with
  | nil => simp [subcodeAt]
  | cons n s ih =>
      cases d with
      | basic i => simp [subcodeAt]
      | empty => simp [subcodeAt]
      | compl d =>
          by_cases hn : n = 0
          · subst n
            simp [subcodeAt, ih]
          · simp [subcodeAt, hn]
      | iUnion d => simp [subcodeAt, ih]

private noncomputable def encodedTreeCode (d : GeneratedCode b) : Tree.TreeCode := by
  classical
  refine ⟨fun s => (subcodeAt d s).isSome, ?_⟩
  intro s n hchild
  change (subcodeAt d (s ++ [n])).isSome = true at hchild
  change (subcodeAt d s).isSome = true
  rw [subcodeAt_append] at hchild
  cases hparent : subcodeAt d s <;> simp [hparent] at hchild ⊢

private def labelOf : GeneratedCode b → ℕ × ℕ
  | .empty => (NodeKind.empty.code, 0)
  | .basic n => (NodeKind.basic.code, n)
  | .compl _ => (NodeKind.compl.code, 0)
  | .iUnion _ => (NodeKind.iUnion.code, 0)

/-- Encode an existing natural-basis generated code in the raw Polish tree carrier.-/
noncomputable def encode (d : GeneratedCode b) : Raw :=
  (encodedTreeCode d, fun s =>
    match subcodeAt d s with
    | some e => labelOf e
    | none => (4, 0))

private theorem subcodeAt_isSome_of_mem (d : GeneratedCode b) {s : List ℕ}
    (hs : s ∈ (encode d).tree) : (subcodeAt d s).isSome = true := by
  exact hs

private noncomputable def encodedNodeRank (d : GeneratedCode b)
    (s : (encode d).tree) : Ordinal.{0} :=
  match subcodeAt d s.1 with
  | some e => e.constructionRank
  | none => 0

private theorem encodedNodeRank_lt_of_child (d : GeneratedCode b)
    {s t : (encode d).tree} (hst : Tree.Child (encode d).tree s t) :
    encodedNodeRank d s < encodedNodeRank d t := by
  obtain ⟨n, hnode⟩ := hst
  have hsSome := subcodeAt_isSome_of_mem d s.2
  have htSome := subcodeAt_isSome_of_mem d t.2
  cases hparent : subcodeAt d t.1 with
  | none => simp [hparent] at htSome
  | some parent =>
      have hchild : subcodeAt d s.1 = subcodeAt parent [n] := by
        rw [hnode, subcodeAt_append, hparent]
        rfl
      cases parent with
      | basic i =>
          have hnone : subcodeAt d s.1 = none := by
            simpa only [subcodeAt] using hchild
          rw [hnone] at hsSome
          contradiction
      | empty =>
          have hnone : subcodeAt d s.1 = none := by
            simpa only [subcodeAt] using hchild
          rw [hnone] at hsSome
          contradiction
      | compl e =>
          by_cases hn : n = 0
          · subst n
            have hchild' : subcodeAt d s.1 = some e := by
              simpa [subcodeAt] using hchild
            unfold encodedNodeRank
            rw [hchild', hparent]
            exact Order.lt_succ _
          · have hchild' : subcodeAt d s.1 = none := by
              simpa [subcodeAt, hn] using hchild
            rw [hchild'] at hsSome
            contradiction
      | iUnion e =>
          have hchild' : subcodeAt d s.1 = some (e n) := by
            simpa [subcodeAt] using hchild
          unfold encodedNodeRank
          rw [hchild', hparent]
          exact GeneratedCode.constructionRank_lt_iUnion e n

private theorem encodedTree_wellFounded (d : GeneratedCode b) :
    Tree.IsWellFounded (encode d).tree :=
  (@WellFounded.onFun _ _ _ (encodedNodeRank d) Ordinal.lt_wf).mono fun _ _ hst =>
    encodedNodeRank_lt_of_child d hst

/-- Every encoded `GeneratedCode` satisfies the exact validity predicate.-/
theorem isValid_encode (d : GeneratedCode b) : IsValid (encode d) := by
  refine ⟨?_, encodedTree_wellFounded d, ?_, ?_⟩
  · change (subcodeAt d []).isSome = true
    simp [subcodeAt]
  · intro s hs
    have hsSome := subcodeAt_isSome_of_mem d hs
    cases hsub : subcodeAt d s with
    | none => simp [hsub] at hsSome
    | some e =>
        cases e <;>
          simp [Raw.IsCoherentAt, IsCoherentLabel, Raw.labels, encode, labelOf, hsub,
            NodeKind.code, NodeKind.ofCode?]
  · intro s hs
    have hsSome := subcodeAt_isSome_of_mem d hs
    cases hsub : subcodeAt d s with
    | none => simp [hsub] at hsSome
    | some e =>
        cases e with
        | basic i =>
            have hkind : (encode d).kindAt? s = some .basic := by
              simp [Raw.kindAt?, Raw.kindCodeAt, Raw.labels, encode, labelOf, hsub,
                NodeKind.code, NodeKind.ofCode?]
            simp only [Raw.HasExpectedChildrenAt, hkind]
            intro n hmem
            have hsome := subcodeAt_isSome_of_mem d hmem
            rw [subcodeAt_append, hsub] at hsome
            simp [subcodeAt] at hsome
        | empty =>
            have hkind : (encode d).kindAt? s = some .empty := by
              simp [Raw.kindAt?, Raw.kindCodeAt, Raw.labels, encode, labelOf, hsub,
                NodeKind.code, NodeKind.ofCode?]
            simp only [Raw.HasExpectedChildrenAt, hkind]
            intro n hmem
            have hsome := subcodeAt_isSome_of_mem d hmem
            rw [subcodeAt_append, hsub] at hsome
            simp [subcodeAt] at hsome
        | compl e =>
            have hkind : (encode d).kindAt? s = some .compl := by
              simp [Raw.kindAt?, Raw.kindCodeAt, Raw.labels, encode, labelOf, hsub,
                NodeKind.code, NodeKind.ofCode?]
            simp only [Raw.HasExpectedChildrenAt, hkind]
            constructor
            · change (subcodeAt d (s ++ [0])).isSome = true
              rw [subcodeAt_append, hsub]
              simp [subcodeAt]
            · intro n hn hmem
              have hsome := subcodeAt_isSome_of_mem d hmem
              rw [subcodeAt_append, hsub] at hsome
              simp [subcodeAt, hn] at hsome
        | iUnion e =>
            have hkind : (encode d).kindAt? s = some .iUnion := by
              simp [Raw.kindAt?, Raw.kindCodeAt, Raw.labels, encode, labelOf, hsub,
                NodeKind.code, NodeKind.ofCode?]
            simp only [Raw.HasExpectedChildrenAt, hkind]
            intro n
            change (subcodeAt d (s ++ [n])).isSome = true
            rw [subcodeAt_append, hsub]
            simp [subcodeAt]

end Encode

end DescriptiveSetTheory.BorelTreeCode
