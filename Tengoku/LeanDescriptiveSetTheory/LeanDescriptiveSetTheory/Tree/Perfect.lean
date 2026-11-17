/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.Splitting
import Tengoku.Seed.Data.List.GetD
import Tengoku.Seed.Topology.Compactness.Compact
import Tengoku.Seed.Topology.Homeomorph.Lemmas
import Tengoku.Seed.Topology.Separation.Hausdorff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cantor branches through perfect trees

A `BinarySplittingSystem T` determines one natural-number sequence for each Cantor point. Output
coordinate `n` is read from the coherent splitting node at binary depth `n + 1`. Strict length
growth makes that coordinate available, and coherence shows that every selected node is an exact
initial segment of the resulting sequence.

Continuity and injectivity are proved separately. Compactness of Cantor space and Hausdorffness of
Baire space are invoked only to upgrade the map to a closed embedding. Consequently the range is
closed, is homeomorphic to Cantor space, and is contained in `Tree.body T`.
-/

open Set
open Topology

namespace DescriptiveSetTheory.Tree

private theorem take_initialSegment {A : Type*} (x : ℕ → A) {m n : ℕ} (hmn : m ≤ n) :
    (initialSegment x n).take m = initialSegment x m := by
  apply List.ext_getElem
  · simp [length_initialSegment, hmn]
  · intro i hi₁ hi₂
    simp [initialSegment]

/-- Initial segments of one sequence are monotone in their lengths.
@isnad1 id=isprefix.1h4v.s4.db8309825f5f from=translated src=- shape=a5a74a5a vocab=5f4549bd
-/
theorem initialSegment_prefix {A : Type*} (x : ℕ → A) {m n : ℕ} (hmn : m ≤ n) :
    initialSegment x m <+: initialSegment x n := by
  rw [List.prefix_iff_eq_take, length_initialSegment]
  exact (take_initialSegment x hmn).symm

namespace BinarySplittingSystem

variable {T : Descriptive.tree ℕ} (S : BinarySplittingSystem T)

/-- The branch selected by a Cantor point. Coordinate `n` is read from the splitting node at
binary depth `n + 1`; the depth/length invariant makes this coordinate in range.-/
def branchMap (q : ℕ → Bool) (n : ℕ) : ℕ :=
  (S.node (initialSegment q (n + 1))).getD n 0

private theorem branchMap_apply_eq_getElem_node (q : ℕ → Bool) (m : ℕ) {i : ℕ}
    (hi : i < (S.node (initialSegment q m)).length) :
    S.branchMap q i = (S.node (initialSegment q m))[i] := by
  have hdepth := S.depth_le_node_length (initialSegment q (i + 1))
  have hib : i < (S.node (initialSegment q (i + 1))).length := by
    exact (Nat.lt_succ_self i).trans_le (by simpa using hdepth)
  rw [branchMap, List.getD_eq_getElem _ _ hib]
  rcases le_total m (i + 1) with hmi | him
  · exact (S.node_prefix_of_prefix (initialSegment_prefix q hmi)).getElem hi |>.symm
  · exact (S.node_prefix_of_prefix (initialSegment_prefix q him)).getElem hib

/-- Every splitting node on a Cantor path is exactly the corresponding finite initial segment of
the selected branch.
@isnad1 id=eq.0h4v.s6.294a0a819120 from=translated src=- shape=3a4a24b8 vocab=7536ff3f
-/
theorem node_eq_initialSegment_branchMap (q : ℕ → Bool) (m : ℕ) :
    S.node (initialSegment q m) =
      initialSegment (S.branchMap q) (S.node (initialSegment q m)).length := by
  apply List.ext_getElem
  · simp [length_initialSegment]
  · intro i hi₁ hi₂
    simpa [initialSegment] using (S.branchMap_apply_eq_getElem_node q m hi₁).symm

/-- At binary depth `m`, the first `m` branch coordinates are the first `m` coordinates of the
corresponding splitting node.
@isnad1 id=eq.0h4v.s6.27c24811fb89 from=translated src=- shape=f977a4ac vocab=d8dbf8fa
-/
theorem initialSegment_branchMap_eq_take (q : ℕ → Bool) (m : ℕ) :
    initialSegment (S.branchMap q) m = (S.node (initialSegment q m)).take m := by
  have hdepth : m ≤ (S.node (initialSegment q m)).length := by
    simpa using S.depth_le_node_length (initialSegment q m)
  calc
    initialSegment (S.branchMap q) m =
        (initialSegment (S.branchMap q) (S.node (initialSegment q m)).length).take m :=
      (take_initialSegment (S.branchMap q) hdepth).symm
    _ = (S.node (initialSegment q m)).take m := by
      rw [← S.node_eq_initialSegment_branchMap q m]

/-- Every selected Cantor branch belongs to the original tree body.
@isnad1 id=mem.0h3v.s6.9729e0dbf412 from=translated src=- shape=620b7773 vocab=cf6b4693
-/
theorem branchMap_mem_body (q : ℕ → Bool) : S.branchMap q ∈ body T := by
  intro m
  rw [S.initialSegment_branchMap_eq_take q m]
  exact Descriptive.Tree.take_mem ⟨S.node (initialSegment q m), S.node_mem _⟩

/-- The range of the Cantor branch map is contained in the original tree body.
@isnad1 id=le.0h2v.s6.7e2fb852bcfc from=translated src=- shape=2e50e233 vocab=fd4429d0
-/
theorem range_branchMap_subset_body : range S.branchMap ⊆ body T := by
  rintro _ ⟨q, rfl⟩
  exact S.branchMap_mem_body q

/-- The Cantor branch map is continuous. Each output coordinate factors through one finite binary
prefix.
@isnad1 id=continuo.0h2v.s6.90358e2788ea from=translated src=- shape=cdd190bd vocab=d28d2e99
-/
theorem continuous_branchMap : Continuous S.branchMap := by
  apply continuous_pi
  intro n
  change Continuous ((fun r : Fin (n + 1) → Bool =>
      (S.node (List.ofFn r)).getD n 0) ∘
    (fun q : ℕ → Bool => fun i : Fin (n + 1) => q i))
  exact continuous_of_discreteTopology.comp
    (continuous_pi fun i => continuous_apply (i : ℕ))

private theorem initialSegments_comparable {A : Type*} (x : ℕ → A) (m n : ℕ) :
    initialSegment x m <+: initialSegment x n ∨
      initialSegment x n <+: initialSegment x m := by
  rcases le_total m n with h | h
  · exact Or.inl (initialSegment_prefix x h)
  · exact Or.inr (initialSegment_prefix x h)

/-- Distinct Cantor paths select distinct branches.
@isnad1 id=injectiv.0h2v.s6.b92b20309a02 from=translated src=- shape=cdd190bd vocab=5c1d04e0
-/
theorem injective_branchMap : Function.Injective S.branchMap := by
  intro q r hqr
  have hsegments : ∀ n, initialSegment q n = initialSegment r n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hbit : q n = r n := by
          by_contra hbit
          have hinc := S.children_incompatible_of_ne (initialSegment q n) hbit
          have hqnode := S.node_eq_initialSegment_branchMap q (n + 1)
          have hrnode := S.node_eq_initialSegment_branchMap r (n + 1)
          rw [initialSegment_succ] at hqnode
          rw [initialSegment_succ, ← ih] at hrnode
          have hcomp :
              S.node (initialSegment q n ++ [q n]) <+:
                  S.node (initialSegment q n ++ [r n]) ∨
                S.node (initialSegment q n ++ [r n]) <+:
                  S.node (initialSegment q n ++ [q n]) := by
            rw [hqnode, hrnode, hqr]
            exact initialSegments_comparable _ _ _
          exact hcomp.elim hinc.1 hinc.2
        simp [initialSegment_succ, ih, hbit]
  funext n
  have h := hsegments (n + 1)
  rw [initialSegment_succ, initialSegment_succ, hsegments n] at h
  simpa using List.append_cancel_left h

/-- The Cantor branch map is a closed embedding into Baire space. Compactness of Cantor space and
Hausdorffness of Baire space are used here, separately from continuity and injectivity.
@isnad1 id=isclosed.0h2v.s6.1ae7d13e2a03 from=translated src=- shape=cdd190bd vocab=2b462d7d
-/
theorem isClosedEmbedding_branchMap : IsClosedEmbedding S.branchMap :=
  S.continuous_branchMap.isClosedEmbedding S.injective_branchMap

/-- The Cantor branch map is a topological embedding.
@isnad1 id=isembedd.0h2v.s6.c1ba452e1502 from=translated src=- shape=cdd190bd vocab=31d504e1
-/
theorem isEmbedding_branchMap : IsEmbedding S.branchMap :=
  S.isClosedEmbedding_branchMap.isEmbedding

/-- A splitting system identifies Cantor space homeomorphically with the range of its branch map.-/
noncomputable def branchHomeomorph : (ℕ → Bool) ≃ₜ range S.branchMap :=
  S.isEmbedding_branchMap.toHomeomorph

/-- The branch-map range is closed in Baire space.
@isnad1 id=isclosed.0h2v.s6.e836848ab7a2 from=translated src=- shape=bb76c807 vocab=dc1069e3
-/
theorem isClosed_range_branchMap : IsClosed (range S.branchMap) :=
  S.isClosedEmbedding_branchMap.isClosed_range

end BinarySplittingSystem

/-- Every perfect natural-number tree contains a closed embedded Cantor copy in its body. This is
the theorem-level constructor; the choice-dependent splitting system remains existential.
@isnad1 id=ex.1h1v.s7.0303d15e969d from=translated src=- shape=b5a8b452 vocab=fbe78dfb
-/
theorem IsPerfectTree.exists_isClosedEmbedding_cantor {T : Descriptive.tree ℕ}
    (hT : IsPerfectTree T) :
    ∃ f : (ℕ → Bool) → (ℕ → ℕ), IsClosedEmbedding f ∧ range f ⊆ body T := by
  rcases hT.exists_binarySplittingSystem with ⟨S⟩
  exact ⟨S.branchMap, S.isClosedEmbedding_branchMap, S.range_branchMap_subset_body⟩

end DescriptiveSetTheory.Tree
