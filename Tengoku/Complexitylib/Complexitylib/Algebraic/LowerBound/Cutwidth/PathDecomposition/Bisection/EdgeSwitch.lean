/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.EdgeSwitch.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.EdgeSwitch.Internal

/-!
# One step of Monien--Preis normalization

Both normalization moves replace `a-b` and `c-d` with `a-c` and `b-d`.
If no helpful set of at most eleven vertices exists, the local configurations
provide distinct endpoints and ensure the new edges are absent. The switch
preserves degrees, outside neighbors, and the cut and boundary of the side.

Reversing a switch loses helpfulness only when the moved set selects exactly
`a,c` or exactly `b,d` among the four endpoints. Otherwise helpfulness does
not decrease; it can increase. In the two exceptional cases a bounded
extension compensates for the loss: at most two added vertices for a
boundary-pair switch, and at most four for a three-boundary-neighbor switch.
Every nontrivial extension completes an originally partly selected `a-b` pair.

These are local statements. `BoundaryNormalization` and `NeighborNormalization`
iterate the two phases and bound their combined reverse extension independently
of the number of switches.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection

open scoped Classical

variable {W : Type} [Fintype W] (H : SimpleGraph W) {a b c d : W}

/-- A valid switch preserves each vertex degree.
@isnad1 id=eq.1h7v.s6.86d8281f0f08 from=translated src=- shape=8f217f35 vocab=94f9bb4f
-/
theorem switchEdges_degree (valid : Switchable H a b c d) (v : W) :
    (switchEdges H a b c d).degree v = H.degree v :=
  Internal.switchEdges_degree H valid v

/-- In particular, regularity is preserved.
@isnad1 id=isregula.2h7v.s6.24f07f512d16 from=translated src=- shape=9b84dcd3 vocab=46b498b8
-/
theorem switchEdges_regular (valid : Switchable H a b c d) {k : Nat}
    (regular : H.IsRegularOfDegree k) : (switchEdges H a b c d).IsRegularOfDegree k :=
  fun v => (switchEdges_degree H valid v).trans (regular.degree_eq v)

/-- Switching edges within one side does not change that side's cut.
@isnad1 id=eq.4h7v.s6.df0e1098eb27 from=translated src=- shape=a1099fc5 vocab=287be7f5
-/
theorem switchEdges_cut {S : Finset W} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hd : d ∈ S) :
    (switchEdges H a b c d).cutFinset S = H.cutFinset S :=
  Internal.switchEdges_cut H ha hb hc hd

/-- Every vertex retains exactly the same neighbors outside the side.
@isnad1 id=eq.4h8v.s7.415755d22e5a from=translated src=- shape=d13bc21d vocab=4b5bb514
-/
theorem switchEdges_neighbors_outside {S : Finset W} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hd : d ∈ S) (v : W) :
    (switchEdges H a b c d).neighborFinset v \ S = H.neighborFinset v \ S :=
  Internal.switchEdges_neighbors_outside H ha hb hc hd v

/-- The boundary vertex set is unchanged.
@isnad1 id=eq.4h7v.s6.9b61b1506be6 from=translated src=- shape=1a6356d4 vocab=a082c7b3
-/
theorem switchEdges_boundary {S : Finset W} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hd : d ∈ S) :
    cutBoundary (switchEdges H a b c d) S = cutBoundary H S :=
  Internal.switchEdges_boundary H ha hb hc hd

/-- Exact helpfulness change, expressed using the four membership indicators.
@isnad1 id=eq.6h8v.s8.a686e55c50e1 from=translated src=- shape=75aa502a vocab=bbc35ba5
-/
theorem helpfulness_switchEdges (valid : Switchable H a b c d)
    {S X : Finset W} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hX : X ⊆ S) :
    helpfulness (switchEdges H a b c d) S X = helpfulness H S X +
      2 * ((if a ∈ X then (1 : ℤ) else 0) - (if d ∈ X then 1 else 0)) *
        ((if c ∈ X then 1 else 0) - (if b ∈ X then 1 else 0)) :=
  Internal.helpfulness_switchEdges H valid ha hb hc hd hX

/-- Apart from the two exceptional membership patterns, reversing a switch
does not decrease helpfulness; it may strictly improve it.
@isnad1 id=le.8h8v.s7.8608c71d8897 from=translated src=- shape=f96957bb vocab=314b8f28
-/
theorem helpfulness_reverse_switch_le (valid : Switchable H a b c d)
    {S X : Finset W} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hX : X ⊆ S)
    (notAC : ¬ (a ∈ X ∧ c ∈ X ∧ b ∉ X ∧ d ∉ X))
    (notBD : ¬ (b ∈ X ∧ d ∈ X ∧ a ∉ X ∧ c ∉ X)) :
    helpfulness (switchEdges H a b c d) S X ≤ helpfulness H S X :=
  Internal.helpfulness_reverse_switch_le H valid ha hb hc hd hX notAC notBD

/-- Reverse a boundary-pair switch by adding at most two vertices without
losing helpfulness. Any enlargement completes a pair with exactly one old endpoint;
only `a`, `b`, and `c` may be added.
@isnad1 id=ex.8h8v.s8.b6a397e6dee2 from=translated src=- shape=1a026202 vocab=5a49eeee
-/
theorem exists_restore_boundary_switch (valid : Switchable H a b c d)
    {S X : Finset W} (degree : ∀ v ∈ S, H.degree v ≤ 3)
    (ha : a ∈ cutBoundary H S) (hb : b ∈ cutBoundary H S)
    (hc : c ∈ S) (hd : d ∈ S) (bc : H.Adj b c) (hX : X ⊆ S) :
    ∃ Y, X ⊆ Y ∧ Y ⊆ S ∧ Y.card ≤ X.card + 2 ∧
      helpfulness (switchEdges H a b c d) S X ≤ helpfulness H S Y ∧
      (Y = X ∨ (a ∈ Y ∧ b ∈ Y ∧ ((a ∈ X ∧ b ∉ X) ∨ (b ∈ X ∧ a ∉ X)))) ∧
      Y ⊆ insert c (insert a (insert b X)) :=
  Internal.exists_restore_boundary_switch H valid degree ha hb hc hd bc hX

/-- Reverse a switch removing a three-boundary-neighbor configuration by
adding at most four vertices. Every enlargement completes a partly selected pair.
Only `a`, `c`, and boundary neighbors of `a` may be added; if `a` was already
selected, only `b` is needed.
@isnad1 id=ex.9h8v.s9.995e6a2bac7c from=translated src=- shape=1de5847f vocab=74dae486
-/
theorem exists_restore_three_neighbor_switch (valid : Switchable H a b c d)
    {S X : Finset W} (degree : ∀ v ∈ S, H.degree v ≤ 3)
    (ha : a ∈ S) (hb : b ∈ cutBoundary H S) (hc : c ∈ S \ cutBoundary H S)
    (hd : d ∈ S) (bc : H.Adj b c)
    (three : (H.neighborFinset a ∩ cutBoundary H S).card = 3) (hX : X ⊆ S) :
    ∃ Y, X ⊆ Y ∧ Y ⊆ S ∧ Y.card ≤ X.card + 4 ∧
      helpfulness (switchEdges H a b c d) S X ≤ helpfulness H S Y ∧
      (Y = X ∨ (a ∈ Y ∧ b ∈ Y ∧ ((a ∈ X ∧ b ∉ X) ∨ (b ∈ X ∧ a ∉ X)))) ∧
      (a ∈ X → Y ⊆ insert b X) ∧
      Y ⊆ insert c (insert a (X ∪ (H.neighborFinset a ∩ cutBoundary H S))) :=
  Internal.exists_restore_three_neighbor_switch H valid degree ha hb hc hd bc three hX

/-- A remaining boundary edge admits the first normalization switch unless
there is already a helpful set of at most eleven vertices.
@isnad1 id=ex.5h5v.s8.d734211046d8 from=translated src=- shape=e3296c4e vocab=1852e7c1
-/
theorem exists_boundary_switch {S : Finset W} (regular : H.IsRegularOfDegree 3)
    (noHelpful : ∀ X ⊆ S, X.card ≤ 11 → helpfulness H S X ≤ 0)
    {a b : W} (ha : a ∈ cutBoundary H S) (hb : b ∈ cutBoundary H S) (ab : H.Adj a b) :
    ∃ c d, Switchable H a b c d ∧ H.Adj b c ∧
      c ∈ S \ cutBoundary H S ∧ d ∈ S \ cutBoundary H S ∧
      (H.neighborFinset c ∩ cutBoundary H S).card ≤ 2 ∧
      (H.neighborFinset d ∩ cutBoundary H S).card ≤ 1 :=
  Internal.exists_boundary_switch H regular noHelpful ha hb ab

/-- A vertex with three boundary neighbors admits the second normalization
switch unless a helpful set of at most eleven vertices already exists.
@isnad1 id=ex.6h5v.s8.cccdfb0282fe from=translated src=- shape=6c857ffa vocab=1852e7c1
-/
theorem exists_three_neighbor_switch {S : Finset W} (regular : H.IsRegularOfDegree 3)
    (noHelpful : ∀ X ⊆ S, X.card ≤ 11 → helpfulness H S X ≤ 0)
    {a b : W} (ha : a ∈ S \ cutBoundary H S) (hb : b ∈ cutBoundary H S)
    (ab : H.Adj a b) (three : (H.neighborFinset a ∩ cutBoundary H S).card = 3) :
    ∃ c d, Switchable H a b c d ∧ H.Adj b c ∧
      c ∈ S \ cutBoundary H S ∧ d ∈ S \ cutBoundary H S ∧
      (H.neighborFinset c ∩ cutBoundary H S).card ≤ 2 ∧
      (H.neighborFinset d ∩ cutBoundary H S).card ≤ 1 :=
  Internal.exists_three_neighbor_switch H regular noHelpful ha hb ab three

end Algebraic.Cutwidth.Bisection
