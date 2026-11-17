import Tengoku.PaperCLean.PaperC.Combinatorics.PinnedGraphResolution
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Data.Finset.Card

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 800000

/-!
# Terminal component count

This file formalizes the elementary combinatorial conclusion in
Proposition 9.11.  Suppose a family has `B - s` components, every component
has at least two vertices, and altogether they use at most `2B` vertices.
Every component larger than two consumes at least one unit of the `2s`
excess budget.  Consequently at most `2s` components are large and at
least `B - 3s` components have size exactly two.

The statement is deliberately independent of the graph model: it applies
to any finite family equipped with a size function, and hence directly to
the supports of connected components.
-/

namespace PaperC
namespace TerminalComponentCount

open Finset

variable {ι : Type*}

/-- Components in the family whose support has exactly two vertices.-/
def pairComponents
    (components : Finset ι) (size : ι → ℕ) : Finset ι :=
  components.filter fun C ↦ size C = 2

/-- Components in the family whose support has more than two vertices.-/
def largeComponents
    (components : Finset ι) (size : ι → ℕ) : Finset ι :=
  components.filter fun C ↦ 3 ≤ size C

/--
@isnad1 id=iff.0h4v.s5.f6b5a5627c83 from=translated src=- shape=31d18f46 vocab=db117a1f
-/
@[simp]
theorem mem_pairComponents
    {components : Finset ι} {size : ι → ℕ} {C : ι} :
    C ∈ pairComponents components size ↔
      C ∈ components ∧ size C = 2 := by
  simp [pairComponents]

/--
@isnad1 id=iff.0h4v.s5.e48b37b78ecc from=translated src=- shape=7b93ae7a vocab=ca610519
-/
@[simp]
theorem mem_largeComponents
    {components : Finset ι} {size : ι → ℕ} {C : ι} :
    C ∈ largeComponents components size ↔
      C ∈ components ∧ 3 ≤ size C := by
  simp [largeComponents]

/--
Every component has size two or at least three, so these two filtered
families partition a family whose members all have size at least two.
@isnad1 id=eq.1h3v.s5.68f7c35b9897 from=translated src=- shape=01b567ed vocab=3e0d1abb
-/
theorem pair_union_large_eq
    [DecidableEq ι]
    {components : Finset ι} {size : ι → ℕ}
    (hsize : ∀ C ∈ components, 2 ≤ size C) :
    pairComponents components size ∪
        largeComponents components size =
      components := by
  ext C
  simp only [pairComponents, largeComponents, mem_union, mem_filter]
  constructor
  · rintro (⟨hC, _⟩ | ⟨hC, _⟩) <;> exact hC
  · intro hC
    have htwo := hsize C hC
    by_cases heq : size C = 2
    · exact Or.inl ⟨hC, heq⟩
    · exact Or.inr ⟨hC, by omega⟩

/-- The two classes in the preceding partition are disjoint.
@isnad1 id=disjoint.0h3v.s4.b32042cef428 from=translated src=- shape=1a836b8d vocab=afa5ddb4
-/
theorem disjoint_pairComponents_largeComponents
    [DecidableEq ι]
    (components : Finset ι) (size : ι → ℕ) :
    Disjoint
      (pairComponents components size)
      (largeComponents components size) := by
  rw [Finset.disjoint_left]
  intro C hpair hlarge
  rw [mem_pairComponents] at hpair
  rw [mem_largeComponents] at hlarge
  omega

/--
The vertex budget bounds the number of components larger than two.

We use `components.card + s = B`, the cancellation-safe natural-number
form of `components.card = B - s`.
@isnad1 id=le.3h5v.s6.e0a8faeb9f8f from=translated src=- shape=9b380328 vocab=9c11c316
-/
theorem card_largeComponents_le_two_mul
    {components : Finset ι} {size : ι → ℕ} {B s : ℕ}
    (hcard : components.card + s = B)
    (hsize : ∀ C ∈ components, 2 ≤ size C)
    (hbudget : (∑ C ∈ components, size C) ≤ 2 * B) :
    (largeComponents components size).card ≤ 2 * s := by
  have hpoint :
      ∀ C ∈ components,
        2 + (if 3 ≤ size C then 1 else 0) ≤ size C := by
    intro C hC
    by_cases hlarge : 3 ≤ size C
    · simp [hlarge]
    · have htwo := hsize C hC
      simp [hlarge]
      omega
  have hsum :
      (∑ C ∈ components,
          (2 + (if 3 ≤ size C then 1 else 0))) ≤
        ∑ C ∈ components, size C :=
    Finset.sum_le_sum fun C hC ↦ hpoint C hC
  have hindicator :
      (∑ C ∈ components, (if 3 ≤ size C then 1 else 0)) =
        (largeComponents components size).card := by
    classical
    rw [largeComponents,
      Finset.card_eq_sum_ite (Finset.filter_subset _ _)]
    apply Finset.sum_congr rfl
    intro C hC
    simp [hC]
  have hexcess :
      2 * components.card +
          (largeComponents components size).card ≤
        2 * B := by
    calc
      2 * components.card +
            (largeComponents components size).card =
          ∑ C ∈ components,
            (2 + (if 3 ≤ size C then 1 else 0)) := by
              rw [Finset.sum_add_distrib]
              simp [hindicator, Nat.mul_comm]
      _ ≤ ∑ C ∈ components, size C := hsum
      _ ≤ 2 * B := hbudget
  omega

/--
Proposition 9.11, terminal-population combinatorics: at least `B - 3s`
members of the family are isolated two-vertex components.
@isnad1 id=le.3h5v.s6.a2a49a6e57cf from=translated src=- shape=2ef7c9b0 vocab=07e681da
-/
theorem card_pairComponents_ge_sub_three_mul
    [DecidableEq ι]
    {components : Finset ι} {size : ι → ℕ} {B s : ℕ}
    (hcard : components.card + s = B)
    (hsize : ∀ C ∈ components, 2 ≤ size C)
    (hbudget : (∑ C ∈ components, size C) ≤ 2 * B) :
    B - 3 * s ≤ (pairComponents components size).card := by
  have hlarge :=
    card_largeComponents_le_two_mul hcard hsize hbudget
  have hpartition :=
    Finset.card_union_of_disjoint
      (disjoint_pairComponents_largeComponents components size)
  rw [pair_union_large_eq hsize] at hpartition
  omega

/--
Bundled form of the two numerical conclusions used to define the terminal
population in Proposition 9.11.
@isnad1 id=and.3h5v.s7.604033e64a86 from=translated src=- shape=aefdc5c1 vocab=2310a5bf
-/
theorem terminal_component_count
    [DecidableEq ι]
    {components : Finset ι} {size : ι → ℕ} {B s : ℕ}
    (hcard : components.card + s = B)
    (hsize : ∀ C ∈ components, 2 ≤ size C)
    (hbudget : (∑ C ∈ components, size C) ≤ 2 * B) :
    (largeComponents components size).card ≤ 2 * s ∧
      B - 3 * s ≤ (pairComponents components size).card :=
  ⟨card_largeComponents_le_two_mul hcard hsize hbudget,
    card_pairComponents_ge_sub_three_mul hcard hsize hbudget⟩

/--
Literal `c = B - s` form of the terminal-component conclusion.  The
side-condition `s ≤ B` records the range in which natural subtraction
agrees with the manuscript's integer calculation.
@isnad1 id=and.4h5v.s7.4ab40f9bb859 from=translated src=- shape=0eb08db5 vocab=d28e7608
-/
theorem terminal_component_count_of_card_eq_sub
    [DecidableEq ι]
    {components : Finset ι} {size : ι → ℕ} {B s : ℕ}
    (hsB : s ≤ B)
    (hcard : components.card = B - s)
    (hsize : ∀ C ∈ components, 2 ≤ size C)
    (hbudget : (∑ C ∈ components, size C) ≤ 2 * B) :
    (largeComponents components size).card ≤ 2 * s ∧
      B - 3 * s ≤ (pairComponents components size).card := by
  apply terminal_component_count (B := B) (s := s)
  · omega
  · exact hsize
  · exact hbudget

/-!
## Connected-component specialization
-/

/--
Graph-facing form of the terminal component count.  Here `size C` is the
literal cardinality of the support of the connected component `C`.
@isnad1 id=and.3h5v.s8.fda34991d15e from=translated src=- shape=034b2e1d vocab=aeaf3f2e
-/
theorem connectedComponent_terminal_count
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {components : Finset G.ConnectedComponent} {B s : ℕ}
    (hcard : components.card + s = B)
    (hsize :
      ∀ C ∈ components, 2 ≤ Fintype.card C.supp)
    (hbudget :
      (∑ C ∈ components, Fintype.card C.supp) ≤ 2 * B) :
    (largeComponents components
          (fun C ↦ Fintype.card C.supp)).card ≤ 2 * s ∧
      B - 3 * s ≤
        (pairComponents components
          (fun C ↦ Fintype.card C.supp)).card := by
  classical
  exact terminal_component_count hcard hsize hbudget

end TerminalComponentCount
end PaperC
