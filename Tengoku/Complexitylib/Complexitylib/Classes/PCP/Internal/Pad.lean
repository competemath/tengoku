/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.ConstraintGraph

/-!
# Padding a constraint graph with isolated vertices

The expander family built by the zig-zag tower supplies graphs only at certain
sizes, far apart from one another. Rather than fold a large expander onto an
arbitrary vertex count — which costs a delicate spectral argument — one can
enlarge the constraint graph instead, up to the next size the family offers.

Nothing is lost by doing so. The added vertices carry no edges, and every
quantity the amplification tracks is counted over *edges*: the number of edges
is unchanged, an assignment matters only through its values on the original
vertices, and so both the unsatisfiability value and satisfiability are
untouched.

## Main definitions

- `Complexity.ConstraintGraph.pad` — the same graph on more vertices

## Main results

- `Complexity.ConstraintGraph.numEdges_pad`, `unsatVal_pad`,
  `satisfiable_pad_iff` — padding changes nothing that matters
-/

@[expose] public section

namespace Complexity

namespace ConstraintGraph

variable {α : Type}

/-- The same constraint graph, on `N ≥ numVerts` vertices; the extra ones carry
no edges. -/
def pad (G : ConstraintGraph α) (N : ℕ) (h : G.numVerts ≤ N) : ConstraintGraph α where
  numVerts := N
  numEdges := G.numEdges
  tail := fun e => Fin.castLE h (G.tail e)
  head := fun e => Fin.castLE h (G.head e)
  rel := G.rel

/--
@isnad1 id=eq.1h3v.s4.ccdc31dada7c from=translated src=- shape=64875ba3 vocab=1258feea
-/
@[simp] theorem numEdges_pad (G : ConstraintGraph α) (N : ℕ) (h : G.numVerts ≤ N) :
    (G.pad N h).numEdges = G.numEdges := rfl

/--
@isnad1 id=eq.1h3v.s4.f2fe028eb912 from=translated src=- shape=e1eb7450 vocab=dd80264b
-/
@[simp] theorem numVerts_pad (G : ConstraintGraph α) (N : ℕ) (h : G.numVerts ≤ N) :
    (G.pad N h).numVerts = N := rfl

/-- Restricting an assignment of the padded graph to the original vertices. -/
def restrict (G : ConstraintGraph α) {N : ℕ} (h : G.numVerts ≤ N)
    (a : (G.pad N h).Assignment) : G.Assignment :=
  fun v => a (Fin.castLE h v)

/-- Extending an assignment to the padded graph, arbitrarily on the new
vertices. -/
noncomputable def extend [Nonempty α] (G : ConstraintGraph α) {N : ℕ}
    (h : G.numVerts ≤ N) (a : G.Assignment) : (G.pad N h).Assignment :=
  fun v => if hv : v.val < G.numVerts then a ⟨v.val, hv⟩ else Classical.arbitrary α

/--
@isnad1 id=eq.1h4v.s5.acba2a415ebd from=translated src=- shape=137837c4 vocab=85acf18d
-/
theorem restrict_extend [Nonempty α] (G : ConstraintGraph α) {N : ℕ} (h : G.numVerts ≤ N)
    (a : G.Assignment) : G.restrict h (G.extend h a) = a := by
  funext v
  rw [restrict, extend]
  exact dite_eq_left v.isLt

/--
@isnad1 id=iff.1h5v.s5.7b2a72723f6c from=translated src=- shape=f8520733 vocab=b10d8136
-/
theorem satisfies_pad_iff (G : ConstraintGraph α) {N : ℕ} (h : G.numVerts ≤ N)
    (a : (G.pad N h).Assignment) (e : Fin (G.pad N h).numEdges) :
    (G.pad N h).Satisfies a e ↔ G.Satisfies (G.restrict h a) e := Iff.rfl

/--
@isnad1 id=eq.1h4v.s5.3106e710f3b7 from=translated src=- shape=06660526 vocab=06a51507
-/
theorem unsatEdges_pad (G : ConstraintGraph α) {N : ℕ} (h : G.numVerts ≤ N)
    (a : (G.pad N h).Assignment) :
    (G.pad N h).unsatEdges a = G.unsatEdges (G.restrict h a) := rfl

/--
@isnad1 id=eq.1h4v.s5.1453a9cb11f4 from=translated src=- shape=1fdab40e vocab=5795271a
-/
theorem unsatFrac_pad (G : ConstraintGraph α) {N : ℕ} (h : G.numVerts ≤ N)
    (a : (G.pad N h).Assignment) :
    (G.pad N h).unsatFrac a = G.unsatFrac (G.restrict h a) := rfl

/-- **Padding does not change the value.**
@isnad1 id=eq.1h3v.s5.2f05e32dea5f from=translated src=- shape=94b0da98 vocab=cd85a961
-/
theorem unsatVal_pad [Fintype α] [Nonempty α] (G : ConstraintGraph α)
    (N : ℕ) (h : G.numVerts ≤ N) :
    (G.pad N h).unsatVal = G.unsatVal := by
  classical
  refine le_antisymm (Finset.le_inf' _ _ fun b _ => ?_) (Finset.le_inf' _ _ fun a _ => ?_)
  · have hle := Finset.inf'_le (G.pad N h).unsatFrac (Finset.mem_univ (G.extend h b))
    rw [unsatFrac_pad, restrict_extend] at hle
    exact hle
  · rw [unsatFrac_pad]
    exact Finset.inf'_le G.unsatFrac (Finset.mem_univ _)

/-- **Padding does not change satisfiability.**
@isnad1 id=iff.1h3v.s4.8d6ed72d6476 from=translated src=- shape=abbeb3fc vocab=41dd1661
-/
theorem satisfiable_pad_iff [Nonempty α] (G : ConstraintGraph α) (N : ℕ)
    (h : G.numVerts ≤ N) :
    (G.pad N h).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨G.restrict h a, fun e => (G.satisfies_pad_iff h a e).1 (ha e)⟩
  · rintro ⟨b, hb⟩
    refine ⟨G.extend h b, fun e => ?_⟩
    rw [satisfies_pad_iff, restrict_extend]
    exact hb e

end ConstraintGraph

end Complexity
