/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
module

public import Tengoku

/-!
# Graph Theory, example sheet 1

Here are the statements (and hopefully soon proofs!) of the questions from the first example sheet
of the Cambridge Part II course Graph Theory.

If you solve a question in Lean, feel free to open a Pull Request on Github!
-/

public section

open Fintype (card)
open Function SimpleGraph
open scoped Cardinal SetRel

namespace GraphTheory
namespace ES1
variable {ι α β γ : Type*}

/-!
### Question 1

Show that a graph $$G$$ which contains an odd circuit, contains an odd cycle.
-/

/-!
### Question 2

Show there are infinitely many planar graphs for which $$e(G) = 3(|G| − 2)$$. Can you give a nice
description of all graphs that satisfy this equality?
-/

-- Planarity is hard

/-!
### Question 3

Show that every graph $$G$$, with $$|G| > 2$$, has two vertices of the same degree.
-/

lemma q3 [Fintype α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    ∃ a b, a ≠ b ∧ G.degree a = G.degree b := by
  suffices ¬Injective (fun v ↦ G.degree v) by
    obtain ⟨a, b, hab, hne⟩ :=
      (Function.not_injective_iff (f := fun v ↦ G.degree v)).mp this
    exact ⟨a, b, hne, hab⟩
  intro hdegree
  let degreeFin : α → Fin (card α) := fun v ↦ ⟨G.degree v, G.degree_lt_card_verts v⟩
  have hdegreeFin : Injective degreeFin := fun _ _ h ↦ hdegree <| congrArg Fin.val h
  have hdegreeFin_bijective : Bijective degreeFin :=
    (Fintype.bijective_iff_injective_and_card degreeFin).2 ⟨hdegreeFin, by simp⟩
  obtain ⟨a, ha⟩ := hdegreeFin_bijective.surjective ⟨0, Fintype.card_pos⟩
  obtain ⟨b, hb⟩ := hdegreeFin_bijective.surjective
    ⟨card α - 1, Nat.sub_lt Fintype.card_pos (by simp)⟩
  have ha_isolated : G.IsIsolated a := (G.degree_eq_zero a).mp <| congrArg Fin.val ha
  have hb_universal : G.IsUniversal b :=
    (G.degree_eq_card_sub_one b).mp <| congrArg Fin.val hb
  exact hb_universal.not_isIsolated a ha_isolated

/-!
### Question 4

Show that in every connected graph with $$|G| ≥ 2$$ there exists a vertex $$v$$ so that $$G − v$$ is
connected.
-/

-- This looks a bit painful as a translation. Probably better stated using connectivity on a set.

/-!
### Question 5

Show that if $$G$$ is acyclic and $$|G| ≥ 1$$, then $$e(G) ≤ n − 1$$.
-/

-- Note: The statement is true without `nonempty α` due to nat subtraction.
lemma q5 [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    G.edgeFinset.card ≤ card α - 1 := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim G ⊥]
  · classical
    obtain ⟨T, hGT, -, hT⟩ := connected_top.exists_isTree_le_of_le_of_isAcyclic le_top hG
    have h1 := Finset.card_le_card (edgeFinset_subset_edgeFinset.mpr hGT)
    have h2 := hT.card_edgeFinset
    lia

/-!
### Question 6

The degree sequence of a graph $$G = ({x_1, . . . , x_n}, E)$$ is the sequence
$$d(x_1), . . . , d(x_n)$$.
For $$n ≥ 2$$, let $$1 ≤ d_1 ≤ d_2 ≤ \dots ≤ d_n$$ be integers. Show that $$(d_i)_{i = 1}^n$$ is a
degree sequence of a tree if and only if $$\sum_{i=1}^n d_i = 2n − 2$$.
-/

/-- The finset of degrees of a finite graph. -/
def degreeSequence [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] : Multiset ℕ :=
  Finset.univ.val.map fun a ↦ G.degree a

/-!
### Question 7

Let $$T_1, \dots, T_k$$ be subtrees of a tree $$T$$. Show that if $$V(T_i) ∩ V(T_j) ≠ ∅$$ for all
$$i, j ∈ [k]$$ then $$V(T_1) ∩ \dots ∩ V(T_k) ≠ ∅$$.
-/

/-!
### Question 8

The average degree of a graph $$G = (V, E)$$ is $$n^{-1} \sum_{x ∈ V} d(x)$$. Show that if the
average degree of $$G$$ is $$d$$ then $$G$$ contains a subgraph with minimum degree $≥ d/2$$.
-/

/-- The average degree of a simple graph is the average of its degrees. -/
def averageDegree [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ :=
  ∑ a, G.degree a / card α

/-!
### Question 9

Say that a graph $$G = (V, E)$$ can be decomposed into cycles if $$E$$ can be partitioned
$$E = E_1 ∪ \dots ∪ E_k$$, where each $$E_i$$ is the edge set of a cycle. Show that $$G$$ can be
decomposed into cycles if and only if all degrees of $$G$$ are even.
-/

-- This looks painful as a translation. It will likely get better once we have Kyle's eulerian paths

/-!
### Question 10

The clique number of a graph $$G$$ is the largest $$t$$ so that $$G$$ contains a complete graph on
$$t$$ vertices.
Show that the possible clique numbers for a regular graph on $$n$$ vertices are
$$1, 2, \dots, n/2$$ and $$n$$.
-/

/-!
### Question 11

Show that the Petersen graph is non-planar.
-/

/-!
### Question 12

Let $$G = (V, E)$$ be a graph. Show that there is a partition $$V = A ∪ B$$ so all the vertices in
the graphs $$G[A]$$ and $$G[B]$$ are of even degree.
-/

-- Note: This is a bit more general than the statement, because we allow partitioning any set of
-- vertices

/-!
### Question 13

A $$m × n$$ Latin rectangle is a $$m × n$$ matrix, with each entry from $${1, . . . , n}$$, such
that no two entries in the same row or column are the same. Prove that every $$m × n$$ Latin
rectangle may be extended to a $$n × n$$ Latin square.
-/

/-- A Latin rectangle is a binary function whose transversals are all injective. -/
def IsLatin (f : α → β → γ) : Prop :=
  (∀ a, Injective (f a)) ∧ ∀ b, Injective fun a ↦ f a b

/-!
### Question 14

Let $$G = (X ∪ Y, E)$$ be a countably infinite bipartite graph with the property that
$$|N(A)| ≥ |A|$$ for all $$A ⊆ X$$. Give an example to show that $$G$$ need not contain a matching
from $$X$$ to $$Y$$ . On the other hand, show that if all of the degrees of $$G$$ are finite then
$$G$$ does contain a matching from $$X$$ to $$Y$$. Does this remain true if $$G$$ is uncountable and
all degrees of $$X$$ are finite (while degrees in $$Y$$ have no restriction)?
-/

-- This translation looks slightly painful because of the `cardinal`.

/-!
### Question 15

Let $$(X, d_X)$$ be a metric space. We say that a function $$f : X → ℝ^2$$ has distortion
$$≤ D$$ if there exists an $$r > 0$$ so that
$$rd_X(x, y) ≤ ‖f(x) − f(y)‖_2 ≤ Drd_X(x, y)$$.
Show that there is some constant $$c > 0$$ such that for all $$n$$ there is a metric space
$$M = ({x_1, \dots, x_n}, d_M)$$ on $$n$$ points so that every function $$f : M → ℝ^2$$ has
distortion $$> cn^{1/2}$$. Does there exist some constant $$c > 0$$ such that for all $$n$$ there is
a metric space $$M = ({x_1, \dots, x_n}, d_M)$$ on $$n$$ points so that every function
$$f : M → ℝ^2$$ has distortion $$> cn$$?
-/

/-- The distortion of a function `f` between metric spaces is the ratio between the maximum and
minimum of `dist (f a) (f b) / dist a b`. -/
noncomputable def distortion [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) : ℝ :=
  (⨆ (a) (b), dist (f a) (f b) / dist a b) / ⨅ (a) (b), dist (f a) (f b) / dist a b

end ES1
end GraphTheory
