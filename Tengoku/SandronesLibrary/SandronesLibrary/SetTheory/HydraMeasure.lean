/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Hydra
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Ordinal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A first ordinal measure for the finite hydra

This file assigns a finite ordinal to every finite hydra and proves strict
decrease for the complete class of cuts whose head is attached to the root.
Deeper cuts can replicate a subtree, so this elementary measure is deliberately
not presented as a ranking for every `Hydra.Step`.
-/

namespace SandronesLibrary.SetTheory.Hydra

/-- The number of nodes in a finite hydra, including its root.-/
def nodeCount : Hydra → Nat
  | .node children => 1 + (children.map nodeCount).sum

/-- The elementary ordinal interpretation regards the finite node count as a
finite ordinal.  It is useful for non-regrowing root cuts, but is not the
Kirby--Paris ordinal assignment for arbitrary regrowing cuts.-/
def ordinalMeasure (h : Hydra) : Ordinal := nodeCount h

private theorem replaceAtWith_erase_count {α : Type*} (weight : α → Nat)
    (xs : List α) (i : Nat) (ys : List α)
    (hpositive : ∀ x, 0 < weight x)
    (hrep : replaceAtWith xs i [] = some ys) :
    (ys.map weight).sum < (xs.map weight).sum := by
  induction xs generalizing i ys with
  | nil => simp [replaceAtWith] at hrep
  | cons x xs ih =>
      cases i with
      | zero =>
          simp [replaceAtWith] at hrep
          subst ys
          simpa using hpositive x
      | succ i =>
          simp only [replaceAtWith] at hrep
          cases htail : replaceAtWith xs i [] with
          | none => simp [htail] at hrep
          | some tail =>
              simp [htail] at hrep
              subst ys
              have hlt := ih i tail htail
              simp only [List.map_cons, List.sum_cons]
              omega

/-- Every successful cut of a head immediately below the root strictly lowers
the elementary ordinal measure.  The theorem covers an arbitrary root child
index, not only the one-head example.
@isnad1 id=lt.1h4v.s5.a7e4bcbed67e from=translated src=- shape=8b1b828c vocab=c7b825c3
-/
theorem ordinalMeasure_decreases_root_cut (stage i : Nat) (before after : Hydra)
    (hcut : chop stage before [i] = some after) :
    ordinalMeasure after < ordinalMeasure before := by
  cases before with
  | node children =>
      simp only [chop] at hcut
      cases hchild : children[i]? with
      | none => simp [hchild] at hcut
      | some child =>
          simp only [hchild] at hcut
          cases child with
          | node grandchildren =>
              cases grandchildren with
              | nil =>
                  cases hrep : replaceAtWith children i [] with
                  | none => simp [hrep] at hcut
                  | some remaining =>
                      rw [hrep] at hcut
                      change some (.node remaining) = some after at hcut
                      injection hcut with hafter
                      subst after
                      have hsum := replaceAtWith_erase_count nodeCount children i remaining
                        (fun h => by cases h; simp [nodeCount]) hrep
                      have hnat : 1 + (remaining.map nodeCount).sum <
                          1 + (children.map nodeCount).sum := by omega
                      simp only [ordinalMeasure, nodeCount]
                      exact (Nat.cast_lt (α := Ordinal)).2 hnat
              | cons grandchild grandchildren => simp at hcut

/--
> **Entry**: settheory.googology.hydra-root-cut-measure
> **一句话**: 以节点数对应的有限序数解释 Hydra 时，任意根旁叶头的合法删除都会使该序数严格下降。
> **依赖**: `settheory.googology.hydra-game-step`、`settheory.ordinal.no-infinite-descent`
> **mathlib**: 自然数到序数的保序嵌入

This is a local descent theorem for non-regrowing root cuts.  It does not say
that deeper regrowing cuts decrease this elementary measure, nor does it claim
termination of every play.
@isnad1 id=lt.0h1v.s4.56e17f96c7c6 from=translated src=- shape=b322a921 vocab=a30b0c13
-/
theorem single_head_ordinal_descent (stage : Nat) :
    ordinalMeasure (.node []) < ordinalMeasure (.node [head]) := by
  exact ordinalMeasure_decreases_root_cut stage 0 (.node [head]) (.node [])
    (chop_single_head stage)

end SandronesLibrary.SetTheory.Hydra
