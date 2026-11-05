/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ProC.Subgroups.Products

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Maps between left quotients

This file defines the canonical projection \(G/L \to G/H\) for nested subgroups and proves its
formula, continuity, surjectivity, functoriality, and compatibility with the quotient action.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.ProC

universe u v

open InverseSystems

/--
The natural projection \(G/K \to G/H\) for closed subgroups K \(\leq\) H is viewed as a
quotient-space map on left cosets.-/
def leftQuotientProjection
    {G : Type u} [Group G] (K H : Subgroup G) (hKH : K ≤ H) :
    G ⧸ K → G ⧸ H :=
  Quotient.map' id <| by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact hKH hab

variable {G : Type u} [Group G]

/--
The projection on left quotients sends the class of \(g\) modulo \(K\) to the class of \(g\)
modulo \(H\).
@isnad1 id=eq.1h4v.s5.d96e1dddde78 from=translated src=- shape=ef757083 vocab=e13328a5
-/
@[simp] theorem leftQuotientProjection_mk
    (K H : Subgroup G) (hKH : K ≤ H) (g : G) :
    leftQuotientProjection K H hKH (QuotientGroup.mk (s := K) g) =
      QuotientGroup.mk (s := H) g := by
  rfl

/-- The natural map between nested left quotients is continuous.
@isnad1 id=continuo.1h3v.s6.d755feba8adf from=translated src=- shape=5522b86e vocab=01d5be4e
-/
theorem continuous_leftQuotientProjection
    [TopologicalSpace G]
    (K H : Subgroup G) (hKH : K ≤ H) :
    Continuous (leftQuotientProjection K H hKH : G ⧸ K → G ⧸ H) := by
  refine (QuotientGroup.isQuotientMap_mk K).continuous_iff.2 ?_
  change Continuous (QuotientGroup.mk (s := H) : G → G ⧸ H)
  exact QuotientGroup.continuous_mk

/-- The left-quotient projection to itself is the identity.
@isnad1 id=eq.0h2v.s5.bd6db108ea34 from=translated src=- shape=5fa42b42 vocab=17fec4e5
-/
@[simp] theorem leftQuotientProjection_id
    (K : Subgroup G) :
    leftQuotientProjection K K le_rfl = id := by
  funext x
  refine Quotient.inductionOn x ?_
  intro g
  rfl

/-- Left-quotient projections compose along chains of subgroup inclusions.
@isnad1 id=eq.2h4v.s6.167003ee3a6e from=translated src=- shape=98f967d9 vocab=80a4e0d6
-/
@[simp] theorem leftQuotientProjection_comp
    (K H L : Subgroup G) (hKH : K ≤ H) (hHL : H ≤ L) :
    leftQuotientProjection H L hHL ∘ leftQuotientProjection K H hKH =
      leftQuotientProjection K L (hKH.trans hHL) := by
  funext x
  refine Quotient.inductionOn x ?_
  intro g
  rfl

/--
Applying the projection map to a completed element returns its corresponding finite-stage
coordinate.
@isnad1 id=eq.2h5v.s6.4cfafa9f534e from=translated src=- shape=8a3ab31d vocab=8aa7bb14
-/
@[simp] theorem leftQuotientProjection_comp_apply
    (K H L : Subgroup G) (hKH : K ≤ H) (hHL : H ≤ L) (x : G ⧸ K) :
    leftQuotientProjection H L hHL (leftQuotientProjection K H hKH x) =
      leftQuotientProjection K L (hKH.trans hHL) x := by
  exact congrFun (leftQuotientProjection_comp (K := K) (H := H) (L := L) hKH hHL) x

/-- Symmetric pointwise form of the composition law for left-quotient projections.
@isnad1 id=eq.2h5v.s6.42645849e0d7 from=translated src=- shape=2700d3cb vocab=8aa7bb14
-/
theorem leftQuotientProjection_comp_apply_symm
    (K H L : Subgroup G) (hKH : K ≤ H) (hHL : H ≤ L) (x : G ⧸ K) :
    leftQuotientProjection K L (hKH.trans hHL) x =
      leftQuotientProjection H L hHL (leftQuotientProjection K H hKH x) := by
  exact (leftQuotientProjection_comp_apply (K := K) (H := H) (L := L) hKH hHL x).symm

/-- The natural map between nested left quotients is surjective.
@isnad1 id=surjecti.1h3v.s5.94b85f5f5561 from=translated src=- shape=fa321e03 vocab=1134d0c3
-/
theorem surjective_leftQuotientProjection
    (K H : Subgroup G) (hKH : K ≤ H) :
    Function.Surjective (leftQuotientProjection K H hKH : G ⧸ K → G ⧸ H) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro g
  exact ⟨QuotientGroup.mk (s := K) g, rfl⟩

/-- Left-quotient projections are equivariant for the ambient left action of G.
@isnad1 id=eq.1h5v.s7.19846abcb398 from=translated src=- shape=e29ada55 vocab=f329617d
-/
@[simp] theorem leftQuotientProjection_smul
    (K H : Subgroup G) (hKH : K ≤ H) (g : G) (x : G ⧸ K) :
    leftQuotientProjection K H hKH (g • x) =
      g • leftQuotientProjection K H hKH x := by
  refine Quotient.inductionOn x ?_
  intro y
  rfl

end ProCGroups.ProC
