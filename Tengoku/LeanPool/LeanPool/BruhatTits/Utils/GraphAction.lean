/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Tengoku
/-!
# Definition of Graph Action

In this file we define group actions on simple graphs.

Let `G` be a group and `X` be a simple graph. Then an action of `G` on `X` is defined as an action
on the vertices of `X` that preserves the adjacency relation.

We show that a graph action induces an action on the edges.

-/

@[expose] public section

open Module

variable {V : Type*}

open SimpleGraph
section «Action»

/-- A group `G` acts as a graph action on `X`, if the adjacency relation is preserved. -/
class GraphAction (G : Type*) [Group G] [MulAction G V] (X : SimpleGraph V) where
  smul_adj_smul (g : G) (x y : V) (h : X.Adj x y) : X.Adj (g • x) (g • y)

variable (G : Type*) [Group G] [MulAction G V] (X : SimpleGraph V) [GraphAction G X]

namespace GraphAction

/--
@isnad1 id=iff.0h6v.s6.ca75c33d564d from=translated src=- shape=15340661 vocab=1c55248e
-/
@[simp]
lemma adj_iff (g : G) (x y : V) : X.Adj (g • x) (g • y) ↔ X.Adj x y := by
  constructor
  · intro h
    simpa using smul_adj_smul g⁻¹ (g • x) (g • y) h
  · exact smul_adj_smul g x y

instance : SMul G (Sym2 V) where
  smul g := Sym2.map (fun x ↦ g • x)

/--
@isnad1 id=eq.0h5v.s6.451d569b59e2 from=translated src=- shape=4645c0cf vocab=4f2ab888
-/
@[simp]
lemma smul_sym2 (g : G) (x y : V) : g • s(x, y) = s(g • x, g • y) :=
  rfl

instance : MulAction G (Sym2 V) where
  one_smul x := by
    refine Sym2.inductionOn x ?_
    intro x y
    simp
  mul_smul g h x := by
    refine Sym2.inductionOn x ?_
    intro x y
    simp [mul_smul]

instance : SMul G X.edgeSet where
  smul g e := ⟨g • e.val, by
    have := e.property
    revert this
    generalize e.val = t
    refine Sym2.inductionOn t ?_
    intro x y
    simp⟩

/--
@isnad1 id=eq.0h5v.s6.eafebc29b0cf from=translated src=- shape=08ec1db9 vocab=7d7d7c20
-/
@[simp]
lemma smul_edgeSet_coe (g : G) (e : X.edgeSet) : (g • e).val = g • e.val := rfl

/-- The action on edges induced by a graph action.
-/
instance : MulAction G X.edgeSet where
  one_smul x := by
    ext : 1
    simp
  mul_smul g x y := by
    ext : 1
    simp [mul_smul]

variable {G} {X}

/--
@isnad1 id=mem.1h5v.s6.5f6a08170a58 from=translated src=- shape=ec32759b vocab=542b0edb
-/
lemma smul_mem_smul_of (g : G) (e : Sym2 V) (x : V) (h : x ∈ e) :
    g • x ∈ g • e := by
  revert h
  refine Sym2.inductionOn e ?_
  intro a b h
  simpa using h

/--
@isnad1 id=iff.0h5v.s6.d0ae0b56af5e from=translated src=- shape=0ebf2b4d vocab=542b0edb
-/
@[simp]
lemma smul_mem_smul_iff (g : G) (e : Sym2 V) (x : V) :
    g • x ∈ g • e ↔ x ∈ e := by
  constructor
  · intro h
    simpa using smul_mem_smul_of g⁻¹ (g • e) (g • x) h
  · exact smul_mem_smul_of g e x

end GraphAction

end «Action»
