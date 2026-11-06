/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Tengoku.Seed.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Tengoku.Seed.AlgebraicGeometry.PullbackCarrier
public import Tengoku.Seed.Topology.Maps.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dominance under open base change

The range of a pullback projection is the inverse image of the range of the
other morphism. Since an open map pulls dense sets back to dense sets,
base change along an open morphism preserves dominance.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Base change along a morphism with open underlying map preserves dominance.
@isnad1 id=isdomina.1h5v.s7.e6f34f9a3b07 from=translated src=- shape=0bf6bf4a vocab=bf35ad84
-/
lemma isDominant_pullback_fst_of_isOpenMap {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (hf : IsOpenMap f) [IsDominant g] :
    IsDominant (pullback.fst f g) := by
  rw [isDominant_iff, DenseRange, Scheme.Pullback.range_fst]
  exact g.denseRange.preimage hf

end AlgebraicGeometry
