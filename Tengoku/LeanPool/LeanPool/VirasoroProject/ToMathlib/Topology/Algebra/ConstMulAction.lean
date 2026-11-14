/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Tengoku

/-!
# LeanPool.VirasoroProject.ToMathlib.Topology.Algebra.ConstMulAction
-/

@[expose] public section
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool 
/--
@isnad1 id=continuo.0h2v.s4.ff6a0ad53792 from=translated src=- shape=b1e3a152 vocab=606f01e2
-/
lemma _root_.Tengoku.LeanPool.continuousConstSMul_of_discreteTopology (𝕜 X : Type*) [TopologicalSpace X]
    [DiscreteTopology X] [SMul 𝕜 X] :
    ContinuousConstSMul 𝕜 X :=
  ⟨fun c ↦ by continuity⟩
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)
