/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeS0IntBlock3
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- This proof is a large `decide` check; we increase `maxHeartbeats` to avoid timeouts.
/--
@isnad1 id=s0intgoa.0h2v.s4.38ddef17c500 from=translated src=- shape=88530bb6 vocab=22e58ef7
-/
theorem s0IntGoal_block3 :
    ∀ p q : Fin 3, S0IntGoal (r := (⟨3, by decide⟩ : Block)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
