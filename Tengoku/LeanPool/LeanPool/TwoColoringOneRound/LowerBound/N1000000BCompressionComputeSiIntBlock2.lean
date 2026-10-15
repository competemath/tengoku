/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock2Vars0to3
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock2Vars12to15
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock2Vars16to19
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock2Vars20to22
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock2Vars4to7
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock2Vars8to11
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock2
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

/--
@isnad1 id=siintgoa.0h3v.s5.554587301d5f from=translated src=- shape=1455bddf vocab=39c0f7c8
-/
theorem siIntGoal_block2 :
    ∀ i : Var, ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := i) p q := by
  intro i p q
  fin_cases i
  · simpa using (siIntGoal_block2_var0 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var1 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var2 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var3 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var4 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var5 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var6 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var7 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var8 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var9 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var10 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var11 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var12 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var13 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var14 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var15 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var16 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var17 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var18 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var19 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var20 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var21 (p := p) (q := q))
  · simpa using (siIntGoal_block2_var22 (p := p) (q := q))

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
