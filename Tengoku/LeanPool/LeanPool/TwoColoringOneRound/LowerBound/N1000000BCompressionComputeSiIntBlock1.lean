/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock1Vars0to3
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock1Vars12to15
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock1Vars16to19
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock1Vars20to22
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock1Vars4to7
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock1Vars8to11
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock1
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

/--
@isnad1 id=siintgoa.0h3v.s5.1d45f44d1e55 from=translated src=- shape=1455bddf vocab=122aa4ea
-/
theorem siIntGoal_block1 :
    ∀ i : Var, ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := i) p q := by
  intro i p q
  fin_cases i
  · simpa using (siIntGoal_block1_var0 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var1 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var2 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var3 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var4 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var5 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var6 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var7 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var8 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var9 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var10 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var11 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var12 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var13 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var14 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var15 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var16 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var17 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var18 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var19 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var20 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var21 (p := p) (q := q))
  · simpa using (siIntGoal_block1_var22 (p := p) (q := q))

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
