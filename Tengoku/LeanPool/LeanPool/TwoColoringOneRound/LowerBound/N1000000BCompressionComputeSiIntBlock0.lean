/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0Vars0to3
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0Vars12to15
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0Vars16to19
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0Vars20to22
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0Vars4to7
import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0Vars8to11
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

/--
@isnad1 id=siintgoa.0h3v.s5.8b855957981a from=translated src=- shape=1455bddf vocab=36b55ad9
-/
theorem siIntGoal_block0 :
    ∀ i : Var, ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := i) p q := by
  intro i p q
  fin_cases i
  · simpa using (siIntGoal_block0_var0 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var1 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var2 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var3 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var4 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var5 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var6 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var7 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var8 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var9 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var10 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var11 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var12 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var13 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var14 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var15 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var16 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var17 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var18 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var19 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var20 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var21 (p := p) (q := q))
  · simpa using (siIntGoal_block0_var22 (p := p) (q := q))

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
