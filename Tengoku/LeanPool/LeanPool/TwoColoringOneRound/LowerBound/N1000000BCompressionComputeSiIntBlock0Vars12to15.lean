/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0Vars12to15
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `12`.
/--
@isnad1 id=siintgoa.0h2v.s5.4b6d24453bdf from=translated src=- shape=27f1885d vocab=41553eec
-/
theorem siIntGoal_block0_var12 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨12, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `13`.
/--
@isnad1 id=siintgoa.0h2v.s5.4627df2e9cc5 from=translated src=- shape=27f1885d vocab=3e2c4210
-/
theorem siIntGoal_block0_var13 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨13, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `14`.
/--
@isnad1 id=siintgoa.0h2v.s5.33ec293ee757 from=translated src=- shape=27f1885d vocab=47dd6f6d
-/
theorem siIntGoal_block0_var14 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨14, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `15`.
/--
@isnad1 id=siintgoa.0h2v.s5.cec3088fbb8c from=translated src=- shape=27f1885d vocab=3af5e998
-/
theorem siIntGoal_block0_var15 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨15, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
