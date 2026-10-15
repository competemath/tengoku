/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock3Vars0to3
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `0`.
/--
@isnad1 id=siintgoa.0h2v.s5.aa4e6c0ac18f from=translated src=- shape=27f1885d vocab=dcc52f2c
-/
theorem siIntGoal_block3_var0 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨0, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `1`.
/--
@isnad1 id=siintgoa.0h2v.s5.64af093eb5a2 from=translated src=- shape=27f1885d vocab=02ec7c07
-/
theorem siIntGoal_block3_var1 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨1, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `2`.
/--
@isnad1 id=siintgoa.0h2v.s5.d062184f16ea from=translated src=- shape=27f1885d vocab=65748ffe
-/
theorem siIntGoal_block3_var2 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨2, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `3`.
/--
@isnad1 id=siintgoa.0h2v.s5.09de6d391b0f from=translated src=- shape=27f1885d vocab=d393bd73
-/
theorem siIntGoal_block3_var3 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨3, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
