/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock1Vars0to3
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `0`.
/--
@isnad1 id=siintgoa.0h2v.s5.46138e8ecc56 from=translated src=- shape=27f1885d vocab=e588c1f8
-/
theorem siIntGoal_block1_var0 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨0, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `1`.
/--
@isnad1 id=siintgoa.0h2v.s5.d231456ff03f from=translated src=- shape=27f1885d vocab=d6a0e48d
-/
theorem siIntGoal_block1_var1 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨1, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `2`.
/--
@isnad1 id=siintgoa.0h2v.s5.aeb26dbf1b25 from=translated src=- shape=27f1885d vocab=28bed4a9
-/
theorem siIntGoal_block1_var2 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨2, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `3`.
/--
@isnad1 id=siintgoa.0h2v.s5.377a69cd1a37 from=translated src=- shape=27f1885d vocab=7d81870a
-/
theorem siIntGoal_block1_var3 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨3, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
