/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock1Vars8to11
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `8`.
/--
@isnad1 id=siintgoa.0h2v.s5.f43ccbcc22f4 from=translated src=- shape=27f1885d vocab=96db0563
-/
theorem siIntGoal_block1_var8 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨8, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `9`.
/--
@isnad1 id=siintgoa.0h2v.s5.eb30aeb4affe from=translated src=- shape=27f1885d vocab=284cb30f
-/
theorem siIntGoal_block1_var9 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨9, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `10`.
/--
@isnad1 id=siintgoa.0h2v.s5.b66f9cf6650d from=translated src=- shape=27f1885d vocab=552f344c
-/
theorem siIntGoal_block1_var10 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨10, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `11`.
/--
@isnad1 id=siintgoa.0h2v.s5.8e56ae908088 from=translated src=- shape=27f1885d vocab=43893d35
-/
theorem siIntGoal_block1_var11 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨11, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
