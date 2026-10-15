/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock3Vars8to11
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `8`.
/--
@isnad1 id=siintgoa.0h2v.s5.49e9be77d321 from=translated src=- shape=27f1885d vocab=e75aacde
-/
theorem siIntGoal_block3_var8 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨8, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `9`.
/--
@isnad1 id=siintgoa.0h2v.s5.e7b8d5e47917 from=translated src=- shape=27f1885d vocab=bb16ea37
-/
theorem siIntGoal_block3_var9 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨9, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `10`.
/--
@isnad1 id=siintgoa.0h2v.s5.d43afa1d23df from=translated src=- shape=27f1885d vocab=ca15eaec
-/
theorem siIntGoal_block3_var10 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨10, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `11`.
/--
@isnad1 id=siintgoa.0h2v.s5.6cba464f58f1 from=translated src=- shape=27f1885d vocab=7207ff70
-/
theorem siIntGoal_block3_var11 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨11, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
