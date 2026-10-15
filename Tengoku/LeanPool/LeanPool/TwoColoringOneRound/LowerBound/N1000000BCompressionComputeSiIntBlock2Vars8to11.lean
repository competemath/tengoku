/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock2Vars8to11
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `8`.
/--
@isnad1 id=siintgoa.0h2v.s5.ebad9bf67857 from=translated src=- shape=27f1885d vocab=3ff1d7d5
-/
theorem siIntGoal_block2_var8 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨8, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `9`.
/--
@isnad1 id=siintgoa.0h2v.s5.7e4b7145c25b from=translated src=- shape=27f1885d vocab=14120e09
-/
theorem siIntGoal_block2_var9 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨9, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `10`.
/--
@isnad1 id=siintgoa.0h2v.s5.fc67273de9f7 from=translated src=- shape=27f1885d vocab=63c1b083
-/
theorem siIntGoal_block2_var10 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨10, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `11`.
/--
@isnad1 id=siintgoa.0h2v.s5.57239a253779 from=translated src=- shape=27f1885d vocab=1399ddce
-/
theorem siIntGoal_block2_var11 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨11, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
