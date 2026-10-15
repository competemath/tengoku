/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0Vars0to3
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `0`.
/--
@isnad1 id=siintgoa.0h2v.s5.ebd1ee40b0c2 from=translated src=- shape=27f1885d vocab=acce4fb5
-/
theorem siIntGoal_block0_var0 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨0, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `1`.
/--
@isnad1 id=siintgoa.0h2v.s5.2a8734016430 from=translated src=- shape=27f1885d vocab=cd9e2ba4
-/
theorem siIntGoal_block0_var1 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨1, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `2`.
/--
@isnad1 id=siintgoa.0h2v.s5.4ee20ca7b7b7 from=translated src=- shape=27f1885d vocab=ca79d97b
-/
theorem siIntGoal_block0_var2 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨2, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `3`.
/--
@isnad1 id=siintgoa.0h2v.s5.c38c4df8dabf from=translated src=- shape=27f1885d vocab=335115bc
-/
theorem siIntGoal_block0_var3 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨3, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
