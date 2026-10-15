/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock6Vars0to3
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `0`.
/--
@isnad1 id=siintgoa.0h2v.s5.4143335f4190 from=translated src=- shape=27f1885d vocab=692dcbcf
-/
theorem siIntGoal_block6_var0 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨0, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `1`.
/--
@isnad1 id=siintgoa.0h2v.s5.491c81c8ff9b from=translated src=- shape=27f1885d vocab=3a434619
-/
theorem siIntGoal_block6_var1 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨1, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `2`.
/--
@isnad1 id=siintgoa.0h2v.s5.70d62f35bcc9 from=translated src=- shape=27f1885d vocab=dcd18b9b
-/
theorem siIntGoal_block6_var2 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨2, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `3`.
/--
@isnad1 id=siintgoa.0h2v.s5.3abe10abb8f8 from=translated src=- shape=27f1885d vocab=2b581887
-/
theorem siIntGoal_block6_var3 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨3, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
