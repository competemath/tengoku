/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0Vars20to22
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `20`.
/--
@isnad1 id=siintgoa.0h2v.s5.69184ef9d065 from=translated src=- shape=27f1885d vocab=cb4673cb
-/
theorem siIntGoal_block0_var20 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨20, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `21`.
/--
@isnad1 id=siintgoa.0h2v.s5.5ffc16b37f82 from=translated src=- shape=27f1885d vocab=45cb584f
-/
theorem siIntGoal_block0_var21 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨21, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `22`.
/--
@isnad1 id=siintgoa.0h2v.s5.c80ab8c9c398 from=translated src=- shape=27f1885d vocab=35b1d26c
-/
theorem siIntGoal_block0_var22 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨22, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
