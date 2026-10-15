/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock5Vars20to22
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `20`.
/--
@isnad1 id=siintgoa.0h2v.s5.bb858c9f2f99 from=translated src=- shape=27f1885d vocab=38eae40d
-/
theorem siIntGoal_block5_var20 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨20, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `21`.
/--
@isnad1 id=siintgoa.0h2v.s5.50d462abeb65 from=translated src=- shape=27f1885d vocab=bdcf6d89
-/
theorem siIntGoal_block5_var21 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨21, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `22`.
/--
@isnad1 id=siintgoa.0h2v.s5.3aeb6991d7f9 from=translated src=- shape=27f1885d vocab=aa06f3c9
-/
theorem siIntGoal_block5_var22 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨22, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
