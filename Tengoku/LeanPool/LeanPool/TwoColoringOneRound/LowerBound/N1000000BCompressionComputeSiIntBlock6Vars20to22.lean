/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock6Vars20to22
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `20`.
/--
@isnad1 id=siintgoa.0h2v.s5.d7918b882197 from=translated src=- shape=27f1885d vocab=ae3d4373
-/
theorem siIntGoal_block6_var20 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨20, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `21`.
/--
@isnad1 id=siintgoa.0h2v.s5.83bc7fb6721a from=translated src=- shape=27f1885d vocab=f1653d0f
-/
theorem siIntGoal_block6_var21 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨21, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `22`.
/--
@isnad1 id=siintgoa.0h2v.s5.1f200ecc274c from=translated src=- shape=27f1885d vocab=87e1c699
-/
theorem siIntGoal_block6_var22 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨22, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
