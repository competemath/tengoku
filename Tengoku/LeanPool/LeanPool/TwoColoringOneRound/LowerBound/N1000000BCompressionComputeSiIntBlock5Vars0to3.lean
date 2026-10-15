/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock5Vars0to3
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `0`.
/--
@isnad1 id=siintgoa.0h2v.s5.50d324e2f6d8 from=translated src=- shape=27f1885d vocab=b4ce5827
-/
theorem siIntGoal_block5_var0 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨0, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `1`.
/--
@isnad1 id=siintgoa.0h2v.s5.eab3b23b8743 from=translated src=- shape=27f1885d vocab=5a124269
-/
theorem siIntGoal_block5_var1 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨1, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `2`.
/--
@isnad1 id=siintgoa.0h2v.s5.2b785b0e639d from=translated src=- shape=27f1885d vocab=8e606140
-/
theorem siIntGoal_block5_var2 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨2, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `3`.
/--
@isnad1 id=siintgoa.0h2v.s5.8828ca4f785e from=translated src=- shape=27f1885d vocab=838a78eb
-/
theorem siIntGoal_block5_var3 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨3, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
