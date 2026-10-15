/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock4Vars12to15
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `12`.
/--
@isnad1 id=siintgoa.0h2v.s5.a2529700baab from=translated src=- shape=27f1885d vocab=0c3eb73a
-/
theorem siIntGoal_block4_var12 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨12, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `13`.
/--
@isnad1 id=siintgoa.0h2v.s5.01abc1c39f11 from=translated src=- shape=27f1885d vocab=32b38e02
-/
theorem siIntGoal_block4_var13 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨13, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `14`.
/--
@isnad1 id=siintgoa.0h2v.s5.ffd16abae561 from=translated src=- shape=27f1885d vocab=fd17eced
-/
theorem siIntGoal_block4_var14 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨14, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `15`.
/--
@isnad1 id=siintgoa.0h2v.s5.9e48349abe9f from=translated src=- shape=27f1885d vocab=14dfff4f
-/
theorem siIntGoal_block4_var15 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨15, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
