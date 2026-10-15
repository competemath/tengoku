/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock2Vars4to7
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `4`.
/--
@isnad1 id=siintgoa.0h2v.s5.4212835feafe from=translated src=- shape=27f1885d vocab=41a3e568
-/
theorem siIntGoal_block2_var4 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨4, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `5`.
/--
@isnad1 id=siintgoa.0h2v.s5.3b7fdd34ca78 from=translated src=- shape=27f1885d vocab=a4a91d41
-/
theorem siIntGoal_block2_var5 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨5, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `6`.
/--
@isnad1 id=siintgoa.0h2v.s5.6159f40ad057 from=translated src=- shape=27f1885d vocab=59f3c8f2
-/
theorem siIntGoal_block2_var6 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨6, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `7`.
/--
@isnad1 id=siintgoa.0h2v.s5.6e0851122990 from=translated src=- shape=27f1885d vocab=adcff5c3
-/
theorem siIntGoal_block2_var7 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨7, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
