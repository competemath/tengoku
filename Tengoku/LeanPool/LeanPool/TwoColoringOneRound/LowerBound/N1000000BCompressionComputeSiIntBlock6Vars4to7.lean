/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock6Vars4to7
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `4`.
/--
@isnad1 id=siintgoa.0h2v.s5.466981b51f1f from=translated src=- shape=27f1885d vocab=93616376
-/
theorem siIntGoal_block6_var4 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨4, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `5`.
/--
@isnad1 id=siintgoa.0h2v.s5.91f14589fa8a from=translated src=- shape=27f1885d vocab=845a7d75
-/
theorem siIntGoal_block6_var5 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨5, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `6`.
/--
@isnad1 id=siintgoa.0h2v.s5.e2200ab03b96 from=translated src=- shape=27f1885d vocab=eab5cbb3
-/
theorem siIntGoal_block6_var6 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨6, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `7`.
/--
@isnad1 id=siintgoa.0h2v.s5.53d7788a6c74 from=translated src=- shape=27f1885d vocab=76535075
-/
theorem siIntGoal_block6_var7 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨7, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
