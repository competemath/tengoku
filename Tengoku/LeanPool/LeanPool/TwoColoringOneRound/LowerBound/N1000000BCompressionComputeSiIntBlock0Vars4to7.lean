/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0Vars4to7
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `4`.
/--
@isnad1 id=siintgoa.0h2v.s5.758914f87022 from=translated src=- shape=27f1885d vocab=ad2d2c05
-/
theorem siIntGoal_block0_var4 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨4, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `5`.
/--
@isnad1 id=siintgoa.0h2v.s5.333bfd640140 from=translated src=- shape=27f1885d vocab=81606855
-/
theorem siIntGoal_block0_var5 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨5, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `6`.
/--
@isnad1 id=siintgoa.0h2v.s5.8bad4c5a19fe from=translated src=- shape=27f1885d vocab=78e4c4cf
-/
theorem siIntGoal_block0_var6 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨6, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `7`.
/--
@isnad1 id=siintgoa.0h2v.s5.04edd50cbd5b from=translated src=- shape=27f1885d vocab=4ec5db6c
-/
theorem siIntGoal_block0_var7 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨7, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
