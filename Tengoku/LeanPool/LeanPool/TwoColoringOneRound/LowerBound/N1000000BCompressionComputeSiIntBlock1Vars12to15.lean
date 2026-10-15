/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock1Vars12to15
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `12`.
/--
@isnad1 id=siintgoa.0h2v.s5.a447adcacb21 from=translated src=- shape=27f1885d vocab=dbfb3569
-/
theorem siIntGoal_block1_var12 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨12, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `13`.
/--
@isnad1 id=siintgoa.0h2v.s5.a5ce156bc263 from=translated src=- shape=27f1885d vocab=3a1b49cc
-/
theorem siIntGoal_block1_var13 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨13, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `14`.
/--
@isnad1 id=siintgoa.0h2v.s5.eb21e5903ed5 from=translated src=- shape=27f1885d vocab=d41bae72
-/
theorem siIntGoal_block1_var14 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨14, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `15`.
/--
@isnad1 id=siintgoa.0h2v.s5.c88849864fa2 from=translated src=- shape=27f1885d vocab=4f825077
-/
theorem siIntGoal_block1_var15 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨15, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
