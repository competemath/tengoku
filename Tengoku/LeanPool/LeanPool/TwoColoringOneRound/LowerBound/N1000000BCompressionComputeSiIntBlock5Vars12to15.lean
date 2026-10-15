/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock5Vars12to15
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `12`.
/--
@isnad1 id=siintgoa.0h2v.s5.6f1c3d789930 from=translated src=- shape=27f1885d vocab=a88b64de
-/
theorem siIntGoal_block5_var12 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨12, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `13`.
/--
@isnad1 id=siintgoa.0h2v.s5.e5b2d2d7a39b from=translated src=- shape=27f1885d vocab=e153584c
-/
theorem siIntGoal_block5_var13 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨13, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `14`.
/--
@isnad1 id=siintgoa.0h2v.s5.bd3c58f4ae36 from=translated src=- shape=27f1885d vocab=fd997d62
-/
theorem siIntGoal_block5_var14 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨14, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `15`.
/--
@isnad1 id=siintgoa.0h2v.s5.af877761d974 from=translated src=- shape=27f1885d vocab=b7780461
-/
theorem siIntGoal_block5_var15 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨15, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
