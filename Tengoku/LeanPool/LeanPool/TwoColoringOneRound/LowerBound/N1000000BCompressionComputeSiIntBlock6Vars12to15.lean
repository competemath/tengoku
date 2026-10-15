/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock6Vars12to15
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `12`.
/--
@isnad1 id=siintgoa.0h2v.s5.897a567e9cf2 from=translated src=- shape=27f1885d vocab=6391f48f
-/
theorem siIntGoal_block6_var12 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨12, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `13`.
/--
@isnad1 id=siintgoa.0h2v.s5.48ac9579c2b2 from=translated src=- shape=27f1885d vocab=5173ce2b
-/
theorem siIntGoal_block6_var13 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨13, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `14`.
/--
@isnad1 id=siintgoa.0h2v.s5.547b8e2f674a from=translated src=- shape=27f1885d vocab=b991c827
-/
theorem siIntGoal_block6_var14 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨14, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `15`.
/--
@isnad1 id=siintgoa.0h2v.s5.34acf373eb07 from=translated src=- shape=27f1885d vocab=1d18f44a
-/
theorem siIntGoal_block6_var15 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨15, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
