/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock2Vars12to15
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `12`.
/--
@isnad1 id=siintgoa.0h2v.s5.85fbd5780ed6 from=translated src=- shape=27f1885d vocab=8235647c
-/
theorem siIntGoal_block2_var12 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨12, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `13`.
/--
@isnad1 id=siintgoa.0h2v.s5.6df62e729b7a from=translated src=- shape=27f1885d vocab=49751861
-/
theorem siIntGoal_block2_var13 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨13, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `14`.
/--
@isnad1 id=siintgoa.0h2v.s5.bcf6ab342483 from=translated src=- shape=27f1885d vocab=4f1b8655
-/
theorem siIntGoal_block2_var14 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨14, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `15`.
/--
@isnad1 id=siintgoa.0h2v.s5.78517a1b716e from=translated src=- shape=27f1885d vocab=838ac333
-/
theorem siIntGoal_block2_var15 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨15, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
