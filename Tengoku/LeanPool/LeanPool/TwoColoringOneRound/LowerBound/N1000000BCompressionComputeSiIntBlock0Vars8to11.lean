/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0Vars8to11
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `8`.
/--
@isnad1 id=siintgoa.0h2v.s5.44b13d0c8ff6 from=translated src=- shape=27f1885d vocab=1f7bfb2e
-/
theorem siIntGoal_block0_var8 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨8, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `9`.
/--
@isnad1 id=siintgoa.0h2v.s5.7c3fcdc7f639 from=translated src=- shape=27f1885d vocab=d32a0034
-/
theorem siIntGoal_block0_var9 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨9, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `10`.
/--
@isnad1 id=siintgoa.0h2v.s5.95fcc94e60f6 from=translated src=- shape=27f1885d vocab=705679c7
-/
theorem siIntGoal_block0_var10 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨10, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `11`.
/--
@isnad1 id=siintgoa.0h2v.s5.675ee910bca7 from=translated src=- shape=27f1885d vocab=cae233d9
-/
theorem siIntGoal_block0_var11 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨11, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
