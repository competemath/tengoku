/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock4Vars8to11
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `8`.
/--
@isnad1 id=siintgoa.0h2v.s5.056e768ddaa5 from=translated src=- shape=27f1885d vocab=07cd437f
-/
theorem siIntGoal_block4_var8 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨8, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `9`.
/--
@isnad1 id=siintgoa.0h2v.s5.88aae068f193 from=translated src=- shape=27f1885d vocab=484597f0
-/
theorem siIntGoal_block4_var9 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨9, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `10`.
/--
@isnad1 id=siintgoa.0h2v.s5.79c4d8d4a930 from=translated src=- shape=27f1885d vocab=6fbfc1e8
-/
theorem siIntGoal_block4_var10 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨10, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `11`.
/--
@isnad1 id=siintgoa.0h2v.s5.f60dec4e74ab from=translated src=- shape=27f1885d vocab=5af7207a
-/
theorem siIntGoal_block4_var11 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨11, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
