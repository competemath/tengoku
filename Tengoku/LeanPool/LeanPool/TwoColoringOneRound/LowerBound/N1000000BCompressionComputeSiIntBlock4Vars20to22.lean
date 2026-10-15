/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock4Vars20to22
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `20`.
/--
@isnad1 id=siintgoa.0h2v.s5.34189456358b from=translated src=- shape=27f1885d vocab=d6976ae8
-/
theorem siIntGoal_block4_var20 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨20, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `21`.
/--
@isnad1 id=siintgoa.0h2v.s5.e234b95c935f from=translated src=- shape=27f1885d vocab=6abbd43d
-/
theorem siIntGoal_block4_var21 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨21, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `22`.
/--
@isnad1 id=siintgoa.0h2v.s5.11a2a10e5fb6 from=translated src=- shape=27f1885d vocab=fa05d043
-/
theorem siIntGoal_block4_var22 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨22, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
