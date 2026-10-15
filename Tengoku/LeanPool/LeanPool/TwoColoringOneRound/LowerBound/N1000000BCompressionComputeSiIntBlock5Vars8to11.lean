/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock5Vars8to11
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `8`.
/--
@isnad1 id=siintgoa.0h2v.s5.f19677164ab4 from=translated src=- shape=27f1885d vocab=b0db66ef
-/
theorem siIntGoal_block5_var8 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨8, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `9`.
/--
@isnad1 id=siintgoa.0h2v.s5.2f171ec066d5 from=translated src=- shape=27f1885d vocab=51a28bfc
-/
theorem siIntGoal_block5_var9 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨9, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `10`.
/--
@isnad1 id=siintgoa.0h2v.s5.e8a1e171d2b6 from=translated src=- shape=27f1885d vocab=1d1e1e37
-/
theorem siIntGoal_block5_var10 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨10, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `11`.
/--
@isnad1 id=siintgoa.0h2v.s5.94374bfe26da from=translated src=- shape=27f1885d vocab=bcc461a3
-/
theorem siIntGoal_block5_var11 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨11, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
