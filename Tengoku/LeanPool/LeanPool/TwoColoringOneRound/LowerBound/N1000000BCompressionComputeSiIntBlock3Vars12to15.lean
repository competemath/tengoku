/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock3Vars12to15
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `12`.
/--
@isnad1 id=siintgoa.0h2v.s5.3434a2632feb from=translated src=- shape=27f1885d vocab=ff610ffc
-/
theorem siIntGoal_block3_var12 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨12, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `13`.
/--
@isnad1 id=siintgoa.0h2v.s5.5c2d16e8e600 from=translated src=- shape=27f1885d vocab=17bbc847
-/
theorem siIntGoal_block3_var13 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨13, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `14`.
/--
@isnad1 id=siintgoa.0h2v.s5.ef56cdb54509 from=translated src=- shape=27f1885d vocab=2cf286a3
-/
theorem siIntGoal_block3_var14 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨14, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `15`.
/--
@isnad1 id=siintgoa.0h2v.s5.0adfc9500351 from=translated src=- shape=27f1885d vocab=8542db16
-/
theorem siIntGoal_block3_var15 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨15, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
