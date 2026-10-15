/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock5Vars4to7
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `4`.
/--
@isnad1 id=siintgoa.0h2v.s5.cd476686266b from=translated src=- shape=27f1885d vocab=d5de7984
-/
theorem siIntGoal_block5_var4 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨4, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `5`.
/--
@isnad1 id=siintgoa.0h2v.s5.b5f4954cb69f from=translated src=- shape=27f1885d vocab=517185f0
-/
theorem siIntGoal_block5_var5 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨5, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `6`.
/--
@isnad1 id=siintgoa.0h2v.s5.0a18841cac99 from=translated src=- shape=27f1885d vocab=ef87a84a
-/
theorem siIntGoal_block5_var6 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨6, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `7`.
/--
@isnad1 id=siintgoa.0h2v.s5.fed93f432d74 from=translated src=- shape=27f1885d vocab=ac9b47e5
-/
theorem siIntGoal_block5_var7 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨7, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
