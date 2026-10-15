/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock6Vars16to19
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `16`.
/--
@isnad1 id=siintgoa.0h2v.s5.d10539b8cb51 from=translated src=- shape=27f1885d vocab=06c2544a
-/
theorem siIntGoal_block6_var16 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨16, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `17`.
/--
@isnad1 id=siintgoa.0h2v.s5.3329fee5928f from=translated src=- shape=27f1885d vocab=7d342fd8
-/
theorem siIntGoal_block6_var17 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨17, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `18`.
/--
@isnad1 id=siintgoa.0h2v.s5.c133309e56dc from=translated src=- shape=27f1885d vocab=3b04b432
-/
theorem siIntGoal_block6_var18 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨18, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `19`.
/--
@isnad1 id=siintgoa.0h2v.s5.85dfe2ebc5e3 from=translated src=- shape=27f1885d vocab=0c225ff8
-/
theorem siIntGoal_block6_var19 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨19, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
