/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock2Vars16to19
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `16`.
/--
@isnad1 id=siintgoa.0h2v.s5.c1b7117c2680 from=translated src=- shape=27f1885d vocab=d685dd6c
-/
theorem siIntGoal_block2_var16 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨16, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `17`.
/--
@isnad1 id=siintgoa.0h2v.s5.4325f316b87b from=translated src=- shape=27f1885d vocab=891ff4ce
-/
theorem siIntGoal_block2_var17 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨17, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `18`.
/--
@isnad1 id=siintgoa.0h2v.s5.6c9187e7d890 from=translated src=- shape=27f1885d vocab=892f9336
-/
theorem siIntGoal_block2_var18 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨18, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `19`.
/--
@isnad1 id=siintgoa.0h2v.s5.14761c5c399a from=translated src=- shape=27f1885d vocab=464a5c21
-/
theorem siIntGoal_block2_var19 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨19, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
