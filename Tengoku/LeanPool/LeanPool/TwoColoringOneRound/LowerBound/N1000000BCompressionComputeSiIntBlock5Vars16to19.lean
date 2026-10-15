/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock5Vars16to19
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `16`.
/--
@isnad1 id=siintgoa.0h2v.s5.b38787519eb2 from=translated src=- shape=27f1885d vocab=469b5dff
-/
theorem siIntGoal_block5_var16 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨16, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `17`.
/--
@isnad1 id=siintgoa.0h2v.s5.ba4332a673ac from=translated src=- shape=27f1885d vocab=ea559bba
-/
theorem siIntGoal_block5_var17 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨17, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `18`.
/--
@isnad1 id=siintgoa.0h2v.s5.a83d1dffa729 from=translated src=- shape=27f1885d vocab=1c28d09b
-/
theorem siIntGoal_block5_var18 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨18, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `5` and variable `19`.
/--
@isnad1 id=siintgoa.0h2v.s5.26a433551ab9 from=translated src=- shape=27f1885d vocab=8a044917
-/
theorem siIntGoal_block5_var19 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨5, by decide⟩ : Block)) (i := (⟨19, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
