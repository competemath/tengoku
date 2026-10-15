/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock3Vars16to19
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `16`.
/--
@isnad1 id=siintgoa.0h2v.s5.5bb925bff951 from=translated src=- shape=27f1885d vocab=62d33f08
-/
theorem siIntGoal_block3_var16 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨16, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `17`.
/--
@isnad1 id=siintgoa.0h2v.s5.4199debb5e80 from=translated src=- shape=27f1885d vocab=1914b5db
-/
theorem siIntGoal_block3_var17 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨17, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `18`.
/--
@isnad1 id=siintgoa.0h2v.s5.8ab271ea699c from=translated src=- shape=27f1885d vocab=ed60beed
-/
theorem siIntGoal_block3_var18 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨18, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `19`.
/--
@isnad1 id=siintgoa.0h2v.s5.0d712c8b3d31 from=translated src=- shape=27f1885d vocab=925688cb
-/
theorem siIntGoal_block3_var19 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨19, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
