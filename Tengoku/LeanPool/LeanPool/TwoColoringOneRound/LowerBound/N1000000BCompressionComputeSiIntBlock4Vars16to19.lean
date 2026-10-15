/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock4Vars16to19
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `16`.
/--
@isnad1 id=siintgoa.0h2v.s5.3c083c5b6e10 from=translated src=- shape=27f1885d vocab=eb8bfb8d
-/
theorem siIntGoal_block4_var16 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨16, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `17`.
/--
@isnad1 id=siintgoa.0h2v.s5.9e936fef23cd from=translated src=- shape=27f1885d vocab=d31d8f4c
-/
theorem siIntGoal_block4_var17 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨17, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `18`.
/--
@isnad1 id=siintgoa.0h2v.s5.049a101f054c from=translated src=- shape=27f1885d vocab=3737d7f9
-/
theorem siIntGoal_block4_var18 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨18, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `19`.
/--
@isnad1 id=siintgoa.0h2v.s5.99d13db7e7eb from=translated src=- shape=27f1885d vocab=3dcb9b08
-/
theorem siIntGoal_block4_var19 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨19, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
