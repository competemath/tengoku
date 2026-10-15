/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock1Vars16to19
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `16`.
/--
@isnad1 id=siintgoa.0h2v.s5.cf301cfcd4a1 from=translated src=- shape=27f1885d vocab=d5cbaec5
-/
theorem siIntGoal_block1_var16 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨16, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `17`.
/--
@isnad1 id=siintgoa.0h2v.s5.a34332ec7a67 from=translated src=- shape=27f1885d vocab=45692e6b
-/
theorem siIntGoal_block1_var17 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨17, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `18`.
/--
@isnad1 id=siintgoa.0h2v.s5.9f004e14f782 from=translated src=- shape=27f1885d vocab=e9fb3f44
-/
theorem siIntGoal_block1_var18 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨18, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `19`.
/--
@isnad1 id=siintgoa.0h2v.s5.4bec16020f52 from=translated src=- shape=27f1885d vocab=b081a3fb
-/
theorem siIntGoal_block1_var19 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨19, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
