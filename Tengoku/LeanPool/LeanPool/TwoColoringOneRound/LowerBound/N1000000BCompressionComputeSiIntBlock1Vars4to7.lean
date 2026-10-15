/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock1Vars4to7
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `4`.
/--
@isnad1 id=siintgoa.0h2v.s5.52eebb7197af from=translated src=- shape=27f1885d vocab=cc6c9cdf
-/
theorem siIntGoal_block1_var4 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨4, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `5`.
/--
@isnad1 id=siintgoa.0h2v.s5.65776a73412c from=translated src=- shape=27f1885d vocab=f4eb72af
-/
theorem siIntGoal_block1_var5 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨5, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `6`.
/--
@isnad1 id=siintgoa.0h2v.s5.ad985f26f4eb from=translated src=- shape=27f1885d vocab=e3cb9523
-/
theorem siIntGoal_block1_var6 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨6, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `1` and variable `7`.
/--
@isnad1 id=siintgoa.0h2v.s5.7d9185f045f7 from=translated src=- shape=27f1885d vocab=8a353cc5
-/
theorem siIntGoal_block1_var7 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨1, by decide⟩ : Block)) (i := (⟨7, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
