/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock4Vars4to7
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `4`.
/--
@isnad1 id=siintgoa.0h2v.s5.f630c9d05d59 from=translated src=- shape=27f1885d vocab=b157831d
-/
theorem siIntGoal_block4_var4 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨4, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `5`.
/--
@isnad1 id=siintgoa.0h2v.s5.bea8d43bece8 from=translated src=- shape=27f1885d vocab=2b95cc27
-/
theorem siIntGoal_block4_var5 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨5, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `6`.
/--
@isnad1 id=siintgoa.0h2v.s5.248a9c4a6758 from=translated src=- shape=27f1885d vocab=e7d20e58
-/
theorem siIntGoal_block4_var6 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨6, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `7`.
/--
@isnad1 id=siintgoa.0h2v.s5.576bd286dfe0 from=translated src=- shape=27f1885d vocab=bf9a4160
-/
theorem siIntGoal_block4_var7 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨7, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
