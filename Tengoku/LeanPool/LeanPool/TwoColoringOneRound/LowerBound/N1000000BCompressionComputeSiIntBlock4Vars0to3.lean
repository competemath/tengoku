/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock4Vars0to3
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `0`.
/--
@isnad1 id=siintgoa.0h2v.s5.d8e241fddd73 from=translated src=- shape=27f1885d vocab=5d3acdd4
-/
theorem siIntGoal_block4_var0 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨0, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `1`.
/--
@isnad1 id=siintgoa.0h2v.s5.1e9f1a161104 from=translated src=- shape=27f1885d vocab=c1d18d55
-/
theorem siIntGoal_block4_var1 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨1, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `2`.
/--
@isnad1 id=siintgoa.0h2v.s5.ef413b69d544 from=translated src=- shape=27f1885d vocab=2706bddd
-/
theorem siIntGoal_block4_var2 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨2, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `3`.
/--
@isnad1 id=siintgoa.0h2v.s5.ac587a14f2a6 from=translated src=- shape=27f1885d vocab=79a21d62
-/
theorem siIntGoal_block4_var3 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨3, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
