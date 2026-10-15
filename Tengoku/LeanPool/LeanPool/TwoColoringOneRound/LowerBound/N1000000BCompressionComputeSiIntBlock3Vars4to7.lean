/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock3Vars4to7
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `4`.
/--
@isnad1 id=siintgoa.0h2v.s5.bde6f65478bc from=translated src=- shape=27f1885d vocab=c70fbac7
-/
theorem siIntGoal_block3_var4 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨4, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `5`.
/--
@isnad1 id=siintgoa.0h2v.s5.23919b0a728a from=translated src=- shape=27f1885d vocab=cfee8d9a
-/
theorem siIntGoal_block3_var5 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨5, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `6`.
/--
@isnad1 id=siintgoa.0h2v.s5.595eba7706fc from=translated src=- shape=27f1885d vocab=49d517f4
-/
theorem siIntGoal_block3_var6 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨6, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `7`.
/--
@isnad1 id=siintgoa.0h2v.s5.f1dc5e015515 from=translated src=- shape=27f1885d vocab=143e06da
-/
theorem siIntGoal_block3_var7 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨7, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
