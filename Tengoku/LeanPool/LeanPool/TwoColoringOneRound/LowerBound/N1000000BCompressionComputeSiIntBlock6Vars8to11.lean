/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock6Vars8to11
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `8`.
/--
@isnad1 id=siintgoa.0h2v.s5.8194b5b2fba9 from=translated src=- shape=27f1885d vocab=d757a4ab
-/
theorem siIntGoal_block6_var8 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨8, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `9`.
/--
@isnad1 id=siintgoa.0h2v.s5.0a4fffce5bb7 from=translated src=- shape=27f1885d vocab=142daf0e
-/
theorem siIntGoal_block6_var9 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨9, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `10`.
/--
@isnad1 id=siintgoa.0h2v.s5.72ae7c0a3581 from=translated src=- shape=27f1885d vocab=ebdf21d1
-/
theorem siIntGoal_block6_var10 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨10, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `6` and variable `11`.
/--
@isnad1 id=siintgoa.0h2v.s5.566bfd9c61e8 from=translated src=- shape=27f1885d vocab=c26863a5
-/
theorem siIntGoal_block6_var11 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨6, by decide⟩ : Block)) (i := (⟨11, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
