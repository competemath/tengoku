/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntGoal
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionComputeSiIntBlock0Vars16to19
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `16`.
/--
@isnad1 id=siintgoa.0h2v.s5.7ac3b9f530fd from=translated src=- shape=27f1885d vocab=b055670e
-/
theorem siIntGoal_block0_var16 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨16, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `17`.
/--
@isnad1 id=siintgoa.0h2v.s5.1975926a2618 from=translated src=- shape=27f1885d vocab=9542af17
-/
theorem siIntGoal_block0_var17 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨17, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `18`.
/--
@isnad1 id=siintgoa.0h2v.s5.4e56f58fb287 from=translated src=- shape=27f1885d vocab=bc98034b
-/
theorem siIntGoal_block0_var18 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨18, by decide⟩ : Var)) p q := by
  decide +kernel

-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `0` and variable `19`.
/--
@isnad1 id=siintgoa.0h2v.s5.a6754c24869d from=translated src=- shape=27f1885d vocab=1ccc69a9
-/
theorem siIntGoal_block0_var19 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨0, by decide⟩ : Block)) (i := (⟨19, by decide⟩ : Var)) p q := by
  decide +kernel

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
