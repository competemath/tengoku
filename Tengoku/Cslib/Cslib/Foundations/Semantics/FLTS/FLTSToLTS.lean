/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Tengoku.Cslib.Cslib.Foundations.Semantics.FLTS.Basic
public import Tengoku.Cslib.Cslib.Foundations.Semantics.LTS.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Converting from `FLTS` to `LTS` -/

@[expose] public section

variable {State Label : Type*}

namespace Cslib.FLTS

/-- `FLTS` is a special case of `LTS`.-/
@[scoped grind =]
def toLTS (flts : FLTS State Label) : LTS State Label where
  Tr s1 μ s2 := flts.tr s1 μ = s2

instance : Coe (FLTS State Label) (LTS State Label) where
  coe := toLTS

/-- `FLTS.toLTS` correctly characterises transitions.
@isnad1 id=iff.0h6v.s5.8ad24cc7fd57 from=translated src=- shape=2e1f3445 vocab=ccc7ca8d
-/
@[scoped grind =]
theorem toLTS_tr {flts : FLTS State Label} {s1 : State} {μ : Label} {s2 : State} :
  flts.toLTS.Tr s1 μ s2 ↔ flts.tr s1 μ = s2 := by rfl

open LTS LTS.MTr in
/-- Characterisation of multistep transitions.
@isnad1 id=iff.0h6v.s5.77f018a95414 from=translated src=- shape=2d178f78 vocab=a3043853
-/
@[scoped grind =]
theorem toLTS_mtr {flts : FLTS State Label} {s1 : State} {μs : List Label} {s2 : State} :
    flts.toLTS.MTr s1 μs s2 ↔ flts.mtr s1 μs = s2 := by
  have : ∀ μ, flts.toLTS.Tr s1 μ (flts.tr s1 μ) := by grind
  constructor <;> intro h
  case mp => induction h <;> grind
  case mpr => induction μs generalizing s1 <;> grind

end Cslib.FLTS
