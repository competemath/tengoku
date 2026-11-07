/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Tengoku.Cslib.Cslib.Foundations.Semantics.FLTS.Basic
public import Tengoku.Cslib.Cslib.Foundations.Semantics.LTS.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Converting from `LTS` to `FLTS` -/

@[expose] public section

variable {State Label : Type*}

namespace Cslib.LTS

/-- Converts an `LTS` into an `FLTS` using the subset construction.-/
@[scoped grind =]
def toFLTS (lts : LTS State Label) : FLTS (Set State) Label where
  tr := lts.setImage

/-- Characterisation of transitions in `LTS.toFLTS` wrt transitions in the original `LTS`.
@isnad1 id=iff.0h6v.s5.96d35be2df0c from=translated src=- shape=3c54fc6c vocab=11e03d7f
-/
@[scoped grind =]
theorem toFLTS_mem_tr {lts : LTS State Label} {S : Set State} {s' : State} {μ : Label} :
  s' ∈ lts.toFLTS.tr S μ ↔ ∃ s ∈ S, lts.Tr s μ s' := by
  simp only [LTS.toFLTS, LTS.setImage, Set.mem_iUnion, exists_prop]
  grind

/-- Characterisation of multistep transitions in `LTS.toFLTS` wrt multistep transitions in the
original `LTS`.
@isnad1 id=iff.0h6v.s5.2cac77838a3a from=translated src=- shape=4aa8e800 vocab=bbb81fa8
-/
@[scoped grind =]
theorem toFLTS_mem_mtr {lts : LTS State Label} {S : Set State} {s' : State} {μs : List Label} :
    s' ∈ lts.toFLTS.mtr S μs ↔ ∃ s ∈ S, lts.MTr s μs s' :=
  ⟨by grind [FLTS.mtr], by grind [FLTS.mtr]⟩

/-- Characterisation of multistep transitions in `LTS.toFLTS` as image transitions in `LTS`.
@isnad1 id=eq.0h3v.s4.37ef77e6fcdb from=translated src=- shape=5d624278 vocab=8cf08643
-/
@[scoped grind =]
theorem toFLTS_mtr_setImageMultistep {lts : LTS State Label} :
  lts.toFLTS.mtr = lts.setImageMultistep := by grind

end Cslib.LTS
