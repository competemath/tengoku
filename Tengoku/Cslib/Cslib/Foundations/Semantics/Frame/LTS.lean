/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Tengoku.Cslib.Cslib.Init
public import Tengoku.Cslib.Cslib.Foundations.Semantics.Frame.Basic
public import Tengoku.Cslib.Cslib.Foundations.Semantics.LTS.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/leanprover/cslib@e806c8e639ed, `Cslib/Foundations/Semantics/Frame/LTS.lean`: removed 1 tag(s) of the custom grind set(s) `modal` from declarations. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! # Modal Frames and LTS -/

@[expose] public section

namespace Cslib.LTS

open PFunctor

variable (lts : LTS State Label)

/-- Transforms `lts` into a corresponding unary `Frame`.-/
def toFrame : Frame State (mkUnary Label) := Frame.ofRelations (fun μ s s' => lts.Tr s μ s')

instance : Coe (LTS State Label) (Frame State (PFunctor.mkUnary Label)) := ⟨LTS.toFrame⟩

/--
@isnad1 id=iff.0h6v.s5.60bc7083f7c1 from=translated src=- shape=93a0de68 vocab=fc48f508
-/
@[simp]
lemma toFrame_r_iff_tr : lts.toFrame.r μ s f ↔ lts.Tr s μ (f default) := by rfl

/--
@isnad1 id=iff.0h6v.s5.e264c9504837 from=translated src=- shape=81e5c8c2 vocab=1bcd577c
-/
@[simp]
lemma toFrame_diagonal_iff_tr : lts.toFrame.diagonal μ s s' ↔ lts.Tr s μ s' := by rfl

end Cslib.LTS
