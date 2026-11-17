/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.Seed.Logic.Equiv.List
import Tengoku.Seed.MeasureTheory.Constructions.Polish.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Boolean codes indexed by finite natural-number lists

The ambient space for coded trees is `List ℕ → Bool`, with its ordinary product topology.
Mathlib's fixed equivalence `List ℕ ≃ ℕ` identifies this space homeomorphically with Cantor
space. This file records that homeomorphism and the resulting Polish instance without changing the
topology on either function space.
-/

namespace DescriptiveSetTheory

/-- Reindex Boolean list codes along mathlib's fixed equivalence `List ℕ ≃ ℕ`.-/
def listNatBoolCodeHomeomorph : (List ℕ → Bool) ≃ₜ (ℕ → Bool) :=
  Homeomorph.piCongrLeft (Y := fun _ : ℕ => Bool) Equiv.listNatEquivNat

/-- Boolean codes indexed by finite natural-number lists form a Polish space.-/
noncomputable instance listNatBoolCodePolishSpace : PolishSpace (List ℕ → Bool) := by
  letI : MetricSpace (ℕ → Bool) :=
    PiNat.metricSpaceOfDiscreteUniformity fun _ => rfl
  exact listNatBoolCodeHomeomorph.isClosedEmbedding.polishSpace

/-- Reading a fixed finite-list coordinate is continuous in the product topology.-/
theorem continuous_listNatBoolCoordinate (s : List ℕ) :
    Continuous (fun c : List ℕ → Bool => c s) :=
  continuous_apply s

/-- A fixed Boolean condition on one finite-list coordinate is clopen.-/
theorem isClopen_listNatBoolCoordinate (s : List ℕ) (b : Bool) :
    IsClopen {c : List ℕ → Bool | c s = b} :=
  (isClopen_discrete {b}).preimage (continuous_listNatBoolCoordinate s)

end DescriptiveSetTheory
