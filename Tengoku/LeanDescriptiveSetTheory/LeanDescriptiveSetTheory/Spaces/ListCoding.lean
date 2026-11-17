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

/-- Boolean codes indexed by finite natural-number lists form a Polish space.
@isnad1 id=polishsp.0h0v.s4.a76532c4925e from=translated src=- shape=6b65f21e vocab=0e441cc3
-/
noncomputable instance listNatBoolCodePolishSpace : PolishSpace (List ℕ → Bool) := by
  letI : MetricSpace (ℕ → Bool) :=
    PiNat.metricSpaceOfDiscreteUniformity fun _ => rfl
  exact listNatBoolCodeHomeomorph.isClosedEmbedding.polishSpace

/-- Reading a fixed finite-list coordinate is continuous in the product topology.
@isnad1 id=continuo.0h1v.s4.9d3de54ec25b from=translated src=- shape=ac64031f vocab=3b243901
-/
theorem continuous_listNatBoolCoordinate (s : List ℕ) :
    Continuous (fun c : List ℕ → Bool => c s) :=
  continuous_apply s

/-- A fixed Boolean condition on one finite-list coordinate is clopen.
@isnad1 id=isclopen.0h2v.s5.2ae482bdab93 from=translated src=- shape=7701bce0 vocab=a4bf5843
-/
theorem isClopen_listNatBoolCoordinate (s : List ℕ) (b : Bool) :
    IsClopen {c : List ℕ → Bool | c s = b} :=
  (isClopen_discrete {b}).preimage (continuous_listNatBoolCoordinate s)

end DescriptiveSetTheory
