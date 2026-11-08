module

public import Tengoku.Seed.Data.Fin.Basic
public import Tengoku.Seed.Data.Real.Basic
public import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Attribution impossibility (core trilemma)

Adapted from DrakeCaraker/dash-impossibility-lean
(`DASHImpossibility/Trilemma.lean`) at revision
`7ec3ef9813a7642fdabe5b73c71d1bed4d5488e2` (software Apache-2.0 per
`CITATION.cff`).

Model-agnostic layer only: feature index type, abstract model + attribution,
Rashomon property, impossibility. Upstream GBDT axioms are not included
(atlas strict-trust). Proof body matches upstream.

Naming note: the predicate is spelled `RashomonProperty` here; upstream names
the identical declaration `RashimonProperty` (misspelled). Identifier corrected
for the atlas facade; the statement and proof are unchanged.
-/

namespace AISafetyAtlas.Upstream.Attribution

/-- Finite set of features with a group labeling (collinearity classes).-/
public structure FeatureIndex where
  /-- Number of features.-/
  P : ℕ
  /-- Number of groups.-/
  L : ℕ
  hP : 0 < P
  /-- Group of each feature.-/
  groupOf : Fin P → Fin L

/-- Membership of feature `j` in group `ℓ`.-/
public def inGroup (fs : FeatureIndex) (ℓ : Fin fs.L) (j : Fin fs.P) : Prop :=
  fs.groupOf j = ℓ

/-- Rashomon: within a group, models exist ranking two features oppositely.-/
@[expose] public def RashomonProperty
    (fs : FeatureIndex)
    (Model : Type)
    (attribution : Fin fs.P → Model → ℝ) : Prop :=
  ∀ (ℓ : Fin fs.L) (j k : Fin fs.P),
    inGroup fs ℓ j → inGroup fs ℓ k → j ≠ k →
    ∃ f f' : Model,
      attribution j f > attribution k f ∧
      attribution k f' > attribution j f'

end AISafetyAtlas.Upstream.Attribution
