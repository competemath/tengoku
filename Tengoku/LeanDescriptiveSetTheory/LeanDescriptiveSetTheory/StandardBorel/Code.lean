/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.Code
import Tengoku.Seed.MeasureTheory.Constructions.Polish.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Codes on standard Borel spaces

`StandardBorelCode X` hides the noncanonical compatible Polish topology selected by
`upgradeStandardBorel X`. Its public semantics live in the caller's original measurable space;
no topology choice and no code witness is claimed to be canonical.
-/

open MeasurableSpace Set

universe u

namespace DescriptiveSetTheory

/-- A Borel code using mathlib's noncanonically selected compatible Polish topology.-/
noncomputable abbrev StandardBorelCode (X : Type u) [MeasurableSpace X]
    [StandardBorelSpace X] :=
  @BorelCode X (upgradeStandardBorel X).toTopologicalSpace

namespace StandardBorelCode

variable {X : Type u} [mX : MeasurableSpace X] [StandardBorelSpace X]

/-- Interpret a standard-Borel code as a subset of the original measurable space.-/
noncomputable def eval (c : StandardBorelCode X) : Set X :=
  @BorelCode.eval X (upgradeStandardBorel X).toTopologicalSpace c

/-- Every standard-Borel code denotes a measurable set in the caller's measurable space.
@isnad1 id=measurab.0h2v.s4.e32a5de7ecfa from=translated src=- shape=10965991 vocab=04bce12e
-/
theorem measurableSet_eval (c : StandardBorelCode X) : MeasurableSet c.eval := by
  let t : Set X := c.eval
  change MeasurableSet t
  rw [eq_borel_upgradeStandardBorel X]
  exact @BorelCode.measurableSet_eval X (upgradeStandardBorel X).toTopologicalSpace c

/-- Measurable sets in a standard Borel space are exactly code denotations.
@isnad1 id=iff.0h2v.s5.1343bacda248 from=translated src=- shape=ba7acf66 vocab=e3ed7394
-/
theorem measurableSet_iff_exists_code {s : Set X} :
    MeasurableSet s ↔ ∃ c : StandardBorelCode X, c.eval = s := by
  constructor
  · intro hs
    have hs' : @MeasurableSet X (@borel X (upgradeStandardBorel X).toTopologicalSpace) s := by
      rw [← eq_borel_upgradeStandardBorel X]
      exact hs
    exact
      (@BorelCode.borelMeasurableSet_iff_exists_code X
        (upgradeStandardBorel X).toTopologicalSpace s).1 hs'
  · rintro ⟨c, rfl⟩
    exact measurableSet_eval c

/-- Every measurable set in a standard Borel space has a (noncanonical) code witness.
@isnad1 id=ex.1h2v.s5.6ae53cf2e5d2 from=translated src=- shape=5dbd526c vocab=e3ed7394
-/
theorem exists_code {s : Set X} (hs : MeasurableSet s) :
    ∃ c : StandardBorelCode X, c.eval = s :=
  measurableSet_iff_exists_code.1 hs

end StandardBorelCode
end DescriptiveSetTheory
