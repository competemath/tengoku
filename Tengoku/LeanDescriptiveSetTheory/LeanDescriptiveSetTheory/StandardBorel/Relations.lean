/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Relations.Sections
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.StandardBorel.Code

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Graph and image codes on standard Borel spaces

This file combines relation algebra with the Lusin--Souslin theorem. Graphs of measurable maps,
images under maps injective on a measurable set, and ranges of measurable embeddings receive
standard-Borel code witnesses with exact evaluation equations.
-/

open MeasurableSpace Set

universe u v

namespace DescriptiveSetTheory

variable {X : Type u} {Y : Type v}

/-- The graph of a measurable map on a measurable set is measurable.
@isnad1 id=measurab.2h4v.s5.2fb940189186 from=translated src=- shape=9c56e173 vocab=acfa20b9
-/
theorem measurableSet_graphOn [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] {s : Set X} {f : X → Y}
    (hs : MeasurableSet s) (hf : Measurable f) : MeasurableSet (s.graphOn f) := by
  rw [Set.graphOn]
  exact hs.image_of_measurable_injOn (measurable_id.prodMk hf) fun _ _ _ _ h =>
    congrArg Prod.fst h

/-- The full graph of a measurable map is measurable.
@isnad1 id=measurab.1h3v.s5.b802d4d797c0 from=translated src=- shape=d2c0d831 vocab=d67189ec
-/
theorem measurableSet_graph_of_measurable [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] {f : X → Y} (hf : Measurable f) :
    MeasurableSet (univ.graphOn f) :=
  measurableSet_graphOn MeasurableSet.univ hf

/-- A measurable map between standard Borel spaces has a code for its full graph.
@isnad1 id=ex.1h3v.s6.f6e0b9dabda1 from=translated src=- shape=5d279fdd vocab=7406cbc8
-/
theorem exists_borelCode_graph_of_measurable [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] {f : X → Y} (hf : Measurable f) :
    ∃ c : StandardBorelCode (X × Y), c.eval = univ.graphOn f :=
  StandardBorelCode.exists_code (measurableSet_graph_of_measurable hf)

/-- Lusin--Souslin, exposed as an exact code witness for an injective measurable image.
@isnad1 id=ex.3h4v.s6.bf8e80b16714 from=translated src=- shape=a4218e9a vocab=f9e6f173
-/
theorem exists_borelCode_image_of_measurable_injOn [MeasurableSpace X]
    [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    {s : Set X} {f : X → Y} (hs : MeasurableSet s) (hf : Measurable f)
    (hinj : InjOn f s) : ∃ c : StandardBorelCode Y, c.eval = f '' s :=
  StandardBorelCode.exists_code (hs.image_of_measurable_injOn hf hinj)

end DescriptiveSetTheory
