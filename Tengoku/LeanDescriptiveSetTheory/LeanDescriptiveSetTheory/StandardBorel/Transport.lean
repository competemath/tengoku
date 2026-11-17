/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.StandardBorel.Code

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Semantic transport of standard-Borel codes

Measurable maps do not act structurally on topology-generated syntax. This file therefore exposes
an existential preimage theorem and an explicitly choice-selected preimage code. All functorial
laws concern evaluated sets, never code syntax.
-/

open Set

universe u v w

namespace DescriptiveSetTheory
namespace StandardBorelCode

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- A measurable preimage of a code denotation has a code witness.-/
theorem exists_code_preimage_of_measurable [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] (f : X → Y) (hf : Measurable f)
    (c : StandardBorelCode Y) : ∃ d : StandardBorelCode X, d.eval = f ⁻¹' c.eval :=
  exists_code (hf (measurableSet_eval c))

/-- A noncanonical code selected for the measurable preimage of a code denotation.-/
noncomputable def chosenPreimage [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] (f : X → Y) (hf : Measurable f)
    (c : StandardBorelCode Y) : StandardBorelCode X :=
  (exists_code_preimage_of_measurable f hf c).choose

/-- The selected preimage code has the promised denotation.-/
@[simp] theorem eval_chosenPreimage [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] (f : X → Y) (hf : Measurable f)
    (c : StandardBorelCode Y) : (chosenPreimage f hf c).eval = f ⁻¹' c.eval :=
  (exists_code_preimage_of_measurable f hf c).choose_spec

/-- Selected preimage is semantically the identity for the identity map.-/
theorem eval_chosenPreimage_id [MeasurableSpace X] [StandardBorelSpace X]
    (c : StandardBorelCode X) : (chosenPreimage id measurable_id c).eval = c.eval := by
  rw [eval_chosenPreimage]
  rfl

/-- Selected preimage respects composition at the level of denotations.-/
theorem eval_chosenPreimage_comp [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [MeasurableSpace Z] [StandardBorelSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Measurable f) (hg : Measurable g)
    (c : StandardBorelCode Z) :
    (chosenPreimage (g ∘ f) (hg.comp hf) c).eval =
      (chosenPreimage f hf (chosenPreimage g hg c)).eval := by
  rw [eval_chosenPreimage, eval_chosenPreimage, eval_chosenPreimage]
  rfl

/-- Transport a code denotation forward along a measurable equivalence. The selected code is
noncanonical; only its evaluation equation is stable API.-/
noncomputable def transportMeasurableEquiv [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] (e : X ≃ᵐ Y)
    (c : StandardBorelCode X) : StandardBorelCode Y :=
  chosenPreimage e.symm e.symm.measurable c

/-- Measurable-equivalence transport denotes the exact forward image.-/
@[simp] theorem eval_transportMeasurableEquiv [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] (e : X ≃ᵐ Y) (c : StandardBorelCode X) :
    (transportMeasurableEquiv e c).eval = e '' c.eval := by
  rw [transportMeasurableEquiv, eval_chosenPreimage]
  exact (e.image_eq_preimage_symm c.eval).symm

/-- Measurable-equivalence transport respects composition at the level of denotations.-/
theorem eval_transportMeasurableEquiv_trans [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [MeasurableSpace Z] [StandardBorelSpace Z]
    (e : X ≃ᵐ Y) (d : Y ≃ᵐ Z) (c : StandardBorelCode X) :
    (transportMeasurableEquiv (e.trans d) c).eval =
      (transportMeasurableEquiv d (transportMeasurableEquiv e c)).eval := by
  rw [eval_transportMeasurableEquiv, eval_transportMeasurableEquiv,
    eval_transportMeasurableEquiv]
  exact (image_image d e c.eval).symm

/-- Transport along an equivalence and then its inverse recovers the original denotation.-/
theorem eval_transportMeasurableEquiv_symm [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] (e : X ≃ᵐ Y) (c : StandardBorelCode X) :
    (transportMeasurableEquiv e.symm (transportMeasurableEquiv e c)).eval = c.eval := by
  rw [eval_transportMeasurableEquiv, eval_transportMeasurableEquiv,
    e.image_eq_preimage_symm]
  exact e.symm.image_preimage c.eval

end StandardBorelCode
end DescriptiveSetTheory
