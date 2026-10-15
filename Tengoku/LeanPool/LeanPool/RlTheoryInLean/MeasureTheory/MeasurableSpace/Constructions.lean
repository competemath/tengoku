/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
module

public import Tengoku

/-!
# LeanPool.RlTheoryInLean.MeasureTheory.MeasurableSpace.Constructions
-/

@[expose] public section

/--
@isnad1 id=measurab.1h4v.s5.8b8fda358a3f from=translated src=- shape=95ecf475 vocab=29d698bf
-/
lemma Measurable.of_uncurry
  {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {f : α → β → γ} (h : Measurable (Function.uncurry f))
  : Measurable f := by
    apply measurable_pi_iff.mpr
    intro a
    apply Measurable.of_uncurry_right h
