/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import Tengoku.LeanPool.LeanPool.LanguageGeneration.Core.ClassGeneration

/-!
# Finite positive witnesses for ordinary generation

This extension uses the upstream sequence-input model without redefining it.
`SetDriven` below refers to dependence on the input set, not set-valued output.
-/

@[expose] public section

namespace GenLimit.FiniteWitness

open GenLimit.Generic

variable {α : Type*}

/-- Run an input-set function on an ordered finite history. -/
noncomputable def ofSet (g : Finset α → α) : Generator α :=
  fun _ xs => g (sequenceSample xs)

/--
@isnad1 id=eq.0h4v.s4.24be4d29cfa4 from=translated src=- shape=82d37392 vocab=20f9d0b8
-/
@[simp] theorem output_ofSet (g : Finset α → α) (stream : Stream α) (t : ℕ) :
    output (ofSet g) stream t = g (sample stream t) := by
  simp [output, ofSet, sequenceSample_prefix]

/-- Existence of one input-set generator in the original positive-text model. -/
def SetDrivenGeneratable (H : LanguageClass α) : Prop :=
  ∃ g : Finset α → α, IsLimitGenerator (ofSet g) H

/--
@isnad1 id=generata.1h2v.s3.c0ed508a48ac from=translated src=- shape=11db0672 vocab=9fdc9b95
-/
theorem setDriven_implies_ordinary {H : LanguageClass α}
    (h : SetDrivenGeneratable H) : GeneratableInLimit H := by
  obtain ⟨g, hg⟩ := h
  exact ⟨ofSet g, hg⟩

end GenLimit.FiniteWitness
