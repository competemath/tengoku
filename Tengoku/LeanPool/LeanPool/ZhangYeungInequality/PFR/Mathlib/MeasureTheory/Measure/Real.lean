/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Tengoku.Seed.MeasureTheory.Measure.Prod
import Tengoku.LeanPool.LeanPool.ZhangYeungInequality.PFR.Mathlib.MeasureTheory.Measure.Prod
import Tengoku.Seed.MeasureTheory.Measure.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LeanPool.ZhangYeungInequality.PFR.Mathlib.MeasureTheory.Measure.Real

Imported Lean Pool material for
`LeanPool.ZhangYeungInequality.PFR.Mathlib.MeasureTheory.Measure.Real`.
-/

public section
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool 
open Function Set
open scoped ENNReal NNReal

namespace MeasureTheory
variable {α β R Ω Ω' : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace Ω'}
  {_ : MeasurableSpace α} {_ : MeasurableSpace β}

/--
@isnad1 id=eq.0h5v.s6.85700a582248 from=translated src=- shape=5237e8cf vocab=56c9d582
-/
lemma _root_.MeasureTheory.Measure.ennreal_smul_real_apply
    (c : ℝ≥0∞) (μ : Measure Ω) (s : Set Ω) :
    (c • μ).real s = c.toReal • μ.real s := by simp

/--
@isnad1 id=eq.0h5v.s6.39ee30e24e16 from=translated src=- shape=df429bc6 vocab=2aab176e
-/
lemma _root_.MeasureTheory.Measure.nnreal_smul_real_apply
    (c : ℝ≥0) (μ : Measure Ω) (s : Set Ω) :
    (c • μ).real s = c • μ.real s := by simp [Measure.real, NNReal.smul_def]

/--
@isnad1 id=eq.3h7v.s6.ce8c5a491649 from=translated src=- shape=7a5f57c4 vocab=754f12fe
-/
lemma _root_.MeasureTheory.Measure.comap_real_apply {s : Set α} {f : α → β} (hfi : Injective f)
    (hf : ∀ s,
      MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    (Measure.comap f μ).real s = μ.real (f '' s) := by
  simp [Measure.real, Measure.comap_apply _ hfi hf μ hs]

/--
@isnad1 id=eq.0h7v.s6.61cf9715ec7a from=translated src=- shape=1eae5aae vocab=821e4003
-/
lemma _root_.MeasureTheory.Measure.prod_real_singleton
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x :
  α × β) :
    (μ.prod ν).real {x} = μ.real {x.1} * ν.real {x.2} := by
  simp [Measure.real, Measure.prod_apply_singleton]

variable [MeasurableSingletonClass Ω] [MeasurableSingletonClass Ω']

/--
@isnad1 id=eq.0h6v.s6.780d349c72f3 from=translated src=- shape=fdaa9a86 vocab=1b502854
-/
lemma measureReal_preimage_fst_singleton_eq_sum [Fintype Ω'] (μ : Measure (Ω × Ω'))
    [IsFiniteMeasure μ] (x : Ω) :
    μ.real (Prod.fst ⁻¹' {x}) = ∑ y : Ω', μ.real {(x, y)} := by
  rw [measureReal_def, measure_preimage_fst_singleton_eq_sum, ENNReal.toReal_sum]
  · rfl
  simp_all

/--
@isnad1 id=eq.0h6v.s6.17025953f155 from=translated src=- shape=d19a9a01 vocab=a3a77b95
-/
lemma measureReal_preimage_snd_singleton_eq_sum [Fintype Ω] (μ : Measure (Ω × Ω'))
    [IsFiniteMeasure μ] (y : Ω') :
    μ.real (Prod.snd ⁻¹' {y}) = ∑ x : Ω, μ.real {(x, y)} := by
  rw [measureReal_def, measure_preimage_snd_singleton_eq_sum, ENNReal.toReal_sum]
  · rfl
  simp_all

end MeasureTheory
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)
