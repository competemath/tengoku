/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
module

public import Tengoku

/-!
# LeanPool.RlTheoryInLean.Defs
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

/--
@isnad1 id=tendsto.2h6v.s5.1e339b95fed4 from=translated src=- shape=a254ac63 vocab=020c6acd
-/
lemma Tendsto.filter_congr
  {α β : Type*} {f : α → β} {a : Filter α} {b b' : Filter β}
  (hb : b = b') (hf : Tendsto f a b) : Tendsto f a b' := by
  simp_all

/--
@isnad1 id=eq.1h5v.s6.5b8d064baf35 from=translated src=- shape=00c54097 vocab=bfa7ecbe
-/
lemma Kernel.congrFun_apply
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {κ₁ κ₂ : Kernel α β}
  (h : κ₁ = κ₂) :
  ∀ a, κ₁ a = κ₂ a := by
  simp_all

/--
@isnad1 id=measurab.2h6v.s5.c418e81ed178 from=translated src=- shape=9f849076 vocab=a9a5f847
-/
lemma Measurable.congr
  {α β : Type*} {ma : MeasurableSpace α} {mb : MeasurableSpace β} {f g : α → β}
  (hfg : f = g) : Measurable f → Measurable g := by
  simp_all

/--
@isnad1 id=integrab.2h6v.s6.a4acfe1ebd11 from=translated src=- shape=d6e515cd vocab=cd56bfc7
-/
lemma Integrable.measure_congr
  {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}
  {β : Type*} {f : α → β}
  [NormedAddCommGroup β]
  {hμν : μ = ν}
  (hf : Integrable f μ) : Integrable f ν := by
  simp_all

/--
@isnad1 id=eq.1h6v.s5.ca01dfcf2be4 from=translated src=- shape=eccd97de vocab=f2c08602
-/
lemma Integral.measure_congr
  {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}
  {β : Type*} {f : α → β}
  [NormedAddCommGroup β] [NormedSpace ℝ β]
  {hμν : μ = ν} : ∫ x, f x ∂ μ = ∫ x, f x ∂ ν := by
  rw [hμν]

/--
@isnad1 id=hasderiv.2h4v.s6.7632a77555bf from=translated src=- shape=e5f55b50 vocab=6ed66805
-/
lemma HasDerivAt.congr
  {f g : ℝ → ℝ} {f' : ℝ} {x : ℝ} (hfg : f = g)
  (h : HasDerivAt f f' x) : HasDerivAt g f' x := by
  simp_all

/--
@isnad1 id=hasderiv.3h5v.s6.43160b48e5ee from=translated src=- shape=4bb16049 vocab=6ed66805
-/
lemma HasDerivAt.congr_congr
  {f g : ℝ → ℝ} {f' g' : ℝ} {x : ℝ}
  (h : HasDerivAt f f' x)
  (hfg : f = g) (hfg' : f' = g') : HasDerivAt g g' x := by
  simp_all

namespace RLTheory

variable {d : ℕ}
/-- Euclidean space of dimension `d`, used for finite-dimensional RL iterates. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

end RLTheory
