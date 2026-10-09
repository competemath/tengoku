module

public import Tengoku.GibbsMeasure.GibbsMeasure.Mathlib.Basic.ENNReal.Basic
public import Tengoku.GibbsMeasure.GibbsMeasure.Mathlib.MeasureTheory.Function.SimpleFunc
public import Tengoku.GibbsMeasure.GibbsMeasure.Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Tengoku.GibbsMeasure.GibbsMeasure.Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Tengoku.GibbsMeasure.GibbsMeasure.Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Tengoku

/-!
# Proper kernels

We define the notion of properness for measure kernels and highlight important consequences.
-/

public section
attribute [local simp] ENNReal.ofReal_indicator_one ENNReal.tOReal_indicator_one


open MeasureTheory ENNReal NNReal Set
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {A B : Set X}
  {f g : X → ℝ} {x₀ : X}

lemma IsProper.ae_eq_const (hπ : IsProper π) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y] {g : X → Y}
    (hg : Measurable[𝓑] g) (x₀ : X) :
    ∀ᵐ x ∂π x₀, g x = g x₀ := by
  let B := g ⁻¹' {g x₀}
  have hB : MeasurableSet[𝓑] B := hg (measurableSet_singleton _)
  have hB' := h𝓑𝓧 _ hB
  have hπB : π.restrict hB' x₀ = π x₀ := by
    rw [hπ.restrict_eq_indicator_smul h𝓑𝓧 hB x₀]
    simp [B]
  rw [ae_iff, ← hπB]
  convert restrict_apply' π hB' x₀ hB'.compl
  · ext a; simp [B]
  · simp

variable [IsFiniteKernel π]

end ProbabilityTheory.Kernel
