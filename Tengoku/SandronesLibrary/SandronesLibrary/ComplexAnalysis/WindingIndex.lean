/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.CycleCarrier
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.PiecewiseC1HomotopyInvariance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The winding number of a cycle

For a closed path `γ` in `ℂ` and a point `w` not on `γ`, the winding number (index)
`n(γ, w)` counts, with orientation, how many times `γ` runs around `w`.  The textbook
definition is the complex path integral

`n(γ, w) = (2πi)⁻¹ ∮_γ dz / (z - w)`.

This file implements that definition for a `Cycle`, i.e. a finitely supported `ℤ`-valued
formal sum of closed paths, on top of the generic `cycleIntegral` of the carrier
`SandronesLibrary.ComplexAnalysis.CycleCarrier`.  The construction is `ℤ`-linear in the
cycle by construction, so additivity, `ℤ`-homogeneity, negation, subtraction and the value
on a single closed path are immediate; we record them as the public interface.

The second half of the file packages the textbook quantifier "the winding number of `γ`
about `w` vanishes for every `w` outside `U`".  Following Ahlfors / Rudin, two cycles are
homologous in `U` when their winding numbers agree at every point outside `U`.  The public
predicates `IsNullHomologousIn` and `IsHomologousIn` *conjoin* `Cycle.SupportedIn` on every
cycle involved.  That conjunct is part of the definition, not a convenience hypothesis: the
winding number is a total function whose value at a point of the cycle's own trace is not the
textbook quantity, so restricting to cycles that lie in `U` is what keeps the outside-`U`
quantifier honest.  A "difference is null-homologous" formulation was deliberately not
adopted, because the trace of a difference is not the union of the traces of the summands
(cancellation can shrink it) and the resulting predicate would not be additively closed.

Current entries:

* `complex-analysis.integral.winding-number-foundation`: the winding number, its `ℤ`-linearity
  in the cycle, the null-homologous / homologous-in-`U` predicates, and their winding-number
  characterisation together with the piecewise-C¹ null-homotopy consumers.
-/

open MeasureTheory
open scoped Interval unitInterval

noncomputable section

namespace SandronesLibrary.ComplexAnalysis

open SandronesLibrary.Topology

/-- The winding number (index) of a cycle about `w`: `(2πi)⁻¹ ∮_γ dz/(z-w)`.

For a single closed path this is the textbook index; for a finite `ℤ`-combination of
closed paths it is the corresponding `ℤ`-linear combination of indices.

> **Entry**: complex-analysis.integral.winding-number-foundation-/
noncomputable def windingNumber (γ : Cycle) (w : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * cycleIntegral (fun z : ℂ => (z - w)⁻¹) γ

/-- The winding number is additive in the cycle.

> **Entry**: complex-analysis.integral.winding-number-foundation
@isnad1 id=eq.0h3v.s5.b86b6e45c372 from=translated src=- shape=e7d4cb01 vocab=a9c50731
-/
theorem windingNumber_add (γ δ : Cycle) (w : ℂ) :
    windingNumber (γ + δ) w = windingNumber γ w + windingNumber δ w := by
  simp only [windingNumber, cycleIntegral_add, mul_add]

/-- The winding number is `ℤ`-homogeneous in the cycle.

> **Entry**: complex-analysis.integral.winding-number-foundation
@isnad1 id=eq.0h3v.s5.9a02bb462772 from=translated src=- shape=17ac4a7d vocab=1f69a0e7
-/
theorem windingNumber_smul (n : ℤ) (γ : Cycle) (w : ℂ) :
    windingNumber (n • γ) w = n • windingNumber γ w := by
  simp only [windingNumber, map_smul, zsmul_eq_mul]
  ring

/-- Negating the cycle negates the winding number.

> **Entry**: complex-analysis.integral.winding-number-foundation
@isnad1 id=eq.0h2v.s4.00f4b451272a from=translated src=- shape=b11e7be8 vocab=9bc5dbee
-/
theorem windingNumber_neg (γ : Cycle) (w : ℂ) : windingNumber (-γ) w = -windingNumber γ w := by
  simp only [windingNumber, map_neg]
  ring

/-- The winding number of the zero cycle vanishes.

> **Entry**: complex-analysis.integral.winding-number-foundation
@isnad1 id=eq.0h1v.s4.ac22e0ea41fe from=translated src=- shape=a0dd47fb vocab=9b7b09de
-/
theorem windingNumber_zero (w : ℂ) : windingNumber (0 : Cycle) w = 0 := by
  simp [windingNumber]

/-- The winding number is additive in the negative direction as well.

> **Entry**: complex-analysis.integral.winding-number-foundation
@isnad1 id=eq.0h3v.s5.b0e01ad7605f from=translated src=- shape=e7d4cb01 vocab=b363ee67
-/
theorem windingNumber_sub (γ δ : Cycle) (w : ℂ) :
    windingNumber (γ - δ) w = windingNumber γ w - windingNumber δ w := by
  simp only [windingNumber, map_sub, mul_sub]

/-- The winding number of a single closed path with multiplicity `n`: the index of the path,
scaled by `n`.  This is the definitional generator case, made usable by `simp`.

> **Entry**: complex-analysis.integral.winding-number-foundation
@isnad1 id=eq.0h3v.s7.5a175260f4a6 from=translated src=- shape=824a5290 vocab=a50f2f3c
-/
@[simp]
theorem windingNumber_single (c : ClosedPath) (n : ℤ) (w : ℂ) :
    windingNumber (Finsupp.single c n) w =
      n • ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * pathIntegral (fun z => (z - w)⁻¹) c.2) := by
  rw [windingNumber, cycleIntegral_single, banachPathIntegral_complex_eq_pathIntegral,
    zsmul_eq_mul]
  ring

/-- `γ` is null-homologous in `U`: the cycle lies in `U` and its winding number vanishes
at every point outside `U`.  The `Cycle.SupportedIn γ U` conjunct is part of the textbook
"cycle in `U`" convention and is what makes the total function `windingNumber` honest here:
outside the trace of `γ` the integrand `dz/(z-w)` is available, so a vanishing index at every
`w ∉ U` is a meaningful statement.

> **Entry**: complex-analysis.integral.winding-number-foundation-/
def IsNullHomologousIn (γ : Cycle) (U : Set ℂ) : Prop :=
  γ.SupportedIn U ∧ ∀ w : ℂ, w ∉ U → windingNumber γ w = 0

/-- Two cycles are homologous in `U` when both lie in `U` and their winding numbers agree at
every point outside `U`.  This is the textbook relative-homology statement; keeping the two
`Cycle.SupportedIn` conjuncts (rather than only support of the difference) prevents the
predicate from asserting an equality of junk values at points of the individual traces.

> **Entry**: complex-analysis.integral.winding-number-foundation-/
def IsHomologousIn (γ₁ γ₂ : Cycle) (U : Set ℂ) : Prop :=
  γ₁.SupportedIn U ∧ γ₂.SupportedIn U ∧
    ∀ w : ℂ, w ∉ U → windingNumber γ₁ w = windingNumber γ₂ w

/-- The null-homology predicate is its supported-and-vanishing quantifier by definition; this
is the public unfolding used downstream.

> **Entry**: complex-analysis.integral.winding-number-foundation
@isnad1 id=iff.0h2v.s5.d1907bc68c9b from=translated src=- shape=7070de87 vocab=b933cb20
-/
theorem isNullHomologousIn_iff (γ : Cycle) (U : Set ℂ) :
    IsNullHomologousIn γ U ↔ γ.SupportedIn U ∧ ∀ w, w ∉ U → windingNumber γ w = 0 :=
  Iff.rfl

/-- The zero cycle is null-homologous in every set.

> **Entry**: complex-analysis.integral.winding-number-foundation
@isnad1 id=isnullho.0h1v.s4.1df62de5f849 from=translated src=- shape=4583a4a8 vocab=0efcdad8
-/
theorem isNullHomologousIn_zero (U : Set ℂ) : IsNullHomologousIn (0 : Cycle) U := by
  refine ⟨?_, ?_⟩
  · intro c hc
    rw [Finsupp.support_zero] at hc
    exact absurd hc (Finset.notMem_empty c)
  · intro w _
    exact windingNumber_zero w

/-- Null-homology is closed under addition, with no additional hypothesis: the supported
conjunct passes to the sum through pieces of the summands, and the winding numbers add.

> **Entry**: complex-analysis.integral.winding-number-foundation
@isnad1 id=isnullho.2h3v.s4.eef28e01526a from=translated src=- shape=17092177 vocab=70dd2603
-/
theorem isNullHomologousIn_add {γ δ : Cycle} {U : Set ℂ}
    (hγ : IsNullHomologousIn γ U) (hδ : IsNullHomologousIn δ U) :
    IsNullHomologousIn (γ + δ) U := by
  refine ⟨hγ.1.add hδ.1, ?_⟩
  intro w hw
  rw [windingNumber_add, hγ.2 w hw, hδ.2 w hw, add_zero]

/-- Two cycles are homologous in `U` exactly when both lie in `U` and have the same winding
number at every point outside `U`.  This is the working winding-number characterisation of
relative homology; its equivalence with a chain-level "difference is null-homologous"
formulation has not been proved in this batch.

> **Entry**: complex-analysis.integral.winding-number-foundation
@isnad1 id=iff.0h3v.s5.550df4be23be from=translated src=- shape=67ca0d19 vocab=fdbaf712
-/
theorem isHomologousIn_iff_windingNumber_eq (γ₁ γ₂ : Cycle) (U : Set ℂ) :
    IsHomologousIn γ₁ γ₂ U ↔
      γ₁.SupportedIn U ∧ γ₂.SupportedIn U ∧
        ∀ w : ℂ, w ∉ U → windingNumber γ₁ w = windingNumber γ₂ w :=
  Iff.rfl

/-- The inverse difference `z ↦ (z - w)⁻¹` is holomorphic on any set avoiding `w`.

> **Entry**: complex-analysis.integral.winding-number-foundation
@isnad1 id=holomorp.1h2v.s4.9c5798c07ff1 from=translated src=- shape=75799dc9 vocab=b9d2e276
-/
theorem holomorphicOnTextbook_inv_sub {U : Set ℂ} {w : ℂ} (hw : w ∉ U) :
    HolomorphicOnTextbook (fun z : ℂ => (z - w)⁻¹) U := by
  rw [holomorphicOnTextbook_iff_forall_differentiableAt]
  intro z hz
  have hzw : z - w ≠ 0 := sub_ne_zero.mpr (fun h => hw (h ▸ hz))
  exact (differentiableAt_id.sub_const w).inv hzw

/-- A holomorphic integrand has zero integral over a cycle all of whose closed pieces are
null-homotopic inside `U` (with the square image staying in `U`).

> **Entry**: complex-analysis.integral.winding-number-foundation
@isnad1 id=eq.4h3v.s9.ac4cd026e68c from=translated src=- shape=2fa99131 vocab=73947b7d
-/
theorem cycleIntegral_eq_zero_of_piecewiseC1_nullHomotopic
    {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (hf : HolomorphicOnTextbook f U)
    (γ : Cycle) (hC1 : γ.PiecewiseC1)
    (hnull : ∀ c ∈ γ.support, ∃ F : c.2.Homotopy (Path.refl c.1),
      ∀ z : unitInterval × unitInterval, pathHomotopySquare F z ∈ U) :
    cycleIntegral f γ = 0 := by
  apply cycleIntegral_eq_zero_of_forall_piece_eq_zero
  intro c hc
  obtain ⟨F, hF⟩ := hnull c hc
  rw [banachPathIntegral_complex_eq_pathIntegral]
  exact pathIntegral_eq_zero_of_piecewiseC1_nullHomotopyWithin hU hf (hC1 c hc) F hF

/-- The winding number about a point outside `U` of a cycle whose pieces are null-homotopic in
`U` vanishes.

> **Entry**: complex-analysis.integral.winding-number-foundation
@isnad1 id=eq.4h3v.s9.3b8c3888e53c from=translated src=- shape=2556022a vocab=bf26691f
-/
theorem windingNumber_eq_zero_of_piecewiseC1_nullHomotopic
    {U : Set ℂ} {w : ℂ} (hU : IsOpen U) (hw : w ∉ U)
    (γ : Cycle) (hC1 : γ.PiecewiseC1)
    (hnull : ∀ c ∈ γ.support, ∃ F : c.2.Homotopy (Path.refl c.1),
      ∀ z : unitInterval × unitInterval, pathHomotopySquare F z ∈ U) :
    windingNumber γ w = 0 := by
  have hzero := cycleIntegral_eq_zero_of_piecewiseC1_nullHomotopic hU
    (holomorphicOnTextbook_inv_sub hw) γ hC1 hnull
  rw [windingNumber, hzero, mul_zero]

/-- A cycle whose pieces are all null-homotopic in `U` is null-homologous in `U`.  This is the
first real consumer of the `IsNullHomologousIn` predicate.

> **Entry**: complex-analysis.integral.winding-number-foundation
@isnad1 id=isnullho.4h2v.s9.d455917ff0e7 from=translated src=- shape=50677f60 vocab=aa376d6c
-/
theorem isNullHomologousIn_of_piecewiseC1_nullHomotopic
    {U : Set ℂ} (hU : IsOpen U)
    (γ : Cycle) (hC1 : γ.PiecewiseC1) (hUγ : γ.SupportedIn U)
    (hnull : ∀ c ∈ γ.support, ∃ F : c.2.Homotopy (Path.refl c.1),
      ∀ z : unitInterval × unitInterval, pathHomotopySquare F z ∈ U) :
    IsNullHomologousIn γ U :=
  ⟨hUγ, fun _ hw => windingNumber_eq_zero_of_piecewiseC1_nullHomotopic hU hw γ hC1 hnull⟩

end SandronesLibrary.ComplexAnalysis
