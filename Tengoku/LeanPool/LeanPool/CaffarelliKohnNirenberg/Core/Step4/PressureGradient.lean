/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientBase
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.NewtonianDerivativeLocalLp
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsBasic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientProduct
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSlice
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceGradientSelection

/-!
# Pressure Gradient

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-! The selector is scalar.  This wrapper applies it to the three spatial
components and packages the resulting representatives as one native `Vec3`
field.  All analytic work is deliberately left in the slice hypothesis: the
wrapper only performs the finite-dimensional measurable assembly. -/

/-! Integrating the one-scale display over a one-sided time interval is a
direct order argument.  The spatial fields may be chosen independently on
the almost-everywhere set; this is the form consumed by the parabolic decay
layer. -/

theorem pressure_gradient_two_scale_decay
    {Φ V : ℝ → ℝ} {C₃ ρ r : ℝ}
    (hC₃ : 0 ≤ C₃) (_ : 0 < ρ) (_ : 0 < r) (_ : r ≤ ρ / 8)
    (hΦ : 0 ≤ Φ ρ)
    (hdecomp : Φ r ≤ V r + Φ (r / 2))
    (hpart : V r ≤ C₃ * (r / ρ) ^ (3 : ℕ) * V ρ)
    (hharm : Φ (r / 2) ≤ C₃ * (r / ρ) ^ (3 : ℕ) *
      (Φ ρ + V ρ)) :
    Φ r ≤ 2 * C₃ * (r / ρ) ^ (3 : ℕ) * (Φ ρ + V ρ) := by
  have hratio : 0 ≤ (r / ρ) ^ (3 : ℕ) := by positivity
  have hV : V r ≤ C₃ * (r / ρ) ^ (3 : ℕ) * (Φ ρ + V ρ) := by
    calc
      V r ≤ C₃ * (r / ρ) ^ (3 : ℕ) * V ρ := hpart
      _ ≤ C₃ * (r / ρ) ^ (3 : ℕ) * (Φ ρ + V ρ) := by
        gcongr
        linarith only [hΦ]
  calc
    Φ r ≤ V r + Φ (r / 2) := hdecomp
    _ ≤ C₃ * (r / ρ) ^ (3 : ℕ) * (Φ ρ + V ρ) +
        C₃ * (r / ρ) ^ (3 : ℕ) * (Φ ρ + V ρ) := add_le_add hV hharm
    _ = 2 * C₃ * (r / ρ) ^ (3 : ℕ) * (Φ ρ + V ρ) := by ring

theorem pressure_gradient_morrey_bound
    {κ : ℝ} {g : ParabolicPoint → ℝ} {C : ℝ≥0∞}
    (hcell : ∀ z : ParabolicPoint, ∀ r : {r : ℝ // 0 < r},
      morreyCell (6 / 5 : ℝ) κ g z r.1 ≤ C) :
    morreyNorm (6 / 5 : ℝ) κ g ≤ C := by
  exact morreyNorm_le_of_cell_bound hcell

end CKN.Core.Step4
