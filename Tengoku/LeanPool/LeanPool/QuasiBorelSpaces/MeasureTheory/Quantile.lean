/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.MeasureTheory.Measure

/-!
# LeanPool.QuasiBorelSpaces.MeasureTheory.Quantile

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.MeasureTheory.Quantile`.
-/

@[expose] public section

namespace MeasureTheory

variable {A : Type*} [MeasurableSpace A]

open scoped unitInterval

/-- The set of rational elements of the unit interval. -/
private def unitIntervalRat : Set I := { r : I | ∃q : ℚ, r.val = q }

/-- The cumulative distribution function as a map from the unit interval to itself. -/
noncomputable def cdf (μ : Measure I) (i : I) : I where
  val := ProbabilityTheory.cdf (μ.map Subtype.val) i
  property := by
    simp only [
      Set.mem_Icc, ProbabilityTheory.cdf_nonneg,
      ProbabilityTheory.cdf_le_one, and_self]

private lemma monotone_cdf (μ : Measure I) : Monotone (cdf μ) := by
  intro r₁ r₂ hr
  apply ProbabilityTheory.monotone_cdf
  apply hr

/-- The quantile distribution function (i.e., the inverse of `cdf`). -/
noncomputable def quantile (μ : Measure I) (i : I) : I :=
  sInf {r : I | i ≤ cdf μ r}

namespace Measure

end Measure

end MeasureTheory
