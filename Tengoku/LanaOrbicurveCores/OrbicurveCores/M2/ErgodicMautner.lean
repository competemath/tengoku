/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.M2.HopfContinuity
import Tengoku.LanaOrbicurveCores.OrbicurveCores.M2.HopfFinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Mautner phenomenon on `Γ \ SL(2, ℝ)`

Let `Γ` be countable with a measurable fundamental set `F ⊆ ℍ` of finite area and finite
multiplicity. Then

* `pou Γ F g = 1_F(g i) / #{γ ∈ Γ | γ g i ∈ F}` is a `Γ`-partition of unity on `SL(2, ℝ)`
  (`tsum_pou`) of finite total mass (`lintegral_pou_lt_top`);
* the weighted `L¹`-norm `∫ pou · |Ψ|` of a `Γ`-invariant `Ψ` is invariant under right
  translations preserving `hopfMeasure` (`lintegral_pou_mul_right`, "unfolding");
* **Mautner** (`ae_mul_unip_eq`): a bounded measurable `Φ` that is left `Γ`-invariant and right
  `A`-invariant is right `N`-invariant almost everywhere.
-/

open MeasureTheory Set Filter Topology Real UpperHalfPlane
open scoped MatrixGroups ENNReal

namespace OrbicurveCores.M2

variable (Γ : Subgroup SL(2, ℝ)) (F : Set ℍ)

/-- The multiplicity of `F` along the orbit of `z`. -/
noncomputable def mult (z : ℍ) : ℝ≥0∞ := ∑' γ : Γ, F.indicator 1 ((γ : SL(2, ℝ)) • z)

/-- The partition of unity. -/
noncomputable def pou (g : SL(2, ℝ)) : ℝ≥0∞ := F.indicator 1 (g • I) * (mult Γ F (g • I))⁻¹

variable {Γ F}

variable (hcov : ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F)
  (hfin : ∀ z : ℍ, {γ : SL(2, ℝ) | γ ∈ Γ ∧ γ • z ∈ F}.Finite)

end OrbicurveCores.M2
