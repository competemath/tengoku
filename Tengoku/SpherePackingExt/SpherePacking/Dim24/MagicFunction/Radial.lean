module
public import Tengoku.Seed.Analysis.InnerProductSpace.PiL2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Radialization helpers

These definitions are only meant to provide a convenient bridge between the paper's
one-variable notation `r ↦ g(r)` (with `r = ‖x‖`) and the Lean functions `g : ℝ²⁴ → ℂ`.

We model the one-variable profile by restricting to the first coordinate axis:
`r ↦ g(axisVec r)`.

## Main definitions
* `axisVec`
* `radialProfile`
-/

namespace SpherePacking.Dim24

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-
We work in a `noncomputable` section: this file is purely analytic and not intended
for computation.
-/
noncomputable section

/-- The first axis vector `(r, 0, 0, ..., 0) ∈ ℝ²⁴`.-/
@[expose]
public noncomputable def axisVec (r : ℝ) : ℝ²⁴ :=
  EuclideanSpace.single (𝕜 := ℝ) (ι := Fin 24) 0 r

/-- The axis vector at `0` is `0`.-/
@[simp] public lemma axisVec_zero : axisVec (0 : ℝ) = 0 := by
  simp [axisVec]

/-- Restrict a function on `ℝ²⁴` to the first axis, to obtain a one-variable radial profile.-/
@[expose]
public noncomputable def radialProfile {α : Type*} (g : ℝ²⁴ → α) (r : ℝ) : α :=
  g (axisVec r)

/-- Unfolding lemma for `radialProfile`.-/
@[simp] public lemma radialProfile_apply {α : Type*} (g : ℝ²⁴ → α) (r : ℝ) :
    radialProfile g r = g (axisVec r) := rfl

end

end SpherePacking.Dim24
