/-
Shared segment parametrisations for the `J₁/J₂` permutation developments.

Both the dimension-8 and dimension-24 `b`-eigenfunction proofs use the same four vertical/horizontal
segments in the upper half plane:

* `z₁line`: `-1 → -1 + I`
* `z₂line`: `-1 + I → I`
* `z₃line`: `1 → 1 + I`
* `z₄line`: `1 + I → I`

We centralize their definitions and basic continuity/imag-part facts here to avoid duplicating
boilerplate across dimensions.
-/
module

public import Tengoku.Seed.Analysis.Complex.Basic
public import Tengoku.Seed.Topology.Basic
public import Tengoku.SpherePackingExt.SpherePacking.MagicFunction.IntegralParametrisations

public import Tengoku.Seed.LinearAlgebra.AffineSpace.AffineMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Set
open scoped Interval Topology

namespace SpherePacking.Contour

noncomputable section

open MagicFunction.Parametrisations

/-- Parametrization of the segment `-1 → -1 + I` (for `t ∈ [0,1]`).-/
@[expose] public def z₁line (t : ℝ) : ℂ := (-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)

/-- Parametrization of the segment `-1 + I → I` (for `t ∈ [0,1]`).-/
@[expose] public def z₂line (t : ℝ) : ℂ := (-1 : ℂ) + (t : ℂ) + Complex.I

/-- Parametrization of the segment `1 → 1 + I` (for `t ∈ [0,1]`).-/
@[expose] public def z₃line (t : ℝ) : ℂ := (1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)

/-- Parametrization of the segment `1 + I → I` (for `t ∈ [0,1]`).-/
@[expose] public def z₄line (t : ℝ) : ℂ := (1 : ℂ) - (t : ℂ) + Complex.I

@[simp] public lemma z₁line_def (t : ℝ) :
    z₁line t = (-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) := rfl

@[simp] public lemma z₂line_def (t : ℝ) : z₂line t = (-1 : ℂ) + (t : ℂ) + Complex.I := rfl

@[simp] public lemma z₃line_def (t : ℝ) :
    z₃line t = (1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) := rfl

@[simp] public lemma z₄line_def (t : ℝ) : z₄line t = (1 : ℂ) - (t : ℂ) + Complex.I := rfl

@[simp] public lemma z₂line_im (t : ℝ) : (z₂line t).im = 1 := by simp [z₂line, add_assoc]

@[simp] public lemma z₄line_im (t : ℝ) : (z₄line t).im = 1 := by
  simp [z₄line, sub_eq_add_neg, add_assoc]

/-! ### `AffineMap.lineMap` descriptions of the `zⱼline` segments -/

/-! ### Matching `MagicFunction.Parametrisations.zⱼ'` with `zⱼline` on `[0,1]` -/

/-! ### `AffineMap.lineMap` equals `zⱼ'` on `[0,1]` -/

/-! ### Convenience lemmas for the left-side segments -/

@[simp] public lemma z₁line_add_one (t : ℝ) : z₁line t + 1 = (Complex.I : ℂ) * (t : ℂ) := by
  simp [z₁line, add_left_comm, add_comm]

@[simp] public lemma z₂line_add_one (t : ℝ) : z₂line t + 1 = (t : ℂ) + Complex.I := by
  simp [z₂line, add_left_comm, add_comm]

end

end SpherePacking.Contour

/-!
### Non-vanishing facts for the left-side segments

Several contour-change arguments require that the two left-side segments avoid `0` so that
`mobiusInv z = -z⁻¹` is well-defined.
These lemmas used to live in `SpherePacking/Contour/Segments.lean`; we keep them here to reduce
file count.
-/

namespace SpherePacking

open Complex Real Set
open scoped Interval

noncomputable section

private lemma ne_zero_of_re_ne_zero {z : ℂ} (hre : z.re ≠ 0) : z ≠ 0 :=
  fun hz => hre (by simpa using congrArg Complex.re hz)

private lemma ne_zero_of_im_ne_zero {z : ℂ} (him : z.im ≠ 0) : z ≠ 0 :=
  fun hz => him (by simpa using congrArg Complex.im hz)

end

end SpherePacking
