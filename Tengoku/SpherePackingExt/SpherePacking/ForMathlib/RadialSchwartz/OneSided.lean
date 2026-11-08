module
public import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.RadialSchwartz.Cutoff
public import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.RadialSchwartz.Multidimensional
import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.BoundsOnIcc

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# One-sided decay to a radial Schwartz function

If `f : ℝ → ℂ` is smooth and satisfies Schwartz-type bounds for all iterated derivatives on `0 ≤ r`,
then the radial function `x ↦ f (‖x‖ ^ 2)` is Schwartz on any real inner product space `F`.

The construction multiplies `f` by a smooth cutoff on `ℝ` (to make it globally Schwartz), then
lifts it to `F` by composing with `‖x‖ ^ 2`.
-/

namespace RadialSchwartz

noncomputable section

open scoped Topology
open Set SchwartzMap

lemma iteratedFDeriv_cutoffC_mul_eq_zero_of_lt {f : ℝ → ℂ} {x : ℝ} (hx : x < -1) (n : ℕ) :
    iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x = 0 := by
  have hEq : (fun r ↦ cutoffC r * f r) =ᶠ[𝓝 x] fun _ ↦ (0 : ℂ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [cutoffC_eq_zero_of_le (le_of_lt hy)]
  simpa using (hEq.iteratedFDeriv (𝕜 := ℝ) n).self_of_nhds

lemma iteratedFDeriv_cutoffC_mul_eq_of_pos {f : ℝ → ℂ} {x : ℝ} (hx : 0 < x) (n : ℕ) :
    iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x = iteratedFDeriv ℝ n f x := by
  have hEq : (fun r ↦ cutoffC r * f r) =ᶠ[𝓝 x] f := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [cutoffC_eq_one_of_nonneg (le_of_lt hy)]
  simpa using (hEq.iteratedFDeriv (𝕜 := ℝ) n).self_of_nhds

lemma exists_bound_on_Icc_of_continuous {g : ℝ → ℝ} (hg : Continuous g) :
    ∃ C, ∀ x ∈ Icc (-1 : ℝ) 0, g x ≤ C := by
  simpa using SpherePacking.ForMathlib.Continuous.exists_upper_bound_on_Icc (g := g) hg
    (a := (-1 : ℝ)) (b := 0) (by norm_num)

namespace Bridge

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### The bridge to `𝓢(F,ℂ)` -/

/-- A cutoff-modified version of a radial profile, used to build a Schwartz function on `ℝ`.-/
@[expose] public def fCut (f : ℝ → ℂ) (r : ℝ) : ℂ := cutoffC r * f r

end Bridge

end

end RadialSchwartz
