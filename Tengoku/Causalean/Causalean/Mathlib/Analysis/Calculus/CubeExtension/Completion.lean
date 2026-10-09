module
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Calculus.CubeExtension.Contraction
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Interpolation

/-!
# Intrinsic fixed-cube Hölder completion

Interior interpolation is stated for within-cube jets. Continuous traces pass
its derivative bounds to every face of the closed cube.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [B ≥ 0](hyp:hB), [a response u is m times continuously differentiable
within the closed normalized cube](hyp:hu), [j ≤ m](hyp:hj), and [the order-j
intrinsic coordinate jet of u in a fixed choice of coordinate directions is
bounded in absolute value by B at every interior point of the cube](hyp:hinterior),
then [the same bound B holds at every point of the closed cube](goal). -/
theorem interior_coordJet_bound_extends {d m j : ℕ}
    {u : (Fin d → ℝ) → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hu : ContDiffOn ℝ m u (cube d)) (hj : j ≤ m)
    (f : Fin j → Fin d)
    (hinterior : ∀ x ∈ openCube d, |coordJetOn (cube d) j u f x| ≤ B) :
    ∀ x ∈ cube d, |coordJetOn (cube d) j u f x| ≤ B := by
  apply within_coordPartial_bound_extends hB hu hj f
  intro x hx
  have h := hinterior x hx
  rw [coordJetOn_cube_eq_ambient hu hj hx] at h
  exact h

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
