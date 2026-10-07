/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Defs
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Internal
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Exact.Internal

/-!
# Threshold decay of Gaussian crossings: proofs

* **Angular window.** Write a point of the plane as `(R cos ψ, R sin ψ)` with `R > 0` and
  `ψ ∈ (-π, π)`, and put `θ = |ψ|`. Then `cos ψ = cos θ` and `|sin ψ| = sin θ`, so for
  `φ ≥ 0` the event `|cos φ x - c| ≤ sin φ |y|` reads
  `R cos (θ + φ) ≤ c ≤ R cos (θ - φ)`. Hence `|c| ≤ R`, and with `m = arccos (c / R)`,
  monotonicity of `arccos` gives `|θ - m| ≤ φ`. So at each radius the event occupies at
  most two arcs of length `2φ`, and none below radius `|c|`.
* **Radial tail.** `R exp (-R²/2)` has antiderivative `-exp (-R²/2)`, so its integral over
  `R > a` is `exp (-a²/2)`.
* **Decay of the angle law.** In polar coordinates the standard planar Gaussian has density
  `exp (-R²/2) / (2π)`. Bounding the angular slice by `4φ` above radius `|c|` and
  integrating the radial tail gives `(2/π) φ exp (-c²/2)`.
* **Crossings.** As in Sheppard's bound, `U = form (α + β)` and `V = form (β - α)` are
  independent and a crossing forces `|U - 2t| ≤ |V|`. Rescaling to standard Gaussians puts
  this event in the above form with `tan φ = ‖β - α‖ / ‖α + β‖` and threshold
  `2t / √(‖α + β‖² + ‖β - α‖²)`; no Anderson step is needed.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory Set Real Filter Topology
open scoped NNReal ENNReal

/-! ### The angular window -/

/-- On `[-π, π]`, `|sin ψ| = sin |ψ|`. -/
theorem abs_sin_eq_sin_abs {ψ : ℝ} (h : |ψ| ≤ π) : |sin ψ| = sin |ψ| := by
  have hs : 0 ≤ sin |ψ| := sin_nonneg_of_nonneg_of_le_pi (abs_nonneg ψ) h
  rcases abs_cases ψ with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hs ⊢
  · exact abs_of_nonneg hs
  · rw [sin_neg] at hs ⊢
    exact abs_of_nonpos (by linarith)

/-- If `cos (θ + φ) ≤ y ≤ cos (θ - φ)` with `θ ∈ [0, π]` and `φ ≥ 0`, then `θ` lies within
`φ` of `arccos y`. -/
theorem abs_sub_arccos_le {θ φ y : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) (hφ : 0 ≤ φ)
    (h1 : cos (θ + φ) ≤ y) (h2 : y ≤ cos (θ - φ)) : |θ - arccos y| ≤ φ := by
  rw [abs_le]
  constructor
  · rcases le_or_gt (θ + φ) π with h | h
    · have := antitone_arccos h1
      rw [arccos_cos (by linarith) h] at this
      linarith
    · linarith [arccos_le_pi y]
  · rcases le_or_gt (θ - φ) 0 with h | h
    · linarith [arccos_nonneg y]
    · have := antitone_arccos h2
      rw [arccos_cos h.le (by linarith)] at this
      linarith

/-- At radius `R > 0` and angle `ψ ∈ [-π, π]`, the event `|cos φ x - c| ≤ sin φ |y|` forces
`|c| ≤ R` and puts `|ψ|` within `φ` of `arccos (c / R)`. -/
theorem polar_event {φ c R ψ : ℝ} (hφ : 0 ≤ φ) (hR : 0 < R) (hψ : |ψ| ≤ π)
    (h : |cos φ * (R * cos ψ) - c| ≤ sin φ * |R * sin ψ|) :
    |c| ≤ R ∧ |(|ψ|) - arccos (c / R)| ≤ φ := by
  rw [abs_mul, abs_of_pos hR, abs_sin_eq_sin_abs hψ, ← cos_abs ψ] at h
  have h' := abs_le.1 h
  have hlo : R * cos (|ψ| + φ) ≤ c := by rw [cos_add]; nlinarith [h'.2]
  have hhi : c ≤ R * cos (|ψ| - φ) := by rw [cos_sub]; nlinarith [h'.1]
  have hc1 : c / R ≤ cos (|ψ| - φ) := by rw [div_le_iff₀ hR]; linarith
  have hc2 : cos (|ψ| + φ) ≤ c / R := by rw [le_div_iff₀ hR]; linarith
  refine ⟨abs_le.2 ⟨?_, ?_⟩, abs_sub_arccos_le (abs_nonneg ψ) hψ hφ hc2 hc1⟩
  · nlinarith [mul_le_mul_of_nonneg_left (neg_one_le_cos (|ψ| + φ)) hR.le]
  · nlinarith [mul_le_mul_of_nonneg_left (cos_le_one (|ψ| - φ)) hR.le]

/-- At radius `R > 0`, the angles in `(-π, π)` of the event `|cos φ x - c| ≤ sin φ |y|` have
total length at most `4φ`, and there are none unless `|c| ≤ R`. -/
theorem volume_polar_event_le {φ c R : ℝ} (hφ : 0 ≤ φ) (hR : 0 < R) :
    volume ({ψ : ℝ | |cos φ * (R * cos ψ) - c| ≤ sin φ * |R * sin ψ|} ∩ Ioo (-π) π) ≤
      (Ici |c|).indicator (fun _ => ENNReal.ofReal (4 * φ)) R := by
  set m := arccos (c / R)
  by_cases hc : |c| ≤ R
  · rw [indicator_of_mem (show R ∈ Ici |c| from hc)]
    calc volume ({ψ : ℝ | |cos φ * (R * cos ψ) - c| ≤ sin φ * |R * sin ψ|} ∩ Ioo (-π) π)
        ≤ volume (Icc (m - φ) (m + φ) ∪ Icc (-(m + φ)) (-(m - φ))) := by
          refine measure_mono fun ψ ⟨h, h1, h2⟩ => ?_
          have := abs_le.1 (polar_event hφ hR (abs_le.2 ⟨h1.le, h2.le⟩) h).2
          rcases abs_cases ψ with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at this
          · exact Or.inl ⟨by linarith, by linarith⟩
          · exact Or.inr ⟨by linarith, by linarith⟩
      _ ≤ volume (Icc (m - φ) (m + φ)) + volume (Icc (-(m + φ)) (-(m - φ))) :=
          measure_union_le _ _
      _ = ENNReal.ofReal (4 * φ) := by
          rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 1
          ring
  · rw [indicator_of_notMem (show R ∉ Ici |c| from hc)]
    have hempty : {ψ : ℝ | |cos φ * (R * cos ψ) - c| ≤ sin φ * |R * sin ψ|} ∩ Ioo (-π) π = ∅ :=
      eq_empty_of_forall_notMem fun ψ ⟨h, h1, h2⟩ =>
        hc (polar_event hφ hR (abs_le.2 ⟨h1.le, h2.le⟩) h).1
    rw [hempty, measure_empty]

/-! ### The radial tail -/

/-! ### Decay of the planar angle law -/

/-- The angle `arctan (√r / √s)` has cosine `√s / √(s + r)` and sine `√r / √(s + r)`. -/
theorem cos_sin_arctan_sqrt_div {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) :
    cos (arctan (√r / √s)) = √s / √(s + r) ∧ sin (arctan (√r / √s)) = √r / √(s + r) := by
  have hs' : 0 < √s := Real.sqrt_pos.2 hs
  have hk : √(1 + (√r / √s) ^ 2) = √(s + r) / √s := by
    rw [div_pow, sq_sqrt hr, sq_sqrt hs.le, show 1 + r / s = (s + r) / s by field_simp,
      Real.sqrt_div (by linarith)]
  rw [cos_arctan, sin_arctan, hk]
  constructor <;> field_simp

end Algebraic.Cutwidth.Gaussian.Internal
