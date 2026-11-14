import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The scalar analytic implicit-function theorem for the real saddle branch. -/

namespace PiIrrationality

open Filter
open scoped Topology ContDiff

/--
@isnad1 id=isinvert.1h1v.s7.336ffa69be60 from=translated src=- shape=b0109325 vocab=82dc5c22
-/
theorem real_linear_isInvertible_of_apply_one_ne_zero (L : ℝ →L[ℝ] ℝ) (hL : L 1 ≠ 0) :
    L.IsInvertible := by
  have he (x : ℝ) : L x = x * L 1 := by
    calc
      L x = L (x • (1 : ℝ)) := by simp
      _ = x • L 1 := L.map_smul x 1
      _ = _ := rfl
  let g : ℝ →L[ℝ] ℝ := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := g)
  · apply ContinuousLinearMap.ext
    intro x
    change L ((L 1)⁻¹ * x) = x
    rw [he ((L 1)⁻¹ * x)]
    field_simp
  · apply ContinuousLinearMap.ext
    intro x
    change (L 1)⁻¹ * L x = x
    rw [he x]
    field_simp

/--
@isnad1 id=ex.3h4v.s8.672f47b67cc8 from=translated src=- shape=68d4b9b1 vocab=a6c488b8
-/
theorem exists_analytic_scalar_implicit {f : (ℝ × ℝ) × ℝ → ℝ} {p : ℝ × ℝ} {y d : ℝ}
    (hf : AnalyticAt ℝ f (p, y)) (hd : HasDerivAt (fun t => f (p, t)) d y)
    (hd0 : d ≠ 0) :
    ∃ g : ℝ × ℝ → ℝ, g p = y ∧ AnalyticAt ℝ g p ∧
      ∀ᶠ q in 𝓝 p, f (q, g q) = f (p, y) := by
  have hc : ContDiffAt ℝ ω f (p, y) := hf.contDiffAt
  have hin : HasFDerivAt (fun t : ℝ => (p, t))
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) y := by
    have hconst : HasFDerivAt (fun _ : ℝ => p) (0 : ℝ →L[ℝ] ℝ × ℝ) y :=
      hasFDerivAt_const p y
    have hid : HasFDerivAt (fun t : ℝ => t) (ContinuousLinearMap.id ℝ ℝ) y :=
      hasFDerivAt_id y
    have hm : (0 : ℝ →L[ℝ] ℝ × ℝ).prod (ContinuousLinearMap.id ℝ ℝ) =
        ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ := by ext t <;> simp
    simpa only [hm] using hconst.prodMk hid
  have hcomp := hf.differentiableAt.hasFDerivAt.comp y hin
  have he := hcomp.unique hd.hasFDerivAt
  have hi : (fderiv ℝ f (p, y) ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ).IsInvertible := by
    apply real_linear_isInvertible_of_apply_one_ne_zero
    rw [he]
    simpa using hd0
  let g := hc.implicitFunction (by simp) hi
  exact ⟨g, hc.implicitFunction_apply_self (by simp) hi,
    (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt,
    hc.eventually_apply_implicitFunction (by simp) hi⟩

end PiIrrationality
