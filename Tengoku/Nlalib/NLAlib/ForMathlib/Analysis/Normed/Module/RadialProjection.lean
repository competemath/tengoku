import Tengoku.Seed.Analysis.Normed.Module.Basic
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Radial projection to a norm ball

The continuous radial retraction makes an almost-everywhere bounded random
vector globally bounded while keeping its law unchanged. It is defined in
every real normed vector space and does not require an inner product.
-/

noncomputable section
set_option autoImplicit false

namespace NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial projection to the closed ball about zero of positive radius `R`.
For `R = 0` it is zero; at negative radii the displayed scalar formula is used.-/
def radialProj (R : ℝ) (x : E) : E := (R / max R ‖x‖) • x

/-- Radial projection at radius zero is the zero map.
@isnad1 id=eq.0h2v.s5.34419f11eca5 from=translated src=- shape=b391549a vocab=3f40729e
-/
@[simp] theorem radialProj_zero (x : E) : radialProj 0 x = 0 := by
  simp [radialProj]

/-- Projection fixes every vector already inside the nonnegative-radius ball.
@isnad1 id=eq.2h3v.s5.5a7a49ce95f8 from=translated src=- shape=1b318f0e vocab=c316cbf8
-/
theorem radialProj_eq_self {R : ℝ} (hR : 0 ≤ R) {x : E} (hx : ‖x‖ ≤ R) :
    radialProj R x = x := by
  rcases hR.eq_or_lt with rfl | hR
  · have hx0 : x = 0 := norm_eq_zero.mp (le_antisymm hx (norm_nonneg _))
    simp [hx0]
  · simp [radialProj, max_eq_left hx, hR.ne']

/-- The projected vector always has norm at most the nonnegative radius.
@isnad1 id=le.1h3v.s5.5eb18cc64b52 from=translated src=- shape=73a6d464 vocab=c316cbf8
-/
theorem norm_radialProj_le {R : ℝ} (hR : 0 ≤ R) (x : E) : ‖radialProj R x‖ ≤ R := by
  rcases hR.eq_or_lt with rfl | hR
  · simp
  have hd : 0 < max R ‖x‖ := hR.trans_le (le_max_left _ _)
  rw [radialProj, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hR.le hd.le), div_mul_eq_mul_div]
  exact (div_le_iff₀ hd).mpr
    (mul_le_mul_of_nonneg_left (le_max_right R ‖x‖) hR.le)

/-- Radial projection is continuous, including radius zero.
@isnad1 id=continuo.1h2v.s5.d52e272b6c1d from=translated src=- shape=a322f847 vocab=c9671a65
-/
theorem continuous_radialProj {R : ℝ} (hR : 0 ≤ R) :
    Continuous (radialProj R : E → E) := by
  rcases hR.eq_or_lt with rfl | hR
  · have hz : (radialProj 0 : E → E) = fun _ => 0 := funext radialProj_zero
    rw [hz]
    exact continuous_const
  exact (continuous_const.div (continuous_const.max continuous_norm)
    (fun x => (hR.trans_le (le_max_left R ‖x‖)).ne')).smul continuous_id

end NormedSpace
