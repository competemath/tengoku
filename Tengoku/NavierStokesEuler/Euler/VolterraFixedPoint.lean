import Tengoku.NavierStokesEuler.Euler.VolterraConvolution
import Tengoku

/-! Banach's theorem applied to the actual singular Volterra integral on continuous paths. -/

noncomputable section

namespace EulerVolterraConvolution

open MeasureTheory Set Metric
open scoped Topology NNReal

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable (T : ℝ) (hT : 0 ≤ T) (K : ℝ → Y →L[ℝ] X) (k : ℝ → ℝ)
variable (hK : ContinuousOn (fun p : ℝ × Y => K p.1 p.2) (Ioi 0 ×ˢ (univ : Set Y)))
variable (hk : IntegrableOn k (Ioc 0 T)) (hk0 : ∀ r ∈ Ioc 0 T, 0 ≤ k r)
variable (hbound : ∀ r ∈ Ioc 0 T, ∀ y, ‖K r y‖ ≤ k r * ‖y‖)

include hK hk hk0 hbound in
/-- The actual Bochner convolution commutes with subtraction of continuous paths. -/
theorem convolution_sub (f g : C(Icc (0 : ℝ) T, Y)) :
    convolution T hT K k hK hk hk0 hbound (f - g) =
      convolution T hT K k hK hk hk0 hbound f - convolution T hT K k hK hk hk0 hbound g := by
  ext t
  change (∫ r in Ioc 0 T, causalIntegrand T hT K (f - g) t r) =
    (∫ r in Ioc 0 T, causalIntegrand T hT K f t r) -
      ∫ r in Ioc 0 T, causalIntegrand T hT K g t r
  rw [← integral_sub (causalIntegrand_integrable T hT K k hK hk hk0 hbound f t)
    (causalIntegrand_integrable T hT K k hK hk hk0 hbound g t)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r => by
    by_cases hr : r ≤ t.val <;> simp [causalIntegrand, indicator, hr, extendPath, map_sub]

include hK hk hk0 hbound in
/-- The actual convolution is Lipschitz with constant equal to its scalar kernel mass. -/
theorem convolution_sub_bound (f g : C(Icc (0 : ℝ) T, Y)) :
    ‖convolution T hT K k hK hk hk0 hbound f - convolution T hT K k hK hk hk0 hbound g‖ ≤
      kernelMass T k * ‖f - g‖ := by
  rw [← convolution_sub T hT K k hK hk hk0 hbound]
  exact convolution_bound T hT K k hK hk hk0 hbound (f - g)

/-- Pointwise application of an actual continuous time-dependent nonlinearity to a path. -/
def pathNonlinearity (F : Icc (0 : ℝ) T → X → Y)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × X => F p.1 p.2))
    (u : C(Icc (0 : ℝ) T, X)) : C(Icc (0 : ℝ) T, Y) where
  toFun t := F t (u t)
  continuous_toFun := hF.comp (continuous_id.prodMk u.continuous)

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
/-- A local Lipschitz nonlinearity induces the same local Lipschitz bound on path space. -/
theorem pathNonlinearity_sub_bound (F : Icc (0 : ℝ) T → X → Y)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × X => F p.1 p.2))
    (R L : ℝ) (hL : 0 ≤ L)
    (hFL : ∀ t x y, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖F t x - F t y‖ ≤ L * ‖x - y‖)
    (u v : C(Icc (0 : ℝ) T, X)) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖pathNonlinearity T F hF u - pathNonlinearity T F hF v‖ ≤ L * ‖u - v‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hL (norm_nonneg _))).mpr
  intro t
  exact (hFL t (u t) (v t) ((u.norm_coe_le_norm t).trans hu) ((v.norm_coe_le_norm t).trans hv)).trans
    (mul_le_mul_of_nonneg_left ((u - v).norm_coe_le_norm t) hL)

/-- The actual nonlinear Volterra map, including the prescribed free evolution. -/
def picard (a : C(Icc (0 : ℝ) T, X)) (F : Icc (0 : ℝ) T → X → Y)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × X => F p.1 p.2))
    (u : C(Icc (0 : ℝ) T, X)) : C(Icc (0 : ℝ) T, X) :=
  a + convolution T hT K k hK hk hk0 hbound (pathNonlinearity T F hF u)

include hK hk hk0 hbound in
/-- The actual Picard map has contraction coefficient equal to kernel mass times nonlinear Lipschitz constant. -/
theorem picard_sub_bound (a : C(Icc (0 : ℝ) T, X)) (F : Icc (0 : ℝ) T → X → Y)
    (hF : Continuous (fun p : Icc (0 : ℝ) T × X => F p.1 p.2))
    (R L : ℝ) (hL : 0 ≤ L)
    (hFL : ∀ t x y, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖F t x - F t y‖ ≤ L * ‖x - y‖)
    (u v : C(Icc (0 : ℝ) T, X)) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖picard T hT K k hK hk hk0 hbound a F hF u - picard T hT K k hK hk hk0 hbound a F hF v‖ ≤
      (kernelMass T k * L) * ‖u - v‖ := by
  simp only [picard, add_sub_add_left_eq_sub]
  exact (convolution_sub_bound T hT K k hK hk hk0 hbound _ _).trans
    ((mul_le_mul_of_nonneg_left (pathNonlinearity_sub_bound T F hF R L hL hFL u v hu hv)
      (kernelMass_nonneg T k hk0)).trans_eq (mul_assoc _ _ _).symm)

end EulerVolterraConvolution
