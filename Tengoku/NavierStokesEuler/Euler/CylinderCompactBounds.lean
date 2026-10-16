import Tengoku.NavierStokesEuler.Euler.CylinderCompactTranslation
import Tengoku.NavierStokesEuler.Euler.ParameterSobolevCoefficient

/-!
True mixed L² derivative bounds for compact smooth cylinder data. One
fixed compact support set supplies the L² mass factor at every order.
The conversion to fixed-Hq word sums is performed once on the initial
datum, before any same-radius inverse estimate is applied.
-/

noncomputable section

namespace EulerCylinderCompact

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerMetricTransport EulerLiftedWeakDerivative
  EulerLpDerivative EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

universe u

variable (P : ℝ) [Fact (0 < P)]

def supportMass (K : Set (LiftDomain P)) (hK : IsCompact K) : ℝ :=
  ‖(indicatorConstLp 2 hK.isClosed.measurableSet hK.measure_ne_top (1 : ℝ) :
    Lp ℝ 2 (liftMeasure P))‖

namespace CompactField

variable {P} {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [Fact (0 < P)] in
theorem derivative_support (A : CompactField P V) : tsupport A.derivative.field ⊆ tsupport A.field := by
  apply closure_minimal _ (isClosed_tsupport A.field)
  intro x hx
  by_contra hn
  exact hx (fieldFDeriv_zero_outside P A.field x hn)

theorem toLp_norm_le (A : CompactField P V) (K : Set (LiftDomain P)) (hK : IsCompact K)
    (hs : tsupport A.field ⊆ K) (C : ℝ) (hb : ∀ x, ‖A.field x‖ ≤ C) :
    ‖A.toLp‖ ≤ C*supportMass P K hK := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [A.toLp_ae,
    (indicatorConstLp_coeFn (p := 2) (μ := liftMeasure P)
      (hs := hK.isClosed.measurableSet) (hμs := hK.measure_ne_top) (c := (1 : ℝ)))] with x ha hk
  rw [ha,hk]
  by_cases hx : x ∈ K
  · simpa only [Set.indicator_of_mem hx,norm_one,mul_one] using hb x
  · have hz : A.field x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
    simp only [Set.indicator_of_notMem hx,hz,norm_zero,mul_zero,le_refl]

end CompactField
end EulerCylinderCompact
