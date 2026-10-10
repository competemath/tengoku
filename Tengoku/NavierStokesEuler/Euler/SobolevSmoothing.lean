import Tengoku.NavierStokesEuler.Euler.CylinderSobolevDerivatives

/-! Genuine one-derivative L² smoothing lifts to the complete cylinder Sobolev scale. -/

noncomputable section

namespace EulerSobolevSmoothing

open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderSobolevSpace
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

variable (A : LiftL2 period →L[ℝ] LiftL2 period) (C : ℝ)
variable (hD : ∀ i : Fin 4, ∀ f : LiftL2 period, ∃ g : LiftL2 period,
  HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t) (A f)) g 0 ∧
    ‖g‖ ≤ C * ‖f‖)

/-- The uniquely determined strong derivative of a genuinely smoothing L² operator. -/
def smoothingDerivative (i : Fin 4) (f : LiftL2 period) : LiftL2 period :=
  Classical.choose (hD i f)

/-- The chosen derivative is the actual strong derivative of the translated output. -/
theorem smoothingDerivative_hasDerivAt (i : Fin 4) (f : LiftL2 period) :
    HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t) (A f))
      (smoothingDerivative period A C hD i f) 0 := (Classical.choose_spec (hD i f)).1

/-- The actual derivative obeys the given L² smoothing estimate. -/
theorem smoothingDerivative_bound (i : Fin 4) (f : LiftL2 period) :
    ‖smoothingDerivative period A C hD i f‖ ≤ C * ‖f‖ := (Classical.choose_spec (hD i f)).2

/-- Uniqueness of strong derivatives proves additivity of the smoothing derivative. -/
theorem smoothingDerivative_add (i : Fin 4) (f g : LiftL2 period) :
    smoothingDerivative period A C hD i (f + g) =
      smoothingDerivative period A C hD i f + smoothingDerivative period A C hD i g := by
  apply (smoothingDerivative_hasDerivAt period A C hD i (f + g)).unique
  simpa only [map_add] using
    (smoothingDerivative_hasDerivAt period A C hD i f).fun_add
      (smoothingDerivative_hasDerivAt period A C hD i g)

/-- Uniqueness of strong derivatives proves homogeneity of the smoothing derivative. -/
theorem smoothingDerivative_smul (i : Fin 4) (r : ℝ) (f : LiftL2 period) :
    smoothingDerivative period A C hD i (r • f) = r • smoothingDerivative period A C hD i f := by
  apply (smoothingDerivative_hasDerivAt period A C hD i (r • f)).unique
  simpa only [map_smul, Pi.smul_def] using
    (smoothingDerivative_hasDerivAt period A C hD i f).const_smul r

/-- Each derivative of the smoothing operator is a bounded linear L² operator. -/
def smoothingDerivativeOperator (i : Fin 4) : LiftL2 period →L[ℝ] LiftL2 period :=
  LinearMap.mkContinuous
    { toFun := smoothingDerivative period A C hD i
      map_add' := smoothingDerivative_add period A C hD i
      map_smul' := smoothingDerivative_smul period A C hD i }
    C (smoothingDerivative_bound period A C hD i)

/-- The bounded derivative operator retains its actual strong-derivative characterization. -/
theorem smoothingDerivativeOperator_hasDerivAt (i : Fin 4) (f : LiftL2 period) :
    HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t) (A f))
      (smoothingDerivativeOperator period A C hD i f) 0 :=
  smoothingDerivative_hasDerivAt period A C hD i f

/-- Differentiating a translation-commuting smoothing operator preserves translation commutation. -/
theorem smoothingDerivative_translation
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (i : Fin 4) (a : LiftDomain period) (f : LiftL2 period) :
    translation period a (smoothingDerivativeOperator period A C hD i f) =
      smoothingDerivativeOperator period A C hD i (translation period a f) := by
  have hd := (translation period a).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    (smoothingDerivative_hasDerivAt period A C hD i f)
  have he : (fun t => translation period a
      (translation period (translationPath period (standardDirection i) t) (A f))) =
      fun t => translation period (translationPath period (standardDirection i) t)
        (A (translation period a f)) := by
    funext t
    rw [hA]
    exact translations_commute period a _ _
  change HasDerivAt (fun t => translation period a
    (translation period (translationPath period (standardDirection i) t) (A f)))
    (translation period a (smoothingDerivative period A C hD i f)) 0 at hd
  rw [he] at hd
  exact hd.unique (smoothingDerivative_hasDerivAt period A C hD i (translation period a f))

/-- A true smoothing operator adds one complete level to any finite strong derivative jet. -/
def gainJet {q : ℕ} {f : LiftL2 period}
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (J : SpatialJet period standardDirection q f) : SpatialJet period standardDirection (q + 1) (A f) :=
  .succ (fun i => smoothingDerivativeOperator period A C hD i f)
    (fun i => EulerPressureJetIdentities.SpatialJet.map
      (smoothingDerivativeOperator period A C hD i)
      (smoothingDerivative_translation period A C hD hA i) J)
    (fun i => smoothingDerivativeOperator_hasDerivAt period A C hD i f)

/-- The Sobolev element obtained by actual one-derivative smoothing. -/
def gain {q : ℕ}
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (u : SobolevSpace period q) : SobolevSpace period (q + 1) :=
  ofJet period (gainJet period A C hD hA (toJet period u))

/-- Smoothing on the Sobolev scale has exactly the original L² output. -/
@[simp]
theorem gain_value {q : ℕ}
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (u : SobolevSpace period q) : value period (gain period A C hD hA u) = A (value period u) :=
  value_ofJet period _

end EulerSobolevSmoothing
