module

public import Tengoku.AtPalomar.Paper.Hyperbolic
public import Tengoku.Seed.Analysis.ODE.ExistUnique
public import Tengoku.Seed.Topology.ContinuousMap.Compact
public import Tengoku
public import Tengoku.Seed.Probability.Process.Adapted
public import Tengoku.Seed.Topology.Order.ProjIcc
public import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Pathwise state equation for a Dirac Parisi measure

For a continuous noise path `W`, subtracting the additive term `β W` from the
post-interface state reduces the equation to an ordinary differential equation.
The bounded globally Lipschitz tanh drift gives existence on the full finite
time interval and pathwise uniqueness, using Picard–Lindelöf.
-/

noncomputable section
open Set MeasureTheory Metric
open scoped NNReal Topology

namespace Paper

/-- The pathwise drift after the additive noise is subtracted.-/
def diracNoiseDrift (β : ℝ) (W : ℝ → ℝ) (t y : ℝ) : ℝ :=
  β ^ 2 * Real.tanh (y + β * W t)

/-- The drift is bounded by `β²`, uniformly in the noise path and state.-/
theorem norm_diracNoiseDrift_le (β : ℝ) (W : ℝ → ℝ) (t y : ℝ) :
    ‖diracNoiseDrift β W t y‖ ≤ β ^ 2 := by
  unfold diracNoiseDrift
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg β), Real.norm_eq_abs]
  exact mul_le_of_le_one_right (sq_nonneg β) (Real.abs_tanh_lt_one _).le

/-- A pathwise solution of the drift ODE on the post-interface interval.-/
structure IsDiracNoiseSolution (β h q : ℝ) (W Y : ℝ → ℝ) : Prop where
  initial : Y q = h
  hasDerivWithinAt : ∀ t ∈ Icc q (1 : ℝ),
    HasDerivWithinAt Y (diracNoiseDrift β W t (Y t)) (Icc q (1 : ℝ)) t

namespace IsDiracNoiseSolution

variable {β h q : ℝ} {W Y Z : ℝ → ℝ}

/-- Every pathwise ODE solution is continuous on its interval.-/
theorem continuousOn (hY : IsDiracNoiseSolution β h q W Y) :
    ContinuousOn Y (Icc q (1 : ℝ)) :=
  HasDerivWithinAt.continuousOn hY.hasDerivWithinAt

end IsDiracNoiseSolution

/-- The state part before and after the interface, reconstructed from the drift correction.-/
def diracStateFromCorrection (β h q : ℝ) (W Y : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ q then h + β * W t else Y t + β * W t

/-- Noise dependence constant on the full post-interface interval.-/
def diracCorrectionConstant (β q : ℝ) : ℝ :=
  gronwallBound 0 (β ^ 2) (β ^ 2 * |β|) (1 - q)

theorem diracCorrectionConstant_nonneg (β q : ℝ) (hq : q ≤ 1) :
    0 ≤ diracCorrectionConstant β q := by
  have hm := gronwallBound_mono (δ := (0 : ℝ)) (K := β ^ 2)
    (ε := β ^ 2 * |β|) le_rfl (by positivity) (sq_nonneg β)
    (show 0 ≤ 1 - q from sub_nonneg.mpr hq)
  simpa [diracCorrectionConstant, gronwallBound_x0] using hm

/-- Extend a compact continuous noise path constantly beyond its endpoints.-/
def compactNoiseExtension (a b : ℝ) (hab : a ≤ b) (w : C(Icc a b, ℝ)) : ℝ → ℝ :=
  fun t => w (projIcc a b hab t)

theorem continuous_compactNoiseExtension (a b : ℝ) (hab : a ≤ b)
    (w : C(Icc a b, ℝ)) : Continuous (compactNoiseExtension a b hab w) :=
  w.continuous.comp continuous_projIcc

/-- Restrict a continuous noise path to its history up to time `t`.-/
def diracNoisePast (t : Icc (0 : ℝ) 1) (w : C(Icc (0 : ℝ) 1, ℝ)) :
    C(Icc (0 : ℝ) (t : ℝ), ℝ) :=
  ⟨fun s => w ⟨s, s.property.1, s.property.2.trans t.property.2⟩,
    w.continuous.comp (continuous_subtype_val.subtype_mk _)⟩

/-- Extend a noise history constantly to the full state time interval.-/
def diracPastExtensionPath (t : Icc (0 : ℝ) 1)
    (w : C(Icc (0 : ℝ) (t : ℝ), ℝ)) : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun s => compactNoiseExtension 0 t t.property.1 w s,
    (continuous_compactNoiseExtension 0 t t.property.1 w).comp continuous_subtype_val⟩

theorem lipschitzWith_diracPastExtensionPath (t : Icc (0 : ℝ) 1) :
    LipschitzWith 1 (diracPastExtensionPath t) := by
  apply LipschitzWith.of_dist_le_mul
  intro w v
  norm_num only [NNReal.coe_one, one_mul]
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro s
  exact ContinuousMap.dist_apply_le_dist (f := w) (g := v) (projIcc (0 : ℝ) (t : ℝ) t.property.1 (s : ℝ))

/-- The continuous integral formulation of the actual additive-noise equation.-/
structure IsDiracStateSolution (β h q : ℝ) (W X : ℝ → ℝ) : Prop where
  continuous : Continuous X
  before : ∀ t ∈ Icc (0 : ℝ) q, X t = h + β * W t
  after : ∀ t ∈ Icc q (1 : ℝ),
    X t = h + β * W t + ∫ s in q..t, β ^ 2 * Real.tanh (X s)

end Paper
