import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.FrameGaugeNormalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An explicit `SO(2)` frame gauge

This file instantiates the general gauge construction with the standard
rotation in the first two codomain coordinates.  Given a smooth spatial angle
field `φ(x)`, it produces a defining-map homotopy which rotates those two
normal equations from angle zero to angle `φ(x)`, without moving the zero
fiber.  This is the concrete frame-normalization move for every discrepancy
already reduced to the stable `SO(2)` block.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff RealInnerProductSpace

namespace Submission

namespace SO2FrameGauge

variable {m : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin (m + 2))
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

/-- First coordinate vector in the codomain.-/
def e0 : F := EuclideanSpace.single 0 1

/-- Second coordinate vector in the codomain.-/
def e1 : F := EuclideanSpace.single 1 1

/-- Rotation through `θ` in the first coordinate plane, written without a
matrix so that joint smoothness is immediate from scalar/vector calculus.-/
def rotate (θ : ℝ) (y : F) : F :=
  y + (((Real.cos θ - 1) * y 0 - Real.sin θ * y 1) • e0) +
    ((Real.sin θ * y 0 + (Real.cos θ - 1) * y 1) • e1)

/--
@isnad1 id=eq.0h3v.s8.bd9bc3c85b6e from=translated src=- shape=2fbb3996 vocab=9de68154
-/
@[simp] theorem rotate_apply_zero (θ : ℝ) (y : F) :
    rotate θ y 0 = Real.cos θ * y 0 - Real.sin θ * y 1 := by
  simp [rotate, e0, e1]
  ring

/--
@isnad1 id=eq.0h3v.s8.4942c0104c31 from=translated src=- shape=ca79ff87 vocab=b4532115
-/
@[simp] theorem rotate_apply_one (θ : ℝ) (y : F) :
    rotate θ y 1 = Real.sin θ * y 0 + Real.cos θ * y 1 := by
  simp [rotate, e0, e1]
  ring

/--
@isnad1 id=eq.2h4v.s7.18d69d620713 from=translated src=- shape=9e25d4c6 vocab=987df272
-/
theorem rotate_apply_other (θ : ℝ) (y : F) {i : Fin (m + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) : rotate θ y i = y i := by
  simp [rotate, e0, e1, hi0, hi1]

/-- Rotation by the negative angle is a left inverse.
@isnad1 id=eq.0h3v.s5.1557980d34a9 from=translated src=- shape=1a014de6 vocab=e9fdad14
-/
theorem rotate_neg_apply (θ : ℝ) (y : F) : rotate (-θ) (rotate θ y) = y := by
  ext i
  by_cases hi0 : i = 0
  · subst i
    simp only [rotate_apply_zero, rotate_apply_one, Real.cos_neg, Real.sin_neg]
    calc
      Real.cos θ * (Real.cos θ * y 0 - Real.sin θ * y 1) -
          -Real.sin θ * (Real.sin θ * y 0 + Real.cos θ * y 1) =
          (Real.sin θ ^ 2 + Real.cos θ ^ 2) * y 0 := by ring
      _ = y 0 := by rw [Real.sin_sq_add_cos_sq, one_mul]
  · by_cases hi1 : i = 1
    · subst i
      simp only [rotate_apply_zero, rotate_apply_one, Real.cos_neg, Real.sin_neg]
      calc
        -Real.sin θ * (Real.cos θ * y 0 - Real.sin θ * y 1) +
            Real.cos θ * (Real.sin θ * y 0 + Real.cos θ * y 1) =
            (Real.sin θ ^ 2 + Real.cos θ ^ 2) * y 1 := by ring
        _ = y 1 := by rw [Real.sin_sq_add_cos_sq, one_mul]
    · rw [rotate_apply_other _ _ hi0 hi1, rotate_apply_other _ _ hi0 hi1]

/-- Rotation by the negative angle is also a right inverse.
@isnad1 id=eq.0h3v.s5.f8a135b7aaac from=translated src=- shape=f8cc8985 vocab=e9fdad14
-/
theorem rotate_apply_neg (θ : ℝ) (y : F) : rotate θ (rotate (-θ) y) = y := by
  simpa using rotate_neg_apply (-θ) y

/-- The explicit rotation as a linear map.-/
def rotateLM (θ : ℝ) : F →ₗ[ℝ] F where
  toFun := rotate θ
  map_add' := by
    intro x y
    ext i
    by_cases hi0 : i = 0
    · subst i
      simp only [rotate_apply_zero, PiLp.add_apply]
      ring
    · by_cases hi1 : i = 1
      · subst i
        simp only [rotate_apply_one, PiLp.add_apply]
        ring
      · rw [rotate_apply_other θ (x + y) hi0 hi1]
        simp only [PiLp.add_apply]
        rw [rotate_apply_other θ x hi0 hi1, rotate_apply_other θ y hi0 hi1]
  map_smul' := by
    intro c x
    ext i
    by_cases hi0 : i = 0
    · subst i
      simp only [rotate_apply_zero, PiLp.smul_apply, RingHom.id_apply]
      ring
    · by_cases hi1 : i = 1
      · subst i
        simp only [rotate_apply_one, PiLp.smul_apply, RingHom.id_apply]
        ring
      · rw [rotate_apply_other θ (c • x) hi0 hi1]
        simp only [PiLp.smul_apply, RingHom.id_apply]
        rw [rotate_apply_other θ x hi0 hi1]

/-- The explicit rotation as a continuous linear map.-/
def rotateCLM (θ : ℝ) : F →L[ℝ] F :=
  (rotateLM θ).toContinuousLinearMap

/--
@isnad1 id=eq.0h3v.s10.9b029c900455 from=translated src=- shape=d0db5e31 vocab=5c777480
-/
@[simp] theorem rotateCLM_apply (θ : ℝ) (y : F) :
    rotateCLM θ y = rotate θ y :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.fc0035c00256 from=translated src=- shape=ceb047c7 vocab=01431a7d
-/
@[simp] theorem rotate_zero (y : F) : rotate 0 y = y := by
  ext i
  by_cases hi0 : i = 0
  · subst i
    simp
  · by_cases hi1 : i = 1
    · subst i
      simp
    · rw [rotate_apply_other _ _ hi0 hi1]

/--
@isnad1 id=eq.0h1v.s9.35db92256bd8 from=translated src=- shape=06e4df31 vocab=42bb04e7
-/
@[simp] theorem rotateCLM_zero : rotateCLM (m := m) 0 = ContinuousLinearMap.id ℝ F := by
  ext y
  simp

/--
@isnad1 id=bijectiv.0h2v.s10.7a44a0ab70a6 from=translated src=- shape=b36500af vocab=2e7edbf2
-/
theorem rotateCLM_bijective (θ : ℝ) : Bijective (rotateCLM (m := m) θ) := by
  constructor
  · intro x y hxy
    change rotate θ x = rotate θ y at hxy
    have h := congrArg (rotate (-θ)) hxy
    simpa only [rotate_neg_apply] using h
  · intro y
    refine ⟨rotate (-θ) y, ?_⟩
    change rotate θ (rotate (-θ) y) = y
    exact rotate_apply_neg θ y

/-- Joint smoothness of angle and vector.
@isnad1 id=contdiff.0h1v.s9.9b3da35cc370 from=translated src=- shape=0d0ba3b3 vocab=49871ab5
-/
theorem contDiff_rotate :
    ContDiff ℝ ∞ (fun p : ℝ × F => rotate p.1 p.2) := by
  unfold rotate e0 e1
  fun_prop

/-- The `SO(2)` rotation is a smooth curve in the continuous endomorphism
space.
@isnad1 id=contdiff.0h1v.s10.15378834dba8 from=translated src=- shape=952f3246 vocab=b95323b6
-/
theorem contDiff_rotateCLM :
    ContDiff ℝ ∞ (rotateCLM (m := m)) := by
  rw [contDiff_clm_apply_iff]
  intro y
  exact contDiff_rotate.comp (contDiff_id.prodMk contDiff_const)

/-- The space-dependent, collar-flat gauge family.-/
def gauge (φ : E → ℝ) (s : ℝ) (x : E) : F →L[ℝ] F :=
  rotateCLM (normRamp s * φ x)

/--
@isnad1 id=contdiff.1h2v.s11.d302760d0dee from=translated src=- shape=33ce38e7 vocab=7e3e7c9d
-/
theorem contDiff_gauge {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun p : ℝ × E => gauge φ p.1 p.2) := by
  apply contDiff_rotateCLM.comp
  exact (contDiff_normRamp.comp contDiff_fst).mul (hφ.comp contDiff_snd)

/--
@isnad1 id=eq.0h3v.s9.3911ef1d4fd3 from=translated src=- shape=c41a2e3b vocab=53393543
-/
@[simp] theorem gauge_zero (φ : E → ℝ) (x : E) :
    gauge φ 0 x = ContinuousLinearMap.id ℝ F := by
  rw [gauge, normRamp_of_le_quarter (show (0 : ℝ) ≤ 1 / 4 by norm_num), zero_mul,
    rotateCLM_zero]

/--
@isnad1 id=bijectiv.0h4v.s10.bcd8585d9e3a from=translated src=- shape=e7ed2290 vocab=7d3ac7c5
-/
theorem gauge_bijective (φ : E → ℝ) (s : ℝ) (x : E) :
    Bijective (gauge φ s x) :=
  rotateCLM_bijective _

/-- The explicit defining-map homotopy rotating the first two normal equations
through the spatial angle field `φ`.-/
def homotopy (X : FramedLevelSet (m + 2)) (φ : E → ℝ)
    (hφ : ContDiff ℝ ∞ φ) :=
  DefiningMapHomotopy.ofGauge X (gauge φ) (contDiff_gauge hφ)
    (gauge_zero φ) (fun s _ x => gauge_bijective φ s x)

/--
@isnad1 id=eq.1h5v.s8.a8cb237b2fe1 from=translated src=- shape=940c267e vocab=19c8adab
-/
@[simp] theorem homotopy_H (X : FramedLevelSet (m + 2)) (φ : E → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (s : ℝ) (x : E) :
    (homotopy X φ hφ).H s x = rotate (normRamp s * φ x) (X.g x) :=
  rfl

/-- At the endpoint the defining equations are rotated through exactly
`φ(x)`.
@isnad1 id=eq.1h4v.s8.957b4a47c1cb from=translated src=- shape=96074cf6 vocab=fac52c15
-/
@[simp] theorem homotopy_H_one (X : FramedLevelSet (m + 2)) (φ : E → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (x : E) :
    (homotopy X φ hφ).H 1 x = rotate (φ x) (X.g x) := by
  rw [homotopy_H, normRamp_of_three_quarter_le (show (3 / 4 : ℝ) ≤ 1 by norm_num),
    one_mul]

end SO2FrameGauge

end Submission
