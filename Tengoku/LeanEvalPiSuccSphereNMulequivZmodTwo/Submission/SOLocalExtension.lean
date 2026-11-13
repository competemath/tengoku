import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.TubeCollapse
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SO2FrameGauge
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SOFrameGauge
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.RelativeNormalizationProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A local extension of an `SO(2)` gauge from the standard circle

This file supplies the actual extension step needed by the local frame
normalization.  A smooth real angle lift on the unit circle, written as a
smooth function of its Cartesian coordinates `(cos θ, sin θ)`, is pulled back
along the radial retraction `(uC, uS)` and multiplied by the standard tubular
cutoff.  The resulting ambient angle field is globally smooth despite the
singular radial coordinates: the cutoff is identically zero on a neighborhood
of the singular axis.

Applying the explicit `SO(2)` block rotation to that ambient angle field gives
a defining-map homotopy which has the prescribed endpoint on the standard
circle and is literally stationary outside the radius-`1/3` tube.
-/

noncomputable section

open Set Function Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

namespace Submission

namespace SOLocalExtension

set_option autoImplicit false

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (m + 3))
local notation "M" => Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ

/-- Pull a smooth angle lift on the circle plane back along the radial
retraction and cut it off inside the standard tubular neighborhood.-/
def circleAngleExtension (a : ℝ × ℝ → ℝ) (x : E) : ℝ :=
  tubeCutoff x * a (uC x, uS x)

/-- The cutoff removes the apparent singularity of the radial retraction, so
the extended angle field is smooth on the whole ambient Euclidean space.
@isnad1 id=contdiff.1h2v.s8.2464859e0365 from=translated src=- shape=f61e49a0 vocab=513492cc
-/
theorem contDiff_circleAngleExtension {a : ℝ × ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (circleAngleExtension (m := m) a) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tubeGood
  · have huC : ContDiffAt ℝ ∞ (uC (m := m)) x :=
      contDiffOn_uC.contDiffAt (isOpen_tubeGood.mem_nhds hx)
    have huS : ContDiffAt ℝ ∞ (uS (m := m)) x :=
      contDiffOn_uS.contDiffAt (isOpen_tubeGood.mem_nhds hx)
    exact contDiff_tubeCutoff.contDiffAt.mul
      (ha.contDiffAt.comp x (huC.prodMk huS))
  · have hrs : radSq x = 0 := by
      have hn := radSq_nonneg x
      have hnot : ¬0 < radSq x := hx
      linarith
    have hr : rad x = 0 := by
      rw [rad, hrs, Real.sqrt_zero]
    have hd : 1 ≤ tubeDistSq x := by
      rw [tubeDistSq, hr]
      nlinarith [sq_nonneg ‖x‖]
    have hgt : 1 / 9 < tubeDistSq x := by linarith
    have hnhds : {y : E | 1 / 9 < tubeDistSq y} ∈ 𝓝 x :=
      (isOpen_lt continuous_const continuous_tubeDistSq).mem_nhds hgt
    apply (contDiffAt_const (x := x) (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hnhds] with y hy
    rw [circleAngleExtension, tubeCutoff_of_ge hy.le, zero_mul]

/-- On the inner tube, where the cutoff is one, the extension is exactly the
radial pullback of the prescribed circle angle.
@isnad1 id=eq.1h3v.s6.00e19d008835 from=translated src=- shape=e732a6c4 vocab=bef4a5e9
-/
theorem circleAngleExtension_eq_of_mem_inner (a : ℝ × ℝ → ℝ) {x : E}
    (hx : x ∈ tubeRegion (m := m) (1 / 4)) :
    circleAngleExtension a x = a (uC x, uS x) := by
  rw [circleAngleExtension, tubeCutoff_eq_one_on_inner hx, one_mul]

/--
@isnad1 id=eq.0h2v.s4.7eba11209231 from=translated src=- shape=418a28e2 vocab=e21d8fd6
-/
lemma rad_circleAt (θ : ℝ) : rad (circleAt (m := m) θ) = 1 := by
  rw [rad, radSq_circleAt, Real.sqrt_one]

/--
@isnad1 id=eq.0h2v.s3.aba0c90c87cc from=translated src=- shape=232808c0 vocab=f698728c
-/
@[simp] lemma uC_circleAt (θ : ℝ) :
    uC (circleAt (m := m) θ) = Real.cos θ := by
  rw [uC, circleAt_apply_zero, rad_circleAt, div_one]

/--
@isnad1 id=eq.0h2v.s3.792b37e9dc3d from=translated src=- shape=232808c0 vocab=60394565
-/
@[simp] lemma uS_circleAt (θ : ℝ) :
    uS (circleAt (m := m) θ) = Real.sin θ := by
  rw [uS, circleAt_apply_one, rad_circleAt, div_one]

/-- On the standard circle the extension recovers the given angle lift
exactly.
@isnad1 id=eq.0h3v.s4.ac95d8cf5fcb from=translated src=- shape=a7bcd40f vocab=e217afc5
-/
@[simp] theorem circleAngleExtension_circleAt (a : ℝ × ℝ → ℝ) (θ : ℝ) :
    circleAngleExtension (m := m) a (circleAt θ) =
      a (Real.cos θ, Real.sin θ) := by
  rw [circleAngleExtension_eq_of_mem_inner a
    (standardCircle_subset_innerTube (circleAt_mem_standardCircle θ)),
    uC_circleAt, uS_circleAt]

/-- The explicit local `SO(2)` gauge homotopy associated to a smooth angle
lift on the standard circle.-/
def localHomotopy (X : FramedLevelSet (m + 2)) (a : ℝ × ℝ → ℝ)
    (ha : ContDiff ℝ ∞ a) :=
  SO2FrameGauge.homotopy X (circleAngleExtension a)
    (contDiff_circleAngleExtension ha)

/-- At the endpoint, the local homotopy realizes exactly the prescribed
circle-valued rotation.
@isnad1 id=eq.1h4v.s7.c097ab1588dd from=translated src=- shape=a8e72fd1 vocab=1d8b3bcd
-/
@[simp] theorem localHomotopy_H_one_circleAt
    (X : FramedLevelSet (m + 2)) (a : ℝ × ℝ → ℝ)
    (ha : ContDiff ℝ ∞ a) (θ : ℝ) :
    (localHomotopy X a ha).H 1 (circleAt θ) =
      SO2FrameGauge.rotate (a (Real.cos θ, Real.sin θ)) (X.g (circleAt θ)) := by
  rw [localHomotopy, SO2FrameGauge.homotopy_H_one,
    circleAngleExtension_circleAt]

/-! ## Direct extension of a general `SO(n)` circle homotopy

The angle-lift construction above is convenient for the explicit `SO(2)`
block.  The following construction is stronger: it extends a homotopy which
already takes values in `SO(m+2)` without choosing a logarithm or interpolating
matrices.  Radially approaching the boundary of the tube simply runs the
given homotopy backwards to its identity endpoint.

The circle input is represented in Cartesian coordinates.  Thus
`R t (cos θ, sin θ)` is the original circle homotopy; values of `R` away from
the unit circle are only an ambient smooth representative and are never used
where the cutoff is nonzero.
-/

/-- Extend a Cartesian representative of an `SO(m+2)` homotopy on the circle
to a spatially supported `SO(m+2)` field.  The first argument is the homotopy
time; multiplying it by the tubular cutoff runs the field back to the identity
before reaching the boundary of the tube.-/
def extendCircleSOHomotopy
    (R : ℝ → ℝ × ℝ → SOGroup (m + 2)) (s : ℝ) (x : E) : SOGroup (m + 2) :=
  R (normRamp s * tubeCutoff x) (uC x, uS x)

/-- The extended `SO(m+2)` field is coordinatewise smooth on parameter-space
times the whole ambient Euclidean space.  At the singular radial axis the
cutoff is identically zero on a neighborhood, and `R 0 = 1` removes all
dependence on the undefined angular direction.
@isnad1 id=contdiff.2h4v.s12.a6da2f746784 from=translated src=- shape=9f110e73 vocab=ba452b38
-/
theorem contDiff_extendCircleSOHomotopy
    {R : ℝ → ℝ × ℝ → SOGroup (m + 2)}
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => ((R p.1 p.2 : SOGroup (m + 2)) : M) i j))
    (hRzero : ∀ z, R 0 z = 1) :
    ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E =>
        ((extendCircleSOHomotopy R p.1 p.2 : SOGroup (m + 2)) : M) i j) := by
  intro i j
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hx : p.2 ∈ tubeGood
  · have huCx : ContDiffAt ℝ ∞ (uC (m := m)) p.2 :=
      contDiffOn_uC.contDiffAt (isOpen_tubeGood.mem_nhds hx)
    have huSx : ContDiffAt ℝ ∞ (uS (m := m)) p.2 :=
      contDiffOn_uS.contDiffAt (isOpen_tubeGood.mem_nhds hx)
    have huC : ContDiffAt ℝ ∞ (fun q : ℝ × E => uC q.2) p :=
      huCx.comp p contDiff_snd.contDiffAt
    have huS : ContDiffAt ℝ ∞ (fun q : ℝ × E => uS q.2) p :=
      huSx.comp p contDiff_snd.contDiffAt
    have ht : ContDiffAt ℝ ∞
        (fun q : ℝ × E => normRamp q.1 * tubeCutoff q.2) p :=
      (contDiff_normRamp.comp contDiff_fst).contDiffAt.mul
        (contDiff_tubeCutoff.comp contDiff_snd).contDiffAt
    exact (hR i j).contDiffAt.comp p (ht.prodMk (huC.prodMk huS))
  · have hrs : radSq p.2 = 0 := by
      have hn := radSq_nonneg p.2
      have hnot : ¬0 < radSq p.2 := hx
      linarith
    have hr : rad p.2 = 0 := by
      rw [rad, hrs, Real.sqrt_zero]
    have hd : 1 ≤ tubeDistSq p.2 := by
      rw [tubeDistSq, hr]
      nlinarith [sq_nonneg ‖p.2‖]
    have hgt : 1 / 9 < tubeDistSq p.2 := by linarith
    have hnhds :
        {q : ℝ × E | 1 / 9 < tubeDistSq q.2} ∈ 𝓝 p :=
      (isOpen_lt continuous_const
        (continuous_tubeDistSq.comp continuous_snd)).mem_nhds hgt
    apply (contDiffAt_const (x := p)
      (c := (((1 : SOGroup (m + 2)) : M) i j))).congr_of_eventuallyEq
    filter_upwards [hnhds] with q hq
    rw [extendCircleSOHomotopy, tubeCutoff_of_ge hq.le, mul_zero,
      hRzero]

/-- The extended family starts at the identity everywhere.
@isnad1 id=eq.1h3v.s12.bc5aa78bf70e from=translated src=- shape=57008bbe vocab=17359a3c
-/
@[simp] theorem extendCircleSOHomotopy_zero
    (R : ℝ → ℝ × ℝ → SOGroup (m + 2))
    (hRzero : ∀ z, R 0 z = 1) (x : E) :
    extendCircleSOHomotopy R 0 x = 1 := by
  rw [extendCircleSOHomotopy,
    normRamp_of_le_quarter (show (0 : ℝ) ≤ 1 / 4 by norm_num),
    zero_mul, hRzero]

/-- The extension is identically the identity outside the outer tube, at every
homotopy time.
@isnad1 id=eq.2h4v.s12.7134a2c0407e from=translated src=- shape=01193a21 vocab=52796edb
-/
theorem extendCircleSOHomotopy_eq_one_off_outer
    (R : ℝ → ℝ × ℝ → SOGroup (m + 2))
    (hRzero : ∀ z, R 0 z = 1) (s : ℝ) {x : E}
    (hx : x ∉ tubeRegion (m := m) (1 / 3)) :
    extendCircleSOHomotopy R s x = 1 := by
  rw [extendCircleSOHomotopy, tubeCutoff_eq_zero_off_outer hx, mul_zero,
    hRzero]

/-- On the standard circle the spatial extension is exactly the original
circle homotopy (with the standard collar-flat reparameterization).
@isnad1 id=eq.0h4v.s10.71d4c4cb42f3 from=translated src=- shape=dfcf59d3 vocab=63abb375
-/
@[simp] theorem extendCircleSOHomotopy_circleAt
    (R : ℝ → ℝ × ℝ → SOGroup (m + 2)) (s θ : ℝ) :
    extendCircleSOHomotopy (m := m) R s (circleAt θ) =
      R (normRamp s) (Real.cos θ, Real.sin θ) := by
  rw [extendCircleSOHomotopy,
    tubeCutoff_eq_one_on_inner
      (standardCircle_subset_innerTube (circleAt_mem_standardCircle θ)),
    mul_one, uC_circleAt, uS_circleAt]

/-- In particular, the endpoint agrees exactly with the prescribed endpoint
field on the circle.
@isnad1 id=eq.0h3v.s10.7464414a058b from=translated src=- shape=f81abbb5 vocab=a332de92
-/
@[simp] theorem extendCircleSOHomotopy_one_circleAt
    (R : ℝ → ℝ × ℝ → SOGroup (m + 2)) (θ : ℝ) :
    extendCircleSOHomotopy (m := m) R 1 (circleAt θ) =
      R 1 (Real.cos θ, Real.sin θ) := by
  rw [extendCircleSOHomotopy_circleAt,
    normRamp_of_three_quarter_le (show (3 / 4 : ℝ) ≤ 1 by norm_num)]

/-- Feed the supported `SO(m+2)` field directly into the general frame-gauge
constructor.  No separate invertibility proof is required because every value
remains in the special orthogonal group.-/
def localSOHomotopy (X : FramedLevelSet (m + 2))
    (R : ℝ → ℝ × ℝ → SOGroup (m + 2))
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => ((R p.1 p.2 : SOGroup (m + 2)) : M) i j))
    (hRzero : ∀ z, R 0 z = 1) :=
  SOFrameGauge.homotopy X (extendCircleSOHomotopy R)
    (contDiff_extendCircleSOHomotopy hR hRzero)
    (extendCircleSOHomotopy_zero R hRzero)

/-- The actual defining-map homotopy restricts on the circle to the supplied
`SO(m+2)` homotopy.
@isnad1 id=eq.2h5v.s12.04b7693bcce6 from=translated src=- shape=2c137dad vocab=f57913db
-/
@[simp] theorem localSOHomotopy_H_circleAt
    (X : FramedLevelSet (m + 2))
    (R : ℝ → ℝ × ℝ → SOGroup (m + 2))
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => ((R p.1 p.2 : SOGroup (m + 2)) : M) i j))
    (hRzero : ∀ z, R 0 z = 1) (s θ : ℝ) :
    (localSOHomotopy X R hR hRzero).H s (circleAt θ) =
      SOFrameGauge.toCLM (R (normRamp s) (Real.cos θ, Real.sin θ))
        (X.g (circleAt θ)) := by
  rw [localSOHomotopy, SOFrameGauge.homotopy_H,
    extendCircleSOHomotopy_circleAt]

end SOLocalExtension

end Submission
