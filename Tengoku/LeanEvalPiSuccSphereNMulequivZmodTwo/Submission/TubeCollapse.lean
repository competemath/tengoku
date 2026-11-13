import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.LevelSet
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.PTAssembly
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SphereClose
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.TubeCircle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The local Thom collapse around the standard twist-`k` circle

This file turns the explicit tube coordinates from `Submission.TubeCircle` into
the local data needed by the inverse Pontryagin--Thom construction.  The main
point is that no choice of an angular branch is made: the normal coordinate map
`wCoord k` is smooth on `tubeGood`, and a global smooth cutoff is obtained from
the squared distance to the circle.

The declarations proved here provide the four local contracts used by the
collapse construction:

* `tubeCutoff` is globally smooth, is one on the radius-`1/4` tube and zero
  outside the radius-`1/3` tube;
* the inner and outer tube regions lie in `tubeGood`, so `wCoord` is smooth on
  all points where the cutoff is active;
* the zero fiber of `wCoord` on `tubeGood` is exactly the standard circle;
* the differential of `wCoord` sends the prescribed normal frame to the
  standard basis.  In particular it is surjective along the circle.

The last item is the framed regular-value calculation.  It is phrased directly
in terms of `fderiv`, so it can be consumed both by a sphere-valued Thom collapse
and by a later `FramedLevelSet` package.
-/

noncomputable section

namespace Submission

open Set Function Metric Filter Topology.Homotopy
open scoped RealInnerProductSpace ContDiff Topology unitInterval

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (m + 3))
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))

/-! ## A smooth cutoff supported in the explicit tube -/

/-- Smooth scalar profile which is `1` up to squared radius `1/16` and `0` from
squared radius `1/9` onwards.-/
def tubeCutoffScalar (s : ℝ) : ℝ :=
  Real.smoothTransition ((16 - 144 * s) / 7)

/--
@isnad1 id=le.0h1v.s3.079ee8a9ab56 from=translated src=- shape=8a62b088 vocab=e79db0ad
-/
lemma tubeCutoffScalar_nonneg (s : ℝ) : 0 ≤ tubeCutoffScalar s :=
  Real.smoothTransition.nonneg _

/--
@isnad1 id=le.0h1v.s3.1f6dbd9c7656 from=translated src=- shape=b14ee516 vocab=e79db0ad
-/
lemma tubeCutoffScalar_le_one (s : ℝ) : tubeCutoffScalar s ≤ 1 :=
  Real.smoothTransition.le_one _

/--
@isnad1 id=eq.1h1v.s5.296f06ea5920 from=translated src=- shape=44469b40 vocab=a74ee5a1
-/
lemma tubeCutoffScalar_of_le {s : ℝ} (hs : s ≤ 1 / 16) :
    tubeCutoffScalar s = 1 := by
  apply Real.smoothTransition.one_of_one_le
  change 1 ≤ (16 - 144 * s) / 7
  linarith

/--
@isnad1 id=eq.1h1v.s5.f5f6aa86b246 from=translated src=- shape=c1676f1c vocab=a74ee5a1
-/
lemma tubeCutoffScalar_of_ge {s : ℝ} (hs : 1 / 9 ≤ s) :
    tubeCutoffScalar s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  change (16 - 144 * s) / 7 ≤ 0
  linarith

/--
@isnad1 id=contdiff.0h0v.s5.518becce8fcd from=translated src=- shape=3cea26be vocab=5b2536e2
-/
lemma contDiff_tubeCutoffScalar : ContDiff ℝ ∞ tubeCutoffScalar := by
  apply Real.smoothTransition.contDiff.comp
  exact ((contDiff_const.sub (contDiff_const.mul contDiff_id)).div_const 7)

/-- Global radial cutoff around the standard circle.  Although `tubeDistSq`
contains a square root, the composition is identically zero near the singular
axis and is therefore globally smooth.-/
def tubeCutoff (v : E) : ℝ := tubeCutoffScalar (tubeDistSq v)

/--
@isnad1 id=le.0h2v.s4.96c6f002c224 from=translated src=- shape=942f9989 vocab=531ff7ab
-/
lemma tubeCutoff_nonneg (v : E) : 0 ≤ tubeCutoff v :=
  tubeCutoffScalar_nonneg _

/--
@isnad1 id=le.0h2v.s4.65aa39ba478d from=translated src=- shape=6496b1fa vocab=531ff7ab
-/
lemma tubeCutoff_le_one (v : E) : tubeCutoff v ≤ 1 :=
  tubeCutoffScalar_le_one _

/--
@isnad1 id=eq.1h2v.s5.c43b1279ce4b from=translated src=- shape=83526c2b vocab=a60cef08
-/
lemma tubeCutoff_of_le {v : E} (hv : tubeDistSq v ≤ 1 / 16) :
    tubeCutoff v = 1 :=
  tubeCutoffScalar_of_le hv

/--
@isnad1 id=eq.1h2v.s5.2ab071f01106 from=translated src=- shape=7eb3eb05 vocab=a60cef08
-/
lemma tubeCutoff_of_ge {v : E} (hv : 1 / 9 ≤ tubeDistSq v) :
    tubeCutoff v = 0 :=
  tubeCutoffScalar_of_ge hv

/-- The radius-`r` tube, expressed using the globally defined squared distance.-/
def tubeRegion (r : ℝ) : Set E := {v | tubeDistSq v < r ^ 2}

/-- Any tube of radius strictly less than one misses the singular circle axis.
@isnad1 id=le.2h2v.s6.b43f1a1d2dda from=translated src=- shape=841f5a2e vocab=e8f6ef5b
-/
lemma tubeRegion_subset_tubeGood {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    tubeRegion (m := m) r ⊆ tubeGood := by
  intro v hv
  have hd : tubeDistSq v < r ^ 2 := hv
  have hs : (rad v - 1) ^ 2 ≤ tubeDistSq v := sq_rad_le_tubeDistSq v
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hrad : 0 < rad v := by
    have hn := rad_nonneg v
    nlinarith [sq_nonneg (rad v - 1)]
  exact (Real.sqrt_pos.mp hrad)

/--
@isnad1 id=le.0h1v.s6.c4cd649f9f82 from=translated src=- shape=1a144dfc vocab=1249e6bc
-/
lemma innerTube_subset_tubeGood :
    tubeRegion (m := m) (1 / 4) ⊆ tubeGood :=
  tubeRegion_subset_tubeGood (by norm_num) (by norm_num)

/--
@isnad1 id=le.0h1v.s6.2f1841798bce from=translated src=- shape=1a144dfc vocab=1249e6bc
-/
lemma outerTube_subset_tubeGood :
    tubeRegion (m := m) (1 / 3) ⊆ tubeGood :=
  tubeRegion_subset_tubeGood (by norm_num) (by norm_num)

/--
@isnad1 id=eq.1h2v.s6.e64e31ea803e from=translated src=- shape=8c0905d0 vocab=59000683
-/
lemma tubeCutoff_eq_one_on_inner {v : E} (hv : v ∈ tubeRegion (m := m) (1 / 4)) :
    tubeCutoff v = 1 := by
  apply tubeCutoff_of_le
  have : tubeDistSq v < (1 / 4 : ℝ) ^ 2 := hv
  norm_num at this ⊢
  exact this.le

/--
@isnad1 id=eq.1h2v.s6.887cd2339d41 from=translated src=- shape=279a42c1 vocab=59000683
-/
lemma tubeCutoff_eq_zero_off_outer {v : E} (hv : v ∉ tubeRegion (m := m) (1 / 3)) :
    tubeCutoff v = 0 := by
  apply tubeCutoff_of_ge
  have : (1 / 3 : ℝ) ^ 2 ≤ tubeDistSq v := not_lt.mp hv
  norm_num at this ⊢
  exact this

/--
@isnad1 id=continuo.0h1v.s6.2c1f10251faa from=translated src=- shape=a134ef14 vocab=a5340f0b
-/
lemma continuous_rad : Continuous (rad (m := m)) :=
  Real.continuous_sqrt.comp contDiff_radSq.continuous

/--
@isnad1 id=continuo.0h1v.s6.73bd526a79ab from=translated src=- shape=a134ef14 vocab=06f2d875
-/
lemma continuous_tubeDistSq : Continuous (tubeDistSq (m := m)) := by
  have hnormsq : Continuous fun v : E => ‖v‖ ^ 2 := continuous_norm.pow 2
  exact (hnormsq.add continuous_const).sub (continuous_const.mul continuous_rad)

/-- The cutoff is genuinely globally smooth, including along the circle axis
where the raw distance formula contains `sqrt (x₀²+x₁²)`.  Near that axis the
distance is bigger than the outer cutoff radius, hence the function is locally
constant zero.
@isnad1 id=contdiff.0h1v.s7.e83831e1834d from=translated src=- shape=41de37fa vocab=55e408c0
-/
theorem contDiff_tubeCutoff : ContDiff ℝ ∞ (tubeCutoff (m := m)) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v ∈ tubeGood
  · have hd : ContDiffAt ℝ ∞ (tubeDistSq (m := m)) v :=
      contDiffOn_tubeDistSq.contDiffAt (isOpen_tubeGood.mem_nhds hv)
    exact contDiff_tubeCutoffScalar.contDiffAt.comp v hd
  · have hrs : radSq v = 0 := by
      have hn := radSq_nonneg v
      have : ¬0 < radSq v := hv
      linarith
    have hr : rad v = 0 := by rw [rad, hrs, Real.sqrt_zero]
    have hd : 1 ≤ tubeDistSq v := by
      rw [tubeDistSq, hr]
      nlinarith [sq_nonneg ‖v‖]
    have hgt : 1 / 9 < tubeDistSq v := by linarith
    have hnhds : {x : E | 1 / 9 < tubeDistSq x} ∈ 𝓝 v :=
      (isOpen_lt continuous_const continuous_tubeDistSq).mem_nhds hgt
    apply (contDiffAt_const (x := v) (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hnhds] with x hx
    exact tubeCutoff_of_ge hx.le

/-- The horizontal chart of the local Thom collapse.  It is the normal coordinate
inside the radius-`1/4` tube and is smoothly switched off before reaching the
singular axis.-/
def tubeCollapseHorizontal (k : ℕ) (v : E) : F :=
  tubeCutoff v • wCoord k v

/--
@isnad1 id=contdiff.0h2v.s8.726ce496853b from=translated src=- shape=6b0ec888 vocab=28446c36
-/
theorem contDiff_tubeCollapseHorizontal (k : ℕ) :
    ContDiff ℝ ∞ (tubeCollapseHorizontal (m := m) k) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v ∈ tubeGood
  · have hw : ContDiffAt ℝ ∞ (wCoord (m := m) k) v :=
      (contDiffOn_wCoord k).contDiffAt (isOpen_tubeGood.mem_nhds hv)
    exact contDiff_tubeCutoff.contDiffAt.smul hw
  · have hrs : radSq v = 0 := by
      have hn := radSq_nonneg v
      have : ¬0 < radSq v := hv
      linarith
    have hr : rad v = 0 := by rw [rad, hrs, Real.sqrt_zero]
    have hd : 1 ≤ tubeDistSq v := by
      rw [tubeDistSq, hr]
      nlinarith [sq_nonneg ‖v‖]
    have hgt : 1 / 9 < tubeDistSq v := by linarith
    have hnhds : {x : E | 1 / 9 < tubeDistSq x} ∈ 𝓝 v :=
      (isOpen_lt continuous_const continuous_tubeDistSq).mem_nhds hgt
    apply (contDiffAt_const (x := v) (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [hnhds] with x hx
    rw [tubeCollapseHorizontal, tubeCutoff_of_ge hx.le, zero_smul]

/--
@isnad1 id=eq.1h3v.s6.d062561f0a5b from=translated src=- shape=774b274f vocab=77ece3b2
-/
lemma tubeCollapseHorizontal_eq_wCoord_of_mem_inner (k : ℕ) {v : E}
    (hv : v ∈ tubeRegion (m := m) (1 / 4)) :
    tubeCollapseHorizontal k v = wCoord k v := by
  rw [tubeCollapseHorizontal, tubeCutoff_eq_one_on_inner hv, one_smul]

/-! ## The local zero fiber -/

/-- The geometric standard circle, without choosing a quotient model for its
angle parameter.-/
def standardCircle : Set E := Set.range (circleAt (m := m))

/--
@isnad1 id=mem.0h2v.s5.425e1430cddc from=translated src=- shape=6de1494d vocab=1e1ed89a
-/
lemma circleAt_mem_standardCircle (θ : ℝ) :
    circleAt (m := m) θ ∈ standardCircle := ⟨θ, rfl⟩

/--
@isnad1 id=eq.0h2v.s4.4d97d3368a29 from=translated src=- shape=418a28e2 vocab=aba54a96
-/
lemma radSq_circleAt (θ : ℝ) : radSq (circleAt (m := m) θ) = 1 := by
  rw [radSq, circleAt_apply_zero, circleAt_apply_one]
  linear_combination Real.sin_sq_add_cos_sq θ

/--
@isnad1 id=mem.0h2v.s5.13b6b873b013 from=translated src=- shape=6de1494d vocab=cd2ba381
-/
lemma circleAt_mem_tubeGood (θ : ℝ) : circleAt (m := m) θ ∈ tubeGood := by
  change 0 < radSq (circleAt (m := m) θ)
  rw [radSq_circleAt]
  norm_num

/--
@isnad1 id=eq.0h3v.s7.2517d5e43182 from=translated src=- shape=8eefda86 vocab=4a50551a
-/
lemma tubeMap_zero (k : ℕ) (θ : ℝ) :
    tubeMap (m := m) k θ 0 = circleAt θ := by
  simp [tubeMap]

/--
@isnad1 id=eq.0h3v.s7.8be71d1bb6e8 from=translated src=- shape=3f614992 vocab=0a7fbad9
-/
lemma wCoord_circleAt (k : ℕ) (θ : ℝ) :
    wCoord (m := m) k (circleAt θ) = 0 := by
  have hA : 0 < tubeA (m := m) k θ (0 : F) := by simp [tubeA]
  have h := wCoord_tubeMap (m := m) k θ hA
  simpa [tubeMap_zero] using h

/-- On its smooth domain, the zero fiber of the explicit normal-coordinate map
is exactly the standard circle.
@isnad1 id=iff.1h3v.s8.c16cd6bd2823 from=translated src=- shape=f55de2ed vocab=c9e2f12d
-/
theorem wCoord_eq_zero_iff_standardCircle (k : ℕ) {v : E} (hv : v ∈ tubeGood) :
    wCoord k v = 0 ↔ v ∈ standardCircle := by
  constructor
  · intro hw
    obtain ⟨θ, hc, hs⟩ := exists_angle hv
    refine ⟨θ, ?_⟩
    have hrec := tubeMap_wCoord (m := m) k hv hc hs
    rw [hw, tubeMap_zero] at hrec
    exact hrec
  · rintro ⟨θ, rfl⟩
    exact wCoord_circleAt k θ

/-- The active (inner-tube) fiber of the horizontal collapse chart is exactly the
standard circle.
@isnad1 id=iff.1h3v.s8.dedadd597ffb from=translated src=- shape=21f4a198 vocab=fcfbf63c
-/
theorem tubeCollapseHorizontal_eq_zero_iff_standardCircle (k : ℕ) {v : E}
    (hv : v ∈ tubeRegion (m := m) (1 / 4)) :
    tubeCollapseHorizontal k v = 0 ↔ v ∈ standardCircle := by
  rw [tubeCollapseHorizontal_eq_wCoord_of_mem_inner k hv]
  exact wCoord_eq_zero_iff_standardCircle k (innerTube_subset_tubeGood hv)

/--
@isnad1 id=eq.0h2v.s4.a7bd31abaaad from=translated src=- shape=418a28e2 vocab=6bc87faa
-/
lemma tubeDistSq_circleAt (θ : ℝ) :
    tubeDistSq (circleAt (m := m) θ) = 0 := by
  have hA : 0 < tubeA (m := m) 0 θ (0 : F) := by simp [tubeA]
  simpa [tubeMap_zero] using tubeDistSq_tubeMap (m := m) 0 θ hA

/--
@isnad1 id=le.0h1v.s6.843c460a7d0a from=translated src=- shape=ac51c8f9 vocab=669816d5
-/
lemma standardCircle_subset_innerTube :
    standardCircle (m := m) ⊆ tubeRegion (1 / 4) := by
  rintro _ ⟨θ, rfl⟩
  change tubeDistSq (circleAt (m := m) θ) < (1 / 4 : ℝ) ^ 2
  rw [tubeDistSq_circleAt]
  norm_num

/--
@isnad1 id=eq.0h2v.s6.06b5176bb611 from=translated src=- shape=5df46cb3 vocab=1e5a11cf
-/
lemma norm_circleAt (θ : ℝ) : ‖circleAt (m := m) θ‖ = 1 := by
  have hsq : ‖circleAt (m := m) θ‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_circleAt_self]
  nlinarith [norm_nonneg (circleAt (m := m) θ)]

/-! ## Smoothness where the local collapse is active -/

/-! ## Differential and prescribed frame evaluation -/

/-- Linear reconstruction from normal coordinates in the prescribed frame.-/
def normalSumCLM (k : ℕ) (θ : ℝ) : F →L[ℝ] E :=
  ∑ i, (EuclideanSpace.proj i : F →L[ℝ] ℝ).smulRight (nuVec k θ i)

/--
@isnad1 id=eq.0h4v.s10.0eb73f0e8fee from=translated src=- shape=c4effac4 vocab=7e15b4e4
-/
@[simp] lemma normalSumCLM_apply (k : ℕ) (θ : ℝ) (w : F) :
    normalSumCLM (m := m) k θ w = ∑ i, w i • nuVec k θ i := by
  simp [normalSumCLM]

/--
@isnad1 id=eq.0h4v.s10.453acd52edae from=translated src=- shape=3df11825 vocab=1ceb9528
-/
lemma normalSumCLM_single (k : ℕ) (θ : ℝ) (i : Fin (m + 2)) :
    normalSumCLM (m := m) k θ (EuclideanSpace.single i 1) = nuVec k θ i := by
  rw [normalSumCLM_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [PiLp.single_apply, ite_eq_right hji, zero_smul]
  · simp

/-- The affine normal slice at a fixed point of the circle.-/
def normalSlice (k : ℕ) (θ : ℝ) (w : F) : E := tubeMap k θ w

/--
@isnad1 id=eq.0h4v.s10.7263b2daf1b7 from=translated src=- shape=59b9e362 vocab=be992bc3
-/
lemma normalSlice_eq (k : ℕ) (θ : ℝ) (w : F) :
    normalSlice (m := m) k θ w = circleAt θ + normalSumCLM k θ w := by
  rw [normalSlice, tubeMap, normalSumCLM_apply]

/--
@isnad1 id=eq.0h3v.s7.4249fe131fc7 from=translated src=- shape=8eefda86 vocab=5b00345e
-/
lemma normalSlice_zero (k : ℕ) (θ : ℝ) :
    normalSlice (m := m) k θ 0 = circleAt θ := by
  rw [normalSlice, tubeMap_zero]

/--
@isnad1 id=hasfderi.0h4v.s9.ebfff960df62 from=translated src=- shape=0463aad8 vocab=e9fc0849
-/
lemma hasFDerivAt_normalSlice (k : ℕ) (θ : ℝ) (w : F) :
    HasFDerivAt (normalSlice (m := m) k θ) (normalSumCLM k θ) w := by
  have h : HasFDerivAt (fun u : F =>
      circleAt (m := m) θ + normalSumCLM k θ u) (normalSumCLM k θ) w :=
    (normalSumCLM (m := m) k θ).hasFDerivAt.const_add (circleAt θ)
  have heq : normalSlice (m := m) k θ = fun w : F =>
      circleAt θ + normalSumCLM k θ w := by
    funext u
    exact normalSlice_eq k θ u
  rw [heq]
  exact h

/-- The exact left-inverse identity holds on a neighbourhood of the origin in
each fixed normal slice.
@isnad1 id=eventual.0h3v.s8.e189e6c45b12 from=translated src=- shape=34a52e35 vocab=6c0e4f1d
-/
lemma wCoord_normalSlice_eventuallyEq (k : ℕ) (θ : ℝ) :
    (fun w : F => wCoord k (normalSlice k θ w)) =ᶠ[𝓝 0] fun w => w := by
  filter_upwards [Metric.ball_mem_nhds (0 : F) (by norm_num : (0 : ℝ) < 1 / 2)]
    with w hw
  have hwnorm : ‖w‖ < 1 / 2 := by
    simpa [dist_zero_right] using hw
  exact wCoord_tubeMap k θ (tubeA_pos k θ hwnorm)

/--
@isnad1 id=contdiff.0h3v.s8.b85e1ba6213d from=translated src=- shape=52329239 vocab=17ac9682
-/
lemma contDiffAt_wCoord_circleAt (k : ℕ) (θ : ℝ) :
    ContDiffAt ℝ ∞ (wCoord (m := m) k) (circleAt θ) :=
  (contDiffOn_wCoord k).contDiffAt
    (isOpen_tubeGood.mem_nhds (circleAt_mem_tubeGood θ))

/-- Differentiating the exact tube-coordinate round trip gives a left inverse for
the normal reconstruction map.
@isnad1 id=eq.0h3v.s11.cef28e86a456 from=translated src=- shape=71547629 vocab=d6c9668c
-/
theorem fderiv_wCoord_comp_normalSumCLM (k : ℕ) (θ : ℝ) :
    (fderiv ℝ (wCoord (m := m) k) (circleAt θ)).comp (normalSumCLM k θ)
      = ContinuousLinearMap.id ℝ F := by
  have hwDiff : DifferentiableAt ℝ (wCoord (m := m) k) (circleAt θ) :=
    (contDiffAt_wCoord_circleAt k θ).differentiableAt (by simp)
  have hwDeriv : HasFDerivAt (wCoord (m := m) k)
      (fderiv ℝ (wCoord k) (circleAt θ)) (normalSlice k θ 0) := by
    simpa only [normalSlice_zero] using hwDiff.hasFDerivAt
  have hcomp := hwDeriv.comp (0 : F) (hasFDerivAt_normalSlice k θ 0)
  have heq : ((wCoord (m := m) k) ∘ normalSlice k θ) =ᶠ[𝓝 0] id := by
    change (fun w : F => wCoord k (normalSlice k θ w)) =ᶠ[𝓝 0] fun w => w
    exact wCoord_normalSlice_eventuallyEq k θ
  have hsame : HasFDerivAt ((wCoord (m := m) k) ∘ normalSlice k θ)
      (ContinuousLinearMap.id ℝ F) 0 :=
    (hasFDerivAt_id (𝕜 := ℝ) (0 : F)).congr_of_eventuallyEq heq
  exact hcomp.unique hsame

/-- **Prescribed frame evaluation.**  The differential of the local normal
coordinate map sends the `i`-th twist-`k` normal vector to the `i`-th standard
basis vector.
@isnad1 id=eq.0h4v.s11.78b60c0be0aa from=translated src=- shape=cbf71b0c vocab=af8677d4
-/
theorem fderiv_wCoord_nuVec (k : ℕ) (θ : ℝ) (i : Fin (m + 2)) :
    fderiv ℝ (wCoord (m := m) k) (circleAt θ) (nuVec k θ i)
      = EuclideanSpace.single i 1 := by
  have h := congrArg (fun L : F →L[ℝ] F => L (EuclideanSpace.single i 1))
    (fderiv_wCoord_comp_normalSumCLM (m := m) k θ)
  simpa [normalSumCLM_single] using h

/-- Thus zero is a regular value of the local coordinate chart along the whole
standard circle.
@isnad1 id=surjecti.0h3v.s11.ada4e617c713 from=translated src=- shape=5075437b vocab=d7fc4ae2
-/
theorem surjective_fderiv_wCoord_circleAt (k : ℕ) (θ : ℝ) :
    Function.Surjective (fderiv ℝ (wCoord (m := m) k) (circleAt θ)) := by
  intro y
  refine ⟨normalSumCLM k θ y, ?_⟩
  have h := congrArg (fun L : F →L[ℝ] F => L y)
    (fderiv_wCoord_comp_normalSumCLM (m := m) k θ)
  exact h

/--
@isnad1 id=isopen.0h2v.s6.7cef1283dfb6 from=translated src=- shape=7b93a302 vocab=59308b29
-/
lemma isOpen_tubeRegion (r : ℝ) : IsOpen (tubeRegion (m := m) r) :=
  isOpen_lt continuous_tubeDistSq continuous_const

/--
@isnad1 id=eventual.0h3v.s7.07fea28512cf from=translated src=- shape=dadfb7c3 vocab=b20f565c
-/
lemma tubeCollapseHorizontal_eventuallyEq_wCoord (k : ℕ) (θ : ℝ) :
    tubeCollapseHorizontal (m := m) k =ᶠ[𝓝 (circleAt θ)] wCoord k := by
  have hmem : circleAt (m := m) θ ∈ tubeRegion (1 / 4) :=
    standardCircle_subset_innerTube (circleAt_mem_standardCircle θ)
  filter_upwards [(isOpen_tubeRegion (m := m) (1 / 4)).mem_nhds hmem] with v hv
  exact tubeCollapseHorizontal_eq_wCoord_of_mem_inner k hv

/--
@isnad1 id=eq.0h3v.s11.0fe8030ae8a3 from=translated src=- shape=19aedb55 vocab=73511837
-/
lemma fderiv_tubeCollapseHorizontal_circleAt (k : ℕ) (θ : ℝ) :
    fderiv ℝ (tubeCollapseHorizontal (m := m) k) (circleAt θ)
      = fderiv ℝ (wCoord k) (circleAt θ) :=
  (tubeCollapseHorizontal_eventuallyEq_wCoord k θ).fderiv_eq

/--
@isnad1 id=eq.0h4v.s11.d88f6b124247 from=translated src=- shape=cbf71b0c vocab=e0f81ae6
-/
theorem fderiv_tubeCollapseHorizontal_nuVec (k : ℕ) (θ : ℝ)
    (i : Fin (m + 2)) :
    fderiv ℝ (tubeCollapseHorizontal (m := m) k) (circleAt θ) (nuVec k θ i)
      = EuclideanSpace.single i 1 := by
  rw [fderiv_tubeCollapseHorizontal_circleAt]
  exact fderiv_wCoord_nuVec k θ i

/--
@isnad1 id=surjecti.0h3v.s11.74ef50c43000 from=translated src=- shape=5075437b vocab=db76a0e7
-/
theorem surjective_fderiv_tubeCollapseHorizontal_circleAt (k : ℕ) (θ : ℝ) :
    Function.Surjective
      (fderiv ℝ (tubeCollapseHorizontal (m := m) k) (circleAt θ)) := by
  rw [fderiv_tubeCollapseHorizontal_circleAt]
  exact surjective_fderiv_wCoord_circleAt k θ

/-- The continuous linear normal-coordinate projection prescribed by the twist
frame at angle `θ`.-/
def normalCoordCLM (k : ℕ) (θ : ℝ) : E →L[ℝ] F :=
  (EuclideanSpace.equiv (Fin (m + 2)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      (InnerProductSpace.toDual ℝ E) (nuVec k θ i))

/--
@isnad1 id=eq.0h5v.s10.2121e577c4e5 from=translated src=- shape=37f18f7c vocab=6f430dfb
-/
@[simp] lemma normalCoordCLM_apply (k : ℕ) (θ : ℝ) (x : E) (i : Fin (m + 2)) :
    normalCoordCLM k θ x i = ⟪nuVec k θ i, x⟫ := by
  rfl

/-! ## A sphere-valued Thom collapse -/

/-- The horizontal isometric coordinate inclusion into the target ambient
`ℝ^{m+3}`; its last coordinate is zero.-/
def targetHorizontalCLM : F →L[ℝ] E :=
  ∑ i, (EuclideanSpace.proj i : F →L[ℝ] ℝ).smulRight (coordVec i.castSucc)

/--
@isnad1 id=eq.0h2v.s10.f939fe73c7dd from=translated src=- shape=76e13bbc vocab=8fd03d35
-/
@[simp] lemma targetHorizontalCLM_apply (w : F) :
    targetHorizontalCLM (m := m) w = ∑ i, w i • coordVec i.castSucc := by
  simp [targetHorizontalCLM]

/--
@isnad1 id=ne.0h2v.s6.148c349e08c4 from=translated src=- shape=9c7d66fe vocab=7ad0bace
-/
lemma castSucc_ne_last (i : Fin (m + 2)) :
    (i.castSucc : Fin (m + 3)) ≠ Fin.last (m + 2) := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_last] at h'
  omega

/--
@isnad1 id=eq.0h3v.s10.74ca876aa1b0 from=translated src=- shape=d8779967 vocab=53de4b3b
-/
@[simp] lemma targetHorizontalCLM_coord (w : F) (i : Fin (m + 2)) :
    targetHorizontalCLM (m := m) w i.castSucc = w i := by
  rw [targetHorizontalCLM_apply, sum_coord]
  rw [Finset.sum_eq_single i]
  · simp [coordVec_apply]
  · intro j _ hji
    change w j * coordVec j.castSucc i.castSucc = 0
    rw [coordVec_apply, ite_eq_right, mul_zero]
    exact fun h => hji (Fin.ext (congrArg Fin.val h).symm)
  · simp

/--
@isnad1 id=eq.0h2v.s10.99e096344fdb from=translated src=- shape=7416e207 vocab=000949d1
-/
@[simp] lemma targetHorizontalCLM_last (w : F) :
    targetHorizontalCLM (m := m) w (Fin.last (m + 2)) = 0 := by
  rw [targetHorizontalCLM_apply, sum_coord]
  apply Finset.sum_eq_zero
  intro i _
  change w i * coordVec i.castSucc (Fin.last (m + 2)) = 0
  rw [coordVec_apply, ite_eq_right, mul_zero]
  exact (castSucc_ne_last i).symm

/-- Unnormalized sphere-collapse vector.  On the circle this is the north pole;
off the outer tube it is the south pole.  The horizontal component records the
cut-off normal coordinate.-/
def tubeCollapseRaw (k : ℕ) (v : E) : E :=
  targetHorizontalCLM (tubeCollapseHorizontal k v)
    + (2 * tubeCutoff v - 1) • eVert

/--
@isnad1 id=eq.0h3v.s8.cbf000b7de43 from=translated src=- shape=a1c77e53 vocab=90196ca7
-/
lemma tubeCollapseRaw_last (k : ℕ) (v : E) :
    tubeCollapseRaw k v (Fin.last (m + 2)) = 2 * tubeCutoff v - 1 := by
  rw [tubeCollapseRaw]
  change targetHorizontalCLM (tubeCollapseHorizontal k v) (Fin.last (m + 2))
      + (2 * tubeCutoff v - 1) * eVert (Fin.last (m + 2)) = _
  rw [targetHorizontalCLM_last, eVert_apply_last]
  ring

/--
@isnad1 id=eq.0h4v.s7.82cea12aa63a from=translated src=- shape=cb179748 vocab=6a4ebcff
-/
lemma tubeCollapseRaw_coord (k : ℕ) (v : E) (i : Fin (m + 2)) :
    tubeCollapseRaw k v i.castSucc = tubeCollapseHorizontal k v i := by
  rw [tubeCollapseRaw]
  change targetHorizontalCLM (tubeCollapseHorizontal k v) i.castSucc
      + (2 * tubeCutoff v - 1) * eVert i.castSucc = _
  rw [targetHorizontalCLM_coord, eVert_apply_ne (castSucc_ne_last i)]
  ring

/--
@isnad1 id=mem.1h2v.s6.ef5045d4a404 from=translated src=- shape=6fc17b22 vocab=0ea48235
-/
lemma tubeGood_of_tubeCutoff_ne_zero {v : E} (hv : tubeCutoff v ≠ 0) :
    v ∈ tubeGood := by
  have hd : tubeDistSq v < 1 / 9 := by
    by_contra h
    exact hv (tubeCutoff_of_ge (not_lt.mp h))
  apply outerTube_subset_tubeGood
  change tubeDistSq v < (1 / 3 : ℝ) ^ 2
  norm_num at hd ⊢
  exact hd

/--
@isnad1 id=ne.0h3v.s7.108cddf1b8fc from=translated src=- shape=6de1e657 vocab=88676c38
-/
lemma tubeCollapseRaw_ne_zero (k : ℕ) (v : E) : tubeCollapseRaw k v ≠ 0 := by
  intro hzero
  have hlast := congrArg (fun z : E => z (Fin.last (m + 2))) hzero
  rw [tubeCollapseRaw_last, PiLp.zero_apply] at hlast
  have hc : tubeCutoff v = 1 / 2 := by linarith
  have hc0 : tubeCutoff v ≠ 0 := by rw [hc]; norm_num
  have hhoriz : tubeCollapseHorizontal k v = 0 := by
    apply (WithLp.equiv 2 _).injective
    funext i
    have hi := congrArg (fun z : E => z i.castSucc) hzero
    rw [tubeCollapseRaw_coord, PiLp.zero_apply] at hi
    exact hi
  have hw : wCoord k v = 0 := by
    rw [tubeCollapseHorizontal, hc] at hhoriz
    exact (smul_eq_zero.mp hhoriz).resolve_left (by norm_num)
  have hvGood : v ∈ tubeGood := tubeGood_of_tubeCutoff_ne_zero hc0
  have hvCircle : v ∈ standardCircle :=
    (wCoord_eq_zero_iff_standardCircle k hvGood).mp hw
  have hvInner : v ∈ tubeRegion (1 / 4) := standardCircle_subset_innerTube hvCircle
  have hc1 : tubeCutoff v = 1 := tubeCutoff_eq_one_on_inner hvInner
  linarith

/--
@isnad1 id=contdiff.0h2v.s8.85adbe0a55dc from=translated src=- shape=6b0ec888 vocab=44cb2783
-/
theorem contDiff_tubeCollapseRaw (k : ℕ) :
    ContDiff ℝ ∞ (tubeCollapseRaw (m := m) k) := by
  have hh : ContDiff ℝ ∞ fun v : E =>
      targetHorizontalCLM (tubeCollapseHorizontal k v) :=
    targetHorizontalCLM.contDiff.comp (contDiff_tubeCollapseHorizontal k)
  have hv : ContDiff ℝ ∞ fun v : E => (2 * tubeCutoff v - 1) • eVert (m := m) :=
    ((contDiff_const.mul contDiff_tubeCutoff).sub contDiff_const).smul contDiff_const
  exact hh.add hv

/-- Ambient normalized representative of the sphere-valued Thom collapse.-/
def tubeThomVec (k : ℕ) (v : E) : E :=
  ‖tubeCollapseRaw k v‖⁻¹ • tubeCollapseRaw k v

/--
@isnad1 id=eq.0h3v.s6.3bc850755246 from=translated src=- shape=05b208d9 vocab=7d3429ef
-/
lemma norm_tubeThomVec (k : ℕ) (v : E) : ‖tubeThomVec k v‖ = 1 := by
  rw [tubeThomVec, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (tubeCollapseRaw_ne_zero k v))

/--
@isnad1 id=contdiff.0h2v.s8.cc7f226b897f from=translated src=- shape=6b0ec888 vocab=1f43716a
-/
theorem contDiff_tubeThomVec (k : ℕ) :
    ContDiff ℝ ∞ (tubeThomVec (m := m) k) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  have hr : ContDiffAt ℝ ∞ (tubeCollapseRaw (m := m) k) v :=
    (contDiff_tubeCollapseRaw (m := m) k).contDiffAt
  have hn : ContDiffAt ℝ ∞ (fun x => ‖tubeCollapseRaw k x‖) v :=
    hr.norm ℝ (tubeCollapseRaw_ne_zero k v)
  exact (hn.inv (norm_ne_zero_iff.mpr (tubeCollapseRaw_ne_zero k v))).smul hr

/-- The actual sphere-valued local Thom collapse.-/
def tubeThomCollapse (k : ℕ) (v : E) : UnitSphere E :=
  ⟨tubeThomVec k v, by
    rw [mem_sphere_zero_iff_norm]
    exact norm_tubeThomVec k v⟩

/--
@isnad1 id=eq.0h1v.s6.ea9dddccf764 from=translated src=- shape=d9262d93 vocab=9ce33e62
-/
lemma norm_eVert : ‖eVert (m := m)‖ = 1 := by
  have hsq : ‖eVert (m := m)‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_eVert_self]
  nlinarith [norm_nonneg (eVert (m := m))]

/-- North pole selected as the regular value of the collapse.-/
def tubeNorth : UnitSphere E :=
  ⟨eVert, by rw [mem_sphere_zero_iff_norm, norm_eVert]⟩

/-- South pole/basepoint of the collapse.-/
def tubeSouth : UnitSphere E :=
  ⟨-eVert, by rw [mem_sphere_zero_iff_norm, norm_neg, norm_eVert]⟩

/--
@isnad1 id=eq.0h1v.s8.6d079e05a847 from=translated src=- shape=83d7ce35 vocab=83438482
-/
@[simp] lemma tubeNorth_coe : ((tubeNorth (m := m) : UnitSphere E) : E) = eVert := rfl

/--
@isnad1 id=eq.0h1v.s9.8d5cbaf06bc2 from=translated src=- shape=f3d6b492 vocab=f69084eb
-/
@[simp] lemma tubeSouth_coe : ((tubeSouth (m := m) : UnitSphere E) : E) = -eVert := rfl

/--
@isnad1 id=eq.0h3v.s7.aeb7bb3e6ffb from=translated src=- shape=3f614992 vocab=7d796492
-/
lemma tubeCollapseHorizontal_circleAt (k : ℕ) (θ : ℝ) :
    tubeCollapseHorizontal (m := m) k (circleAt θ) = 0 := by
  rw [tubeCollapseHorizontal, wCoord_circleAt, smul_zero]

/--
@isnad1 id=eq.0h3v.s4.588f027256c6 from=translated src=- shape=c5100c41 vocab=5fe2cdd6
-/
lemma tubeCollapseRaw_circleAt (k : ℕ) (θ : ℝ) :
    tubeCollapseRaw (m := m) k (circleAt θ) = eVert := by
  rw [tubeCollapseRaw, tubeCollapseHorizontal_circleAt, map_zero, zero_add]
  have hmem : circleAt (m := m) θ ∈ tubeRegion (1 / 4) :=
    standardCircle_subset_innerTube (circleAt_mem_standardCircle θ)
  rw [tubeCutoff_eq_one_on_inner hmem]
  norm_num

/--
@isnad1 id=eq.0h3v.s4.661e93d48449 from=translated src=- shape=c5100c41 vocab=4520ca59
-/
lemma tubeThomVec_circleAt (k : ℕ) (θ : ℝ) :
    tubeThomVec (m := m) k (circleAt θ) = eVert := by
  rw [tubeThomVec, tubeCollapseRaw_circleAt, norm_eVert, inv_one, one_smul]

/--
@isnad1 id=eq.0h3v.s7.e0d616566f9a from=translated src=- shape=1e1ce24c vocab=20350c12
-/
@[simp] theorem tubeThomCollapse_circleAt (k : ℕ) (θ : ℝ) :
    tubeThomCollapse (m := m) k (circleAt θ) = tubeNorth := by
  apply Subtype.ext
  exact tubeThomVec_circleAt k θ

/--
@isnad1 id=eq.1h3v.s8.6eee63ddffce from=translated src=- shape=efebebf6 vocab=c88500b7
-/
lemma tubeCollapseRaw_off_outer (k : ℕ) {v : E}
    (hv : v ∉ tubeRegion (m := m) (1 / 3)) :
    tubeCollapseRaw k v = -eVert := by
  have hc : tubeCutoff v = 0 := tubeCutoff_eq_zero_off_outer hv
  have hh : tubeCollapseHorizontal k v = 0 := by
    rw [tubeCollapseHorizontal, hc, zero_smul]
  rw [tubeCollapseRaw, hh, map_zero, zero_add, hc]
  norm_num

/--
@isnad1 id=eq.1h3v.s8.eeed867af0db from=translated src=- shape=efebebf6 vocab=55a2084d
-/
lemma tubeThomVec_off_outer (k : ℕ) {v : E}
    (hv : v ∉ tubeRegion (m := m) (1 / 3)) :
    tubeThomVec k v = -eVert := by
  rw [tubeThomVec, tubeCollapseRaw_off_outer k hv, norm_neg, norm_eVert,
    inv_one, one_smul]

/--
@isnad1 id=eq.1h3v.s8.fdd9a82d36f1 from=translated src=- shape=7e55e9b1 vocab=6987687f
-/
theorem tubeThomCollapse_off_outer (k : ℕ) {v : E}
    (hv : v ∉ tubeRegion (m := m) (1 / 3)) :
    tubeThomCollapse k v = tubeSouth := by
  apply Subtype.ext
  exact tubeThomVec_off_outer k hv

/-- The north-pole fiber of the sphere-valued collapse is exactly the standard
circle, globally (not merely after restricting to the inner tube).
@isnad1 id=iff.0h3v.s7.599dbdd39b6a from=translated src=- shape=b36973ad vocab=befa8ee1
-/
theorem tubeThomCollapse_eq_north_iff (k : ℕ) {v : E} :
    tubeThomCollapse k v = tubeNorth ↔ v ∈ standardCircle := by
  constructor
  · intro hcollapse
    have hvec : tubeThomVec k v = eVert := congrArg Subtype.val hcollapse
    have hraw : tubeCollapseRaw k v ≠ 0 := tubeCollapseRaw_ne_zero k v
    have hnorm : ‖tubeCollapseRaw k v‖ ≠ 0 := norm_ne_zero_iff.mpr hraw
    have hinv : ‖tubeCollapseRaw k v‖⁻¹ ≠ 0 := inv_ne_zero hnorm
    have hhoriz : tubeCollapseHorizontal k v = 0 := by
      apply (WithLp.equiv 2 _).injective
      funext i
      have hi := congrArg (fun z : E => z i.castSucc) hvec
      change ‖tubeCollapseRaw k v‖⁻¹ * tubeCollapseRaw k v i.castSucc
          = eVert i.castSucc at hi
      rw [tubeCollapseRaw_coord, eVert_apply_ne (castSucc_ne_last i)] at hi
      exact (mul_eq_zero.mp hi).resolve_left hinv
    have hc0 : tubeCutoff v ≠ 0 := by
      intro hc
      have hlast := congrArg (fun z : E => z (Fin.last (m + 2))) hvec
      change ‖tubeCollapseRaw k v‖⁻¹
          * tubeCollapseRaw k v (Fin.last (m + 2)) = eVert (Fin.last (m + 2)) at hlast
      rw [tubeCollapseRaw_last, eVert_apply_last, hc] at hlast
      have hpos : 0 < ‖tubeCollapseRaw k v‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hraw)
      norm_num at hlast
      linarith
    have hw : wCoord k v = 0 := by
      rw [tubeCollapseHorizontal] at hhoriz
      exact (smul_eq_zero.mp hhoriz).resolve_left hc0
    exact (wCoord_eq_zero_iff_standardCircle k
      (tubeGood_of_tubeCutoff_ne_zero hc0)).mp hw
  · rintro ⟨θ, rfl⟩
    exact tubeThomCollapse_circleAt k θ

/--
@isnad1 id=eq.0h2v.s7.9c4c51419246 from=translated src=- shape=2bdbec09 vocab=2c51cd53
-/
theorem tubeThomCollapse_fiber (k : ℕ) :
    {v : E | tubeThomCollapse k v = tubeNorth} = standardCircle := by
  ext v
  exact tubeThomCollapse_eq_north_iff k

/-! ## Cubical representative and stable homotopy class -/

/--
@isnad1 id=continuo.0h2v.s9.95b442e39002 from=translated src=- shape=47c976d4 vocab=5400a922
-/
theorem continuous_tubeThomCollapse (k : ℕ) :
    Continuous (tubeThomCollapse (m := m) k) := by
  apply Continuous.subtype_mk
  exact (contDiff_tubeThomVec (m := m) k).continuous

/-- Continuous-map packaging of the ambient collapse.-/
def tubeThomCollapseCM (k : ℕ) : C(E, UnitSphere E) :=
  ⟨tubeThomCollapse k, continuous_tubeThomCollapse k⟩

/-- Affine expansion of the unit cube to `[-3,3]^{m+3}`.  The factor is chosen so
that every boundary face lies far outside the radius-`1/3` tube.-/
def cubeToTubeAmbient (t : I^(Fin (m + 3))) : E :=
  WithLp.toLp 2 fun i => 6 * (t i : ℝ) - 3

/--
@isnad1 id=eq.0h3v.s8.fb0ce9e1ffe3 from=translated src=- shape=183faffb vocab=f921c250
-/
@[simp] lemma cubeToTubeAmbient_apply (t : I^(Fin (m + 3))) (i : Fin (m + 3)) :
    cubeToTubeAmbient (m := m) t i = 6 * (t i : ℝ) - 3 := rfl

/--
@isnad1 id=continuo.0h1v.s7.07c61699fc4b from=translated src=- shape=393619d2 vocab=ee061151
-/
theorem continuous_cubeToTubeAmbient :
    Continuous (cubeToTubeAmbient (m := m)) := by
  have h : cubeToTubeAmbient (m := m) = fun t =>
      (EuclideanSpace.equiv (Fin (m + 3)) ℝ).symm
        (fun i => 6 * (t i : ℝ) - 3) := rfl
  rw [h]
  apply (EuclideanSpace.equiv (Fin (m + 3)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  exact (continuous_const.mul
    (continuous_subtype_val.comp (continuous_apply i))).sub continuous_const

/--
@isnad1 id=le.2h3v.s8.63597ce702ac from=translated src=- shape=9beb3a8e vocab=c34acb77
-/
lemma radSq_add_coordSq_le_normSq (v : E) {j : Fin (m + 3)}
    (hj0 : j ≠ 0) (hj1 : j ≠ 1) :
    radSq v + v j ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [normSq_eq_sum_sq]
  have hsub : ({0, 1, j} : Finset (Fin (m + 3))) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hsum : ∑ i ∈ ({0, 1, j} : Finset (Fin (m + 3))), v i ^ 2
      = radSq v + v j ^ 2 := by
    have hset : ({0, 1, j} : Finset (Fin (m + 3))) = {j, 0, 1} := by
      ext i
      simp [or_comm, or_left_comm, or_assoc]
    rw [hset, Finset.sum_insert (by simp [hj0, hj1]),
      Finset.sum_insert
        (by simp : (0 : Fin (m + 3)) ∉ ({1} : Finset (Fin (m + 3)))),
      Finset.sum_singleton]
    unfold radSq
    ring
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => sq_nonneg _

/--
@isnad1 id=le.2h3v.s8.082a41e2cb90 from=translated src=- shape=25613d29 vocab=2cff8b89
-/
lemma coordSq_le_tubeDistSq_of_ne (v : E) {j : Fin (m + 3)}
    (hj0 : j ≠ 0) (hj1 : j ≠ 1) :
    v j ^ 2 ≤ tubeDistSq v := by
  have hcoord := radSq_add_coordSq_le_normSq v hj0 hj1
  have hrsq := rad_sq v
  rw [tubeDistSq]
  nlinarith [sq_nonneg (rad v - 1)]

/--
@isnad1 id=eq.1h3v.s7.fc2a08c3b7a0 from=translated src=- shape=1f3a03bf vocab=2b09bde2
-/
lemma cubeToTubeAmbient_boundary_abs {t : I^(Fin (m + 3))}
    {j : Fin (m + 3)} (hj : t j = 0 ∨ t j = 1) :
    |cubeToTubeAmbient (m := m) t j| = 3 := by
  rcases hj with hj | hj
  · rw [cubeToTubeAmbient_apply, hj, Set.Icc.coe_zero]
    norm_num
  · rw [cubeToTubeAmbient_apply, hj, Set.Icc.coe_one]
    norm_num

/-- Every boundary point of the expanded cube is outside the outer tube.
@isnad1 id=not.1h2v.s7.f7edd01cf234 from=translated src=- shape=00de6928 vocab=52f7d18f
-/
theorem cubeToTubeAmbient_boundary_off_outer {t : I^(Fin (m + 3))}
    (ht : t ∈ Cube.boundary (Fin (m + 3))) :
    cubeToTubeAmbient (m := m) t ∉ tubeRegion (1 / 3) := by
  obtain ⟨j, hj⟩ := ht
  have habs := cubeToTubeAmbient_boundary_abs (m := m) hj
  have hsq : cubeToTubeAmbient (m := m) t j ^ 2 = 9 := by
    nlinarith [sq_abs (cubeToTubeAmbient (m := m) t j)]
  have hd : 1 / 9 ≤ tubeDistSq (cubeToTubeAmbient (m := m) t) := by
    by_cases hj0 : j = 0
    · subst j
      have hrsq := rad_sq (cubeToTubeAmbient (m := m) t)
      have hr0 := rad_nonneg (cubeToTubeAmbient (m := m) t)
      have hrad : 3 ≤ rad (cubeToTubeAmbient (m := m) t) := by
        rw [radSq] at hrsq
        nlinarith [sq_nonneg (cubeToTubeAmbient (m := m) t 1)]
      have hdist := sq_rad_le_tubeDistSq (cubeToTubeAmbient (m := m) t)
      nlinarith [sq_nonneg (rad (cubeToTubeAmbient (m := m) t) - 1)]
    · by_cases hj1 : j = 1
      · subst j
        have hrsq := rad_sq (cubeToTubeAmbient (m := m) t)
        have hr0 := rad_nonneg (cubeToTubeAmbient (m := m) t)
        have hrad : 3 ≤ rad (cubeToTubeAmbient (m := m) t) := by
          rw [radSq] at hrsq
          nlinarith [sq_nonneg (cubeToTubeAmbient (m := m) t 0)]
        have hdist := sq_rad_le_tubeDistSq (cubeToTubeAmbient (m := m) t)
        nlinarith [sq_nonneg (rad (cubeToTubeAmbient (m := m) t) - 1)]
      · have hdist := coordSq_le_tubeDistSq_of_ne
          (cubeToTubeAmbient (m := m) t) hj0 hj1
        nlinarith
  intro hin
  change tubeDistSq (cubeToTubeAmbient (m := m) t) < (1 / 3 : ℝ) ^ 2 at hin
  norm_num at hin
  exact (not_lt_of_ge hd) hin

/-- The cube boundary is sent to the south-pole basepoint.
@isnad1 id=eq.1h3v.s8.58952f9338aa from=translated src=- shape=ae49b0b9 vocab=a544ccdf
-/
theorem tubeThomCollapse_cube_boundary (k : ℕ) {t : I^(Fin (m + 3))}
    (ht : t ∈ Cube.boundary (Fin (m + 3))) :
    tubeThomCollapse k (cubeToTubeAmbient t) = tubeSouth :=
  tubeThomCollapse_off_outer k (cubeToTubeAmbient_boundary_off_outer ht)

/-- Cubical generalized loop represented by the explicit twist-`k` Thom collapse.-/
def tubeThomGenLoop (k : ℕ) :
    Ω^ (Fin (m + 3)) (UnitSphere E) tubeSouth :=
  ⟨(tubeThomCollapseCM k).comp
      ⟨cubeToTubeAmbient, continuous_cubeToTubeAmbient⟩,
    fun t ht => tubeThomCollapse_cube_boundary k ht⟩

/--
@isnad1 id=eq.0h3v.s11.0948f6530f89 from=translated src=- shape=fb429b9f vocab=fcf7f101
-/
@[simp] lemma tubeThomGenLoop_apply (k : ℕ) (t : I^(Fin (m + 3))) :
    tubeThomGenLoop (m := m) k t = tubeThomCollapse k (cubeToTubeAmbient t) := rfl

/-- The explicit stable homotopy class of the twist-`k` circle collapse.-/
def tubeThomClass (k : ℕ) :
    HomotopyGroup (Fin (m + 3)) (UnitSphere E) tubeSouth :=
  ⟦tubeThomGenLoop k⟧

/-- The two standard representatives used by the final parity argument.-/
def tubeThomClassZero :
    HomotopyGroup (Fin (m + 3)) (UnitSphere E) tubeSouth := tubeThomClass 0

def tubeThomClassOne :
    HomotopyGroup (Fin (m + 3)) (UnitSphere E) tubeSouth := tubeThomClass 1

/--
@isnad1 id=eq.0h1v.s5.44d22536b78f from=translated src=- shape=ed7d3c5f vocab=770d6b72
-/
lemma eVert_eq_eLast : eVert (m := m) = eLast (m + 2) := by
  apply (WithLp.equiv 2 _).injective
  funext j
  simp [eVert, coordVec, eLast, PiLp.single_apply]

/--
@isnad1 id=eq.0h1v.s7.ba219a2e3a93 from=translated src=- shape=699e8a64 vocab=a1dec8cc
-/
lemma tubeSouth_eq_southPole :
    (tubeSouth (m := m) : UnitSphere E) = southPole (m + 2) := by
  apply Subtype.ext
  show -eVert (m := m) = -eLast (m + 2)
  rw [eVert_eq_eLast]

/-- The explicit cubical tube loop with the canonical `southPole` basepoint
used by `StableSpherePi`.  Only the boundary proof changes; the underlying
continuous map is definitionally `tubeThomGenLoop`.-/
def tubeThomStableGenLoop (k : ℕ) :
    Ω^ (Fin (m + 3)) (UnitSphere E) (southPole (m + 2)) :=
  ⟨(tubeThomGenLoop (m := m) k).1, fun t ht =>
    ((tubeThomGenLoop (m := m) k).2 t ht).trans tubeSouth_eq_southPole⟩

/--
@isnad1 id=eq.0h3v.s11.1c0bd6f16fdd from=translated src=- shape=5dfdbddb vocab=b6597cdf
-/
@[simp] theorem tubeThomStableGenLoop_apply (k : ℕ)
    (t : I^(Fin (m + 3))) :
    tubeThomStableGenLoop (m := m) k t =
      tubeThomCollapse k (cubeToTubeAmbient t) :=
  rfl

/-- The same class in the canonical `StableSpherePi` abbreviation used by the
final assembly.-/
def tubeThomStableClass (k : ℕ) : StableSpherePi (m + 2) :=
  ⟦tubeThomStableGenLoop k⟧

def tubeThomStableClassZero : StableSpherePi (m + 2) := tubeThomStableClass 0

def tubeThomStableClassOne : StableSpherePi (m + 2) := tubeThomStableClass 1

/-- A cubical parameter for every point of the standard circle.-/
def circleCubePoint (θ : ℝ) : I^(Fin (m + 3)) := fun i =>
  Set.projIcc (0 : ℝ) 1 zero_le_one ((circleAt (m := m) θ i + 3) / 6)

/--
@isnad1 id=eq.0h3v.s7.358f059a35ea from=translated src=- shape=d50e63f9 vocab=d323ad16
-/
lemma circleCubePoint_coe (θ : ℝ) (i : Fin (m + 3)) :
    ((circleCubePoint (m := m) θ i : I) : ℝ) = (circleAt θ i + 3) / 6 := by
  have habs : |circleAt (m := m) θ i| ≤ 1 := by
    rw [← norm_circleAt (m := m) θ]
    exact abs_coordinate_le_norm (circleAt (m := m) θ) i
  have hb := abs_le.mp habs
  rw [circleCubePoint, Set.coe_projIcc, min_eq_right (by linarith),
    max_eq_right (by linarith)]

/--
@isnad1 id=eq.0h2v.s4.5b8751d40cdb from=translated src=- shape=cffc0b14 vocab=5fd31eab
-/
lemma cubeToTubeAmbient_circleCubePoint (θ : ℝ) :
    cubeToTubeAmbient (m := m) (circleCubePoint θ) = circleAt θ := by
  apply (WithLp.equiv 2 _).injective
  funext i
  change 6 * (((circleCubePoint (m := m) θ i : I) : ℝ)) - 3 = circleAt θ i
  rw [circleCubePoint_coe]
  ring

/--
@isnad1 id=eq.0h3v.s11.3b577c49d2eb from=translated src=- shape=f0e64b99 vocab=be9e5b10
-/
@[simp] theorem tubeThomGenLoop_circleCubePoint (k : ℕ) (θ : ℝ) :
    tubeThomGenLoop (m := m) k (circleCubePoint θ) = tubeNorth := by
  rw [tubeThomGenLoop_apply, cubeToTubeAmbient_circleCubePoint]
  exact tubeThomCollapse_circleAt k θ

/-! ### Framing/parity contract exposed to the delta calculation -/

/-- The parity carried by the twist-`k` normal framing.  The differential theorem
`fderiv_tubeCollapseHorizontal_nuVec` is the geometric realization of this
declared twist.-/
def tubeTwistParity (k : ℕ) : ZMod 2 := k

/--
@isnad1 id=eq.0h0v.s6.0994424f9e92 from=translated src=- shape=3a1213c4 vocab=a03b32e4
-/
@[simp] theorem tubeTwistParity_zero : tubeTwistParity 0 = 0 := rfl

/--
@isnad1 id=eq.0h0v.s6.f34a8f570d85 from=translated src=- shape=3a1213c4 vocab=a03b32e4
-/
@[simp] theorem tubeTwistParity_one : tubeTwistParity 1 = 1 := rfl

/-- Packaged local regular-fiber data needed when the north fiber is converted to
a `FramedLevelSet` component.-/
structure TubeNorthFiberContract (k : ℕ) where
  fiber_eq : {v : E | tubeThomCollapse (m := m) k v = tubeNorth} =
    standardCircle (m := m)
  localMapSmooth : ContDiff ℝ ∞ (tubeCollapseHorizontal (m := m) k)
  localFiber : ∀ {v : E}, v ∈ tubeRegion (m := m) (1 / 4) →
    (tubeCollapseHorizontal (m := m) k v = 0 ↔ v ∈ standardCircle)
  regular : ∀ θ, Function.Surjective
    (fderiv ℝ (tubeCollapseHorizontal (m := m) k) (circleAt θ))
  frame : ∀ θ (i : Fin (m + 2)),
    fderiv ℝ (tubeCollapseHorizontal (m := m) k) (circleAt θ) (nuVec k θ i)
      = EuclideanSpace.single i 1
  parity : ZMod 2
  parity_eq : parity = k

/-- The explicit collapse satisfies the full local regular-fiber/framing contract.-/
def tubeNorthFiberContract (k : ℕ) : TubeNorthFiberContract (m := m) k where
  fiber_eq := tubeThomCollapse_fiber k
  localMapSmooth := contDiff_tubeCollapseHorizontal k
  localFiber := fun hv => tubeCollapseHorizontal_eq_zero_iff_standardCircle k hv
  regular := surjective_fderiv_tubeCollapseHorizontal_circleAt k
  frame := fderiv_tubeCollapseHorizontal_nuVec k
  parity := tubeTwistParity k
  parity_eq := rfl

/--
@isnad1 id=eq.0h2v.s6.a796b30bc1bf from=translated src=- shape=b3abb7d5 vocab=94e6b4d0
-/
@[simp] theorem tubeNorthFiberContract_parity (k : ℕ) :
    (tubeNorthFiberContract (m := m) k).parity = (k : ZMod 2) := rfl

/--
@isnad1 id=ne.0h1v.s5.35c055b7b5be from=translated src=- shape=da9570e6 vocab=c6197f89
-/
theorem tubeNorthFiberContract_zero_one_parity_ne :
    (tubeNorthFiberContract (m := m) 0).parity ≠
      (tubeNorthFiberContract (m := m) 1).parity := by
  norm_num

end Submission
