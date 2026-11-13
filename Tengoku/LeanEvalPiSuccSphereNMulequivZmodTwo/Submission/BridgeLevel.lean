import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SmoothApprox
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.PlateauSmooth
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.Sard
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.LevelSet

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The forward Pontryagin–Thom bridge: from homotopy classes to framed level sets

For a class `z ∈ π_{n+1}(Sⁿ)` based at the south pole we produce, via smooth
approximation (`SmoothApprox`), the southern plateau `Θ` (`PlateauSmooth`) and a
Sard-generic regular value (`Sard`), a `FramedLevelSet n` presenting the level set
of the "horizontal coordinates" map of a smooth representative:

* `Submission.nprep a : ℝ^{n+1} → ℝ^{n+1}` — the normalized plateaued raw map; it is
  `C^∞`, sphere-valued, equal to the south pole on the collar of the cube boundary,
  and its restriction to the cube is the plateaued representative `prepLoop a`,
  a generalized loop with `⟦prepLoop a⟧ = z`;
* `Submission.bridgeHMap a := init ∘ nprep a : ℝ^{n+1} → ℝⁿ` — the first `n`
  coordinates ("horizontal coordinates") of `nprep`;
* `Submission.bridgeFLS a y … : FramedLevelSet n` with `g := bridgeHMap - y` for a
  Sard-regular value `y` with `0 < ‖y‖ < 1/8`;
* the exact fiber description (`Submission.bridgeFLS_fiber`): the fiber is
  `{v | nprep a v = northPoint y} ∪ {v | nprep a v = southPointOf y}` where
  `northPoint y`/`southPointOf y` are the two points of `Sⁿ` lying over `y`,
  together with the criterion `Submission.nprep_eq_northPoint_iff` telling the two
  parts of the fiber apart by the sign of the vertical coordinate;
* `Submission.BridgeData`, `Submission.exists_bridgeData` — the packaged
  data-carrying bridge.

## Design note (important for downstream waves)

The original wave specification asked for a plateau `Θ` for which the fiber over a
small regular value `y` is *only* the northern preimage `{v | nprep v = northPoint y}`.
This is topologically impossible for any map of the form `coordinates ∘ (sphere-valued
map)`: a total map `q : Sⁿ → ℝⁿ` with a single regular zero would restrict, on a small
sphere around the zero, to a degree-`±1` map `S^{n-1} → ℝⁿ \ {0} ≃ S^{n-1}` that is
nullhomotopic in the complement — a contradiction.  Since a representative of a
nontrivial class is necessarily surjective onto `Sⁿ`, both points over `y` always have
nonempty preimage.  Consequently this module delivers the *two-point* fiber with an
exact dichotomy and a clean separation criterion (the sign of the vertical
coordinate); extracting the northern half as the zero set of a single global map
requires the tubular-neighbourhood collapse of the inverse Pontryagin–Thom direction
and is deferred to that layer.
-/

noncomputable section

open scoped Topology unitInterval ContDiff
open Metric Set Function Topology.Homotopy

namespace Submission

/-! ### Dropping and appending the last coordinate -/

/-- The linear map `ℝ^{m+1} → ℝ^m` forgetting the last coordinate.-/
def initLM (m : ℕ) :
    EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) where
  toFun w := WithLp.toLp 2 (Fin.init (WithLp.ofLp w))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The continuous linear map `ℝ^{m+1} → ℝ^m` forgetting the last coordinate.-/
def initCLM (m : ℕ) :
    EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (initLM m).toContinuousLinearMap

@[simp] lemma initCLM_apply (m : ℕ) (w : EuclideanSpace ℝ (Fin (m + 1)))
    (j : Fin m) : initCLM m w j = w j.castSucc :=
  rfl

/-- The linear map `ℝ^m → ℝ^{m+1}` appending a last coordinate `0`.-/
def embedLM (m : ℕ) :
    EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) where
  toFun y := WithLp.toLp 2 (Fin.snoc (WithLp.ofLp y) 0)
  map_add' y z := by
    apply (WithLp.equiv 2 _).injective
    funext i
    induction i using Fin.lastCases with
    | last => simp [Fin.snoc_last]
    | cast j => simp [Fin.snoc_castSucc]
  map_smul' c y := by
    apply (WithLp.equiv 2 _).injective
    funext i
    induction i using Fin.lastCases with
    | last => simp [Fin.snoc_last]
    | cast j => simp [Fin.snoc_castSucc]

/-- The continuous linear map `ℝ^m → ℝ^{m+1}` appending a last coordinate `0`.-/
def embedCLM (m : ℕ) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
  (embedLM m).toContinuousLinearMap

@[simp] lemma embedCLM_apply_castSucc (m : ℕ) (y : EuclideanSpace ℝ (Fin m))
    (j : Fin m) : embedCLM m y j.castSucc = y j := by
  show (Fin.snoc (α := fun _ => ℝ) (WithLp.ofLp y) 0) j.castSucc = y j
  exact Fin.snoc_castSucc _ _ j

@[simp] lemma embedCLM_apply_last (m : ℕ) (y : EuclideanSpace ℝ (Fin m)) :
    embedCLM m y (Fin.last m) = 0 := by
  show (Fin.snoc (α := fun _ => ℝ) (WithLp.ofLp y) 0) (Fin.last m) = 0
  exact Fin.snoc_last _ _

lemma initCLM_embedCLM (m : ℕ) (y : EuclideanSpace ℝ (Fin m)) :
    initCLM m (embedCLM m y) = y := by
  apply (WithLp.equiv 2 _).injective
  funext j
  simp

lemma initCLM_eLast (n : ℕ) : initCLM n (eLast n) = 0 := by
  apply (WithLp.equiv 2 _).injective
  funext j
  have hne : (j.castSucc : Fin (n + 1)) ≠ Fin.last n := (Fin.castSucc_lt_last j).ne
  simp [eLast, hne]

/-- Every vector splits as its horizontal part plus its vertical part.-/
lemma eq_embed_init_add {n : ℕ} (w : EuclideanSpace ℝ (Fin (n + 1))) :
    w = embedCLM n (initCLM n w) + vertC w • eLast n := by
  apply (WithLp.equiv 2 _).injective
  funext i
  induction i using Fin.lastCases with
  | last => simp [vertC, eLast]
  | cast j =>
    have hne : (j.castSucc : Fin (n + 1)) ≠ Fin.last n := (Fin.castSucc_lt_last j).ne
    simp [eLast, hne]

lemma norm_sq_eq_sum {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

/-- Pythagoras for the horizontal/vertical splitting.-/
lemma norm_sq_split {n : ℕ} (w : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖w‖ ^ 2 = ‖initCLM n w‖ ^ 2 + vertC w ^ 2 := by
  rw [norm_sq_eq_sum, norm_sq_eq_sum, Fin.sum_univ_castSucc]
  simp [vertC]

/-! ### The two points of the sphere over a horizontal value -/

/-- The northern point of the unit sphere over `y ∈ ℝⁿ` (for `‖y‖ ≤ 1`).-/
def northPoint {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  embedCLM n y + Real.sqrt (1 - ‖y‖ ^ 2) • eLast n

/-- The southern point of the unit sphere over `y ∈ ℝⁿ` (for `‖y‖ ≤ 1`).-/
def southPointOf {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  embedCLM n y - Real.sqrt (1 - ‖y‖ ^ 2) • eLast n

lemma initCLM_northPoint {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    initCLM n (northPoint y) = y := by
  rw [northPoint, map_add, map_smul, initCLM_embedCLM, initCLM_eLast, smul_zero,
    add_zero]

lemma initCLM_southPointOf {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    initCLM n (southPointOf y) = y := by
  rw [southPointOf, map_sub, map_smul, initCLM_embedCLM, initCLM_eLast, smul_zero,
    sub_zero]

lemma vertC_northPoint {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    vertC (northPoint y) = Real.sqrt (1 - ‖y‖ ^ 2) := by
  show (northPoint y) (Fin.last n) = _
  rw [northPoint]
  simp [eLast]

lemma vertC_southPointOf {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    vertC (southPointOf y) = -Real.sqrt (1 - ‖y‖ ^ 2) := by
  show (southPointOf y) (Fin.last n) = _
  rw [southPointOf]
  simp [eLast]

/-- Dichotomy: a unit vector with horizontal part `y` is the northern or the
southern point over `y`.-/
lemma init_eq_iff {n : ℕ} {w : EuclideanSpace ℝ (Fin (n + 1))} (hw : ‖w‖ = 1)
    (y : EuclideanSpace ℝ (Fin n)) :
    initCLM n w = y ↔ w = northPoint y ∨ w = southPointOf y := by
  constructor
  · intro h
    have hsplit : ‖w‖ ^ 2 = ‖initCLM n w‖ ^ 2 + vertC w ^ 2 := norm_sq_split w
    rw [hw, h] at hsplit
    have hsq : vertC w ^ 2 = 1 - ‖y‖ ^ 2 := by linarith [hsplit]
    have habs : |vertC w| = Real.sqrt (1 - ‖y‖ ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs, hsq]
    have hdecomp : w = embedCLM n (initCLM n w) + vertC w • eLast n :=
      eq_embed_init_add w
    rcases (abs_eq (Real.sqrt_nonneg _)).mp habs with hv | hv
    · left
      rw [northPoint, ← hv, ← h]
      exact hdecomp
    · right
      rw [southPointOf, sub_eq_add_neg, ← neg_smul, ← hv, ← h]
      exact hdecomp
  · rintro (rfl | rfl)
    · exact initCLM_northPoint y
    · exact initCLM_southPointOf y

lemma vertC_northPoint_pos {n : ℕ} {y : EuclideanSpace ℝ (Fin n)}
    (hy : ‖y‖ < 1) : 0 < vertC (northPoint y) := by
  rw [vertC_northPoint]
  apply Real.sqrt_pos.mpr
  have h0 : 0 ≤ ‖y‖ := norm_nonneg y
  nlinarith

lemma vertC_southPointOf_neg {n : ℕ} {y : EuclideanSpace ℝ (Fin n)}
    (hy : ‖y‖ < 1) : vertC (southPointOf y) < 0 := by
  rw [vertC_southPointOf, neg_lt, neg_zero]
  apply Real.sqrt_pos.mpr
  have h0 : 0 ≤ ‖y‖ := norm_nonneg y
  nlinarith

/-! ### Smooth normalization -/

/-- Normalizing a smooth nonvanishing map into an inner product space is smooth.-/
lemma contDiff_normalize_comp {X E' : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    {f : X → E'} (hf : ContDiff ℝ ∞ f) (h0 : ∀ x, f x ≠ 0) :
    ContDiff ℝ ∞ fun x => ‖f x‖⁻¹ • f x := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hnorm : ContDiffAt ℝ ∞ (fun x => ‖f x‖) x := hf.contDiffAt.norm ℝ (h0 x)
  exact (hnorm.inv (norm_ne_zero_iff.mpr (h0 x))).smul hf.contDiffAt

/-! ### The plateaued representative of an approximation -/

variable {n : ℕ}

/-- The normalized raw map of an approximation, as an everywhere-defined
sphere-valued (`‖·‖ = 1`) map on `ℝ^{n+1}`.-/
def nraw {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
    (southPole n)} (a : Approximation p) :
    (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)) :=
  fun v => ‖a.raw v‖⁻¹ • a.raw v

/-- The plateaued raw map: apply the ambient plateau to the normalized raw map.-/
def praw {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
    (southPole n)} (a : Approximation p) :
    (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)) :=
  fun v => plateauAux (nraw a v)

/-- The normalized plateaued map: a sphere-valued `C^∞` map on all of `ℝ^{n+1}`.-/
def nprep {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
    (southPole n)} (a : Approximation p) :
    (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)) :=
  fun v => ‖praw a v‖⁻¹ • praw a v

variable {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
    (southPole n)} (a : Approximation p)

lemma norm_nraw (v : Fin (n + 1) → ℝ) : ‖nraw a v‖ = 1 :=
  norm_normalize (a.raw_ne_zero v)

lemma contDiff_nraw : ContDiff ℝ ∞ (nraw a) :=
  contDiff_normalize_comp a.contDiff_raw a.raw_ne_zero

lemma contDiff_praw : ContDiff ℝ ∞ (praw a) :=
  contDiff_plateauAux.comp (contDiff_nraw a)

lemma praw_ne_zero (v : Fin (n + 1) → ℝ) : praw a v ≠ 0 :=
  plateauAux_ne_zero (norm_nraw a v)

lemma norm_nprep (v : Fin (n + 1) → ℝ) : ‖nprep a v‖ = 1 :=
  norm_normalize (praw_ne_zero a v)

lemma contDiff_nprep : ContDiff ℝ ∞ (nprep a) :=
  contDiff_normalize_comp (contDiff_praw a) (praw_ne_zero a)

/-- On the collar of the cube boundary, the normalized plateaued map is the south
pole.-/
lemma nprep_of_mem_collar {v : Fin (n + 1) → ℝ}
    (hv : v ∈ closedAmbientCollar (Fin (n + 1))) :
    nprep a v = -eLast n := by
  have hraw : a.raw v = ((southPole n) : EuclideanSpace ℝ (Fin (n + 1))) :=
    a.raw_eq_basepoint_on_collar v hv
  have hnraw : nraw a v = -eLast n := by
    rw [nraw, hraw, southPole_coe, norm_neg, norm_eLast]
    simp
  have hvert : vertC (-eLast n : EuclideanSpace ℝ (Fin (n + 1))) = -1 := by
    show (-eLast n) (Fin.last n) = -1
    simp [eLast]
  have hpraw : praw a v = -eLast n := by
    rw [praw, hnraw]
    exact plateauAux_of_le (by rw [hvert]; norm_num)
  show ‖praw a v‖⁻¹ • praw a v = -eLast n
  rw [hpraw, norm_neg, norm_eLast]
  simp

/-! ### The horizontal-coordinates map -/

/-- The horizontal coordinates of the normalized plateaued map: a total `C^∞` map
`ℝ^{n+1} → ℝⁿ` (in cube coordinates).-/
def bridgeHMap {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
    (southPole n)} (a : Approximation p) :
    (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin n) :=
  fun v => initCLM n (nprep a v)

lemma contDiff_bridgeHMap : ContDiff ℝ ∞ (bridgeHMap a) :=
  (initCLM n).contDiff.comp (contDiff_nprep a)

lemma bridgeHMap_of_mem_collar {v : Fin (n + 1) → ℝ}
    (hv : v ∈ closedAmbientCollar (Fin (n + 1))) : bridgeHMap a v = 0 := by
  rw [bridgeHMap, nprep_of_mem_collar a hv, map_neg, initCLM_eLast, neg_zero]

/-- The fiber dichotomy for the horizontal-coordinates map.-/
lemma bridgeHMap_eq_iff (v : Fin (n + 1) → ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    bridgeHMap a v = y ↔ nprep a v = northPoint y ∨ nprep a v = southPointOf y :=
  init_eq_iff (norm_nprep a v) y

/-- Among fiber points, the northern point is recognized by the positivity of the
vertical coordinate.-/
lemma nprep_eq_northPoint_iff {v : Fin (n + 1) → ℝ}
    {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ < 1) (hfib : bridgeHMap a v = y) :
    nprep a v = northPoint y ↔ 0 < vertC (nprep a v) := by
  constructor
  · intro h
    rw [h]
    exact vertC_northPoint_pos hy
  · intro h
    rcases (bridgeHMap_eq_iff a v y).mp hfib with hn | hs
    · exact hn
    · exfalso
      rw [hs] at h
      exact absurd h (not_lt.mpr (le_of_lt (vertC_southPointOf_neg hy)))

/-! ### The plateaued generalized loop -/

/-- The plateaued representative, as a generalized loop: post-composition of the
representative of the approximation with the plateau `Θ`.-/
def prepLoop {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
    (southPole n)} (a : Approximation p) :
    Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n) :=
  genLoopMap (plateauMap n) plateauMap_southPole a.representative

/-- On the cube, the plateaued loop is the normalized plateaued map.-/
lemma prepLoop_coe (t : I^ (Fin (n + 1))) :
    ((prepLoop a t) : EuclideanSpace ℝ (Fin (n + 1)))
      = nprep a (fun i => (t i : ℝ)) := by
  show ((plateauMap n (a.representative t)) : EuclideanSpace ℝ (Fin (n + 1))) = _
  rw [plateauMap_coe]
  have hcoe : ((a.representative t) : EuclideanSpace ℝ (Fin (n + 1)))
      = nraw a (fun i => (t i : ℝ)) := a.representative_coe t
  rw [hcoe]
  rfl

/-! ### Sard: choice of a small regular value -/

/-- The horizontal-coordinates map, transported to the Euclidean domain.-/
def bridgeHMapE {p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1))))
    (southPole n)} (a : Approximation p) :
    EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n) :=
  fun x => bridgeHMap a (WithLp.ofLp x)

lemma contDiff_bridgeHMapE : ContDiff ℝ ∞ (bridgeHMapE a) :=
  (contDiff_bridgeHMap a).comp (EuclideanSpace.equiv (Fin (n + 1)) ℝ).contDiff

/-- Sard's theorem provides a regular value `y` of the horizontal-coordinates map
with `0 < ‖y‖ < 1/8`.  It is chosen in the fixed positive half-space used later
to join independently chosen bridge values without passing through the origin.-/
theorem exists_bridge_regular_value (hn : 0 < n) :
    ∃ y : EuclideanSpace ℝ (Fin n),
      0 < ‖y‖ ∧ ‖y‖ < 1 / 8 ∧ 0 < y ⟨0, hn⟩ ∧
        IsRegularValue (bridgeHMapE a) y := by
  set z₀ : EuclideanSpace ℝ (Fin n) :=
    EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 / 16 : ℝ) with hz₀
  have hz₀norm : ‖z₀‖ = 1 / 16 := by
    rw [hz₀, PiLp.norm_single, Real.norm_eq_abs]
    norm_num
  obtain ⟨y, hy_ball, hy_reg⟩ :=
    sard_exists_regular_value_in_ball (contDiff_bridgeHMapE a) z₀
      (by norm_num : (0 : ℝ) < 1 / 32)
  have hdist : ‖y - z₀‖ < 1 / 32 := by
    rw [← dist_eq_norm]
    exact mem_ball.mp hy_ball
  have habs : |‖y‖ - ‖z₀‖| ≤ ‖y - z₀‖ := abs_norm_sub_norm_le y z₀
  rw [abs_le] at habs
  have hcoord : |y ⟨0, hn⟩ - 1 / 16| < 1 / 32 := by
    have hle := PiLp.norm_apply_le (y - z₀) ⟨0, hn⟩
    have hval : (y - z₀) ⟨0, hn⟩ = y ⟨0, hn⟩ - 1 / 16 := by
      simp [hz₀]
    rw [Real.norm_eq_abs, hval] at hle
    exact hle.trans_lt hdist
  refine ⟨y, ?_, ?_, ?_, hy_reg⟩
  · rw [hz₀norm] at habs
    linarith [habs.1]
  · rw [hz₀norm] at habs
    linarith [habs.2]
  · rw [abs_lt] at hcoord
    linarith [hcoord.1]

/-! ### The framed level set -/

/-- The framed level set attached to an approximation and a regular value of its
horizontal-coordinates map.-/
def bridgeFLS (y : EuclideanSpace ℝ (Fin n)) (hy : y ≠ 0)
    (hreg : IsRegularValue (bridgeHMapE a) y) : FramedLevelSet n where
  g := fun x => bridgeHMapE a x - y
  smooth := (contDiff_bridgeHMapE a).sub contDiff_const
  fiber_bounded := by
    apply (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin (n + 1))))
      (r := (n + 1 : ℝ))).subset
    intro x hx
    have hfx : bridgeHMapE a x = y := sub_eq_zero.mp hx
    have hnc : WithLp.ofLp x ∉ closedAmbientCollar (Fin (n + 1)) := by
      intro hc
      apply hy
      rw [← hfx]
      exact (bridgeHMap_of_mem_collar a hc).symm ▸ rfl
    have hcoord : ∀ i, |x i| ≤ 1 := by
      intro i
      have h1 : ¬(x i ≤ 1 / 5 ∨ 4 / 5 ≤ x i) := fun h => hnc ⟨i, h⟩
      rw [not_or, not_le, not_le] at h1
      exact abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have hnorm : ‖x‖ ≤ n + 1 := by
      have h1 : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := norm_sq_eq_sum x
      have h2 : (∑ i, x i ^ 2) ≤ ∑ _i : Fin (n + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have := hcoord i
        nlinarith [abs_nonneg (x i), sq_abs (x i)]
      have h3 : (∑ _i : Fin (n + 1), (1 : ℝ)) = n + 1 := by simp
      have h4 : ‖x‖ ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hn1 : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
        calc ‖x‖ ^ 2 = ∑ i, x i ^ 2 := h1
          _ ≤ n + 1 := h2.trans_eq h3
          _ ≤ ((n : ℝ) + 1) ^ 2 := hn1
      have h5 : (0 : ℝ) ≤ n + 1 := by positivity
      nlinarith [norm_nonneg x]
    rw [mem_closedBall, dist_zero_right]
    exact hnorm
  regular := by
    intro x hx
    have hfx : bridgeHMapE a x = y := sub_eq_zero.mp hx
    have hderiv : fderiv ℝ (fun x => bridgeHMapE a x - y) x
        = fderiv ℝ (bridgeHMapE a) x := fderiv_sub_const y
    rw [hderiv]
    exact hreg x hfx

/-- The fiber of the bridge level set is exactly the two-point-preimage of the two
sphere points over `y`.-/
theorem bridgeFLS_fiber (y : EuclideanSpace ℝ (Fin n)) (hy : y ≠ 0)
    (hreg : IsRegularValue (bridgeHMapE a) y) :
    (bridgeFLS a y hy hreg).fiber
      = {x | nprep a (WithLp.ofLp x) = northPoint y
          ∨ nprep a (WithLp.ofLp x) = southPointOf y} := by
  ext x
  show bridgeHMapE a x - y = 0 ↔ _
  rw [sub_eq_zero]
  exact bridgeHMap_eq_iff a (WithLp.ofLp x) y

/-! ### The packaged bridge data -/

/-- All data produced by the forward bridge for a homotopy class `z`: a smooth
approximation of a representative, a Sard-regular value `y` of the
horizontal-coordinates map with `0 < ‖y‖ < 1/8`, and the identification of the
class.-/
structure BridgeData (n : ℕ)
    (z : HomotopyGroup (Fin (n + 1))
      (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)) where
  /-- The underlying generalized loop.-/
  p : Ω^ (Fin (n + 1)) (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)
  /-- The smooth approximation of `p`.-/
  approx : Approximation p
  /-- The regular value of the horizontal-coordinates map.-/
  y : EuclideanSpace ℝ (Fin n)
  norm_y_pos : 0 < ‖y‖
  norm_y_lt : ‖y‖ < 1 / 8
  /-- Every bridge value lies in the same positive coordinate half-space.-/
  axis_pos : ∀ hn : 0 < n, 0 < y ⟨0, hn⟩
  regular_y : IsRegularValue (bridgeHMapE approx) y
  class_eq : z = ⟦approx.representative⟧

namespace BridgeData

variable {z : HomotopyGroup (Fin (n + 1))
    (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)}
  (B : BridgeData n z)

lemma y_ne_zero : B.y ≠ 0 := by
  intro h0
  have := B.norm_y_pos
  rw [h0, norm_zero] at this
  exact lt_irrefl 0 this

lemma norm_y_lt_one : ‖B.y‖ < 1 := B.norm_y_lt.trans (by norm_num)

/-- The framed level set of the bridge data.-/
def fls : FramedLevelSet n := bridgeFLS B.approx B.y B.y_ne_zero B.regular_y

/-- The fiber of the bridge level set: the two-point-preimage dichotomy.-/
theorem fiber_eq :
    B.fls.fiber = {x | nprep B.approx (WithLp.ofLp x) = northPoint B.y
      ∨ nprep B.approx (WithLp.ofLp x) = southPointOf B.y} :=
  bridgeFLS_fiber B.approx B.y B.y_ne_zero B.regular_y

/-- The northern-part criterion on the fiber.-/
theorem mem_north_iff {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∈ B.fls.fiber) :
    nprep B.approx (WithLp.ofLp x) = northPoint B.y
      ↔ 0 < vertC (nprep B.approx (WithLp.ofLp x)) := by
  have hfib : bridgeHMap B.approx (WithLp.ofLp x) = B.y := by
    have : bridgeHMapE B.approx x - B.y = 0 := hx
    exact sub_eq_zero.mp this
  exact nprep_eq_northPoint_iff B.approx B.norm_y_lt_one hfib

end BridgeData

/-- Existence of bridge data for every homotopy class (the forward
Pontryagin–Thom bridge).-/
theorem exists_bridgeData (hn : 0 < n)
    (z : HomotopyGroup (Fin (n + 1))
      (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)) :
    Nonempty (BridgeData n z) := by
  obtain ⟨p, a, hz⟩ := exists_approximation_of_homotopy_class z
  obtain ⟨y, hy0, hy8, hyaxis, hyreg⟩ := exists_bridge_regular_value a hn
  have hyaxis' : ∀ hn' : 0 < n, 0 < y ⟨0, hn'⟩ := by
    intro hn'
    simpa using hyaxis
  exact ⟨⟨p, a, y, hy0, hy8, hyaxis', hyreg, hz⟩⟩

end Submission
