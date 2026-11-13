import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SignedCobordismCategory

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Elementary normalization moves as signed cobordisms

Two generic move realizations used by the normalization of signed framed
level sets (`SignedDeltaNormalizationData.normalize`):

* `DefiningMapHomotopy`: a smooth one-parameter family of defining maps with a
  **common regular zero fiber** yields a signed framed level cobordism whose
  underlying manifold never moves.  This is the level-set formulation of a
  homotopy of framings — in particular every frame rotation produced by the
  `π₁(SO(n+1))` normalization step enters the cobordism calculus through this
  single lemma.

* `signInterpolationCobordism`: two sign labels with the same sign pattern on
  a common fiber are connected by a signed cylinder.  Hence only the pattern
  of the label on the fiber matters, never the labelling function itself.

Both constructions run along one collar-flat switch `normRamp`, so all collar
obligations are literal.
-/

noncomputable section

open Set Function Metric
open scoped Topology ContDiff

namespace Submission

variable {n : ℕ}

/-! ## The collar-flat switch -/

/-- Collar-flat switch: `0` through `1/4`, `1` from `3/4` on, valued in
`[0, 1]`.-/
def normRamp (t : ℝ) : ℝ :=
  Real.smoothTransition (2 * (t - 1 / 4))

lemma contDiff_normRamp : ContDiff ℝ ∞ normRamp :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const))

lemma normRamp_of_le_quarter {t : ℝ} (ht : t ≤ 1 / 4) : normRamp t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma normRamp_of_three_quarter_le {t : ℝ} (ht : 3 / 4 ≤ t) : normRamp t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma normRamp_nonneg (t : ℝ) : 0 ≤ normRamp t :=
  Real.smoothTransition.nonneg _

lemma normRamp_le_one (t : ℝ) : normRamp t ≤ 1 :=
  Real.smoothTransition.le_one _

/-! ## Transporting a label to a presentation with smaller fiber -/

namespace FiberSign

/-- A sign label restricts to any presentation whose fiber is contained in the
original one; the labelling function is unchanged.-/
def restrict {X Y : FramedLevelSet n} (S : FiberSign X)
    (h : Y.fiber ⊆ X.fiber) : FiberSign Y where
  toFun := S.toFun
  continuous := S.continuous
  nonzero x hx := S.nonzero x (h hx)

@[simp] theorem restrict_apply {X Y : FramedLevelSet n} (S : FiberSign X)
    (h : Y.fiber ⊆ X.fiber) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    S.restrict h x = S x :=
  rfl

end FiberSign

/-! ## Homotopies of defining maps -/

/-- A smooth one-parameter family of defining maps sharing one regular zero
fiber over the whole parameter interval.  This is a homotopy of framings: the
framed one-manifold never moves, only its defining equations (hence its
normal frame) do.-/
structure DefiningMapHomotopy (X₀ X₁ : FramedLevelSet n) where
  /-- The family of defining maps.-/
  H : ℝ → EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n)
  /-- Joint smoothness in the parameter and the point.-/
  smooth : ContDiff ℝ ∞
    fun p : ℝ × EuclideanSpace ℝ (Fin (n + 1)) => H p.1 p.2
  /-- The family starts at the source presentation.-/
  H_zero : H 0 = X₀.g
  /-- The family ends at the target presentation.-/
  H_one : H 1 = X₁.g
  /-- The zero set is the source fiber throughout the parameter interval.-/
  fiber_eq : ∀ s, 0 ≤ s → s ≤ 1 →
    {x | H s x = 0} = X₀.fiber
  /-- Every family member is regular on the common fiber.-/
  regular : ∀ s, 0 ≤ s → s ≤ 1 → ∀ x ∈ X₀.fiber,
    Function.Surjective (fderiv ℝ (H s) x)

namespace DefiningMapHomotopy

variable {X₀ X₁ : FramedLevelSet n}

/-- The target fiber coincides with the source fiber.-/
theorem fiber_subset (D : DefiningMapHomotopy X₀ X₁) :
    X₁.fiber ⊆ X₀.fiber := by
  intro x hx
  have hmem : x ∈ {x | D.H 1 x = 0} := by
    show D.H 1 x = 0
    rw [D.H_one]
    exact hx
  rwa [D.fiber_eq 1 zero_le_one le_rfl] at hmem

variable (D : DefiningMapHomotopy X₀ X₁)

/-- The space-time map of the homotopy, run along the collar-flat switch.-/
def cobMap (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  D.H (normRamp (vertC v)) (initCLM (n + 1) v)

lemma cobMap_spaceTime (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    D.cobMap (spaceTime x t) = D.H (normRamp t) x := by
  rw [cobMap, initCLM_spaceTime, vertC_spaceTime]

lemma contDiff_cobMap : ContDiff ℝ ∞ D.cobMap := by
  have hpair : ContDiff ℝ ∞
      fun v : EuclideanSpace ℝ (Fin (n + 1 + 1)) =>
        (normRamp (vertC v), initCLM (n + 1) v) :=
    (contDiff_normRamp.comp contDiff_vertC).prodMk (initCLM (n + 1)).contDiff
  exact D.smooth.comp hpair

/-- Any zero of the switched family lies spatially on the common fiber.-/
lemma mem_fiber_of_cobMap_eq_zero {v : EuclideanSpace ℝ (Fin (n + 1 + 1))}
    (hv : D.cobMap v = 0) : initCLM (n + 1) v ∈ X₀.fiber := by
  have hmem : initCLM (n + 1) v ∈ {x | D.H (normRamp (vertC v)) x = 0} := hv
  rwa [D.fiber_eq _ (normRamp_nonneg _) (normRamp_le_one _)] at hmem

lemma cobMap_spatial_bounded :
    ∃ R, ∀ v, D.cobMap v = 0 → ‖initCLM (n + 1) v‖ ≤ R := by
  obtain ⟨R, hR⟩ := X₀.fiber_bounded.subset_closedBall 0
  refine ⟨R, fun v hv => ?_⟩
  have := hR (D.mem_fiber_of_cobMap_eq_zero hv)
  rwa [mem_closedBall, dist_zero_right] at this

/-- The switched family is regular on its zero surface: the spatial derivative
of the current family member is already surjective.-/
theorem cobMap_regular :
    ∀ v, D.cobMap v = 0 → Function.Surjective (fderiv ℝ D.cobMap v) := by
  intro v hv y
  have hxfib : initCLM (n + 1) v ∈ X₀.fiber :=
    D.mem_fiber_of_cobMap_eq_zero hv
  obtain ⟨h₀, hh₀⟩ :=
    D.regular (normRamp (vertC v)) (normRamp_nonneg _) (normRamp_le_one _)
      (initCLM (n + 1) v) hxfib y
  refine ⟨embedCLM (n + 1) h₀, ?_⟩
  -- Chain rule along the fixed-time slice embedding `x' ↦ spaceTime x' (vertC v)`.
  have hGd : HasFDerivAt D.cobMap (fderiv ℝ D.cobMap v)
      (spaceTime (initCLM (n + 1) v) (vertC v)) := by
    rw [spaceTime_init_vert]
    exact (D.contDiff_cobMap.differentiable infty_ne_zero v).hasFDerivAt
  have hA : HasFDerivAt
      (fun x' : EuclideanSpace ℝ (Fin (n + 1)) => spaceTime x' (vertC v))
      (embedCLM (n + 1)) (initCLM (n + 1) v) :=
    hasFDerivAt_spaceTime _ _
  have hcomp := hGd.comp (initCLM (n + 1) v) hA
  have hfun : (D.cobMap ∘
      fun x' : EuclideanSpace ℝ (Fin (n + 1)) => spaceTime x' (vertC v)) =
      D.H (normRamp (vertC v)) := by
    funext x'
    show D.cobMap (spaceTime x' (vertC v)) = _
    rw [cobMap_spaceTime]
  rw [hfun] at hcomp
  have hslice : fderiv ℝ (D.H (normRamp (vertC v))) (initCLM (n + 1) v) =
      (fderiv ℝ D.cobMap v).comp (embedCLM (n + 1)) :=
    hcomp.fderiv
  rw [hslice] at hh₀
  simpa [ContinuousLinearMap.comp_apply] using hh₀

/-- The framed level cobordism realizing a homotopy of defining maps.-/
def toCobordism : FramedLevelCobordism n where
  X₀ := X₀
  X₁ := X₁
  G := D.cobMap
  smooth := D.contDiff_cobMap
  spatial_bounded := D.cobMap_spatial_bounded
  regular := D.cobMap_regular
  collar_zero := fun x t ht => by
    rw [cobMap_spaceTime, normRamp_of_le_quarter ht, D.H_zero]
  collar_one := fun x t ht => by
    rw [cobMap_spaceTime, normRamp_of_three_quarter_le ht, D.H_one]

/-- The signed cobordism carrying a source label across a homotopy of defining
maps: the label is transported unchanged since the fiber never moves.-/
def signedCobordism (S : FiberSign X₀) :
    SignedFramedLevelCobordism S (S.restrict D.fiber_subset) where
  cobordism := D.toCobordism
  source_eq := rfl
  target_eq := rfl
  toFun v := S (initCLM (n + 1) v)
  continuous := S.continuous.comp (initCLM (n + 1)).continuous
  nonzero := fun v hv => S.nonzero _ (D.mem_fiber_of_cobMap_eq_zero hv)
  collar_zero := fun x t _ => by rw [initCLM_spaceTime]
  collar_one := fun x t _ => by
    rw [initCLM_spaceTime]
    rfl

theorem nonempty_signedCobordism (S : FiberSign X₀) :
    Nonempty (SignedFramedLevelCobordism S (S.restrict D.fiber_subset)) :=
  ⟨D.signedCobordism S⟩

end DefiningMapHomotopy

/-! ## Sign interpolation over a fixed presentation -/

section SignInterpolation

variable {X : FramedLevelSet n}

/-- Two labels with the same sign pattern on the fiber are connected by a
signed cylinder over the identity cobordism: the label is interpolated along
the collar-flat switch and never vanishes on the (product) fiber.-/
def signInterpolationCobordism (S T : FiberSign X)
    (h : ∀ x ∈ X.fiber, (0 < S x ↔ 0 < T x)) :
    SignedFramedLevelCobordism S T where
  cobordism := FramedLevelCobordism.refl X
  source_eq := rfl
  target_eq := rfl
  toFun v := (1 - normRamp (vertC v)) * S (initCLM (n + 1) v) +
    normRamp (vertC v) * T (initCLM (n + 1) v)
  continuous := by
    have hr : Continuous fun v : EuclideanSpace ℝ (Fin (n + 1 + 1)) =>
        normRamp (vertC v) :=
      contDiff_normRamp.continuous.comp contDiff_vertC.continuous
    exact ((continuous_const.sub hr).mul
        (S.continuous.comp (initCLM (n + 1)).continuous)).add
      (hr.mul (T.continuous.comp (initCLM (n + 1)).continuous))
  nonzero := by
    intro v hv
    have hmem : initCLM (n + 1) v ∈ X.fiber := hv
    have hr0 : 0 ≤ normRamp (vertC v) := normRamp_nonneg _
    have hr1 : normRamp (vertC v) ≤ 1 := normRamp_le_one _
    have hS0 : S (initCLM (n + 1) v) ≠ 0 := S.nonzero _ hmem
    have hT0 : T (initCLM (n + 1) v) ≠ 0 := T.nonzero _ hmem
    rcases Ne.lt_or_gt hS0 with hSneg | hSpos
    · -- both labels negative on this fiber point
      have hTneg : T (initCLM (n + 1) v) < 0 := by
        rcases Ne.lt_or_gt hT0 with h' | h'
        · exact h'
        · exact absurd ((h _ hmem).mpr h') (not_lt.mpr hSneg.le)
      have h1 : (1 - normRamp (vertC v)) * S (initCLM (n + 1) v) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hSneg.le
      have h2 : normRamp (vertC v) * T (initCLM (n + 1) v) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hr0 hTneg.le
      rcases le_total (normRamp (vertC v)) (1 / 2) with hr | hr
      · have hstrict : (1 - normRamp (vertC v)) * S (initCLM (n + 1) v) < 0 :=
          mul_neg_of_pos_of_neg (by linarith) hSneg
        exact ne_of_lt (by linarith)
      · have hstrict : normRamp (vertC v) * T (initCLM (n + 1) v) < 0 :=
          mul_neg_of_pos_of_neg (by linarith) hTneg
        exact ne_of_lt (by linarith)
    · -- both labels positive on this fiber point
      have hTpos : 0 < T (initCLM (n + 1) v) := (h _ hmem).mp hSpos
      have h1 : 0 ≤ (1 - normRamp (vertC v)) * S (initCLM (n + 1) v) :=
        mul_nonneg (by linarith) hSpos.le
      have h2 : 0 ≤ normRamp (vertC v) * T (initCLM (n + 1) v) :=
        mul_nonneg hr0 hTpos.le
      rcases le_total (normRamp (vertC v)) (1 / 2) with hr | hr
      · have hstrict : 0 < (1 - normRamp (vertC v)) * S (initCLM (n + 1) v) :=
          mul_pos (by linarith) hSpos
        exact ne_of_gt (by linarith)
      · have hstrict : 0 < normRamp (vertC v) * T (initCLM (n + 1) v) :=
          mul_pos (by linarith) hTpos
        exact ne_of_gt (by linarith)
  collar_zero := fun x t ht => by
    rw [initCLM_spaceTime, vertC_spaceTime, normRamp_of_le_quarter ht]
    ring
  collar_one := fun x t ht => by
    rw [initCLM_spaceTime, vertC_spaceTime, normRamp_of_three_quarter_le ht]
    ring

/-- Only the sign pattern of a label on the fiber matters for the signed
cobordism relation.-/
theorem nonempty_signedCobordism_of_sign_pattern (S T : FiberSign X)
    (h : ∀ x ∈ X.fiber, (0 < S x ↔ 0 < T x)) :
    Nonempty (SignedFramedLevelCobordism S T) :=
  ⟨signInterpolationCobordism S T h⟩

end SignInterpolation

/-! ## Slice regularity transfer -/

/-- If the fixed-time slice through a zero has surjective spatial derivative,
then the space-time map has surjective derivative there.-/
lemma surjective_fderiv_of_slice
    {G : EuclideanSpace ℝ (Fin (n + 1 + 1)) → EuclideanSpace ℝ (Fin n)}
    (hG : ContDiff ℝ ∞ G) {v : EuclideanSpace ℝ (Fin (n + 1 + 1))}
    (hslice : Function.Surjective
      (fderiv ℝ (fun x' => G (spaceTime x' (vertC v))) (initCLM (n + 1) v))) :
    Function.Surjective (fderiv ℝ G v) := by
  intro y
  obtain ⟨h₀, hh₀⟩ := hslice y
  refine ⟨embedCLM (n + 1) h₀, ?_⟩
  have hGd : HasFDerivAt G (fderiv ℝ G v)
      (spaceTime (initCLM (n + 1) v) (vertC v)) := by
    rw [spaceTime_init_vert]
    exact (hG.differentiable infty_ne_zero v).hasFDerivAt
  have hA : HasFDerivAt
      (fun x' : EuclideanSpace ℝ (Fin (n + 1)) => spaceTime x' (vertC v))
      (embedCLM (n + 1)) (initCLM (n + 1) v) := hasFDerivAt_spaceTime _ _
  have hcomp : HasFDerivAt (fun x' => G (spaceTime x' (vertC v)))
      ((fderiv ℝ G v).comp (embedCLM (n + 1))) (initCLM (n + 1) v) :=
    hGd.comp (initCLM (n + 1) v) hA
  rw [hcomp.fderiv] at hh₀
  simpa [ContinuousLinearMap.comp_apply] using hh₀

/-! ## Affine slides

Translating and rescaling a whole presentation is a signed cobordism.  The
move `x ↦ c • x + b` (with `c > 0`) is realized by pulling the defining map
back through the collar-flat interpolated inverse.  This is the spatial
positioning tool of the normalization: it separates circles before
juxtaposition and shrinks them into standard charts. -/

/-- The interpolated scale `(1 - r) + r·c`, positive on `[0, 1]` for `c > 0`.-/
def slideScale (c r : ℝ) : ℝ := 1 - r + r * c

@[simp] lemma slideScale_zero (c : ℝ) : slideScale c 0 = 1 := by
  unfold slideScale
  ring

@[simp] lemma slideScale_one (c : ℝ) : slideScale c 1 = c := by
  unfold slideScale
  ring

lemma slideScale_pos {c : ℝ} (hc : 0 < c) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    0 < slideScale c r := by
  unfold slideScale
  by_cases hr : r = 1
  · subst hr
    simpa using hc
  · have hrlt : r < 1 := lt_of_le_of_ne h1 hr
    exact lt_of_lt_of_le (sub_pos.mpr hrlt)
      (le_add_of_nonneg_right (mul_nonneg h0 hc.le))

lemma slideScale_le_max {c : ℝ} (hc : 0 < c) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    slideScale c r ≤ max 1 c := by
  unfold slideScale
  nlinarith [le_max_left (1 : ℝ) c, le_max_right (1 : ℝ) c]

/-- The affine track of the slide: at switch value `r` the point is pulled
back through `x ↦ ((1 - r) + r·c)⁻¹ • (x - r • b)`.-/
def slideTrack (c : ℝ) (b : EuclideanSpace ℝ (Fin (n + 1)))
    (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (slideScale c (normRamp (vertC v)))⁻¹ •
    (initCLM (n + 1) v - normRamp (vertC v) • b)

lemma slideTrack_spaceTime (c : ℝ) (b x : EuclideanSpace ℝ (Fin (n + 1)))
    (t : ℝ) :
    slideTrack c b (spaceTime x t) =
      (slideScale c (normRamp t))⁻¹ • (x - normRamp t • b) := by
  rw [slideTrack, initCLM_spaceTime, vertC_spaceTime]

lemma slideTrack_of_le_quarter (c : ℝ) (b x : EuclideanSpace ℝ (Fin (n + 1)))
    {t : ℝ} (ht : t ≤ 1 / 4) : slideTrack c b (spaceTime x t) = x := by
  rw [slideTrack_spaceTime, normRamp_of_le_quarter ht, slideScale_zero]
  simp

lemma slideTrack_of_three_quarter_le (c : ℝ)
    (b x : EuclideanSpace ℝ (Fin (n + 1))) {t : ℝ} (ht : 3 / 4 ≤ t) :
    slideTrack c b (spaceTime x t) = c⁻¹ • (x - b) := by
  rw [slideTrack_spaceTime, normRamp_of_three_quarter_le ht, slideScale_one,
    one_smul]

lemma contDiff_slideTrack (c : ℝ) (hc : 0 < c)
    (b : EuclideanSpace ℝ (Fin (n + 1))) :
    ContDiff ℝ ∞ (slideTrack c b (n := n)) := by
  have hr : ContDiff ℝ ∞
      fun v : EuclideanSpace ℝ (Fin (n + 1 + 1)) => normRamp (vertC v) :=
    contDiff_normRamp.comp contDiff_vertC
  have hscale : ContDiff ℝ ∞
      fun v : EuclideanSpace ℝ (Fin (n + 1 + 1)) =>
        slideScale c (normRamp (vertC v)) :=
    (contDiff_const.sub hr).add (hr.mul contDiff_const)
  have hinv : ContDiff ℝ ∞
      fun v : EuclideanSpace ℝ (Fin (n + 1 + 1)) =>
        (slideScale c (normRamp (vertC v)))⁻¹ :=
    hscale.inv fun v =>
      (slideScale_pos hc (normRamp_nonneg _) (normRamp_le_one _)).ne'
  have hvec : ContDiff ℝ ∞
      fun v : EuclideanSpace ℝ (Fin (n + 1 + 1)) =>
        initCLM (n + 1) v - normRamp (vertC v) • b :=
    (initCLM (n + 1)).contDiff.sub (hr.smul contDiff_const)
  exact hinv.smul hvec

/-- A defining map is regular along any invertible scale-and-translate
pullback of its fiber.-/
lemma FramedLevelSet.surjective_fderiv_affine (X : FramedLevelSet n) {a : ℝ}
    (ha : a ≠ 0) (w : EuclideanSpace ℝ (Fin (n + 1)))
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : X.g (a⁻¹ • (x - w)) = 0) :
    Function.Surjective (fderiv ℝ (fun x' => X.g (a⁻¹ • (x' - w))) x) := by
  have hA : HasFDerivAt
      (fun x' : EuclideanSpace ℝ (Fin (n + 1)) => a⁻¹ • (x' - w))
      (a⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1)))) x :=
    ((hasFDerivAt_id x).sub_const w).const_smul a⁻¹
  have hg : HasFDerivAt X.g (fderiv ℝ X.g (a⁻¹ • (x - w))) (a⁻¹ • (x - w)) :=
    (X.smooth.differentiable infty_ne_zero _).hasFDerivAt
  have hcomp : HasFDerivAt (fun x' => X.g (a⁻¹ • (x' - w)))
      ((fderiv ℝ X.g (a⁻¹ • (x - w))).comp
        (a⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))))) x :=
    hg.comp x hA
  rw [hcomp.fderiv, ContinuousLinearMap.coe_comp]
  apply (X.regular _ hx).comp
  intro y
  refine ⟨a • y, ?_⟩
  rw [smul_apply, ContinuousLinearMap.id_apply, smul_smul,
    inv_mul_cancel₀ ha, one_smul]

/-- The scale-and-translate pullback presentation: its fiber is the image of
the original fiber under `x ↦ c • x + b`.-/
def FramedLevelSet.affinePullback (X : FramedLevelSet n) (c : ℝ) (hc : c ≠ 0)
    (b : EuclideanSpace ℝ (Fin (n + 1))) : FramedLevelSet n where
  g x := X.g (c⁻¹ • (x - b))
  smooth := X.smooth.comp ((contDiff_id.sub contDiff_const).const_smul c⁻¹)
  fiber_bounded := by
    obtain ⟨R, hR⟩ := X.fiber_bounded.subset_closedBall 0
    apply (Metric.isBounded_closedBall
      (x := (0 : EuclideanSpace ℝ (Fin (n + 1)))) (r := |c| * R + ‖b‖)).subset
    intro x hx
    have hz : c⁻¹ • (x - b) ∈ X.fiber := hx
    have hzR : ‖c⁻¹ • (x - b)‖ ≤ R := by
      have := hR hz
      rwa [mem_closedBall, dist_zero_right] at this
    have hxeq : x = c • (c⁻¹ • (x - b)) + b := by
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
      abel
    rw [mem_closedBall, dist_zero_right, hxeq]
    calc ‖c • (c⁻¹ • (x - b)) + b‖
        ≤ ‖c • (c⁻¹ • (x - b))‖ + ‖b‖ := norm_add_le _ _
      _ = |c| * ‖c⁻¹ • (x - b)‖ + ‖b‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |c| * R + ‖b‖ := by
          have habs : (0 : ℝ) ≤ |c| := abs_nonneg c
          have := mul_le_mul_of_nonneg_left hzR habs
          linarith
  regular := fun x hx => X.surjective_fderiv_affine hc _ hx

/-- The pullback fiber is the affine image of the original fiber.-/
theorem FramedLevelSet.affinePullback_fiber (X : FramedLevelSet n) (c : ℝ)
    (hc : c ≠ 0) (b : EuclideanSpace ℝ (Fin (n + 1))) :
    (X.affinePullback c hc b).fiber = (fun z => c • z + b) '' X.fiber := by
  ext x
  constructor
  · intro hx
    refine ⟨c⁻¹ • (x - b), hx, ?_⟩
    change c • (c⁻¹ • (x - b)) + b = x
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    abel
  · rintro ⟨z, hz, rfl⟩
    show X.g (c⁻¹ • (c • z + b - b)) = 0
    rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hc, one_smul]
    exact hz

/-- The transported sign label on an affine pullback.-/
def FiberSign.affinePullback {X : FramedLevelSet n} (S : FiberSign X) (c : ℝ)
    (hc : c ≠ 0) (b : EuclideanSpace ℝ (Fin (n + 1))) :
    FiberSign (X.affinePullback c hc b) where
  toFun x := S (c⁻¹ • (x - b))
  continuous := S.continuous.comp
    ((continuous_id.sub continuous_const).const_smul c⁻¹)
  nonzero x hx := S.nonzero _ hx

/-- The framed level cobordism sliding a presentation onto its affine
pullback.-/
def slideCobordism (X : FramedLevelSet n) (c : ℝ) (hc : 0 < c)
    (b : EuclideanSpace ℝ (Fin (n + 1))) : FramedLevelCobordism n where
  X₀ := X
  X₁ := X.affinePullback c hc.ne' b
  G := fun v => X.g (slideTrack c b v)
  smooth := X.smooth.comp (contDiff_slideTrack c hc b)
  spatial_bounded := by
    obtain ⟨R, hR⟩ := X.fiber_bounded.subset_closedBall 0
    refine ⟨max 1 c * R + ‖b‖, fun v hv => ?_⟩
    have hz : slideTrack c b v ∈ X.fiber := hv
    have hzR : ‖slideTrack c b v‖ ≤ R := by
      have := hR hz
      rwa [mem_closedBall, dist_zero_right] at this
    have h0 := normRamp_nonneg (vertC v)
    have h1 := normRamp_le_one (vertC v)
    have hapos := slideScale_pos hc h0 h1
    have hxeq : initCLM (n + 1) v =
        slideScale c (normRamp (vertC v)) • slideTrack c b v +
          normRamp (vertC v) • b := by
      rw [slideTrack, smul_smul, mul_inv_cancel₀ hapos.ne', one_smul]
      abel
    rw [hxeq]
    have hnorm1 : ‖slideScale c (normRamp (vertC v)) • slideTrack c b v‖ ≤
        max 1 c * R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hapos]
      have hmax := slideScale_le_max hc h0 h1
      have hR0 : (0 : ℝ) ≤ R := le_trans (norm_nonneg _) hzR
      nlinarith [norm_nonneg (slideTrack c b v)]
    have hnorm2 : ‖normRamp (vertC v) • b‖ ≤ ‖b‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
      nlinarith [norm_nonneg b]
    calc ‖slideScale c (normRamp (vertC v)) • slideTrack c b v +
          normRamp (vertC v) • b‖
        ≤ ‖slideScale c (normRamp (vertC v)) • slideTrack c b v‖ +
            ‖normRamp (vertC v) • b‖ := norm_add_le _ _
      _ ≤ max 1 c * R + ‖b‖ := add_le_add hnorm1 hnorm2
  regular := by
    intro v hv
    apply surjective_fderiv_of_slice (X.smooth.comp (contDiff_slideTrack c hc b))
    show Function.Surjective
      (fderiv ℝ (fun x' => X.g (slideTrack c b (spaceTime x' (vertC v))))
        (initCLM (n + 1) v))
    have hfun : (fun x' => X.g (slideTrack c b (spaceTime x' (vertC v)))) =
        fun x' => X.g ((slideScale c (normRamp (vertC v)))⁻¹ •
          (x' - normRamp (vertC v) • b)) := by
      funext x'
      rw [slideTrack_spaceTime]
    rw [hfun]
    exact X.surjective_fderiv_affine
      (slideScale_pos hc (normRamp_nonneg _) (normRamp_le_one _)).ne' _ hv
  collar_zero := fun x t ht => by
    show X.g (slideTrack c b (spaceTime x t)) = X.g x
    rw [slideTrack_of_le_quarter c b x ht]
  collar_one := fun x t ht => by
    show X.g (slideTrack c b (spaceTime x t)) = X.g (c⁻¹ • (x - b))
    rw [slideTrack_of_three_quarter_le c b x ht]

/-- The signed slide: a label rides along the affine track.-/
def signedSlideCobordism {X : FramedLevelSet n} (S : FiberSign X) (c : ℝ)
    (hc : 0 < c) (b : EuclideanSpace ℝ (Fin (n + 1))) :
    SignedFramedLevelCobordism S (S.affinePullback c hc.ne' b) where
  cobordism := slideCobordism X c hc b
  source_eq := rfl
  target_eq := rfl
  toFun v := S (slideTrack c b v)
  continuous := S.continuous.comp (contDiff_slideTrack c hc b).continuous
  nonzero := fun v hv => S.nonzero _ hv
  collar_zero := fun x t ht => by
    show S (slideTrack c b (spaceTime x t)) = S x
    rw [slideTrack_of_le_quarter c b x ht]
  collar_one := fun x t ht => by
    show S (slideTrack c b (spaceTime x t)) = S.affinePullback c hc.ne' b x
    rw [slideTrack_of_three_quarter_le c b x ht]
    change S (c⁻¹ • (x - b)) = S (c⁻¹ • (x - b))
    rfl

/-- Every scale-and-translate repositioning is realized by a signed
cobordism.-/
theorem nonempty_signedSlideCobordism {X : FramedLevelSet n} (S : FiberSign X)
    (c : ℝ) (hc : 0 < c) (b : EuclideanSpace ℝ (Fin (n + 1))) :
    Nonempty (SignedFramedLevelCobordism S (S.affinePullback c hc.ne' b)) :=
  ⟨signedSlideCobordism S c hc b⟩

end Submission
