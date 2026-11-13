import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.AmbientNormalizationPrimitive

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Concrete affine ambient isotopies

This file turns the scale-and-translate positioning move into an actual
`SmoothAmbientIsotopy`.  For `c > 0` and translation vector `b`, the endpoint
diffeomorphism is `x ↦ c • x + b`.  The positive scale is interpolated with
the global collar-flat switch, so the forward and inverse families are smooth
on all of `ℝ`, not merely on the geometric interval.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff RealInnerProductSpace

namespace Submission

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

namespace SmoothAmbientIsotopy

/-- The positive scale used by the global affine isotopy.-/
def ambientAffineScale (c s : ℝ) : ℝ :=
  slideScale c (normRamp s)

/--
@isnad1 id=lt.1h2v.s4.68ae4ab6f8dc from=translated src=- shape=d58f95ac vocab=bd7a6805
-/
lemma ambientAffineScale_pos {c : ℝ} (hc : 0 < c) (s : ℝ) :
    0 < ambientAffineScale c s :=
  slideScale_pos hc (normRamp_nonneg s) (normRamp_le_one s)

/--
@isnad1 id=eq.0h1v.s4.a6dfd4980301 from=translated src=- shape=1d838610 vocab=690decf1
-/
@[simp] theorem ambientAffineScale_zero (c : ℝ) :
    ambientAffineScale c 0 = 1 := by
  rw [ambientAffineScale, normRamp_of_le_quarter (by norm_num), slideScale_zero]

/--
@isnad1 id=eq.0h1v.s3.412d04b274e3 from=translated src=- shape=1fa26838 vocab=690decf1
-/
@[simp] theorem ambientAffineScale_one (c : ℝ) :
    ambientAffineScale c 1 = c := by
  rw [ambientAffineScale, normRamp_of_three_quarter_le (by norm_num), slideScale_one]

/-- Forward affine track.-/
def affineForward (c : ℝ) (b : E) (s : ℝ) (x : E) : E :=
  ambientAffineScale c s • x + normRamp s • b

/-- Inverse affine track.-/
def affineInverse (c : ℝ) (b : E) (s : ℝ) (x : E) : E :=
  (ambientAffineScale c s)⁻¹ • (x - normRamp s • b)

/--
@isnad1 id=contdiff.0h3v.s9.b4efdf30b0a4 from=translated src=- shape=2e526301 vocab=866a45b9
-/
theorem contDiff_affineForward (c : ℝ) (b : E) :
    ContDiff ℝ ∞ (fun p : ℝ × E => affineForward c b p.1 p.2) := by
  have hr : ContDiff ℝ ∞ (fun p : ℝ × E => normRamp p.1) :=
    contDiff_normRamp.comp contDiff_fst
  have ha : ContDiff ℝ ∞ (fun p : ℝ × E => ambientAffineScale c p.1) :=
    (contDiff_const.sub hr).add (hr.mul contDiff_const)
  exact (ha.smul contDiff_snd).add (hr.smul contDiff_const)

/--
@isnad1 id=contdiff.1h3v.s9.22295b86330f from=translated src=- shape=9058c73b vocab=7f4dad0e
-/
theorem contDiff_affineInverse (c : ℝ) (hc : 0 < c) (b : E) :
    ContDiff ℝ ∞ (fun p : ℝ × E => affineInverse c b p.1 p.2) := by
  have hr : ContDiff ℝ ∞ (fun p : ℝ × E => normRamp p.1) :=
    contDiff_normRamp.comp contDiff_fst
  have ha : ContDiff ℝ ∞ (fun p : ℝ × E => ambientAffineScale c p.1) :=
    (contDiff_const.sub hr).add (hr.mul contDiff_const)
  have hainv : ContDiff ℝ ∞
      (fun p : ℝ × E => (ambientAffineScale c p.1)⁻¹) :=
    ha.inv fun p => (ambientAffineScale_pos hc p.1).ne'
  exact hainv.smul (contDiff_snd.sub (hr.smul contDiff_const))

/--
@isnad1 id=eq.0h4v.s6.6efea80a6c18 from=translated src=- shape=7ab4c03c vocab=a3a8c22a
-/
@[simp] theorem affineForward_zero (c : ℝ) (b x : E) :
    affineForward c b 0 x = x := by
  simp [affineForward, normRamp_of_le_quarter (show (0 : ℝ) ≤ 1 / 4 by norm_num)]

/--
@isnad1 id=eq.0h4v.s6.7f1e3743fe92 from=translated src=- shape=7ab4c03c vocab=81f02b5b
-/
@[simp] theorem affineInverse_zero (c : ℝ) (b x : E) :
    affineInverse c b 0 x = x := by
  simp [affineInverse, normRamp_of_le_quarter (show (0 : ℝ) ≤ 1 / 4 by norm_num)]

/--
@isnad1 id=eq.0h4v.s8.095cc0426882 from=translated src=- shape=84680e6c vocab=f3236504
-/
@[simp] theorem affineForward_one (c : ℝ) (b x : E) :
    affineForward c b 1 x = c • x + b := by
  simp [affineForward,
    normRamp_of_three_quarter_le (show (3 / 4 : ℝ) ≤ 1 by norm_num)]

/--
@isnad1 id=eq.0h4v.s8.728511c0cc89 from=translated src=- shape=579e1d8c vocab=0e57ae62
-/
@[simp] theorem affineInverse_one (c : ℝ) (b x : E) :
    affineInverse c b 1 x = c⁻¹ • (x - b) := by
  simp [affineInverse,
    normRamp_of_three_quarter_le (show (3 / 4 : ℝ) ≤ 1 by norm_num)]

/-- The global smooth ambient isotopy from the identity to
`x ↦ c • x + b`.-/
def affine (c : ℝ) (hc : 0 < c) (b : E) : SmoothAmbientIsotopy n where
  forward := affineForward c b
  inverse := affineInverse c b
  forward_smooth := contDiff_affineForward c b
  inverse_smooth := contDiff_affineInverse c hc b
  forward_zero := by
    funext x
    exact affineForward_zero c b x
  left_inv := by
    intro s hs x
    change (ambientAffineScale c s)⁻¹ •
      (ambientAffineScale c s • x + normRamp s • b - normRamp s • b) = x
    rw [add_sub_cancel_right, smul_smul,
      inv_mul_cancel₀ (ambientAffineScale_pos hc s).ne', one_smul]
  right_inv := by
    intro s hs x
    change ambientAffineScale c s •
      ((ambientAffineScale c s)⁻¹ • (x - normRamp s • b)) +
        normRamp s • b = x
    rw [smul_smul, mul_inv_cancel₀ (ambientAffineScale_pos hc s).ne', one_smul]
    abel
  inverse_fderiv_surjective := by
    intro s hs x
    let a : ℝ := ambientAffineScale c s
    let w : E := normRamp s • b
    have ha : a ≠ 0 := (ambientAffineScale_pos hc s).ne'
    have hderiv : fderiv ℝ (affineInverse c b s) x =
        a⁻¹ • ContinuousLinearMap.id ℝ E := by
      have hbase : HasFDerivAt (fun y : E => y - w)
          (ContinuousLinearMap.id ℝ E) x :=
        (hasFDerivAt_id x).sub_const w
      have h : HasFDerivAt (fun y : E => a⁻¹ • (y - w))
          (a⁻¹ • ContinuousLinearMap.id ℝ E) x :=
        hbase.const_smul (R := ℝ) a⁻¹
      change fderiv ℝ (fun y : E => a⁻¹ • (y - w)) x = _
      exact h.fderiv
    rw [hderiv]
    intro y
    refine ⟨a • y, ?_⟩
    rw [smul_apply, ContinuousLinearMap.id_apply, smul_smul,
      inv_mul_cancel₀ ha, one_smul]

/--
@isnad1 id=eq.1h5v.s6.e9e896bdbfdf from=translated src=- shape=1fd9ad42 vocab=7c5b0e0b
-/
@[simp] theorem affine_forward (c : ℝ) (hc : 0 < c) (b : E) (s : ℝ) (x : E) :
    (affine c hc b).forward s x = affineForward c b s x :=
  rfl

/--
@isnad1 id=eq.1h5v.s6.b7137110215e from=translated src=- shape=1fd9ad42 vocab=a1bd9dec
-/
@[simp] theorem affine_inverse (c : ℝ) (hc : 0 < c) (b : E) (s : ℝ) (x : E) :
    (affine c hc b).inverse s x = affineInverse c b s x :=
  rfl

/--
@isnad1 id=eq.1h4v.s8.e73bb2e76648 from=translated src=- shape=6fc7b380 vocab=b0937d9f
-/
@[simp] theorem affine_forward_endpoint (c : ℝ) (hc : 0 < c) (b x : E) :
    (affine c hc b).forward 1 x = c • x + b :=
  affineForward_one c b x

/--
@isnad1 id=eq.1h4v.s8.99e319fec6e9 from=translated src=- shape=e9905bd1 vocab=6a5152c9
-/
@[simp] theorem affine_inverse_endpoint (c : ℝ) (hc : 0 < c) (b x : E) :
    (affine c hc b).inverse 1 x = c⁻¹ • (x - b) :=
  affineInverse_one c b x

/-- Translation as a concrete ambient isotopy.-/
def translation (b : E) : SmoothAmbientIsotopy n :=
  affine 1 zero_lt_one b

/--
@isnad1 id=eq.0h3v.s8.ac81f21f2ad2 from=translated src=- shape=e5bf0dc1 vocab=7a347798
-/
@[simp] theorem translation_forward_endpoint (b x : E) :
    (translation b).forward 1 x = x + b := by
  simp [translation]

/--
@isnad1 id=eq.0h3v.s8.cd911c5d7136 from=translated src=- shape=cdc78759 vocab=5b72cbc1
-/
@[simp] theorem translation_inverse_endpoint (b x : E) :
    (translation b).inverse 1 x = x - b := by
  simp [translation]

/-- Positive dilation as a concrete ambient isotopy.-/
def positiveDilation (c : ℝ) (hc : 0 < c) : SmoothAmbientIsotopy n :=
  affine c hc 0

/--
@isnad1 id=eq.1h3v.s7.138aeb864639 from=translated src=- shape=78112955 vocab=b6e60d92
-/
@[simp] theorem positiveDilation_forward_endpoint
    (c : ℝ) (hc : 0 < c) (x : E) :
    (positiveDilation c hc).forward 1 x = c • x := by
  simp [positiveDilation]

/--
@isnad1 id=eq.1h3v.s7.8e63b74370dd from=translated src=- shape=37ca9879 vocab=6e594205
-/
@[simp] theorem positiveDilation_inverse_endpoint
    (c : ℝ) (hc : 0 < c) (x : E) :
    (positiveDilation c hc).inverse 1 x = c⁻¹ • x := by
  simp [positiveDilation]

end SmoothAmbientIsotopy

end Submission
