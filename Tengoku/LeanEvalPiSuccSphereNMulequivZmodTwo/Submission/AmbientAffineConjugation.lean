import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.AmbientLocalizedRotation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Affine conjugation of ambient isotopies

The explicit local rotation is initially centered at the origin.  Conjugating
an ambient isotopy by a fixed affine diffeomorphism moves its support to an
arbitrary translated linear chart.  This is the positioning operation needed
to apply local normalization moves independently in disjoint neighborhoods.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Topology ContDiff RealInnerProductSpace

namespace Submission
namespace SmoothAmbientIsotopy

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- Forward map obtained by conjugating an ambient move by `x ↦ b + L x`.-/
def affineConjugateForward (A : SmoothAmbientIsotopy n) (L : E ≃L[ℝ] E)
    (b : E) (s : ℝ) (x : E) : E :=
  b + L (A.forward s (L.symm (x - b)))

/-- Inverse map of the affine conjugate.-/
def affineConjugateInverse (A : SmoothAmbientIsotopy n) (L : E ≃L[ℝ] E)
    (b : E) (s : ℝ) (x : E) : E :=
  b + L (A.inverse s (L.symm (x - b)))

/--
@isnad1 id=contdiff.0h4v.s10.28bcd4eebf14 from=translated src=- shape=d290d53e vocab=a773909c
-/
theorem contDiff_affineConjugateForward (A : SmoothAmbientIsotopy n)
    (L : E ≃L[ℝ] E) (b : E) :
    ContDiff ℝ ∞
      (fun p : ℝ × E => affineConjugateForward A L b p.1 p.2) := by
  have hinner : ContDiff ℝ ∞ (fun p : ℝ × E => L.symm (p.2 - b)) :=
    L.symm.contDiff.comp (contDiff_snd.sub contDiff_const)
  have hmove : ContDiff ℝ ∞
      (fun p : ℝ × E => A.forward p.1 (L.symm (p.2 - b))) :=
    A.forward_smooth.comp (contDiff_fst.prodMk hinner)
  exact contDiff_const.add (L.contDiff.comp hmove)

/--
@isnad1 id=contdiff.0h4v.s10.7d44183778ff from=translated src=- shape=d290d53e vocab=6d092227
-/
theorem contDiff_affineConjugateInverse (A : SmoothAmbientIsotopy n)
    (L : E ≃L[ℝ] E) (b : E) :
    ContDiff ℝ ∞
      (fun p : ℝ × E => affineConjugateInverse A L b p.1 p.2) := by
  have hinner : ContDiff ℝ ∞ (fun p : ℝ × E => L.symm (p.2 - b)) :=
    L.symm.contDiff.comp (contDiff_snd.sub contDiff_const)
  have hmove : ContDiff ℝ ∞
      (fun p : ℝ × E => A.inverse p.1 (L.symm (p.2 - b))) :=
    A.inverse_smooth.comp (contDiff_fst.prodMk hinner)
  exact contDiff_const.add (L.contDiff.comp hmove)

/--
@isnad1 id=leftinve.1h5v.s9.74bc9c2c8785 from=translated src=- shape=93c724c1 vocab=e394683b
-/
theorem affineConjugate_leftInverse (A : SmoothAmbientIsotopy n)
    (L : E ≃L[ℝ] E) (b : E) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    LeftInverse (affineConjugateInverse A L b s)
      (affineConjugateForward A L b s) := by
  intro x
  change b + L (A.inverse s
    (L.symm (b + L (A.forward s (L.symm (x - b))) - b))) = x
  rw [add_sub_cancel_left, L.symm_apply_apply, A.left_inv s hs,
    L.apply_symm_apply]
  abel

/--
@isnad1 id=rightinv.1h5v.s9.17fe2a9e42a9 from=translated src=- shape=93c724c1 vocab=0be329c1
-/
theorem affineConjugate_rightInverse (A : SmoothAmbientIsotopy n)
    (L : E ≃L[ℝ] E) (b : E) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    RightInverse (affineConjugateInverse A L b s)
      (affineConjugateForward A L b s) := by
  intro x
  change b + L (A.forward s
    (L.symm (b + L (A.inverse s (L.symm (x - b))) - b))) = x
  rw [add_sub_cancel_left, L.symm_apply_apply, A.right_inv s hs,
    L.apply_symm_apply]
  abel

/-- Conjugation by an arbitrary continuous linear equivalence and translation
preserves the full smooth ambient-isotopy structure.-/
def conjugateAffine (A : SmoothAmbientIsotopy n) (L : E ≃L[ℝ] E) (b : E) :
    SmoothAmbientIsotopy n where
  forward := affineConjugateForward A L b
  inverse := affineConjugateInverse A L b
  forward_smooth := contDiff_affineConjugateForward A L b
  inverse_smooth := contDiff_affineConjugateInverse A L b
  forward_zero := by
    funext x
    simp [affineConjugateForward, A.forward_zero]
  left_inv := affineConjugate_leftInverse A L b
  right_inv := affineConjugate_rightInverse A L b
  inverse_fderiv_surjective := by
    intro s hs x
    let f : E → E := affineConjugateForward A L b s
    let g : E → E := affineConjugateInverse A L b s
    have hf : ContDiff ℝ ∞ f := by
      exact (contDiff_affineConjugateForward A L b).comp
        (contDiff_const.prodMk contDiff_id)
    have hg : ContDiff ℝ ∞ g := by
      exact (contDiff_affineConjugateInverse A L b).comp
        (contDiff_const.prodMk contDiff_id)
    let y : E := g x
    have hfy : f y = x := affineConjugate_rightInverse A L b s hs x
    have hgf : (fun z => g (f z)) = id := by
      funext z
      exact affineConjugate_leftInverse A L b s hs z
    have hcomp : HasFDerivAt (fun z => g (f z))
        ((fderiv ℝ g (f y)).comp (fderiv ℝ f y)) y :=
      ((hg.differentiable (by simp) (f y)).hasFDerivAt.comp y
        (hf.differentiable (by simp) y).hasFDerivAt)
    rw [hgf] at hcomp
    have hderiv0 : (fderiv ℝ g (f y)).comp (fderiv ℝ f y) =
        ContinuousLinearMap.id ℝ E :=
      hcomp.fderiv.symm.trans (hasFDerivAt_id y).fderiv
    have hderiv : (fderiv ℝ g x).comp (fderiv ℝ f y) =
        ContinuousLinearMap.id ℝ E := by
      rwa [hfy] at hderiv0
    intro z
    refine ⟨fderiv ℝ f y z, ?_⟩
    have hz := congrArg (fun M : E →L[ℝ] E => M z) hderiv
    simpa [ContinuousLinearMap.comp_apply] using hz

/--
@isnad1 id=eq.0h6v.s12.35d68197960d from=translated src=- shape=561d7f90 vocab=bd576d6a
-/
@[simp] theorem conjugateAffine_forward (A : SmoothAmbientIsotopy n)
    (L : E ≃L[ℝ] E) (b : E) (s : ℝ) (x : E) :
    (A.conjugateAffine L b).forward s x =
      b + L (A.forward s (L.symm (x - b))) :=
  rfl

/--
@isnad1 id=eq.0h6v.s12.f2c4c8c891e7 from=translated src=- shape=561d7f90 vocab=ec50623f
-/
@[simp] theorem conjugateAffine_inverse (A : SmoothAmbientIsotopy n)
    (L : E ≃L[ℝ] E) (b : E) (s : ℝ) (x : E) :
    (A.conjugateAffine L b).inverse s x =
      b + L (A.inverse s (L.symm (x - b))) :=
  rfl

/-- Affine conjugation transports the relative fixed set by the same affine
chart.
@isnad1 id=fixedon.1h5v.s11.9d8224f81d19 from=translated src=- shape=b0b7e1d5 vocab=03b0f34c
-/
theorem FixedOn.conjugateAffine {A : SmoothAmbientIsotopy n} {K : Set E}
    (hA : A.FixedOn K) (L : E ≃L[ℝ] E) (b : E) :
    (A.conjugateAffine L b).FixedOn
      {x | L.symm (x - b) ∈ K} := by
  intro s hs x hx
  rw [conjugateAffine_forward, hA s hs _ hx]
  simp

/-! ## Positioned local rotations -/

variable {m : ℕ}

local notation "E₂" => EuclideanSpace ℝ (Fin (m + 2))

/-- Scalar dilation by a nonzero real number as a continuous linear
equivalence.-/
def dilationCLE (r : ℝ) (hr : r ≠ 0) : E₂ ≃L[ℝ] E₂ :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)

/--
@isnad1 id=eq.1h3v.s11.3135c5f78da9 from=translated src=- shape=7ede4a10 vocab=85c58f8a
-/
@[simp] theorem dilationCLE_apply (r : ℝ) (hr : r ≠ 0) (x : E₂) :
    dilationCLE r hr x = r • x := by
  rw [dilationCLE, ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def]
  have hval : (↑(Units.mk0 r hr) : ℝ) = r := rfl
  rw [hval]

/--
@isnad1 id=eq.1h3v.s11.186eee644282 from=translated src=- shape=69659ffc vocab=8e92020e
-/
@[simp] theorem dilationCLE_symm_apply (r : ℝ) (hr : r ≠ 0) (x : E₂) :
    (dilationCLE r hr).symm x = r⁻¹ • x := by
  rw [dilationCLE]
  change (ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)⁻¹) x = r⁻¹ • x
  rw [ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def,
    Units.val_inv_eq_inv_val]
  have hval : (↑(Units.mk0 r hr) : ℝ) = r := rfl
  rw [hval]

/-- The explicit local plane rotation, transported to the affine chart
`x = b + L u`.-/
def affineLocalizedPlaneRotation (θ : ℝ) (L : E₂ ≃L[ℝ] E₂) (b : E₂) :
    SmoothAmbientIsotopy (m + 1) :=
  (localizedPlaneRotation (m := m) θ).conjugateAffine L b

/-- The positioned move fixes every point whose affine-chart coordinate lies
outside the squared-radius-two support ball.
@isnad1 id=fixedon.0h4v.s11.6c415f629c1a from=translated src=- shape=fd14c2fc vocab=094e4d74
-/
theorem affineLocalizedPlaneRotation_fixedOn (θ : ℝ)
    (L : E₂ ≃L[ℝ] E₂) (b : E₂) :
    (affineLocalizedPlaneRotation (m := m) θ L b).FixedOn
      {x | 2 ≤ localRadialSq (L.symm (x - b))} := by
  exact (localizedPlaneRotation_fixedOn (m := m) θ).conjugateAffine L b

/-- On the transported inner ball, the endpoint is the corresponding affine
conjugate of the full plane rotation.
@isnad1 id=eq.1h5v.s13.24eb1a68bdf9 from=translated src=- shape=704730d8 vocab=067e0eee
-/
theorem affineLocalizedPlaneRotation_endpoint_of_le_one (θ : ℝ)
    (L : E₂ ≃L[ℝ] E₂) (b : E₂) {x : E₂}
    (hx : localRadialSq (L.symm (x - b)) ≤ 1) :
    (affineLocalizedPlaneRotation (m := m) θ L b).forward 1 x =
      b + L (SO2FrameGauge.rotate θ (L.symm (x - b))) := by
  rw [affineLocalizedPlaneRotation, conjugateAffine_forward,
    localizedPlaneRotation_endpoint_of_le_one θ hx]

/-- A local rotation supported near the Euclidean ball of radius `r` centered
at `b`.-/
def ballLocalizedPlaneRotation (θ r : ℝ) (hr : 0 < r) (b : E₂) :
    SmoothAmbientIsotopy (m + 1) :=
  affineLocalizedPlaneRotation θ (dilationCLE r hr.ne') b

end SmoothAmbientIsotopy
end Submission
