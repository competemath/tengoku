import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.AmbientNormalizationPrimitive

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conjugating an ambient isotopy by an accumulated endpoint

Componentwise normalization starts with local moves written in the original
coordinates.  After some components have already been moved, the next local
move must be transported by the endpoint diffeomorphism accumulated so far.
This file supplies that transport for `SmoothAmbientIsotopy`.

If `A` is the accumulated isotopy and `B` is the next move, then

`B.conjugateByEndpoint A = A₁ ∘ Bₛ ∘ A₁⁻¹`.

Consequently a set fixed by `B` is transported to its current image under
`A₁`, and composing `A` with the conjugate applies the original endpoint moves
in their intended order.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Topology ContDiff RealInnerProductSpace

namespace Submission
namespace SmoothAmbientIsotopy

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- Forward family `A₁ ∘ Bₛ ∘ A₁⁻¹`.-/
def endpointConjugateForward (B A : SmoothAmbientIsotopy n)
    (s : ℝ) (x : E) : E :=
  A.forward 1 (B.forward s (A.inverse 1 x))

/-- Inverse family `A₁ ∘ Bₛ⁻¹ ∘ A₁⁻¹`.-/
def endpointConjugateInverse (B A : SmoothAmbientIsotopy n)
    (s : ℝ) (x : E) : E :=
  A.forward 1 (B.inverse s (A.inverse 1 x))

/--
@isnad1 id=contdiff.0h3v.s9.de5a60839353 from=translated src=- shape=2976e745 vocab=4d053b3e
-/
theorem contDiff_endpointConjugateForward (B A : SmoothAmbientIsotopy n) :
    ContDiff ℝ ∞ (fun p : ℝ × E =>
      endpointConjugateForward B A p.1 p.2) := by
  have hAinv : ContDiff ℝ ∞ (fun p : ℝ × E => A.inverse 1 p.2) :=
    (A.contDiff_inverse_slice 1).comp contDiff_snd
  have hB : ContDiff ℝ ∞
      (fun p : ℝ × E => B.forward p.1 (A.inverse 1 p.2)) :=
    B.forward_smooth.comp (contDiff_fst.prodMk hAinv)
  exact (A.contDiff_forward_slice 1).comp hB

/--
@isnad1 id=contdiff.0h3v.s9.05dbb5160aab from=translated src=- shape=2976e745 vocab=ca61dfef
-/
theorem contDiff_endpointConjugateInverse (B A : SmoothAmbientIsotopy n) :
    ContDiff ℝ ∞ (fun p : ℝ × E =>
      endpointConjugateInverse B A p.1 p.2) := by
  have hAinv : ContDiff ℝ ∞ (fun p : ℝ × E => A.inverse 1 p.2) :=
    (A.contDiff_inverse_slice 1).comp contDiff_snd
  have hB : ContDiff ℝ ∞
      (fun p : ℝ × E => B.inverse p.1 (A.inverse 1 p.2)) :=
    B.inverse_smooth.comp (contDiff_fst.prodMk hAinv)
  exact (A.contDiff_forward_slice 1).comp hB

/--
@isnad1 id=leftinve.1h4v.s6.c689ef843729 from=translated src=- shape=c6fd566f vocab=7964a634
-/
theorem endpointConjugate_leftInverse (B A : SmoothAmbientIsotopy n)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    LeftInverse (endpointConjugateInverse B A s)
      (endpointConjugateForward B A s) := by
  intro x
  simp only [endpointConjugateInverse, endpointConjugateForward]
  rw [A.left_inv 1 ⟨zero_le_one, le_rfl⟩,
    B.left_inv s hs, A.right_inv 1 ⟨zero_le_one, le_rfl⟩]

/--
@isnad1 id=rightinv.1h4v.s6.2025ca2610d2 from=translated src=- shape=c6fd566f vocab=c8b4c4ff
-/
theorem endpointConjugate_rightInverse (B A : SmoothAmbientIsotopy n)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    RightInverse (endpointConjugateInverse B A s)
      (endpointConjugateForward B A s) := by
  intro x
  simp only [endpointConjugateInverse, endpointConjugateForward]
  rw [A.left_inv 1 ⟨zero_le_one, le_rfl⟩,
    B.right_inv s hs, A.right_inv 1 ⟨zero_le_one, le_rfl⟩]

/-- Transport a local move by the endpoint diffeomorphism of an accumulated
ambient isotopy.-/
def conjugateByEndpoint (B A : SmoothAmbientIsotopy n) :
    SmoothAmbientIsotopy n where
  forward := endpointConjugateForward B A
  inverse := endpointConjugateInverse B A
  forward_smooth := contDiff_endpointConjugateForward B A
  inverse_smooth := contDiff_endpointConjugateInverse B A
  forward_zero := by
    funext x
    simp only [endpointConjugateForward, B.forward_zero, id_eq]
    exact A.right_inv 1 ⟨zero_le_one, le_rfl⟩ x
  left_inv := endpointConjugate_leftInverse B A
  right_inv := endpointConjugate_rightInverse B A
  inverse_fderiv_surjective := by
    intro s hs x
    let f : E → E := endpointConjugateForward B A s
    let g : E → E := endpointConjugateInverse B A s
    have hf : ContDiff ℝ ∞ f :=
      (contDiff_endpointConjugateForward B A).comp
        (contDiff_const.prodMk contDiff_id)
    have hg : ContDiff ℝ ∞ g :=
      (contDiff_endpointConjugateInverse B A).comp
        (contDiff_const.prodMk contDiff_id)
    let y : E := g x
    have hfy : f y = x := endpointConjugate_rightInverse B A s hs x
    have hgf : (fun z => g (f z)) = id := by
      funext z
      exact endpointConjugate_leftInverse B A s hs z
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
@isnad1 id=eq.0h5v.s6.3f3e65619be0 from=translated src=- shape=48e807e6 vocab=2ebe67f8
-/
@[simp] theorem conjugateByEndpoint_forward (B A : SmoothAmbientIsotopy n)
    (s : ℝ) (x : E) :
    (B.conjugateByEndpoint A).forward s x =
      A.forward 1 (B.forward s (A.inverse 1 x)) :=
  rfl

/--
@isnad1 id=eq.0h5v.s6.5ac3b71d9a08 from=translated src=- shape=8590d132 vocab=2ebe67f8
-/
@[simp] theorem conjugateByEndpoint_inverse (B A : SmoothAmbientIsotopy n)
    (s : ℝ) (x : E) :
    (B.conjugateByEndpoint A).inverse s x =
      A.forward 1 (B.inverse s (A.inverse 1 x)) :=
  rfl

/-- On the current image of an original point, endpoint conjugation is the
literal transported original move.
@isnad1 id=eq.0h5v.s6.de974781eb9b from=translated src=- shape=1d768207 vocab=cfbefa3e
-/
theorem conjugateByEndpoint_forward_endpoint_image
    (B A : SmoothAmbientIsotopy n) (s : ℝ) (x : E) :
    (B.conjugateByEndpoint A).forward s (A.forward 1 x) =
      A.forward 1 (B.forward s x) := by
  rw [conjugateByEndpoint_forward,
    A.left_inv 1 ⟨zero_le_one, le_rfl⟩]

/-- A relative fixed set is transported to its current endpoint image.
@isnad1 id=fixedon.1h4v.s6.fb9ada006d29 from=translated src=- shape=d375b90b vocab=d6b519ce
-/
theorem FixedOn.conjugateByEndpoint {B A : SmoothAmbientIsotopy n}
    {K : Set E} (hB : B.FixedOn K) :
    (B.conjugateByEndpoint A).FixedOn (A.forward 1 '' K) := by
  intro s hs x hx
  obtain ⟨y, hyK, rfl⟩ := hx
  rw [conjugateByEndpoint_forward_endpoint_image, hB s hs y hyK]

/-- Endpoint conjugation transports the image of every set by the accumulated
endpoint map.
@isnad1 id=eq.0h5v.s7.998e2f0dbbf1 from=translated src=- shape=77aa3ba9 vocab=a6d39c3a
-/
theorem conjugateByEndpoint_forward_image (B A : SmoothAmbientIsotopy n)
    (s : ℝ) (K : Set E) :
    (B.conjugateByEndpoint A).forward s '' (A.forward 1 '' K) =
      A.forward 1 '' (B.forward s '' K) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hyK, rfl⟩, rfl⟩
    exact ⟨B.forward s y, ⟨y, hyK, rfl⟩,
      (conjugateByEndpoint_forward_endpoint_image B A s y).symm⟩
  · rintro ⟨_, ⟨y, hyK, rfl⟩, rfl⟩
    exact ⟨A.forward 1 y, ⟨y, hyK, rfl⟩,
      conjugateByEndpoint_forward_endpoint_image B A s y⟩

/-- Composing the accumulated move with the transported next move applies the
two original endpoint maps in order.
@isnad1 id=eq.0h4v.s6.9ee3d430b13b from=translated src=- shape=ee50cfeb vocab=4bcd7956
-/
theorem followedBy_conjugateByEndpoint_forward_one
    (A B : SmoothAmbientIsotopy n) (x : E) :
    (A.followedBy (B.conjugateByEndpoint A)).forward 1 x =
      A.forward 1 (B.forward 1 x) := by
  rw [followedBy_forward,
    conjugateByEndpoint_forward_endpoint_image]

end SmoothAmbientIsotopy
end Submission
