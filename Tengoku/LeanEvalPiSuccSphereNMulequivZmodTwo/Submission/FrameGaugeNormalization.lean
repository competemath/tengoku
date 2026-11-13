import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.AmbientNormalizationPrimitive

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Smooth gauge changes of a framed defining map

Once an embedded fiber circle has been moved to its standard position, its
normal framing is changed by multiplying the defining equations by a smooth
field of invertible linear maps.  This file proves the analytic step in full.

For a framed defining map `g` and a smooth field `Q(x)` of invertible
continuous linear endomorphisms of the codomain, the gauge transform is

`x ↦ Q(x) (g(x))`.

It has exactly the same zero fiber.  At a point of that fiber, the product-rule
term differentiating `Q` vanishes because `g(x)=0`; hence its derivative is
literally `Q(x) ∘ Dg(x)` and remains surjective.  The same calculation for a
two-parameter field `Q(s,x)` produces a genuine `DefiningMapHomotopy` and can
be fed directly to `SmoothAmbientIsotopy.signedNormalizationCobordism`.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff RealInnerProductSpace

namespace Submission

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))
local notation "F" => EuclideanSpace ℝ (Fin n)

/-! ## The derivative calculation -/

/-- At a zero of `g`, differentiating a varying linear gauge contributes no
product-rule correction.
@isnad1 id=eq.3h4v.s12.391f7383ce55 from=translated src=- shape=783d534e vocab=2b4628d3
-/
theorem fderiv_gauge_apply_of_eq_zero
    {Q : E → F →L[ℝ] F} {g : E → F}
    (hQ : ContDiff ℝ ∞ Q) (hg : ContDiff ℝ ∞ g)
    {x : E} (hx : g x = 0) :
    fderiv ℝ (fun y => Q y (g y)) x =
      (Q x).comp (fderiv ℝ g x) := by
  rw [fderiv_clm_apply
    (hQ.differentiable (by simp) x)
    (hg.differentiable (by simp) x), hx]
  simp

/-! ## A single gauge transform -/

namespace FramedLevelSet

/-- Multiplication of a framed defining map by a smooth pointwise invertible
linear gauge.-/
def gaugeTransform (X : FramedLevelSet n) (Q : E → F →L[ℝ] F)
    (hQ : ContDiff ℝ ∞ Q) (hQbij : ∀ x, Bijective (Q x)) :
    FramedLevelSet n where
  g x := Q x (X.g x)
  smooth := hQ.clm_apply X.smooth
  fiber_bounded := by
    have hfiber : {x : E | Q x (X.g x) = 0} = X.fiber := by
      ext x
      constructor
      · intro hx
        apply (hQbij x).1
        simpa using hx
      · intro hx
        change X.g x = 0 at hx
        simp [hx]
    rw [hfiber]
    exact X.fiber_bounded
  regular := by
    intro x hx
    have hxg : X.g x = 0 := by
      apply (hQbij x).1
      simpa using hx
    rw [fderiv_gauge_apply_of_eq_zero hQ X.smooth hxg]
    exact (hQbij x).2.comp (X.regular x hxg)

/--
@isnad1 id=eq.2h4v.s11.e6251e419be7 from=translated src=- shape=7f76c986 vocab=6b575163
-/
@[simp] theorem gaugeTransform_g (X : FramedLevelSet n)
    (Q : E → F →L[ℝ] F) (hQ : ContDiff ℝ ∞ Q)
    (hQbij : ∀ x, Bijective (Q x)) (x : E) :
    (X.gaugeTransform Q hQ hQbij).g x = Q x (X.g x) :=
  rfl

/-- A pointwise invertible gauge does not move the zero fiber.
@isnad1 id=eq.2h3v.s10.93b111acc27f from=translated src=- shape=e162b256 vocab=cc9f85f1
-/
theorem gaugeTransform_fiber (X : FramedLevelSet n)
    (Q : E → F →L[ℝ] F) (hQ : ContDiff ℝ ∞ Q)
    (hQbij : ∀ x, Bijective (Q x)) :
    (X.gaugeTransform Q hQ hQbij).fiber = X.fiber := by
  ext x
  constructor
  · intro hx
    change Q x (X.g x) = 0 at hx
    apply (hQbij x).1
    simpa using hx
  · intro hx
    change X.g x = 0 at hx
    change Q x (X.g x) = 0
    simp [hx]

end FramedLevelSet

namespace FiberSign

/-- Since a gauge transform has the same fiber, a sign label transports
unchanged.-/
def gaugeTransform {X : FramedLevelSet n} (S : FiberSign X)
    (Q : E → F →L[ℝ] F) (hQ : ContDiff ℝ ∞ Q)
    (hQbij : ∀ x, Bijective (Q x)) :
    FiberSign (X.gaugeTransform Q hQ hQbij) :=
  S.restrict (by rw [FramedLevelSet.gaugeTransform_fiber])

/--
@isnad1 id=eq.2h5v.s10.7fa7652e5da8 from=translated src=- shape=f1481944 vocab=7d8936c0
-/
@[simp] theorem gaugeTransform_apply {X : FramedLevelSet n} (S : FiberSign X)
    (Q : E → F →L[ℝ] F) (hQ : ContDiff ℝ ∞ Q)
    (hQbij : ∀ x, Bijective (Q x)) (x : E) :
    S.gaugeTransform Q hQ hQbij x = S x :=
  rfl

end FiberSign

/-! ## A smooth family of gauges -/

/-- Joint smoothness gives smoothness of every fixed-parameter gauge.
@isnad1 id=contdiff.1h3v.s11.e007b2ae2131 from=translated src=- shape=8dbe06e4 vocab=a3cd9f1e
-/
theorem contDiff_gauge_slice
    {Q : ℝ → E → F →L[ℝ] F}
    (hQ : ContDiff ℝ ∞ (fun p : ℝ × E => Q p.1 p.2)) (s : ℝ) :
    ContDiff ℝ ∞ (Q s) :=
  hQ.comp (contDiff_const.prodMk contDiff_id)

namespace DefiningMapHomotopy

/-- A smooth family of invertible gauges is a common-fiber homotopy of framed
defining maps.  It is the direct formal target of a smooth `SO(n)` frame-loop
homotopy.-/
def ofGauge (X : FramedLevelSet n)
    (Q : ℝ → E → F →L[ℝ] F)
    (hQ : ContDiff ℝ ∞ (fun p : ℝ × E => Q p.1 p.2))
    (hQzero : ∀ x, Q 0 x = ContinuousLinearMap.id ℝ F)
    (hQbij : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, Bijective (Q s x)) :
    DefiningMapHomotopy X
      (X.gaugeTransform (Q 1) (contDiff_gauge_slice hQ 1)
        (fun x => hQbij 1 ⟨zero_le_one, le_rfl⟩ x)) where
  H s x := Q s x (X.g x)
  smooth := hQ.clm_apply (X.smooth.comp contDiff_snd)
  H_zero := by
    funext x
    rw [hQzero x]
    rfl
  H_one := rfl
  fiber_eq := by
    intro s hs0 hs1
    ext x
    constructor
    · intro hx
      apply (hQbij s ⟨hs0, hs1⟩ x).1
      simpa using hx
    · intro hx
      change X.g x = 0 at hx
      simp [hx]
  regular := by
    intro s hs0 hs1 x hx
    rw [fderiv_gauge_apply_of_eq_zero
      (contDiff_gauge_slice hQ s) X.smooth hx]
    exact (hQbij s ⟨hs0, hs1⟩ x).2.comp (X.regular x hx)

/--
@isnad1 id=eq.3h5v.s11.ed6632a51558 from=translated src=- shape=05ba06b7 vocab=239c9bcd
-/
@[simp] theorem ofGauge_H (X : FramedLevelSet n)
    (Q : ℝ → E → F →L[ℝ] F)
    (hQ : ContDiff ℝ ∞ (fun p : ℝ × E => Q p.1 p.2))
    (hQzero : ∀ x, Q 0 x = ContinuousLinearMap.id ℝ F)
    (hQbij : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, Bijective (Q s x))
    (s : ℝ) (x : E) :
    (ofGauge X Q hQ hQzero hQbij).H s x = Q s x (X.g x) :=
  rfl

end DefiningMapHomotopy

end Submission
