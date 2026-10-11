/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Abstract tangent-space Hilbert projections

This file is **Layer A** of the Hahn (1998) semiparametric-efficiency
formalization: pure Hilbert-space geometry, no measure theory and no causal
content. It supplies the geometry that a statistical efficiency theorem can
use after separately identifying a pathwise derivative and regular influence
functions.

Fix a real Hilbert space `H` and a *tangent subspace* `T : Submodule ℝ H`
(in applications, the closure of the set of scores of regular parametric
submodels). The predicate `IsGradient T g ψ` says only that `g` and `ψ` have
the same inner products against `T`. The projection `efficientIF T g` and its
squared norm `effBound T g` are geometric objects; they acquire their usual
semiparametric interpretation only when `g` represents a functional's pathwise
derivative. Pythagoras gives the corresponding squared-norm inequality for every
`IsGradient` vector.

The closing section records the *tangent-shrinking corollary* (the abstract
"role of the propensity score"): if the reference influence function already
lies in the smaller tangent space, shrinking the tangent space leaves the
efficiency bound unchanged.
-/

module
public import Tengoku

/-! # Tangent-space projection geometry

This file defines equality of directional inner products along a tangent
subspace, the orthogonal projection of a reference vector, and the projection's
squared norm. It proves the associated minimum-norm and tangent-shrinking
identities used after a statistical model supplies the pathwise-gradient bridge. -/

@[expose] public section

namespace Causalean.Estimation.Efficiency

open scoped InnerProductSpace RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Given [a real normed inner-product space](hyp:H), [a linear subspace designated as the tangent
space](hyp:T), and [two vectors, a reference influence function and a candidate
gradient](hyp:g,ψ), the [candidate is a gradient of the reference relative to the
tangent space](goal) exactly when, for every vector in that subspace, its inner
product with the candidate equals its inner product with the reference.

`ψ` is a *gradient* of `g` relative to the tangent space `T` when its inner
product against every tangent direction matches that of `g`. In semiparametric
models this relation can compare influence functions once a separate theorem
identifies `g` with the functional's pathwise derivative. -/
def IsGradient (T : Submodule ℝ H) (g ψ : H) : Prop :=
  ∀ s ∈ T, ⟪ψ, s⟫_ℝ = ⟪g, s⟫_ℝ

/-- Given [a real normed inner-product space](hyp:H), [a tangent subspace admitting an orthogonal
projection](hyp:T), and [a reference vector](hyp:g), the [projected reference
vector](goal) is the orthogonal projection of `g` onto that tangent subspace.

When `g` represents a functional's pathwise derivative, this projection is the
usual canonical gradient. -/
noncomputable def efficientIF (T : Submodule ℝ H) [T.HasOrthogonalProjection]
    (g : H) : H :=
  (T.orthogonalProjectionOnto g : H)

/-- Given [a real normed inner-product space](hyp:H), [a tangent subspace admitting an orthogonal
projection](hyp:T), and [a reference vector](hyp:g), the [projection-norm
functional](goal) is the squared norm of the projected reference vector.

It is a semiparametric efficiency bound only after `g` has been connected to a
functional's pathwise derivative in a statistical model. -/
noncomputable def effBound (T : Submodule ℝ H) [T.HasOrthogonalProjection]
    (g : H) : ℝ :=
  ‖efficientIF T g‖ ^ 2

variable {T : Submodule ℝ H} [T.HasOrthogonalProjection]

/-- `efficientIF` is the coerced star-projection (the projection seen as an
endomorphism of `H`).
@isnad1 id=eq.0h3v.s8.779c68cc14e2 from=translated src=- shape=758aa11b vocab=e3902d82
-/
theorem efficientIF_eq_starProjection (g : H) :
    efficientIF T g = T.starProjection g := rfl

/-- The efficient influence function lies in the tangent space.
@isnad1 id=mem.0h3v.s7.da6d3b1b0228 from=translated src=- shape=7c9e8084 vocab=f069aa17
-/
theorem efficientIF_mem (g : H) : efficientIF T g ∈ T :=
  (T.orthogonalProjectionOnto g).2

omit [T.HasOrthogonalProjection] in
/-- A vector is a gradient of `g` iff it differs from `g` by an element of the
orthogonal complement of the tangent space.
@isnad1 id=iff.0h4v.s7.034a33526a6b from=translated src=- shape=a47e84a8 vocab=5143f30d
-/
theorem isGradient_iff_sub_mem_orthogonal (g ψ : H) :
    IsGradient T g ψ ↔ ψ - g ∈ Tᗮ := by
  constructor
  · intro h
    rw [Submodule.mem_orthogonal]
    intro s hs
    rw [inner_sub_right, real_inner_comm ψ s, real_inner_comm g s, h s hs, sub_self]
  · intro h s hs
    rw [Submodule.mem_orthogonal] at h
    have hzero := h s hs
    rw [inner_sub_right, sub_eq_zero] at hzero
    rw [real_inner_comm s ψ, real_inner_comm s g, hzero]

/-- The efficient influence function is itself a gradient of `g`.
@isnad1 id=isgradie.0h3v.s5.933397d7e2f0 from=translated src=- shape=3ec53e69 vocab=0084cbcd
-/
theorem efficientIF_isGradient (g : H) : IsGradient T g (efficientIF T g) := by
  intro s hs
  exact T.inner_orthogonalProjectionOnto_eq_of_mem_right ⟨s, hs⟩ g

/-- A gradient `ψ` projects onto the same efficient influence function as `g`.
@isnad1 id=eq.1h4v.s10.a1a8ccdddca8 from=translated src=- shape=c8b4b678 vocab=bc1ed1cc
-/
theorem orthogonalProjection_eq_of_isGradient {g ψ : H} (h : IsGradient T g ψ) :
    (T.orthogonalProjectionOnto ψ : H) = efficientIF T g := by
  have hsub : ψ - g ∈ Tᗮ := (isGradient_iff_sub_mem_orthogonal g ψ).1 h
  have hz : T.orthogonalProjectionOnto (ψ - g) = 0 :=
    T.orthogonalProjectionOnto_eq_zero_iff.mpr hsub
  have hlin : T.orthogonalProjectionOnto ψ - T.orthogonalProjectionOnto g
      = T.orthogonalProjectionOnto (ψ - g) := by
    rw [map_sub]
  rw [hz, sub_eq_zero] at hlin
  rw [efficientIF, hlin]

/-- **Pythagoras for gradients.** [For any function `ψ` that is a gradient at `g`](hyp:h),
[the squared norm of `ψ` splits into the efficiency bound plus the squared norm of the
remainder orthogonal to the efficient influence function](goal).
@isnad1 id=eq.1h4v.s7.46f9528860c3 from=translated src=- shape=b54a0b4f vocab=1bc99bc0
-/
theorem normSq_gradient_decomp {g ψ : H} (h : IsGradient T g ψ) :
    ‖ψ‖ ^ 2 = ‖efficientIF T g‖ ^ 2 + ‖ψ - efficientIF T g‖ ^ 2 := by
  have hproj : (T.orthogonalProjectionOnto ψ : H) = efficientIF T g :=
    orthogonalProjection_eq_of_isGradient h
  have hmem : efficientIF T g ∈ T := efficientIF_mem g
  have horth : ψ - efficientIF T g ∈ Tᗮ := by
    rw [← hproj]
    exact T.sub_starProjection_mem_orthogonal ψ
  have hzero : ⟪efficientIF T g, ψ - efficientIF T g⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal _ _).1 horth _ hmem
  have hsplit : ψ = efficientIF T g + (ψ - efficientIF T g) := by abel
  calc ‖ψ‖ ^ 2 = ‖efficientIF T g + (ψ - efficientIF T g)‖ ^ 2 := by rw [← hsplit]
    _ = ‖efficientIF T g‖ ^ 2 + ‖ψ - efficientIF T g‖ ^ 2 := by
        rw [norm_add_sq_real, hzero]; ring

/-- **Efficiency lower bound.** [For any function `ψ` that is a gradient at `g`](hyp:h),
[the efficiency bound is at most the squared norm of `ψ`](goal).
@isnad1 id=le.1h4v.s6.8ec5daa0818b from=translated src=- shape=5fad80fa vocab=674c57e9
-/
theorem effBound_le_normSq {g ψ : H} (h : IsGradient T g ψ) :
    effBound T g ≤ ‖ψ‖ ^ 2 := by
  rw [effBound, normSq_gradient_decomp h]
  have : (0 : ℝ) ≤ ‖ψ - efficientIF T g‖ ^ 2 := sq_nonneg _
  linarith

/-- **Sharpness.** [For any function `ψ` that is a gradient at `g`](hyp:h), [`ψ` attains the
efficiency bound if and only if it equals the efficient influence function](goal).
@isnad1 id=iff.1h4v.s6.36a0b7e833af from=translated src=- shape=292751f4 vocab=46b2c494
-/
theorem norm_eq_iff_eq_efficientIF {g ψ : H} (h : IsGradient T g ψ) :
    ‖ψ‖ ^ 2 = effBound T g ↔ ψ = efficientIF T g := by
  rw [effBound, normSq_gradient_decomp h]
  constructor
  · intro heq
    have hsq : ‖ψ - efficientIF T g‖ ^ 2 = 0 := by linarith
    have hnorm : ‖ψ - efficientIF T g‖ = 0 := by
      exact pow_eq_zero_iff (by norm_num) |>.1 hsq
    rw [norm_eq_zero, sub_eq_zero] at hnorm
    exact hnorm
  · intro heq
    rw [heq, sub_self, norm_zero]; ring

/-- A gradient that lies in the tangent space is the efficient influence
function.
@isnad1 id=eq.2h4v.s7.5bcfd2902b60 from=translated src=- shape=09e965b8 vocab=3705be4e
-/
theorem efficientIF_unique {g ψ : H} (h : IsGradient T g ψ) (hψ : ψ ∈ T) :
    ψ = efficientIF T g := by
  have hproj : (T.orthogonalProjectionOnto ψ : H) = efficientIF T g :=
    orthogonalProjection_eq_of_isGradient h
  rw [← hproj]
  exact (T.starProjection_eq_self_iff.mpr hψ).symm

/-! ### Tangent-shrinking corollary (abstract "role of the propensity score") -/

/-- If the reference gradient already lies in the tangent space, the efficient
influence function equals it.
@isnad1 id=eq.1h3v.s7.f654b8aa76fa from=translated src=- shape=c36cacc5 vocab=f069aa17
-/
theorem efficientIF_eq_self_of_mem (T : Submodule ℝ H) [T.HasOrthogonalProjection]
    {g : H} (hg : g ∈ T) : efficientIF T g = g := by
  rw [efficientIF_eq_starProjection]
  exact T.starProjection_eq_self_iff.mpr hg

/-- **Tangent-shrinking corollary.** If the reference influence function lies in
the smaller tangent space `T' ≤ T`, then both the smaller and larger tangent
spaces leave it fixed, so the efficiency bound is unchanged. Interpretation:
knowing the propensity score shrinks the tangent space, but if `ψ_AIPW` already
lives in the smaller space the efficiency bound does not move.
@isnad1 id=and.2h4v.s8.707095d2306b from=translated src=- shape=211217e9 vocab=7458700e
-/
theorem effBound_eq_of_mem_sub
    (T T' : Submodule ℝ H) [T.HasOrthogonalProjection] [T'.HasOrthogonalProjection]
    (hle : T' ≤ T) {g : H} (hg : g ∈ T') :
    efficientIF T' g = g ∧ efficientIF T g = g ∧ effBound T' g = effBound T g := by
  have h1 : efficientIF T' g = g := efficientIF_eq_self_of_mem T' hg
  have h2 : efficientIF T g = g := efficientIF_eq_self_of_mem T (hle hg)
  exact ⟨h1, h2, by rw [effBound, effBound, h1, h2]⟩

end Causalean.Estimation.Efficiency
