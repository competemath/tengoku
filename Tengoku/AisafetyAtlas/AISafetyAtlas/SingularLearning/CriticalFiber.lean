module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.HadamardCongruence
public import Tengoku.Seed.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Tengoku.Seed.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The critical fibre, and the Gromoll–Meyer splitting along it

`HadamardCongruence` proves the second half of the parametrised Morse splitting: given that the
`W`-directional derivative of `f` vanishes along a section of the `V`-fibration, it flattens the
`W` part of `f` onto one fixed quadratic form. Its own docstring records the gap — the vanishing
is **assumed**, and nothing there establishes it for a particular `f`. This module closes that
gap and assembles the two halves into the splitting itself.

## What is here

* **The critical fibre.** `exists_critical_fiber`: for `f` smooth on `W × V` with `0` a critical
  point and the `W`-block of the Hessian at `0` invertible as a map `W → W∗`, the equation
  `∂_W f (η, ζ) = 0` has a smooth solution `η = ξ ζ` on a neighbourhood of `0` in `V`, with
  `ξ 0 = 0`. The proof is the inverse function theorem applied to
  `Φ (η, ζ) = (Q₀⁻¹ (∂_W f (η, ζ)), ζ)`, whose derivative at the origin is the shear
  `(u, v) ↦ (u + C v, v)`; `Φ` preserves the second coordinate, so its local inverse does too and
  the fibre coordinate reads off the first component of `Φ⁻¹ (0, ζ)`. Smoothness of the inverse on
  an **open** set — not merely at one point, which is all `ContDiffAt.contDiffOn` can give at
  `C^∞` — comes from `OpenPartialHomeomorph.contDiffAt_symm` applied at every point of the target
  where `fderiv ℝ Φ` is still invertible, a set that is open because the invertible operators are.

* **The congruence along a moving section.** `exists_shifted_congruence_normal_form` is
  `exists_partial_congruence_normal_form` with two changes that the fibre forces. The base point of
  the Taylor expansion moves along a smooth section `c : V → W` rather than sitting on `{0} × V`,
  and criticality is asked only on a neighbourhood `Uv ∋ 0` rather than on all of `V`, because a
  fibre produced by the implicit function theorem is local and can never satisfy the global
  hypothesis. `shiftedHessianAverage` is the corresponding family of forms; at the origin it is
  still the `W`-block of the Hessian, which is why no second-derivative chain rule is needed
  anywhere in this file. `exists_partial_congruence_normal_form_of_nhds` is the case `c = 0`:
  the neighbourhood form of the existing statement, obtained by intersecting the produced
  neighbourhood with `Prod.snd ⁻¹' Uv`.

* **The splitting.** `exists_gromoll_meyer_splitting` combines the two: near a critical point whose
  Hessian is nondegenerate on `W`, there are a chart `Θ` and a germ `g` on the complement with

      f q - f 0 = 2⁻¹ * Q₀ (Θ q).1 (Θ q).1 + g q.2,

  which is the printed equation. `Θ` is delivered in the **forward** direction — it maps the
  original coordinates to the normal-form ones, `Θ q = (R (q.1 - c q.2, q.2) (q.1 - c q.2), q.2)`
  — and it is a local diffeomorphism at the origin: `ContDiffOn ℝ ∞ Θ U` together with
  `HasFDerivAt Θ e 0` for an explicit `e : (W × V) ≃L[ℝ] (W × V)`, the shear by `-fderiv ℝ c 0`.
  That pair, not the equality of germs, is what a downstream volume-order argument needs, and it
  is why the conclusion carries an equivalence rather than a bare continuous linear map. The
  second coordinate is untouched, `(Θ q).2 = q.2`, so `g` is read at the same fibre coordinate on
  both sides.

The critical fibre `c` is returned alongside `Θ`, with `g ζ = f (c ζ, ζ) - f 0`. Without it `g`
would be an opaque function of the caller's own loss and nothing could be said about it; with it,
`g` is the restriction of `f` to the critical fibre, which is the printed germ, and a consumer can
compute it. `Examples/SingularLearning/CriticalFiber.lean` uses exactly that to show the germ is
not constant on the model `f (η, ζ) = η² − ζ⁴`, which is the whole point of this splitting as
against a strict Morse–Bott one.

## Auxiliaries

`shear D` is `(u, v) ↦ (u + D v, v)` as a continuous linear equivalence of `W × V`; it is the
derivative of both the fibre chart `Φ` above and of the shift `(η, ζ) ↦ (η + c ζ, ζ)`.

`exists_contDiff_eqOn_of_contDiffOn` extends a germ that is `C^∞` on an open set to a globally
`C^∞` function agreeing with it near a chosen point, by multiplying by a bump. It is the reason
`exists_gromoll_meyer_splitting` carries `[FiniteDimensional ℝ V]`: what supplies the bump is
Mathlib's bump-function typeclass, which a finite-dimensional real normed space satisfies and a
general Banach space need not, and the congruence machinery inherited from `HadamardCongruence`
asks for a section that is smooth on all of `V`, not merely near the origin. Nothing else in this file needs
finite dimensionality, and `exists_critical_fiber` and the shifted congruence are stated over
Banach spaces.

## What is still assumed

The splitting `W ⊕ V` is handed in, exactly as in `HadamardCongruence`: `V` is given, and that the
`W`-block of the Hessian is invertible is a hypothesis. What this module removes is the separate
assumption that `{0} × V` is critical in the `W` directions — that is now derived, and the fibre
along which it holds is produced rather than assumed to be a coordinate axis. What remains, and is
not attempted here, is the construction of the decomposition `W ⊕ V` from a degenerate critical
point, that is, the identification of `V` with the kernel of the Hessian.
-/

noncomputable section

open Filter Topology

open scoped ContDiff

namespace AISafetyAtlas.SingularLearning

section Shear

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The shear `(u, v) ↦ (u + D v, v)`**, as a continuous linear equivalence of `W × V`.-/
@[expose] public def shear (D : V →L[ℝ] W) : (W × V) ≃L[ℝ] (W × V) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ W V + D.comp (ContinuousLinearMap.snd ℝ W V)).prod
      (ContinuousLinearMap.snd ℝ W V))
    ((ContinuousLinearMap.fst ℝ W V - D.comp (ContinuousLinearMap.snd ℝ W V)).prod
      (ContinuousLinearMap.snd ℝ W V))
    (fun p ↦ by simp) (fun p ↦ by simp)

@[simp] public theorem shear_apply (D : V →L[ℝ] W) (p : W × V) :
    shear D p = (p.1 + D p.2, p.2) := rfl

end Shear

section Extension

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

end Extension

section CriticalFiber

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

end CriticalFiber

section ShiftedSplitting

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

end ShiftedSplitting

section GromollMeyer

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

end GromollMeyer

end AISafetyAtlas.SingularLearning

end
