module

public import Tengoku
public import Tengoku.Seed.Analysis.InnerProductSpace.PiL2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Congruence of a smooth family of bilinear forms, over an arbitrary parameter

`vendor/TauCeti/` supplies Palais's congruence lemma and the Banach Morse lemma built on it.
This module carries three things forward that a consumer of that cone needs and that the cone
does not state.

## What is here

* **Invertibility of the congruence family.** `TauCeti.exists_congruence_of_symmetric_family`
  produces `R` with `R 0 = 1` and `ContDiffOn ℝ ∞ R U`, and — as
  `vendor/TauCeti/PROVENANCE.md` records in as many words — it does **not** claim that `R v` is
  invertible. `exists_open_isInvertible` derives that on a smaller open set, from continuity and
  the openness of the invertible operators (`ContinuousLinearEquiv.isOpen`), and
  `exists_congruence_isInvertible_of_symmetric_family` is the vendored statement with that
  clause added.

* **An arbitrary parameter space.** The vendored congruence indexes its family of forms on `E`
  by `E` itself, which is all the Morse lemma needs, because there the parameter *is* the
  displacement. A Morse–Bott argument needs a family of forms on `W` indexed by `W × V`, and no
  substitution turns one into the other: the parameter space and the form space are genuinely
  different there. `exists_congruence_of_symmetric_family_param` is Palais's argument with the
  two separated. Its proof is upstream's, with the index type generalised and the base point
  moved off the origin; the operator square root it runs on is the vendored
  `TauCeti.sqrtNearOne`, not a second construction.

* **A parameterised splitting, in the Gromoll–Meyer form.**
  `exists_partial_congruence_normal_form` is the consequence: for `f : W × V → ℝ` whose
  `W`-directional derivative vanishes along `{0} × V`, and whose `W`-block Hessian at the origin
  is invertible, there is a smooth invertible family `R` on a neighbourhood of the origin with

      f (η, ζ) = f (0, ζ) + 2⁻¹ * Q₀ (R (η, ζ) η) (R (η, ζ) η),

  where `Q₀` is the `W`-block of the Hessian at the origin. So `ψ (η, ζ) = R (η, ζ) η` is a
  `ζ`-dependent chart in the `W` directions, flattening the `W` part of `f` onto one fixed
  quadratic form — the same form for every `ζ` — and leaving the germ `g ζ = f (0, ζ)` on the
  fibre untouched. Nothing is assumed about `g`; in particular it need not vanish, and it need
  not be quadratic. `exists_partial_congruence_normal_form_of_vanishing` is the strict
  Morse–Bott special case `g = 0`.

## The hypothesis that is assumed, not derived

`∂_W f (0, ζ) = 0` is a hypothesis of `exists_partial_congruence_normal_form`. It says that
`{0} × V` is critical in the `W` directions, which is what makes the first-order term of the
Taylor expansion in `η` drop out; establishing it for a particular `f` is a separate obligation
and is not attempted here. Nothing in this module derives it, and nothing here says that any
particular loss satisfies it.

## What is *not* here

This is not the full Gromoll–Meyer splitting lemma. That is
`exists_gromoll_meyer_splitting`, in `CriticalFiber`, which supplies the critical
fibre this module assumes and localizes the hypothesis below to a neighbourhood. That lemma takes a degenerate critical point
and *constructs* the splitting `W ⊕ V` — the nondegenerate directions and the kernel of the
Hessian — before producing the germ on the kernel. Here the splitting is handed in: `V` is given,
and the criticality of `f` along `{0} × V` in the `W` directions is a hypothesis. What is
produced is the second half of that lemma's conclusion, the normal form on the `W` factor
together with an arbitrary germ on the `V` factor. The gap recorded at the end of
`vendor/TauCeti/PROVENANCE.md` is therefore narrowed, not closed: what remains is the
construction of the splitting itself.

## What was already present, and is not restated

`TauCeti.IsNondegenerateCriticalPoint.exists_normal_form` is the Morse lemma in the form
`f (x + v) = f x + 2⁻¹ * D²f x (φ v) (φ v)` with `φ 0 = 0` and `fderiv ℝ φ 0 = id`. It is not
reproved. `exists_normal_form_of_hessian_nondegenerate` only restates it over a
finite-dimensional space with the nondegeneracy hypothesis in the form a matrix-space consumer
can discharge — the classical one, that the Hessian bilinear form annihilates no nonzero
vector — using the vendored `TauCeti.ContinuousLinearMap.isInvertible_of_injective` to reach
invertibility of the map into the dual. `exists_normal_form_euclidean` is that statement at
`EuclideanSpace ℝ (Fin n)`.
-/

noncomputable section

open Filter Topology

open scoped ContDiff

namespace AISafetyAtlas.SingularLearning

section Congruence

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

end Congruence

section NormalForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end NormalForm

section MorseBott

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Restriction of a continuous bilinear form on `W × V` to its `W` block**, packaged as a
continuous linear map so that smooth dependence on a parameter transports for free.-/
@[expose] public def blockW (W V : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ((W × V) →L[ℝ] (W × V) →L[ℝ] ℝ) →L[ℝ] (W →L[ℝ] W →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ W ((W × V) →L[ℝ] ℝ) (W →L[ℝ] ℝ)
      ((ContinuousLinearMap.compL ℝ W (W × V) ℝ).flip (ContinuousLinearMap.inl ℝ W V))).comp
    ((ContinuousLinearMap.compL ℝ W (W × V) ((W × V) →L[ℝ] ℝ)).flip
      (ContinuousLinearMap.inl ℝ W V))

@[simp] public theorem blockW_apply (T : (W × V) →L[ℝ] (W × V) →L[ℝ] ℝ) (w w' : W) :
    blockW W V T w w' = T (w, 0) (w', 0) := rfl

end MorseBott

end AISafetyAtlas.SingularLearning

end
