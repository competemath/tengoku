/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.Tauceti.TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
-- supplies `UpperHalfPlane.forall_smul_eq_self_iff_mem_center`, which identifies the kernel
public import Tengoku

/-!
# The rational projective action on the upper half-plane

`GL(2, ℚ)⁺` does not act on `ℍ`; `PSL(2, ℝ)` does. This file supplies the homomorphism
between them, `ratPosToPSL2R`, and identifies its kernel on the determinant-one locus.

Hecke operators are indexed by double cosets of matrices with *rational* entries, so every
geometric statement about them has to be pushed along such a homomorphism before Mathlib's
`ℍ`-API applies. The change of scalars `GL(2, ℚ) →* GL(2, ℝ)` alone will not do: it is
injective, so it keeps `-1`, which acts trivially on `ℍ`. Anything demanding a *faithful*
action — `MeasureTheory.IsFundamentalDomain` in particular, whose a.e.-disjointness clause
is `Pairwise` over group elements — is then unsatisfiable. Passing to `PSL(2, ℝ)` collapses
exactly the scalars, and `eq_one_or_neg_one_of_mem_ratPosToPSL2R_ker_of_det_eq_one` says that on the
determinant-one locus nothing else is lost: an element of the kernel with determinant one is
`±1`. (Only that containment is proved here; the converse, that `±1` do lie in the kernel, is not
needed by any consumer and is not claimed.)

## Main definitions

* `TauCeti.ratPosToRealPos`: the change of scalars `GL(2, ℚ)⁺ →* GL(2, ℝ)⁺`.
* `TauCeti.ratPosToPSL2R`: the composite `GL(2, ℚ)⁺ →* GL(2, ℝ)⁺ →* PSL(2, ℝ)`.

## Main results

* `UpperHalfPlane.ratPosToPSL2R_smul`: `ratPosToPSL2R g` acts on `ℍ` as the real matrix does.
* `TauCeti.eq_one_or_neg_one_of_mem_ratPosToPSL2R_ker_of_det_eq_one`: an element of
  `ker ratPosToPSL2R` with determinant one is `±1` — a containment, not an identification.
* `TauCeti.ratPosToPSL2R_ker_inf_le`: the consequence consumers apply —
  `ker ratPosToPSL2R ⊓ H ≤ Γ` whenever `H` lies in the determinant-one locus and `-1 ∈ Γ`, which
  holds of every `Γ₀(N)`.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.5
-/

public section

open Matrix UpperHalfPlane

open scoped MatrixGroups

namespace TauCeti

/-- The change of scalars `GL(2, ℚ)⁺ →* GL(2, ℝ)⁺`, the restriction of
`Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)` to the positive-determinant subgroups. Its
underlying `GL (Fin 2) ℝ` matrix is that map applied to `g` definitionally, so a goal mixing
the two spellings closes by `rfl`. -/
noncomputable def ratPosToRealPos : GL(2, ℚ)⁺ →* GL(2, ℝ)⁺ :=
  (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)).restrict fun _ ↦
    Matrix.GeneralLinearGroup.map_mem_glpos Rat.cast_strictMono

/-- The underlying `GL (Fin 2) ℝ` matrix of `ratPosToRealPos g` is the entrywise change of
scalars `ℚ → ℝ` applied to `g`. -/
-- `by rfl`, not `rfl`: `ratPosToRealPos` is not `@[expose]`, so a theorem exported from this
-- module cannot unfold it in term mode.
@[simp]
theorem coe_ratPosToRealPos (g : GL(2, ℚ)⁺) :
    (ratPosToRealPos g : GL (Fin 2) ℝ) =
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (g : GL (Fin 2) ℚ) := by rfl

/-- **The rational projective action.** `GL(2, ℚ)⁺` acts on `ℍ` through `PSL(2, ℝ)`: the change
of scalars `ratPosToRealPos` followed by the projectivization `glPosToPSL2R`. Compute the
action with `UpperHalfPlane.ratPosToPSL2R_smul`; unlike `ratPosToRealPos` this map is
deliberately *not* injective, as it collapses the scalar matrices, which act trivially on `ℍ`. -/
noncomputable def ratPosToPSL2R : GL(2, ℚ)⁺ →* PSL(2, ℝ) := glPosToPSL2R.comp ratPosToRealPos

/-- `ratPosToPSL2R g` acts on `ℍ` exactly as the real matrix `g` does. Rewriting with this
turns a goal about the `PSL(2, ℝ)`-action into one about Mathlib's `GL(2, ℝ)`-action on `ℍ`;
it is the `ℚ`-coefficient counterpart of `UpperHalfPlane.glPosToPSL2R_smul`. -/
@[simp]
theorem _root_.UpperHalfPlane.ratPosToPSL2R_smul (g : GL(2, ℚ)⁺) (τ : ℍ) :
    ratPosToPSL2R g • τ =
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (g : GL (Fin 2) ℚ) • τ := by
  unfold ratPosToPSL2R
  rw [MonoidHom.comp_apply, glPosToPSL2R_smul]
  -- the last step is `coe_ratPosToRealPos` under the action, not a definitional unfolding
  exact congrArg (fun m : GL (Fin 2) ℝ ↦ m • τ) (coe_ratPosToRealPos g)

end TauCeti
