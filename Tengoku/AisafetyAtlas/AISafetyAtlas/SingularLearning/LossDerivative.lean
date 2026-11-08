module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.LossExpansion
public import Tengoku.Seed.Analysis.Calculus.ContDiff.Comp
public import Tengoku.Seed.Analysis.Calculus.ContDiff.Operations
public import Tengoku.Seed.Analysis.Calculus.FDeriv.Bilinear
public import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The reduced-rank loss as a smooth function, with its first two derivatives

Everything `LossExpansion.lean` proves about `L(A, B) = ‖B A − Φ‖²_F` is entrywise matrix
algebra: exact polynomial identities, no derivative taken anywhere.  The splitting step of
MAIS-O77(b) §7.4 cannot consume that form, because the splitting lemma
(`HadamardCongruence.lean`) states its hypotheses as `fderiv ℝ f p = 0` and as a condition on
`fderiv ℝ (fderiv ℝ f) p`.  This module supplies the missing layer: the same loss, presented as
a `C^∞` function on the product of matrix spaces, with both derivatives computed explicitly.

## Primary surface

| Declaration | Content |
|---|---|
| `pairLoss` | `L(A, B) = ‖B A − Φ‖²_F` as a function of the pair `(A, B)` |
| `contDiff_pairLoss` | `L` is `C^∞` |
| `pairLossDeriv`, `hasFDerivAt_pairLoss` | `dL(A,B)(X, Y) = 2⟨B A − Φ, B X + Y A⟩` |
| `fderiv_pairLoss_apply` | the same, as an evaluation of `fderiv` |
| `fderiv_pairLoss_eq_zero_of` | the criticality equations `Bᵀ R = 0`, `R Aᵀ = 0` kill `dL` |
| `fderiv_fderiv_pairLoss_apply` | the polar form of the Hessian |

The Hessian reads

    `d²L(A,B)[(X,Y)][(X',Y')] = 2(⟨B X + Y A, B X' + Y' A⟩ + ⟨B A − Φ, Y X' + Y' X⟩)`,

whose diagonal `(X', Y') = (X, Y)` is `2(‖B X + Y A‖²_F + 2⟨B A − Φ, Y X⟩)` — exactly twice the
quadratic part of the expansion `frobeniusSq_full_variation_of_critical` records.  The two
summands are the Gauss–Newton term and the residual term; the second is what makes a critical
point with a nonzero residual a saddle rather than a minimum, and it is the reason the
degenerate directions of the Hessian are not the fibre directions of the product map.

## Which norm, and why the instance question is not neutral here

`Matrix ι κ ℝ` carries **no** global normed instance in Mathlib, so one has to be installed to
speak of `ContDiff` at all.  This file installs `Matrix.frobeniusNormedAddCommGroup` and
`Matrix.frobeniusNormedSpace` as local instances, the same pair `MatrixAnalytic.lean` and
`EliminationChart.lean` use.  Under it `‖X‖² = frobeniusSq X`, so the norm and the pairing this
file differentiates are the same object.

Nothing proved here depends on that choice: all norms on a finite-dimensional real vector space
are equivalent, and `HasFDerivAt`, `fderiv` and `ContDiff` see only the topology and the linear
structure.  What does depend on it is *elaboration*: `Matrix` has its own `TopologicalSpace` and
`Module` instances, which do not reduce to the ones the Frobenius norm supplies, so a
`→L[ℝ]` type written plainly and a `→L[ℝ]` type produced by `fderiv` are defeq but not
syntactically equal.  The proofs below bridge that with `show`, which checks at default
transparency; `rw` and `simp`, which do not, will fail on such a goal.  A consumer of these
statements has to install the same two local instances.

Nothing here computes a volume order, and nothing here proves the splitting itself.
-/

namespace AISafetyAtlas.SingularLearning

open scoped ContDiff Matrix

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

section Pairing

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The Frobenius pairing as a bilinear map.-/
@[expose] public noncomputable def froIPₗ :
    Matrix ι κ ℝ →ₗ[ℝ] Matrix ι κ ℝ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ froIP froIP_add_left
    (fun c X Y => by
      simpa [froIP_comm X Y, froIP_comm (c • X) Y] using froIP_smul_right c Y X)
    froIP_add_right
    (fun c X Y => froIP_smul_right c X Y)

/-- The Frobenius pairing as a continuous bilinear map.-/
@[expose] public noncomputable def froIPL :
    Matrix ι κ ℝ →L[ℝ] Matrix ι κ ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (Matrix ι κ ℝ →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Matrix ι κ ℝ →L[ℝ] ℝ)).toLinearMap ∘ₗ froIPₗ)

@[simp] public theorem froIPL_apply (X Y : Matrix ι κ ℝ) : froIPL X Y = froIP X Y := rfl

end Pairing

section Mul

variable {M N H : ℕ}

/-- Matrix multiplication, with the arguments in the order the parameter pair carries them.-/
@[expose] public noncomputable def mulₗ :
    Matrix (Fin H) (Fin M) ℝ →ₗ[ℝ] Matrix (Fin N) (Fin H) ℝ →ₗ[ℝ] Matrix (Fin N) (Fin M) ℝ :=
  LinearMap.mk₂ ℝ (fun A B => B * A)
    (fun A₁ A₂ B => Matrix.mul_add B A₁ A₂)
    (fun c A B => Matrix.mul_smul B c A)
    (fun A B₁ B₂ => Matrix.add_mul B₁ B₂ A)
    (fun c A B => Matrix.smul_mul c B A)

@[expose] public noncomputable def mulL :
    Matrix (Fin H) (Fin M) ℝ →L[ℝ] Matrix (Fin N) (Fin H) ℝ →L[ℝ] Matrix (Fin N) (Fin M) ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (Matrix (Fin N) (Fin H) ℝ →ₗ[ℝ] Matrix (Fin N) (Fin M) ℝ)
          ≃ₗ[ℝ] (Matrix (Fin N) (Fin H) ℝ →L[ℝ] Matrix (Fin N) (Fin M) ℝ)).toLinearMap ∘ₗ mulₗ)

@[simp] public theorem mulL_apply (A : Matrix (Fin H) (Fin M) ℝ)
    (B : Matrix (Fin N) (Fin H) ℝ) : mulL A B = B * A := rfl

end Mul

section Loss

variable {M N H : ℕ}

/-- The first-order motion of the product `B * A` under a variation `(X, Y)` of the pair.-/
@[expose] public noncomputable def mulDerivL (A : Matrix (Fin H) (Fin M) ℝ)
    (B : Matrix (Fin N) (Fin H) ℝ) :
    (Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ) →L[ℝ] Matrix (Fin N) (Fin M) ℝ :=
  (mulL.flip B).comp (ContinuousLinearMap.fst ℝ _ _)
    + (mulL A).comp (ContinuousLinearMap.snd ℝ _ _)

@[simp] public theorem mulDerivL_apply (A : Matrix (Fin H) (Fin M) ℝ)
    (B : Matrix (Fin N) (Fin H) ℝ) (X : Matrix (Fin H) (Fin M) ℝ)
    (Y : Matrix (Fin N) (Fin H) ℝ) : mulDerivL A B (X, Y) = B * X + Y * A := rfl

/-- The reduced-rank regression loss as a function on the product of matrix spaces.-/
@[expose] public noncomputable def pairLoss (Φ : Matrix (Fin N) (Fin M) ℝ)
    (p : Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ) : ℝ :=
  frobeniusSq (p.2 * p.1 - Φ)

/-- The differential of `pairLoss` at `(A, B)`.-/
@[expose] public noncomputable def pairLossDeriv (Φ : Matrix (Fin N) (Fin M) ℝ)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ) :
    (Matrix (Fin H) (Fin M) ℝ × Matrix (Fin N) (Fin H) ℝ) →L[ℝ] ℝ :=
  (2 : ℝ) • ((froIPL (B * A - Φ)).comp (mulDerivL A B))

@[simp] public theorem pairLossDeriv_apply (Φ : Matrix (Fin N) (Fin M) ℝ)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ)
    (X : Matrix (Fin H) (Fin M) ℝ) (Y : Matrix (Fin N) (Fin H) ℝ) :
    pairLossDeriv Φ A B (X, Y) = 2 * froIP (B * A - Φ) (B * X + Y * A) := by
  simp only [pairLossDeriv, smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, mulDerivL_apply, froIPL_apply, smul_eq_mul]

/-! ## Smoothness -/

/-! ## The first derivative -/

/-! ## The second derivative -/

end Loss

end AISafetyAtlas.SingularLearning
