/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/
module

public import Tengoku.LeanPool.LeanPool.Chudnovsky.PicardFuchs
public import Tengoku.LeanPool.LeanPool.Chudnovsky.Basic
public import Tengoku.LeanPool.LeanPool.Chudnovsky.Clausen
import Tengoku.LeanPool.LeanPool.Chudnovsky.Estimates
import Tengoku.LeanPool.LeanPool.Chudnovsky.Ramanujan
public import Tengoku

/-!
# Kummer's solution of the Picard–Fuchs equation

This file covers chapter 8 of Milla's proof of the Chudnovsky formula (arXiv:1809.00533v6,
`130_Kummer.tex`).

## Main definitions

* `Chudnovsky.kummerB` : Kummer's solution
  `b(J) = J^(-1/4) · (1-J)^(1/4) · ₂F₁(1/12, 5/12; 1; 1/J)` (paper Thm. `satzbj`), realized
  with principal-branch `cpow`. (The paper allows an arbitrary fixed branch of the fourth
  roots; since the Picard–Fuchs equation is homogeneous the choice is immaterial there.)

## Main statements (all proved)

* `Chudnovsky.kummerB_satisfiesPicardFuchs` : `b(J)` solves the Picard–Fuchs equation
  (paper Thm. `satzbj`). The paper states this for all `|J| > 1`; with the principal branch
  we must additionally stay off the branch cuts, i.e. off the real axis (for `J` real with
  `|J| > 1` either `J` or `1 - J` is a negative real).
* `Chudnovsky.norm_inv_J_lt_one` : `1/J(τ)` lies in the unit disc on `Region` (from
  `Estimates.lean`'s `one_lt_norm_J`), so that the hypergeometric series converges.
* `Chudnovsky.E₄_eq_hyp2F1_pow_four` : the chapter's output `omegastrich`, in the branch-free
  fourth-power form recommended by PLAN A7:
  `E₄(τ) = (₂F₁(1/12, 5/12; 1; 1/J(τ)))⁴` for `τ ∈ Region`, proved by the Wronskian
  comparison argument described in the section `OmegaStrich` below (using Ramanujan's
  derivative identities from `Ramanujan.lean` in place of the paper's period integrals).

## Faithfulness note on `omegastrich`

The paper's Thm. `omegastrich` reads
`Δ(τ)^(1/12) = (2π / 12^(1/4)) · J(τ)^(-1/12) · ₂F₁(1/12, 5/12; 1; 1/J(τ))`,
with all roots determined only up to roots of unity until the Main Theorem's connectedness
argument (paper Remark `bemwurzel`); here `Δ` is the *lattice* discriminant
`g₂³ - 27g₃² = (2π)¹² · Δ_Mathlib`. Raising to the 12th power and using
`1728·J = E₄³/Δ_Mathlib` (`Chudnovsky.mul_J_eq`) gives the branch-free equivalent
`E₄³ = F¹²`; the classical (and correct on `Region`) branch refinement is `E₄ = F⁴`, which is
what chapter 9 consumes after the PLAN A7 reformulation. TODO: if the final assembly of
`MainTheorem.lean` turns out to need the literal `Δ^(1/12)` statement (it uses `ωtilde₁ = Δ^(1/12)`
only through `F` and `dF/dJ`), add it here with an explicit principal-branch bookkeeping.
-/

@[expose] public section

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm

/-- **Kummer's solution** `b(J) = J^(-1/4) · (1-J)^(1/4) · ₂F₁(1/12, 5/12; 1; 1/J)` of the
Picard–Fuchs equation (paper Thm. `satzbj`), taken with principal-branch complex powers. -/
def kummerB (z : ℂ) : ℂ :=
  z ^ (-(1 / 4) : ℂ) * (1 - z) ^ ((1 / 4) : ℂ) * hyp2F1 z⁻¹

/-- On `Region`, the argument `1/J(τ)` of the hypergeometric function lies in the open unit
disc (via `Estimates.lean`'s `one_lt_norm_J`).
@isnad1 id=lt.1h1v.s4.60cf969d9ad6 from=translated src=- shape=119fd7b1 vocab=ce867bee
-/
theorem norm_inv_J_lt_one {τ : ℍ} (hτ : τ ∈ Region) : ‖(J τ)⁻¹‖ < 1 := by
  rw [norm_inv]
  exact inv_lt_one_of_one_lt₀ (one_lt_norm_J hτ)

/-! ### The branch-free `omegastrich`: `E₄ = ₂F₁(1/12, 5/12; 1; 1/J)⁴` on `Region`

The proof follows the "differentiate and compare" strategy of PLAN A7, in a *Wronskian*
form that needs no quantitative estimates near `i∞`:

1. Near `i∞`, the hypergeometric pair `(X, Y) = (F(1/J), F′(1/J))` (with
   `F = ₂F₁(1/12, 5/12; 1; ·)`) and the modular pair
   `(Xtilde, Ytilde) = (E₄^{1/4}, E₄^{1/4}·E₄³·(E₂E₄-E₆)/(12·(E₄³-E₆²)·E₆))` both solve the same
   linear 2×2 system `D Z = M(τ)·Z`: the first by the hypergeometric ODE and the chain
   rule with `D (1/J) = (1/J)·E₆/E₄` (from Ramanujan's identities), the second again by
   Ramanujan's identities.  Here `M₁₂ = (1/J)E₆/E₄`, `M₂₁ = (5/144)E₄²/E₆`,
   `M₂₂ = ((3/2)(1/J) - 1)·E₄²/E₆`, and the principal branch `E₄^{1/4}` is harmless
   since `E₄ ≈ 1` near `i∞`.
2. The Wronskian `w = XYtilde - YXtilde` solves the scalar ODE `D w = M₂₂·w` where `M₂₂ → -1`
   at `i∞`.  Along each vertical line `t ↦ x₀ + it` the function `t ↦ ‖w‖²·e^{-2πt}` is
   monotone nondecreasing (as soon as `Re M₂₂ ≤ -1/2`), while `w → 0` at `i∞` (both
   pairs converge to `(1, 5/144)`); hence `w ≡ 0`.
3. `w ≡ 0` forces `(Xtilde/X)′ = 0`, so `Xtilde/X` is constant `= 1` (its limit at `i∞`) on
   `{Im τ > A}`, whence `E₄ = Xtilde⁴ = X⁴` there — no fourth-root ambiguity survives the
   fourth power.
4. The identity spreads to all of `Region` by the identity theorem
   (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` on the half-plane
   `{5/4 < Im z}`, on which both sides are holomorphic since `‖J‖ > 1` there).

The only limit that is not pure soft analysis is `Ytilde → 5/144`, and even it needs no new
estimates: by `D E₄ = q·Φ′(q)` (`normalizedDeriv_eq_q_mul_deriv_cuspFunction`) with
`Φ′(0) = 240` (`E₄_qExpansion_coeff_one`), and `Δ/q = kfun → 1` (from `lemk`),
`(E₂E₄-E₆)/(E₄³-E₆²) = 3qΦ′(q)/(1728·q·kfun) → 720/1728 = 5/12`. -/

section OmegaStrich

open Filter Function EisensteinSeries Derivative SlashInvariantForm

open scoped Real Topology MatrixGroups CongruenceSubgroup ModularForm Manifold
  InnerProductSpace

/-! #### The two solution pairs, at the level of `ℂ` -/

/-- The hypergeometric solution `X = F(1/J)`. -/
private def XhC : ℂ → ℂ := fun z => hyp2F1 (J (ofComplex z))⁻¹

/-- Its companion `Y = F′(1/J)`. -/
private def YhC : ℂ → ℂ := fun z => deriv hyp2F1 (J (ofComplex z))⁻¹

/-- The modular solution `Xtilde = E₄^{1/4}` (principal branch). -/
private def XtC : ℂ → ℂ := fun z => E₄ (ofComplex z) ^ (1 / 4 : ℂ)

/-- Its companion `Ytilde = E₄^{1/4}·E₄³·(E₂E₄-E₆) / (12·(E₄³-E₆²)·E₆)`, the unique modular
expression with `D Xtilde = M₁₂·Ytilde`. -/
private def YtC : ℂ → ℂ := fun z =>
  E₄ (ofComplex z) ^ (1 / 4 : ℂ) * E₄ (ofComplex z) ^ 3
    * (E2 (ofComplex z) * E₄ (ofComplex z) - E₆ (ofComplex z))
    / (12 * (E₄ (ofComplex z) ^ 3 - E₆ (ofComplex z) ^ 2) * E₆ (ofComplex z))

/-- The Wronskian `w = X·Ytilde - Y·Xtilde` of the two pairs. -/
private def WrC : ℂ → ℂ := fun z => XhC z * YtC z - YhC z * XtC z

/-- The lower-right entry `M₂₂ = ((3/2)(1/J) - 1)·E₄²/E₆` of the coefficient matrix. -/
private def m22 (τ : ℍ) : ℂ := (3 / 2 * (J τ)⁻¹ - 1) * (E₄ τ ^ 2 / E₆ τ)

/-! #### Elementary algebra around `1/J` -/

/-! #### Derivatives of the Eisenstein series at the `ℂ`-level

These repackage the Ramanujan identities `deriv_comp_ofComplex_E2/E₄/E₆` as `HasDerivAt`
statements for the compositions with `ofComplex`, ready for the chain rule. -/

/-! #### The linear 2×2 system satisfied by both pairs -/

/-! #### Limits of the two pairs at `i∞`

All limits are soft consequences of `E₂, E₄, E₆ → 1` except `Ytilde → 5/144`, which uses the
cusp-function factorization of `D E₄` and `kfun → 1`. -/

/-! #### Small helpers for the "eventually" bookkeeping -/

/-! #### The vertical-line Wronskian argument -/

end OmegaStrich

end Chudnovsky
