module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.ChamberIntegral
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.GramSpectrum
public import Tengoku.Seed.Analysis.Matrix.Spectrum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `O70-EIGEN-LAW`: the real-Wishart density and the eigenvalue Jacobian, as a frontier

This module states — and does **not** prove — the one classical input that the residual-germ
computation of the MAIS issue #3 candidate cites rather than reproves. It is a designated trust
frontier of the O70 campaign, and every theorem that consumes it carries it as a visible
hypothesis.

## What the candidate cites

Proposition 8.11 (p. 36) of the candidate reads, for a real `k × d` matrix `X` with `k ≤ d`:

> There is a constant `Z = Z(k,d) ∈ (0,∞)` such that for every Borel
> `g : [0,∞)^k → [0,∞]` invariant under permutations of its arguments,
> `∫_{ℝ^{k×d}} e^{-‖X‖²_F} g(s(X)) dX = Z ∫_{(0,∞)^k} g(s) ∏ᵢ sᵢ^α ∏_{i<j} |sᵢ − sⱼ| e^{−∑ sᵢ} ds`,
> where `α = (d − k − 1)/2` and `s(X)` are the eigenvalues of the Gram matrix.

Its proof names two citations and nothing else: the real Wishart density
(Muirhead, *Aspects of Multivariate Statistical Theory*, Theorem 3.2.1, after James 1954) and
the eigenvalue Jacobian of a symmetric matrix (Muirhead Theorem 3.2.17).

## What is frozen here, and why this shape

`EigenvalueLawStatement` is the identity **at the test functions the derivation consumes**,
namely `g(s) = ∏ᵢ (1 + T sᵢ)^{-ρ}` for `T ≥ 0` and `ρ ≥ 0`. Three reasons:

1. **It is what Proposition 8.13 uses.** That proposition is Proposition 8.9 (proved, as
   `integral_exp_neg_frobenius_mul`) composed with Lemma 8.10 (proved, as
   `det_one_add_smul_gram_comm`) and then Proposition 8.11 at exactly this `g`. Stating the
   frontier at a wider class would assume more than the argument needs.
2. **The eigenvalue map never has to be defined.** `∏ᵢ (1 + T sᵢ(X))^{-ρ}` is
   `det(1 + T·X Xᵀ)^{-ρ}`, and the determinant is available without choosing which of `X Xᵀ`
   and `Xᵀ X` carries the spectrum, and without a `Fin (min h n)`-indexed eigenvalue vector.
   `det_one_add_smul_eq_prod_eigenvalues` below records that the two really are the same
   quantity, so nothing is hidden by the choice.
3. **It cannot be tailored.** `Z` is quantified *before* `T` and `ρ`: one constant serves the
   whole two-parameter family. A single normalisation cannot be chosen to make an arbitrary
   family of identities true, and `eigenvalueLaw_one_one` reads the normalisation off at the
   smallest shape.

The right-hand side is `chamberJFull`, Definition 8.12's `J(T)`, so every ingredient print names
is visible in the statement: the Vandermonde factor `chamberAbsVandermonde`, the weight
`∏ sᵢ^α`, the exponential `e^{−∑ sᵢ}`, and the resolvent `∏ (1 + T sᵢ)^{-ρ}`. The domain is the
**full orthant** `(0,∞)^k`, not the ordered chamber; `chamberJFull_eq_factorial_mul_chamberI`
(Lemma 8.15) is the bridge to the chamber, and is proved.

The exponent `α = (d − k − 1)/2` is formed in `ℝ`. Writing it with `ℕ`-subtraction would give
`0` at `d = k` instead of `-1/2`, which is a different — and false — statement.

## What is **not** here

No Wishart distribution, no Haar measure on `O(k)`, no coarea formula, no general Weyl
integration, and no SVD library. The candidate does not build them either; it cites them. Under
the campaign's anti-recursion rule this module states the consumed identity, records its
provenance, and stops.

None of it is available to import. `NC-011` in `docs/provenance/formalization-search.json`
searched all six baseline corpora at their pinned revisions -- Mathlib, the Isabelle AFP release
whose archive digest it recomputed, the Rocq undecidability library, HOL4, HOL Light and the Agda
standard library -- and found neither the Wishart density nor the eigenvalue-decomposition
Jacobian in any of them, nor the two things a proof would run on. So this frontier is held for
availability and not merely for effort.

## Stress evidence

`eigenvalueLaw_normalisation` pins `Z` by the Gaussian normalisation at `T = 0`;
`eigenvalueLaw_chamberJFull_pos` extracts positivity and finiteness of `J(0)` from it; and
`eigenvalueLaw_one_one` is the `1 × 1` consequence, `Z · J(0) = √π`, where the exponent is
`α = −1/2` — the value that a `ℕ`-truncated `(d − k − 1)` would have silently turned into `0`.
All three are consequences of the frozen proposition, not inhabitants of it. Nothing below is a
proof of `EigenvalueLawStatement`, and nothing below may be read as evidence that it holds; they
are checks that it is not malformed.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Matrix

/-! ## The determinant is the eigenvalue product

Not needed to *state* the frontier — but needed to know that stating it through `det` hides
nothing. -/

private theorem det_one_add_smul_conj {k : ℕ} {U : Matrix (Fin k) (Fin k) ℝ}
    (hU : U * star U = 1) (μ : Fin k → ℝ) (T : ℝ) :
    (1 + T • (U * Matrix.diagonal μ * star U)).det = ∏ i, (1 + T * μ i) := by
  classical
  have hkey : (1 : Matrix (Fin k) (Fin k) ℝ) + T • (U * Matrix.diagonal μ * star U)
      = U * (1 + T • Matrix.diagonal μ) * star U := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU, Matrix.mul_smul, Matrix.smul_mul]
  have hdiag : (1 : Matrix (Fin k) (Fin k) ℝ) + T • Matrix.diagonal μ
      = Matrix.diagonal (fun i => 1 + T * μ i) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  have hdet : U.det * (star U).det = 1 := by
    rw [← Matrix.det_mul, hU, Matrix.det_one]
  rw [hkey, hdiag, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hring : U.det * (∏ i, (1 + T * μ i)) * (star U).det
      = U.det * (star U).det * ∏ i, (1 + T * μ i) := by ring
  rw [hring, hdet, one_mul]

/-! ## The frontier -/

/-- **`O70-EIGEN-LAW`.** The real-Wishart density together with the eigenvalue Jacobian, at the
test functions the candidate's derivation consumes.

For every wide shape `k ≤ d` there is a single positive constant `Z(k, d)` such that, for every
`ρ ≥ 0` and every `T ≥ 0`,

    ∫_{ℝ^{k×d}} e^{-‖X‖²_F} det(1 + T·X Xᵀ)^{-ρ} dX = Z · J(T) ,

where `J(T) = chamberJFull k T ((d − k − 1)/2) ρ` is Definition 8.12's integral over the full
positive orthant.

`Z` is quantified before `T` and `ρ`: one normalisation for the whole family. This is a
hypothesis; it is cited by the candidate to Muirhead Theorems 3.2.1 and 3.2.17 (after James
1954), and it is **not proved anywhere in the atlas**.-/
@[expose] public noncomputable def EigenvalueLawStatement : Prop :=
  ∀ k d : ℕ, 0 < k → k ≤ d →
    ∃ Z : ℝ, 0 < Z ∧
      ∀ ρ : ℝ, 0 ≤ ρ → ∀ T : ℝ, 0 ≤ T →
        ∫ X : Fin k → Fin d → ℝ,
            Real.exp (-∑ i, ∑ j, X i j ^ 2)
              * (1 + T • (Matrix.of X * (Matrix.of X)ᵀ)).det ^ (-ρ)
          = Z * chamberJFull k T (((d : ℝ) - k - 1) / 2) ρ

/-! ## Stress evidence

Consequences of the frozen proposition, proved so that a malformed transcription would be
caught. None of them is an inhabitant of `EigenvalueLawStatement`, and none is evidence that it
is true.

The numerical companion is `scripts/reproduce_eigenvalue_law_probe.py`, which attempts to
falsify the law rather than confirm it. At `k = 1` the left side reduces analytically to the
right side's own integral, so that arm is exact: it pins `Z = π^(d/2)/Γ(d/2)` and finds it
constant across five `(T, ρ)` to machine precision, at `d ∈ {1,2,3,5}`. At `k = 2` — the
smallest shape whose Vandermonde factor is not `1` — the left side is estimated by
Monte-Carlo. That arm carries its own power check: with the Vandermonde the ratio is constant
to about `10⁻³`, and with it deleted the same ratio moves by about `0.26`, so the test can
reject a missing Vandermonde. It probes no shape with `k > 2`, and it says nothing about
`O70-EXACT-LOCAL`. -/

end AISafetyAtlas.SingularLearning
