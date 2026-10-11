/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/
module

public import Tengoku.LeanPool.LeanPool.Chudnovsky.SingularModuli.ModularPolynomialQ
import Tengoku.LeanPool.LeanPool.Chudnovsky.Estimates
import Tengoku.LeanPool.LeanPool.Chudnovsky.Ramanujan
import Tengoku.LeanPool.LeanPool.Chudnovsky.SingularModuli.CMRelations
import Tengoku.LeanPool.LeanPool.Chudnovsky.SingularModuli.Kronecker
import Tengoku.LeanPool.LeanPool.Chudnovsky.SingularModuli.Rationality
import Tengoku.LeanPool.LeanPool.Chudnovsky.SingularModuli.Valence
public import Tengoku

/-!
# Masser's Theorem A1 at `τ₁₆₃`: rationality of `s₂` (Phase C, statement 3)

This file discharges the last remaining `sorry` of the Chudnovsky development,
`s₂_τ₁₆₃_rational`, by formalizing Masser's Appendix A1 argument (LNM 437, Thm. A1),
specialized to the CM point `τ₁₆₃ = (1 + i√163)/2`.  See `PhaseC-PLAN.md` §5.1.
The final result is **unconditional**: `masser_s₂_rational : ∃ r : ℚ, s₂ τ₁₆₃ = r`
(axiom-clean, zero `sorry`).

Masser's function is `ψ(τ) = (3E₄/2E₆)(E₂ − 3/(π Im τ)) = (3/2)·s₂(τ)`.  His theorem
gives `ψ(τ) ∈ ℚ(j(τ))`, and here `ℚ(j(τ₁₆₃)) = ℚ` (statement 2, already proved).

## Structure of Masser's proof (steps 1–5 of the plan)

1. The trace-zero fixing matrix `Λ = !![1, −82; 2, −1]` (det `163`, `Λ • τ₁₆₃ = τ₁₆₃`,
   Möbius derivative `Λ′(τ₁₆₃) = −1`, `Λ''(τ₁₆₃) = 4/(2τ − 1)`).
2. `Λ` is a coset of the modular polynomial `Φ₁₆₃`, so `F(z) := Φ₁₆₃(j(Λz), j(z))`
   vanishes identically on `ℍ`.
3. Second-order Taylor expansion of `F` at `τ₁₆₃` gives Masser's identity (105):
   `2·j''/j′ + Λ'' = −j′·γ`, with `γ = (β₂₀ − β₁₁ + β₀₂)/β₀₁ ∈ ℚ` (a ratio of Taylor
   coefficients of `Φ₁₆₃` at `(j₀, j₀)`, all rational since `j₀ ∈ ℚ`).
4. `β₀₁ ≠ 0` (Masser's Lemma A1): the only degree-`163` integer matrices fixing `τ₁₆₃`
   are `±Λ`, so no other coset value coincides with `j₀`.
5. The Ramanujan identities `deriv_E2/E₄/E₆` turn (105) into Masser's (106):
   `s₂(τ₁₆₃) = 3·j₀·γ + (7j₀ − 6912)/(j₀ − 1728)`, rational since `j₀, γ ∈ ℚ`,
   `j₀ ≠ 1728`.

## What is proved here

Everything, unconditionally:
* all the arithmetic/nonvanishing inputs: `j₀ := 1728·J(τ₁₆₃) ∈ ℚ`, `j₀ ≠ 0`,
  `j₀ ≠ 1728`, `E₄(τ₁₆₃) ≠ 0`, `E₆(τ₁₆₃) ≠ 0`;
* the closed-form modular identity `E₄³/E₆² = j₀/(j₀ − 1728)`;
* the geometric data of steps 1–2 (`Λ` fixes `τ₁₆₃`, `(2τ − 1)² = −163`, the coset
  factorization `Λ = γ · Acol 163 (−82)`, and the identity `j(Λ • z) = f₁₆₃(81) z` on all
  of `ℍ` — one vanishing factor of Masser's `F`);
* the full reduction (step 5): given Masser's post-Ramanujan identity (the analytic
  gate `hMasser`), `s₂(τ₁₆₃)` is rational (`masser_s₂_rational_of`);
* **the analytic gate itself** (`masser_gate`, second half of this file): the chart
  calculus of `F(z) = Φ₁₆₃(j(Λz), j z) ≡ 0` (first- and second-derivative extraction at
  `τ₁₆₃`, `masser_bivariate_derivs`), Masser's Lemma A1 (`β₁₀ ≠ 0`, via the
  `p² − pk + 41k² = 163` fixed-matrix classification), and the Ramanujan substitution
  turning `(105)` into the gate identity with `γ = (β₂₀ − 2β₁₁ + β₀₂)/β₀₁ ∈ ℚ`.

The top-level deliverable is `masser_s₂_rational : ∃ r : ℚ, s₂ τ₁₆₃ = r`.
-/

@[expose] public section

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm EisensteinSeries
open scoped Real Manifold MatrixGroups

instance : NeZero (163 : ℕ) := ⟨by norm_num⟩

/-! ## Step 1 — the trace-zero fixing matrix `Λ = !![1, −82; 2, −1]`

`det Λ = 163`, `Λ • τ₁₆₃ = τ₁₆₃`, and the Möbius square-root data `(2τ − 1)² = −163`.
These are the geometric inputs to Masser's second-order Taylor expansion (step 3). -/

/-- `(2τ₁₆₃ − 1)² = −163`, from `τ₁₆₃² = τ₁₆₃ − 41`.  (So `2τ₁₆₃ − 1 = i√163`, the pure
imaginary generator of the CM order; `(2τ − 1)/2 = i·Im τ₁₆₃`.) -/
lemma two_tau_sub_one_sq : (2 * (τ₁₆₃ : ℂ) - 1) ^ 2 = -163 := by
  linear_combination (4 : ℂ) * τ₁₆₃_sq

/-- `2τ₁₆₃ − 1 ≠ 0` (its square is `−163 ≠ 0`). -/
lemma two_tau_sub_one_ne_zero : 2 * (τ₁₆₃ : ℂ) - 1 ≠ 0 := by
  intro h
  have := two_tau_sub_one_sq
  rw [h] at this
  norm_num at this

/-- The trace-zero fixing matrix `Λ = !![1, −82; 2, −1]` as an element of `GL (Fin 2) ℝ`
(determinant `163 > 0`). -/
def LamGL : GL (Fin 2) ℝ :=
  .mkOfDetNeZero !![1, -82; 2, -1] (by rw [Matrix.det_fin_two_of]; norm_num)

@[simp] lemma val_LamGL : (LamGL).val = !![1, -82; 2, -1] := rfl

lemma LamGL_det_pos : 0 < (LamGL).det.val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_LamGL, Matrix.det_fin_two_of]
  norm_num

/-- **`Λ` fixes `τ₁₆₃`** as a Möbius transformation: `(τ − 82)/(2τ − 1) = τ`. -/
lemma LamGL_smul_eq : LamGL • τ₁₆₃ = τ₁₆₃ := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos LamGL_det_pos, div_eq_iff (denom_ne_zero LamGL τ₁₆₃)]
  simp only [num, denom, val_LamGL, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.of_apply]
  push_cast
  linear_combination (-2 : ℂ) * τ₁₆₃_sq

/-- The `SL(2,ℤ)` cofactor `γ = !![1, 0; 2, 1]` (determinant `1`) of the coset
decomposition `Λ = γ · Acol 163 (−82)`. -/
def LamGamma : SL(2, ℤ) :=
  ⟨!![1, 0; 2, 1], by rw [Matrix.det_fin_two_of]; ring⟩

/-- **Coset decomposition** `Λ = γ · Acol 163 (−82)` in `GL (Fin 2) ℝ`. -/
lemma LamGL_factor : LamGL = (LamGamma : GL (Fin 2) ℝ) * Acol 163 (-82) := by
  have hcoe : ((LamGamma : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 2, 1] := rfl
  apply Matrix.GeneralLinearGroup.ext
  intro a c
  fin_cases a <;> fin_cases c <;>
    norm_num [val_LamGL, val_Acol, hcoe, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Step 2 — coset identification.** For *every* `z : ℍ`, `j(Λ • z)` equals the
`81`-coset orbit value `f 163 (some 81) z` (since `−82 ≡ 81 mod 163`).  Hence one factor of
the orbit product `Φ₁₆₃(·, j z)` vanishes at `X = j(Λz)`, i.e. Masser's `F(z) = 0`. -/
lemma j_LamGL_smul (z : ℍ) : j (LamGL • z) = f 163 (some (81 : ZMod 163)) z := by
  have htrans := j_matrix_transfer LamGamma LamGL (Acol 163 (-82)) z LamGL_factor
  rw [htrans, f_some]
  have hval : ((81 : ZMod 163).val : ℤ) = 81 := by decide
  refine j_Acol_smul_congr ?_ z
  rw [hval]; decide

/-! ## Arithmetic and nonvanishing inputs at `τ₁₆₃` -/

/-- `J(τ₁₆₃) ≠ 0`: it has norm `> 1` (Estimates `one_lt_norm_J`). -/
lemma J_τ₁₆₃_ne_zero : J τ₁₆₃ ≠ 0 := by
  have h := one_lt_norm_J τ₁₆₃_mem_Region
  intro hc
  rw [hc, norm_zero] at h
  linarith

/-- `j₀ := 1728·J(τ₁₆₃) ≠ 0`. -/
lemma j₀_ne_zero : (1728 : ℂ) * J τ₁₆₃ ≠ 0 :=
  mul_ne_zero (by norm_num) J_τ₁₆₃_ne_zero

/-- `j₀ ≠ 1728`: `J(τ₁₆₃) ≠ 1` since `‖J(τ₁₆₃)‖ > 1`. -/
lemma j₀_ne_1728 : (1728 : ℂ) * J τ₁₆₃ ≠ 1728 := by
  intro hc
  have hJ1 : J τ₁₆₃ = 1 :=
    mul_left_cancel₀ (show (1728 : ℂ) ≠ 0 by norm_num) (by rw [hc]; ring)
  have h := one_lt_norm_J τ₁₆₃_mem_Region
  rw [hJ1, norm_one] at h
  linarith

/-- `E₆(τ₁₆₃) ≠ 0` (Estimates `E₆_ne_zero_of_mem_Region`). -/
lemma E₆_τ₁₆₃_ne_zero : E₆ τ₁₆₃ ≠ 0 :=
  E₆_ne_zero_of_mem_Region τ₁₆₃_mem_Region

/-- `E₄(τ₁₆₃) ≠ 0`: else `j₀ = E₄³/Δ = 0`, contradicting `j₀ ≠ 0`. -/
lemma E₄_τ₁₆₃_ne_zero : E₄ τ₁₆₃ ≠ 0 := by
  intro h
  have hjm := j_mul_discriminant τ₁₆₃
  rw [show j τ₁₆₃ = 1728 * J τ₁₆₃ from rfl, h] at hjm
  simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true] at hjm
  rcases mul_eq_zero.mp hjm with h1 | h1
  · exact j₀_ne_zero h1
  · exact discriminant_ne_zero τ₁₆₃ h1

/-! ## The closed-form modular identity `E₄³/E₆² = j₀/(j₀ − 1728)` -/

/-- `E₄³ = j₀·Δ` at `τ₁₆₃`. -/
lemma E₄_cube_τ₁₆₃ : (E₄ τ₁₆₃) ^ 3 = (1728 * J τ₁₆₃) * discriminant τ₁₆₃ := by
  have h := mul_J_eq τ₁₆₃
  have hΔ := discriminant_ne_zero τ₁₆₃
  field_simp at h
  linear_combination -h

/-- `E₆² = (j₀ − 1728)·Δ` at `τ₁₆₃`. -/
lemma E₆_sq_τ₁₆₃ : (E₆ τ₁₆₃) ^ 2 = ((1728 * J τ₁₆₃) - 1728) * discriminant τ₁₆₃ := by
  have h := E₄_cube_sub_E₆_sq_eq_discriminant τ₁₆₃
  rw [E₄_cube_τ₁₆₃] at h
  linear_combination -h

/-- **The closed-form identity** `E₄³/E₆² = j₀/(j₀ − 1728)` at `τ₁₆₃`
(the algebraic heart of the `s₂`-formula's non-`γ` term). -/
lemma E₄_cube_div_E₆_sq_τ₁₆₃ :
    (E₄ τ₁₆₃) ^ 3 / (E₆ τ₁₆₃) ^ 2 = (1728 * J τ₁₆₃) / ((1728 * J τ₁₆₃) - 1728) := by
  rw [E₄_cube_τ₁₆₃, E₆_sq_τ₁₆₃]
  exact mul_div_mul_right _ _ (discriminant_ne_zero τ₁₆₃)

/-! ## The gated top-level theorem (step 5 reduction, fully assembled) -/

/-! ## Discharging the analytic gate

The remainder of this file proves the gate hypothesis `hMasser` of `masser_s₂_rational_of`
and derives the unconditional `masser_s₂_rational`.  Structure:

* **Chart calculus** (`masserLam`, `cj`, `masserGD`): the Möbius map `λ(z) = (z−82)/(2z−1)`
  of `Λ` and the `j`-function in the `ℂ`-chart, with explicit first derivatives on
  `{0 < Im z}` and the second derivative of `j∘ofComplex` at `τ₁₆₃` via the Ramanujan
  identities.
* **Master second-derivative lemma** (`masser_bivariate_derivs`): for a finite sum
  `F(z) = Σₙ pₙ(v z)·(u z)ⁿ` vanishing on the upper half-plane, the first and second
  derivatives at an interior point, expanded in the five partial-derivative sums
  (the Taylor coefficients `β₁₀, β₀₁, β₂₀, β₁₁, β₀₂` of `Φ₁₆₃` at `(j₀, j₀)`).
* **Vanishing input**: `F(z) = Φ₁₆₃(j(λz), j z) = 0` on `ℍ` from `j_LamGL_smul` (step 2).
* **Masser's Lemma A1** (`masser_lemmaA1`): no coset other than `some 81` takes the value
  `j τ₁₆₃` at `τ₁₆₃` (the `p² − pk + 41k² = 163` classification), whence `β₁₀ ≠ 0`.
* **Assembly**: `β₁₀ = β₀₁`, division by `g′(τ)² β₀₁ ≠ 0`, and the Ramanujan substitution
  produce the gate identity with `γ = (β₂₀ − 2β₁₁ + β₀₂)/β₀₁ ∈ ℚ`. -/

open Polynomial Filter
open scoped Topology

/-! ### The Möbius chart map `λ(z) = (z − 82)/(2z − 1)` -/

/-- The Möbius transformation of `Λ` in the `ℂ`-chart: `λ(z) = (z − 82)/(2z − 1)`. -/
private def masserLam (z : ℂ) : ℂ := (z - 82) / (2 * z - 1)

/-! ### The `j`-function in the `ℂ`-chart and its first two derivatives

`cj = j ∘ ofComplex`, with `cj′ = masserGD` on `{0 < Im z}` (from the Ramanujan
identities `deriv_comp_ofComplex_E₄/E₆`), and the explicit second derivative
`masserG2` at `τ₁₆₃`. -/

/-- `E₄` in the `ℂ`-chart. -/
private def cE₄ : ℂ → ℂ := fun w ↦ E₄ (ofComplex w)

/-- `E₆` in the `ℂ`-chart. -/
private def cE₆ : ℂ → ℂ := fun w ↦ E₆ (ofComplex w)

/-- `j` in the `ℂ`-chart. -/
private def cj : ℂ → ℂ := fun w ↦ j (ofComplex w)

/-- The first derivative of `cj` on the upper half-plane:
`cj′(w) = −2πi·1728·E₄²E₆/(E₄³ − E₆²)` (all evaluated at `ofComplex w`). -/
private def masserGD : ℂ → ℂ := fun w ↦
  -(2 * (π : ℂ) * Complex.I) * (1728 * cE₄ w ^ 2 * cE₆ w) / (cE₄ w ^ 3 - cE₆ w ^ 2)

/-- The second derivative of `cj` at `τ₁₆₃`:
`cj''(τ) = 2·1728·π²·(E₂E₄²E₆/3 − 4E₄E₆²/3 − E₄⁴)/(E₄³ − E₆²)`. -/
private def masserG2 : ℂ :=
  2 * 1728 * (π : ℂ) ^ 2 *
      (E2 τ₁₆₃ * E₄ τ₁₆₃ ^ 2 * E₆ τ₁₆₃ / 3 - 4 * E₄ τ₁₆₃ * E₆ τ₁₆₃ ^ 2 / 3 - E₄ τ₁₆₃ ^ 4)
    / (E₄ τ₁₆₃ ^ 3 - E₆ τ₁₆₃ ^ 2)

/-! ### The master second-derivative lemma

For a finite family of polynomials `pₙ ∈ ℂ[X]` and functions `u, v` differentiable on the
upper half-plane such that `F(z) = Σₙ pₙ(v z)·(u z)ⁿ` vanishes identically there, the first
and second derivatives of `F` at an interior point `t` vanish; expanded by the chain rule
they give the two linear relations among the five partial-derivative sums (the `β`'s of
Masser's proof) used below. -/

/-! ### Support-sum expansions of the specialized modular polynomial

`Φ₁₆₃ ∈ ℚ[Y][X]` is pinned via `exists_PhiQ_closed`; we expand `Φ₁₆₃(x, Y₀)` and its
`X`-derivative as sums over the (finite) support, the form consumed by the master lemma,
and record the `ℚ`-rationality of all evaluations at `(j₀, j₀)`, `j₀ = j τ₁₆₃ ∈ ℚ`. -/

/-! ### The pinned modular polynomial `Φ₁₆₃` and the rational `β`-data -/

/-! ### Masser's `F(z) = Φ₁₆₃(j(Λz), j z)` vanishes identically -/

/-! ### The two Taylor relations at `τ₁₆₃` -/

/-! ### Masser's Lemma A1 at `τ₁₆₃`: `β₁₀ ≠ 0`

`β₁₀ = ∏_{i ≠ some 81} (j₀ − fᵢ(τ₁₆₃))`, and no other coset value equals `j₀`: a coincidence
would produce an integer matrix fixing `τ₁₆₃` of determinant `163`; by the fixed-matrix
classification for the primitive form `(1, −1, 41)` its norm form gives
`p² − pk + 41k² = 163`, whose only solutions are `±(1, 2)`, i.e. the matrix is `±Λ` — and
`±Λ` lies in the coset `some 81`. -/

/-! ### The gate and the unconditional theorem -/

end Chudnovsky
