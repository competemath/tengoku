import Tengoku.Nlalib.NLAlib.Krylov.Solvers.PolynomialMethods

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The coupled Chebyshev iteration and its exact bounds

The scalar `ρ` recursion and the coupled direction/iterate recursion are implemented directly.
Their iterates equal the existing normalized-Chebyshev polynomial iterates, proving the
algorithm realization as well as the exact reciprocal-Chebyshev residual and energy bounds.

Source: Saad (2003), §12.3, Algorithm 12.1; Golub–Varga (1961).
Atlas: `chebyshev-iteration`.
-/

noncomputable section

open scoped Matrix Polynomial
open Polynomial

namespace NLAlib

/-- Scalar coefficients of Chebyshev iteration: `ρ₀ = 1/σ` and
`ρₖ₊₁ = 1/(2σ - ρₖ)`, where `σ = (b+a)/(b-a)`. Inverses are total; the positive-interval
hypotheses in the realization theorem exclude zero denominators.
Source: Saad (2003), Algorithm 12.1.
atlas: chebyshev-iteration (partial)-/
def chebyshevRho (a b : ℝ) : ℕ → ℝ
  | 0 => ((b + a) / (b - a))⁻¹
  | k + 1 => (2 * ((b + a) / (b - a)) - chebyshevRho a b k)⁻¹

/-- Initial scalar coefficient of the Chebyshev recursion.
@isnad1 id=eq.0h2v.s5.a931ac794a63 from=translated src=- shape=a8a47941 vocab=7d479df8
-/
@[simp] theorem chebyshevRho_zero (a b : ℝ) :
    chebyshevRho a b 0 = ((b + a) / (b - a))⁻¹ := rfl

/-- The scalar coefficient satisfies the advertised reciprocal recursion.
@isnad1 id=eq.0h3v.s6.89aeba0e19e9 from=translated src=- shape=20db8ec4 vocab=21692653
-/
theorem chebyshevRho_succ (a b : ℝ) (k : ℕ) :
    chebyshevRho a b (k + 1) =
      (2 * ((b + a) / (b - a)) - chebyshevRho a b k)⁻¹ := rfl

private theorem eval_T_nat_add_two (σ : ℝ) (k : ℕ) :
    (Chebyshev.T ℝ ((k + 2 : ℕ) : ℤ)).eval σ =
      2 * σ * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval σ -
        (Chebyshev.T ℝ (k : ℤ)).eval σ := by
  rw [show ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 by omega, Chebyshev.T_add_two,
    show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by omega]
  simp

private theorem eval_T_center_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) (k : ℕ) :
    0 < (Chebyshev.T ℝ (k : ℤ)).eval ((b + a) / (b - a)) :=
  zero_lt_one.trans_le (Chebyshev.one_le_eval_T_real _
    (by rw [one_le_div (by linarith)]; linarith))

/-- The recursively computed scalar is the ratio `Tₖ(σ)/Tₖ₊₁(σ)`.
Source: Saad (2003), Algorithm 12.1 and the Chebyshev three-term identity.
atlas: chebyshev-iteration (partial)
@isnad1 id=eq.2h3v.s7.36eb22f36aaa from=translated src=- shape=8f2024b2 vocab=3f595234
-/
theorem chebyshevRho_eq_eval_T_div_eval_T_succ {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (k : ℕ) :
    chebyshevRho a b k = (Chebyshev.T ℝ (k : ℤ)).eval ((b + a) / (b - a)) /
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval ((b + a) / (b - a)) := by
  induction k with
  | zero => simp [chebyshevRho, Chebyshev.T_zero, Chebyshev.T_one, one_div]
  | succ k ih =>
    rw [chebyshevRho_succ, ih]
    have hτ := (eval_T_center_pos ha hab (k + 1)).ne'
    have hden :
        2 * ((b + a) / (b - a)) -
            (Chebyshev.T ℝ (k : ℤ)).eval ((b + a) / (b - a)) /
              (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval ((b + a) / (b - a)) =
          (Chebyshev.T ℝ ((k + 2 : ℕ) : ℤ)).eval ((b + a) / (b - a)) /
            (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval ((b + a) / (b - a)) := by
      rw [eval_T_nat_add_two]
      field_simp
    rw [hden, inv_div]

/-- Positive spectral endpoints give positive scalar coefficients at every step.
atlas: chebyshev-iteration (partial)
@isnad1 id=lt.2h3v.s5.88d78c447c5d from=translated src=- shape=5788bb3c vocab=ce7f4d1c
-/
theorem chebyshevRho_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) (k : ℕ) :
    0 < chebyshevRho a b k := by
  rw [chebyshevRho_eq_eval_T_div_eval_T_succ ha hab]
  exact div_pos (eval_T_center_pos ha hab k) (eval_T_center_pos ha hab (k + 1))

/-- Every denominator in the scalar Chebyshev recursion is positive on a positive interval.
atlas: chebyshev-iteration (partial)
@isnad1 id=lt.2h3v.s6.062aa31fd6ec from=translated src=- shape=040964d0 vocab=310db1dc
-/
theorem two_mul_div_sub_chebyshevRho_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) (k : ℕ) :
    0 < 2 * ((b + a) / (b - a)) - chebyshevRho a b k := by
  exact inv_pos.mp (chebyshevRho_pos ha hab (k + 1))

variable {n : Type*} [Fintype n] [DecidableEq n]

private def chebyshevRecurrenceState (a b : ℝ) (A : Matrix n n ℝ) (c x₀ : n → ℝ) :
    ℕ → (n → ℝ) × (n → ℝ)
  | 0 => (x₀, (2 / (b + a)) • (c - A *ᵥ x₀))
  | k + 1 =>
      let s := chebyshevRecurrenceState a b A c x₀ k
      let x := s.1 + s.2
      (x, (chebyshevRho a b (k + 1) * chebyshevRho a b k) • s.2 +
        (4 * chebyshevRho a b (k + 1) / (b - a)) • (c - A *ᵥ x))

/-- The actual coupled Chebyshev iterate, with one matrix-vector residual evaluation per step.
Source: Saad (2003), Algorithm 12.1.
atlas: chebyshev-iteration (partial)-/
def chebyshevRecurrenceIterate (a b : ℝ) (A : Matrix n n ℝ) (c x₀ : n → ℝ) (k : ℕ) : n → ℝ :=
  (chebyshevRecurrenceState a b A c x₀ k).1

/-- The direction in the coupled Chebyshev method, initialized by `d₀ = r₀/θ`.
Source: Saad (2003), Algorithm 12.1.-/
def chebyshevRecurrenceDirection (a b : ℝ) (A : Matrix n n ℝ) (c x₀ : n → ℝ) (k : ℕ) : n → ℝ :=
  (chebyshevRecurrenceState a b A c x₀ k).2

omit [DecidableEq n] in
/-- The coupled Chebyshev method begins at `x₀`.
@isnad1 id=eq.0h6v.s5.71bf1b8e9709 from=translated src=- shape=9d928537 vocab=05ecaaec
-/
@[simp] theorem chebyshevRecurrenceIterate_zero (a b : ℝ) (A : Matrix n n ℝ)
    (c x₀ : n → ℝ) : chebyshevRecurrenceIterate a b A c x₀ 0 = x₀ := rfl

omit [DecidableEq n] in
/-- The first direction is `r₀/θ`, with `θ = (b+a)/2`.
@isnad1 id=eq.0h6v.s6.99ca02124ff1 from=translated src=- shape=1d53287e vocab=67984c1d
-/
@[simp] theorem chebyshevRecurrenceDirection_zero (a b : ℝ) (A : Matrix n n ℝ)
    (c x₀ : n → ℝ) :
    chebyshevRecurrenceDirection a b A c x₀ 0 = (2 / (b + a)) • (c - A *ᵥ x₀) := rfl

omit [DecidableEq n] in
/-- Each actual coupled step updates `xₖ₊₁ = xₖ + dₖ`.
atlas: chebyshev-iteration (partial)
@isnad1 id=eq.0h7v.s6.4f040e48f357 from=translated src=- shape=2684f6ac vocab=ffa1fc6d
-/
theorem chebyshevRecurrenceIterate_succ (a b : ℝ) (A : Matrix n n ℝ)
    (c x₀ : n → ℝ) (k : ℕ) :
    chebyshevRecurrenceIterate a b A c x₀ (k + 1) =
      chebyshevRecurrenceIterate a b A c x₀ k + chebyshevRecurrenceDirection a b A c x₀ k := rfl

omit [DecidableEq n] in
/-- The actual directions satisfy `dₖ₊₁ = ρₖ₊₁ρₖdₖ + (2ρₖ₊₁/δ)rₖ₊₁`.
Source: Saad (2003), Algorithm 12.1.
atlas: chebyshev-iteration (partial)
@isnad1 id=eq.0h7v.s7.58badee36790 from=translated src=- shape=7fbf2021 vocab=605cd5df
-/
theorem chebyshevRecurrenceDirection_succ (a b : ℝ) (A : Matrix n n ℝ)
    (c x₀ : n → ℝ) (k : ℕ) :
    chebyshevRecurrenceDirection a b A c x₀ (k + 1) =
      (chebyshevRho a b (k + 1) * chebyshevRho a b k) •
          chebyshevRecurrenceDirection a b A c x₀ k +
        (4 * chebyshevRho a b (k + 1) / (b - a)) •
          (c - A *ᵥ chebyshevRecurrenceIterate a b A c x₀ (k + 1)) := rfl

private theorem chebyshevIterate_sub_succ {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (A : Matrix n n ℝ) (c x₀ : n → ℝ) (k : ℕ) :
    chebyshevIterate a b A c x₀ (k + 2) - chebyshevIterate a b A c x₀ (k + 1) =
      (chebyshevRho a b (k + 1) * chebyshevRho a b k) •
          (chebyshevIterate a b A c x₀ (k + 1) - chebyshevIterate a b A c x₀ k) +
        (4 * chebyshevRho a b (k + 1) / (b - a)) •
          (c - A *ᵥ chebyshevIterate a b A c x₀ (k + 1)) := by
  rw [chebyshevRho_eq_eval_T_div_eval_T_succ ha hab (k + 1),
    chebyshevRho_eq_eval_T_div_eval_T_succ ha hab k]
  let τ₀ := (Chebyshev.T ℝ (k : ℤ)).eval ((b + a) / (b - a))
  let τ₁ := (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval ((b + a) / (b - a))
  let τ₂ := (Chebyshev.T ℝ ((k + 2 : ℕ) : ℤ)).eval ((b + a) / (b - a))
  have hτ₁ : τ₁ ≠ 0 := (eval_T_center_pos ha hab (k + 1)).ne'
  have hτ₂ : τ₂ ≠ 0 := (eval_T_center_pos ha hab (k + 2)).ne'
  have hba : b - a ≠ 0 := by linarith
  have hcoef : 4 / (b - a) * τ₁ * ((b + a) / 2) = τ₂ + τ₀ := by
    have ht := eval_T_nat_add_two ((b + a) / (b - a)) k
    have hs : 4 / (b - a) * τ₁ * ((b + a) / 2) =
        2 * ((b + a) / (b - a)) * τ₁ := by field_simp; ring
    rw [hs]
    change τ₂ = 2 * ((b + a) / (b - a)) * τ₁ - τ₀ at ht
    linarith
  have hprod : τ₂ * (τ₁ / τ₂ * (τ₀ / τ₁)) = τ₀ := by field_simp
  have hprod' : τ₂ * (4 * (τ₁ / τ₂) / (b - a)) = 4 / (b - a) * τ₁ := by field_simp
  have hx₂ := chebyshevIterate_add_two ha hab A c x₀ k
  change chebyshevIterate a b A c x₀ (k + 2) = τ₂⁻¹ •
    ((4 / (b - a) * τ₁) • (((b + a) / 2) • chebyshevIterate a b A c x₀ (k + 1) +
      (c - A *ᵥ chebyshevIterate a b A c x₀ (k + 1))) -
      τ₀ • chebyshevIterate a b A c x₀ k) at hx₂
  change _ = (τ₁ / τ₂ * (τ₀ / τ₁)) • _ + (4 * (τ₁ / τ₂) / (b - a)) • _
  apply smul_right_injective (M := n → ℝ) hτ₂
  change τ₂ • (chebyshevIterate a b A c x₀ (k + 2) -
      chebyshevIterate a b A c x₀ (k + 1)) =
    τ₂ • ((τ₁ / τ₂ * (τ₀ / τ₁)) •
      (chebyshevIterate a b A c x₀ (k + 1) - chebyshevIterate a b A c x₀ k) +
      (4 * (τ₁ / τ₂) / (b - a)) • (c - A *ᵥ chebyshevIterate a b A c x₀ (k + 1)))
  rw [smul_sub, hx₂]
  simp only [smul_smul, mul_inv_cancel₀ hτ₂, one_smul]
  simp only [smul_add, smul_sub, smul_smul, hprod, hprod', hcoef, add_smul]
  abel

private theorem chebyshevRecurrence_eq_polynomial_pair {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (A : Matrix n n ℝ) (c x₀ : n → ℝ) (k : ℕ) :
    chebyshevRecurrenceIterate a b A c x₀ k = chebyshevIterate a b A c x₀ k ∧
    chebyshevRecurrenceDirection a b A c x₀ k =
      chebyshevIterate a b A c x₀ (k + 1) - chebyshevIterate a b A c x₀ k := by
  induction k with
  | zero =>
    constructor
    · simp only [chebyshevRecurrenceIterate_zero, chebyshevIterate_zero]
    · rw [chebyshevRecurrenceDirection_zero, chebyshevIterate_one ha hab,
        chebyshevIterate_zero]
      abel
  | succ k ih =>
    have hx : chebyshevRecurrenceIterate a b A c x₀ (k + 1) =
        chebyshevIterate a b A c x₀ (k + 1) := by
      rw [chebyshevRecurrenceIterate_succ, ih.1, ih.2]
      abel
    refine ⟨hx, ?_⟩
    rw [chebyshevRecurrenceDirection_succ, ih.2, hx]
    exact (chebyshevIterate_sub_succ ha hab A c x₀ k).symm

/-- The explicitly implemented coupled `ρₖ,dₖ,xₖ` algorithm realizes the normalized Chebyshev
polynomial iterate at every step. No matrix positivity assumption is needed for this algebraic
realization. Source: Saad (2003), Algorithm 12.1.
atlas: chebyshev-iteration (partial)
@isnad1 id=eq.2h7v.s6.d9fd944d71d9 from=translated src=- shape=91878bbf vocab=1ae5e3a6
-/
theorem chebyshevRecurrenceIterate_eq_chebyshevIterate {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (A : Matrix n n ℝ) (c x₀ : n → ℝ) (k : ℕ) :
    chebyshevRecurrenceIterate a b A c x₀ k = chebyshevIterate a b A c x₀ k :=
  (chebyshevRecurrence_eq_polynomial_pair ha hab A c x₀ k).1

/-- The actual recurrence has exactly the normalized Chebyshev residual polynomial.
Source: Saad (2003), §12.3.
atlas: chebyshev-iteration (partial)
@isnad1 id=eq.2h7v.s8.190c546fbf84 from=translated src=- shape=f86c037e vocab=6d2c7963
-/
theorem sub_mulVec_chebyshevRecurrenceIterate {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (A : Matrix n n ℝ) (c x₀ : n → ℝ) (k : ℕ) :
    c - A *ᵥ chebyshevRecurrenceIterate a b A c x₀ k =
      aeval A (chebyshevResidual a b k) *ᵥ (c - A *ᵥ x₀) := by
  rw [chebyshevRecurrenceIterate_eq_chebyshevIterate ha hab,
    sub_mulVec_chebyshevIterate ha hab]

/-- The exact reciprocal-Chebyshev residual bound holds for the actual coupled recurrence.
Source: Saad (2003), §12.3.
atlas: chebyshev-iteration (partial)
@isnad1 id=le.4h7v.s8.8247469b1570 from=translated src=- shape=b0071ce2 vocab=cac00c7b
-/
theorem norm_sub_mulVec_chebyshevRecurrenceIterate_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b) (c x₀ : n → ℝ) (k : ℕ) :
    ‖WithLp.toLp 2 (c - A *ᵥ chebyshevRecurrenceIterate a b A c x₀ k)‖ ≤
      (1 / (Chebyshev.T ℝ (k : ℤ)).eval ((b + a) / (b - a))) *
        ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖ := by
  rw [sub_mulVec_chebyshevRecurrenceIterate ha hab]
  have hsq := dotProduct_aeval_mulVec_self_le hA (p := chebyshevResidual a b k) hspec
    (fun x hx => abs_eval_chebyshevResidual_le ha hab hx) (c - A *ᵥ x₀)
  have hnonneg : 0 ≤ 1 / (Chebyshev.T ℝ (k : ℤ)).eval ((b + a) / (b - a)) :=
    (one_div_pos.mpr (eval_T_center_pos ha hab k)).le
  rw [← norm_toLp_sq_eq_dotProduct_self, ← norm_toLp_sq_eq_dotProduct_self] at hsq
  nlinarith [norm_nonneg (WithLp.toLp 2 (aeval A (chebyshevResidual a b k) *ᵥ (c - A *ᵥ x₀))),
    mul_nonneg hnonneg (norm_nonneg (WithLp.toLp 2 (c - A *ᵥ x₀)))]

/-- The explicit coupled recurrence has the usual condition-number residual rate.
Source: Saad (2003), §12.3.
atlas: chebyshev-iteration (partial)
@isnad1 id=le.4h7v.s8.50d1bca5dca4 from=translated src=- shape=4472921b vocab=b8d20199
-/
theorem norm_sub_mulVec_chebyshevRecurrenceIterate_le_two_mul_pow
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b) (c x₀ : n → ℝ) (k : ℕ) :
    ‖WithLp.toLp 2 (c - A *ᵥ chebyshevRecurrenceIterate a b A c x₀ k)‖ ≤
      (2 * ((√b - √a) / (√b + √a)) ^ k) * ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖ :=
  (norm_sub_mulVec_chebyshevRecurrenceIterate_le hA ha hab hspec c x₀ k).trans
    (mul_le_mul_of_nonneg_right (inv_eval_T_real_le_two_mul_pow k ha hab) (norm_nonneg _))

/-- The exact reciprocal-Chebyshev factor also bounds squared `A` energy of the actual
recurrence error. Source: Saad (2003), §12.3.
atlas: chebyshev-iteration (partial)
@isnad1 id=le.5h8v.s8.606a80560c12 from=translated src=- shape=cb9a30f8 vocab=cc47d5ce
-/
theorem quadForm_chebyshevRecurrenceIterate_sub_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b) {c xs : n → ℝ}
    (hxs : A *ᵥ xs = c) (x₀ : n → ℝ) (k : ℕ) :
    quadForm A (chebyshevRecurrenceIterate a b A c x₀ k - xs) ≤
      (1 / (Chebyshev.T ℝ (k : ℤ)).eval ((b + a) / (b - a))) ^ 2 *
        quadForm A (x₀ - xs) := by
  rw [chebyshevRecurrenceIterate_eq_chebyshevIterate ha hab,
    chebyshevIterate_sub ha hab hxs]
  exact quadForm_aeval_mulVec_le hA (fun x hx => ha.le.trans hx.1) hspec
    (fun x hx => abs_eval_chebyshevResidual_le ha hab hx) (x₀ - xs)

/-- The actual recurrence has the usual condition-number rate in squared `A` energy.
Source: Saad (2003), §12.3.
atlas: chebyshev-iteration (partial)
@isnad1 id=le.5h8v.s8.dd349bfa952a from=translated src=- shape=4515aa54 vocab=22552399
-/
theorem quadForm_chebyshevRecurrenceIterate_sub_le_two_mul_pow
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b) {c xs : n → ℝ}
    (hxs : A *ᵥ xs = c) (x₀ : n → ℝ) (k : ℕ) :
    quadForm A (chebyshevRecurrenceIterate a b A c x₀ k - xs) ≤
      (2 * ((√b - √a) / (√b + √a)) ^ k) ^ 2 * quadForm A (x₀ - xs) := by
  rw [chebyshevRecurrenceIterate_eq_chebyshevIterate ha hab]
  exact quadForm_chebyshevIterate_sub_le hA ha hab hspec hxs x₀ k

end NLAlib
