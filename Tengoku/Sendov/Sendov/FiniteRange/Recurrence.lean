/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Tengoku.Sendov.Sendov.Common.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Moments by a verified recurrence

`Sendov.integral_moment` computes `∫ t in 0..1, t ^ 3 * Q ^ k` as the multinomial double
sum `(M)`.  That formula is correct but has `Θ(k²)` terms, and expanding it with `simp`
becomes impossible around `k = 20`: at `n = 53` the 676-term expansion exhausts two million
heartbeats.

This file computes the same integral by a recurrence instead.  Clearing denominators with
`D = 2 (n-1) (3+α)`, the quadratic `D * Q` has *integer* coefficients as a polynomial in
`α`:

  `D * Q t = g₀ + g₁ t + g₂ t²`,  `g₀ = D`,  `g₁ = -2Dc`,  `g₂ = DA`,

so the coefficients of `(D * Q t) ^ k` in `t` satisfy

  `Rec (k+1) j = g₀ * Rec k j + g₁ * Rec k (j-1) + g₂ * Rec k (j-2)`,

which is just multiplication of the previous row by a fixed quadratic.  Integrating term by
term against `t ^ 3` then gives the moment.  This replaces `Θ(k²)` summands by `k` steps on
vectors of length `≤ 2k+1`.

The essential point is that the coefficients are held as *integers*, not as real
expressions: a recurrence carried out symbolically over `ℝ` would grow its terms by a factor
of three per step and reproduce the blow-up in another form.  So polynomials in `α` are
represented here by `List ℤ` (dense, lowest degree first) with their own arithmetic, and
`Sendov.pev` is the evaluation homomorphism into `ℝ`.  Everything a degree needs is then a
kernel computation on integer data.

## Main statements

* `Sendov.pev_padd`, `Sendov.pev_pmul`: evaluation is a ring homomorphism;
* `Sendov.rev_qrow`: `qrow` computes the coefficients of `(g₀ + g₁t + g₂t²) ^ k`;
* `Sendov.integral_irow`: integrating a row against `t ^ (i+3)` gives `irow`;
* `Sendov.integral_moment_rec`: the moment, via the recurrence.
-/

namespace Sendov

open MeasureTheory

/-! ### Integer polynomials in `α`, densely represented, lowest degree first -/

/-- Evaluation of a dense integer polynomial at a real point, by Horner's rule.-/
def pev : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => (a : ℝ) + x * pev p x

/-- Addition of dense integer polynomials.-/
def padd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: padd p q

/-- Multiplication of dense integer polynomials.-/
def pmul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q => padd (q.map (fun b => a * b)) (0 :: pmul p q)

/--
@isnad1 id=eq.0h1v.s3.24b9b5b6f802 from=translated src=- shape=dedddc79 vocab=f07dd37e
-/
@[simp] lemma pev_nil (x : ℝ) : pev [] x = 0 := rfl

/--
@isnad1 id=eq.0h3v.s5.53cc869f1737 from=translated src=- shape=ec8bda9b vocab=2e6cc6ef
-/
@[simp] lemma pev_cons (a : ℤ) (p : List ℤ) (x : ℝ) :
    pev (a :: p) x = (a : ℝ) + x * pev p x := rfl

/--
@isnad1 id=eq.0h3v.s4.19e5d22f79f0 from=translated src=- shape=fec59c0e vocab=196a7e0d
-/
lemma pev_padd (p q : List ℤ) (x : ℝ) : pev (padd p q) x = pev p x + pev q x := by
  induction p generalizing q with
  | nil => simp [padd]
  | cons a p ih =>
    cases q with
    | nil => simp [padd]
    | cons b q =>
      simp only [padd, pev_cons, ih]
      push_cast
      ring

/--
@isnad1 id=eq.0h3v.s5.6403e444f46e from=translated src=- shape=68d6867a vocab=dd070959
-/
lemma pev_map_mul (a : ℤ) (q : List ℤ) (x : ℝ) :
    pev (q.map (fun b => a * b)) x = (a : ℝ) * pev q x := by
  induction q with
  | nil => simp
  | cons b q ih =>
    simp only [List.map_cons, pev_cons, ih]
    push_cast
    ring

/--
@isnad1 id=eq.0h3v.s4.501c095c0343 from=translated src=- shape=fec59c0e vocab=9b92258a
-/
lemma pev_pmul (p q : List ℤ) (x : ℝ) : pev (pmul p q) x = pev p x * pev q x := by
  induction p with
  | nil => simp [pmul]
  | cons a p ih =>
    simp only [pmul, pev_padd, pev_map_mul, pev_cons, ih]
    push_cast
    ring

/-! ### Rows: polynomials in `t` whose coefficients are polynomials in `α` -/

/-- Evaluation of a row at `α` (coefficientwise) and `t` (by Horner's rule).-/
def rev : List (List ℤ) → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | p :: r, α, t => pev p α + t * rev r α t

/-- Addition of rows.-/
def radd : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], s => s
  | p :: r, [] => p :: r
  | p :: r, q :: s => padd p q :: radd r s

/-- Multiply every coefficient of a row by a fixed polynomial in `α`.-/
def rscale (g : List ℤ) (r : List (List ℤ)) : List (List ℤ) := r.map (pmul g)

/--
@isnad1 id=eq.0h2v.s4.90eb0d77dcf7 from=translated src=- shape=0249b776 vocab=b99b9eed
-/
@[simp] lemma rev_nil (α t : ℝ) : rev [] α t = 0 := rfl

/--
@isnad1 id=eq.0h4v.s5.6870a0f45922 from=translated src=- shape=373ca462 vocab=926de5f3
-/
@[simp] lemma rev_cons (p : List ℤ) (r : List (List ℤ)) (α t : ℝ) :
    rev (p :: r) α t = pev p α + t * rev r α t := rfl

/--
@isnad1 id=eq.0h4v.s5.1844bc2ff5fd from=translated src=- shape=22f84fa8 vocab=452bf1f1
-/
lemma rev_radd (r s : List (List ℤ)) (α t : ℝ) :
    rev (radd r s) α t = rev r α t + rev s α t := by
  induction r generalizing s with
  | nil => simp [radd]
  | cons p r ih =>
    cases s with
    | nil => simp [radd]
    | cons q s =>
      simp only [radd, rev_cons, pev_padd, ih]
      ring

/--
@isnad1 id=eq.0h4v.s5.de48952a2035 from=translated src=- shape=419e65cd vocab=4fafbb34
-/
lemma rev_rscale (g : List ℤ) (r : List (List ℤ)) (α t : ℝ) :
    rev (rscale g r) α t = pev g α * rev r α t := by
  induction r with
  | nil => simp [rscale]
  | cons p r ih =>
    simp only [rscale, List.map_cons, rev_cons, pev_pmul] at *
    rw [ih]
    ring

/--
@isnad1 id=eq.0h3v.s4.72dedd0cee01 from=translated src=- shape=ea0410ce vocab=8f9afecb
-/
lemma rev_shift (r : List (List ℤ)) (α t : ℝ) :
    rev (([] : List ℤ) :: r) α t = t * rev r α t := by
  simp

/-! ### The recurrence -/

/-- One step of the recurrence: multiply a row by `g₀ + g₁ t + g₂ t²`.-/
def qstep (g₀ g₁ g₂ : List ℤ) (r : List (List ℤ)) : List (List ℤ) :=
  radd (rscale g₀ r) (radd ([] :: rscale g₁ r) ([] :: [] :: rscale g₂ r))

/-- The coefficients of `(g₀ + g₁ t + g₂ t²) ^ k`, as a polynomial in `t` whose
coefficients are integer polynomials in `α`.-/
def qrow (g₀ g₁ g₂ : List ℤ) : ℕ → List (List ℤ)
  | 0 => [[1]]
  | k + 1 => qstep g₀ g₁ g₂ (qrow g₀ g₁ g₂ k)

/--
@isnad1 id=eq.0h6v.s6.325a8988d98f from=translated src=- shape=c8b0d975 vocab=304e269d
-/
lemma rev_qrow (g₀ g₁ g₂ : List ℤ) (k : ℕ) (α t : ℝ) :
    rev (qrow g₀ g₁ g₂ k) α t = (pev g₀ α + pev g₁ α * t + pev g₂ α * t ^ 2) ^ k := by
  induction k with
  | zero => simp [qrow]
  | succ k ih =>
    simp only [qrow, qstep, rev_radd, rev_rscale, rev_shift, ih, pow_succ]
    ring

/-! ### Integration -/

/-- `irow r i α = ∑ⱼ (coefficient j of r, at α) / (i + j + 4)`, the value of
`∫ t in 0..1, t ^ (i+3) * rev r α t`.-/
noncomputable def irow : List (List ℤ) → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | p :: r, i, α => pev p α / (i + 4) + irow r (i + 1) α

/--
@isnad1 id=continuo.0h2v.s4.cfdac3b290f5 from=translated src=- shape=259c9cf3 vocab=3a75a4de
-/
lemma continuous_rev (r : List (List ℤ)) (α : ℝ) : Continuous fun t : ℝ => rev r α t := by
  induction r with
  | nil => simpa using continuous_const
  | cons p r ih =>
    simp only [rev_cons]
    exact continuous_const.add (continuous_id.mul ih)

/--
@isnad1 id=eq.0h3v.s6.dee7dfc086e9 from=translated src=- shape=d4fb4d33 vocab=f3a3262b
-/
lemma integral_irow (r : List (List ℤ)) (i : ℕ) (α : ℝ) :
    (∫ t in (0 : ℝ)..1, t ^ (i + 3) * rev r α t) = irow r i α := by
  induction r generalizing i with
  | nil => simp [irow]
  | cons p r ih =>
    have hfun : (fun t : ℝ => t ^ (i + 3) * rev (p :: r) α t)
        = fun t : ℝ => pev p α * t ^ (i + 3) + t ^ (i + 1 + 3) * rev r α t := by
      funext t
      simp only [rev_cons]
      ring
    have h1 : IntervalIntegrable (fun t : ℝ => pev p α * t ^ (i + 3)) volume 0 1 :=
      (by fun_prop : Continuous fun t : ℝ => pev p α * t ^ (i + 3)).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun t : ℝ => t ^ (i + 1 + 3) * rev r α t) volume 0 1 :=
      ((continuous_pow _).mul (continuous_rev r α)).intervalIntegrable _ _
    rw [hfun, intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
      integral_pow, ih]
    simp only [irow]
    push_cast
    ring

/-- **The moment, by the recurrence.**  If `D * Q t` has the integer coefficient
polynomials `g₀, g₁, g₂` in `α`, then the moment is a kernel computation on those integers.
No hypothesis beyond `D ≠ 0` is needed: this is a polynomial identity.
@isnad1 id=eq.2h7v.s7.d1db87ac5016 from=translated src=- shape=1a8495be vocab=40bc64d7
-/
theorem integral_moment_rec {n k : ℕ} {α D : ℝ} {g₀ g₁ g₂ : List ℤ} (hD : D ≠ 0)
    (hQ : ∀ t : ℝ, D * Q n α t = pev g₀ α + pev g₁ α * t + pev g₂ α * t ^ 2) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ k) = irow (qrow g₀ g₁ g₂ k) 0 α / D ^ k := by
  have hpow : ∀ t : ℝ, t ^ 3 * Q n α t ^ k
      = (t ^ (0 + 3) * rev (qrow g₀ g₁ g₂ k) α t) / D ^ k := by
    intro t
    rw [rev_qrow, ← hQ t, mul_pow]
    field_simp
    ring
  simp only [hpow]
  rw [intervalIntegral.integral_div, integral_irow]

/-! ### The coefficients for a given degree

With `D = 2 (n-1) (3+α)` one has `D * Q t = g₀ + g₁ t + g₂ t²` where, as polynomials in `α`
with integer coefficients,

  `g₀ = 6(n-1) + 2(n-1) α`,
  `g₁ = -12(n-1) + (12 - 2(n-1)) α + 4 α²`,
  `g₂ = 6(n-1) + (2(n-1) - 12) α - 4 α²`. -/

/-- `D` itself, as an integer polynomial in `α`.-/
def gg0 (n : ℕ) : List ℤ := [6 * ((n : ℤ) - 1), 2 * ((n : ℤ) - 1)]

/-- `-2 D c`, as an integer polynomial in `α`.-/
def gg1 (n : ℕ) : List ℤ := [-12 * ((n : ℤ) - 1), 12 - 2 * ((n : ℤ) - 1), 4]

/-- `D A`, as an integer polynomial in `α`.-/
def gg2 (n : ℕ) : List ℤ := [6 * ((n : ℤ) - 1), 2 * ((n : ℤ) - 1) - 12, -4]

/--
@isnad1 id=eq.0h1v.s3.02bc8daa63dc from=translated src=- shape=0cfb200e vocab=5db8fd32
-/
@[simp] lemma gg0_length (n : ℕ) : (gg0 n).length = 2 := rfl

/--
@isnad1 id=eq.0h1v.s3.d52402a6c117 from=translated src=- shape=0cfb200e vocab=7bec0a72
-/
@[simp] lemma gg1_length (n : ℕ) : (gg1 n).length = 3 := rfl

/--
@isnad1 id=eq.0h1v.s3.f18e67e9e711 from=translated src=- shape=0cfb200e vocab=0168e70a
-/
@[simp] lemma gg2_length (n : ℕ) : (gg2 n).length = 3 := rfl

/--
@isnad1 id=eq.2h3v.s7.6b67cc6dcecb from=translated src=- shape=efbc65c3 vocab=9156b956
-/
lemma DQ_eq (n : ℕ) (hn : 2 ≤ n) (α t : ℝ) (hα : 0 ≤ α) :
    (2 * M n * (3 + α)) * Q n α t
      = pev (gg0 n) α + pev (gg1 n) α * t + pev (gg2 n) α * t ^ 2 := by
  have hM : ((n : ℝ) - 1) ≠ 0 := by
    have h := M_pos hn
    simp only [M] at h
    linarith
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  simp only [gg0, gg1, gg2, pev_cons, pev_nil, Q, c, A, M]
  push_cast
  field_simp
  ring

/-- **The moment for a given degree, by the recurrence.**  Every ingredient on the right is
a kernel computation on integers, apart from the final evaluation at `α`.
@isnad1 id=eq.2h3v.s7.e0947f5b4004 from=translated src=- shape=275702c5 vocab=fe460607
-/
theorem integral_moment_of (n k : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ k)
      = irow (qrow (gg0 n) (gg1 n) (gg2 n) k) 0 α / (2 * M n * (3 + α)) ^ k := by
  have hM : 0 < M n := M_pos hn
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  exact integral_moment_rec (n := n) (k := k) (by positivity) (fun t => DQ_eq n hn α t hα)

end Sendov
