/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Analysis.Complex.Liouville
import Tengoku.Seed.Analysis.Complex.TaylorSeries
import Tengoku.Seed.LinearAlgebra.Lagrange
import Tengoku.Seed.Algebra.MvPolynomial.Rename

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Liouville's theorem with polynomial growth

An entire function `f` on `ℂ^d` with `‖f z‖ ≤ C (1 + ‖z‖)^N` is a polynomial.

In one variable the Cauchy estimates
(`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`) kill every Taylor coefficient of
order `> N`, and the Taylor series of an entire function converges everywhere
(`Complex.taylorSeries_eq_of_entire'`). In `d + 1` variables, for fixed `z'` the function
`t ↦ f (t, z')` is a polynomial of degree `≤ N`, hence equal to its Lagrange interpolation at the
nodes `0, 1, …, N`; the values `z' ↦ f (i, z')` at the nodes are entire of polynomial growth in
`d` variables, hence polynomials by induction.

## Main results

- `Differentiable.exists_polynomial_eq_of_norm_le_pow`: the one-variable statement, with a
  degree bound.
- `Differentiable.exists_mvPolynomial_eq_of_norm_le_pow`: the statement on `Fin d → ℂ`.
-/

open Polynomial Metric Finset

namespace Differentiable

/-- A number `a ≥ 0` with `a * R ≤ K` for every `R ≥ 1` is zero. -/
private lemma eq_zero_of_mul_le {a K : ℝ} (ha : 0 ≤ a) (h : ∀ R : ℝ, 1 ≤ R → a * R ≤ K) :
    a = 0 := by
  by_contra hne
  have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
  have h1 := h (max 1 (K / a + 1)) (le_max_left _ _)
  have h2 : a * (K / a + 1) ≤ a * max 1 (K / a + 1) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) ha
  have h3 : a * (K / a + 1) = K + a := by field_simp
  linarith

/-- **Cauchy estimates kill the high Taylor coefficients**: if `g` is entire with
`‖g t‖ ≤ C (1 + ‖t‖)^N`, every derivative of order `n > N` vanishes at `0`. -/
theorem iteratedDeriv_eq_zero_of_norm_le_pow {g : ℂ → ℂ} (hg : Differentiable ℂ g) {C : ℝ}
    {N : ℕ} (hb : ∀ t, ‖g t‖ ≤ C * (1 + ‖t‖) ^ N) {n : ℕ} (hn : N < n) :
    iteratedDeriv n g 0 = 0 := by
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hb 0)
    simpa using this
  apply norm_eq_zero.1
  refine eq_zero_of_mul_le (norm_nonneg _) (K := n.factorial * (C * 2 ^ N)) fun R hR ↦ ?_
  have hR0 : 0 < R := by linarith
  have hest := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0)
    (C := C * (1 + R) ^ N) n hR0 hg.diffContOnCl fun z hz ↦ by
      have hz' : ‖z‖ = R := by simpa using hz
      simpa [hz'] using hb z
  -- `(1 + R)^N ≤ 2^N R^N ≤ 2^N R^(n-1)`, so the bound times `R` is at most `n! C 2^N`.
  have hpow : (1 + R) ^ N ≤ 2 ^ N * R ^ (n - 1) := by
    calc (1 + R) ^ N ≤ (2 * R) ^ N := by
          gcongr; linarith
      _ = 2 ^ N * R ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * R ^ (n - 1) := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (by omega)) (by positivity)
  have hRn : R ^ n = R ^ (n - 1) * R := by
    rw [← pow_succ]; congr 1; omega
  have hRn1 : 0 < R ^ (n - 1) := pow_pos hR0 _
  calc ‖iteratedDeriv n g 0‖ * R ≤ n.factorial * (C * (1 + R) ^ N) / R ^ n * R := by
        gcongr
    _ = n.factorial * (C * (1 + R) ^ N) / R ^ (n - 1) := by
        rw [hRn]; field_simp
    _ ≤ n.factorial * (C * (2 ^ N * R ^ (n - 1))) / R ^ (n - 1) := by
        gcongr
    _ = n.factorial * (C * 2 ^ N) := by
        field_simp

/-- **Liouville with polynomial growth, one variable**: an entire `g` with
`‖g t‖ ≤ C (1 + ‖t‖)^N` is a polynomial of degree `≤ N`. -/
theorem exists_polynomial_eq_of_norm_le_pow {g : ℂ → ℂ} (hg : Differentiable ℂ g) {C : ℝ}
    {N : ℕ} (hb : ∀ t, ‖g t‖ ≤ C * (1 + ‖t‖) ^ N) :
    ∃ p : ℂ[X], p.degree < ↑(N + 1) ∧ ∀ t, g t = p.eval t := by
  set a : ℕ → ℂ := fun n ↦ (n.factorial : ℂ)⁻¹ * iteratedDeriv n g 0 with ha
  refine ⟨∑ i : Fin (N + 1), Polynomial.C (a i) * X ^ (i : ℕ), degree_sum_fin_lt _, fun t ↦ ?_⟩
  have hz : ∀ n ∉ Finset.range (N + 1), a n * (t - 0) ^ n = 0 := fun n hn ↦ by
    have : N < n := by simpa using hn
    simp [ha, iteratedDeriv_eq_zero_of_norm_le_pow hg hb this]
  rw [← Complex.taylorSeries_eq_of_entire' (c := 0) (z := t) hg, tsum_eq_sum hz,
    eval_finsetSum, ← Fin.sum_univ_eq_sum_range]
  simp [ha]

/-- The sup norm of `Fin.cons t z'` is at most `‖t‖ + ‖z'‖`. -/
private lemma norm_cons_le {d : ℕ} (t : ℂ) (z' : Fin d → ℂ) :
    ‖(Fin.cons t z' : Fin (d + 1) → ℂ)‖ ≤ ‖t‖ + ‖z'‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simpa using (norm_le_pi_norm z' j).trans (le_add_of_nonneg_left (norm_nonneg t))

/-- `t ↦ Fin.cons t z'` is differentiable. -/
private lemma differentiable_cons_left {d : ℕ} (z' : Fin d → ℂ) :
    Differentiable ℂ (fun t : ℂ ↦ (Fin.cons t z' : Fin (d + 1) → ℂ)) := by
  refine differentiable_pi.2 fun i ↦ ?_
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

/-- `z' ↦ Fin.cons t z'` is differentiable. -/
private lemma differentiable_cons_right {d : ℕ} (t : ℂ) :
    Differentiable ℂ (fun z' : Fin d → ℂ ↦ (Fin.cons t z' : Fin (d + 1) → ℂ)) := by
  refine differentiable_pi.2 fun i ↦ ?_
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simpa using differentiable_apply j

/-- **Liouville with polynomial growth**: an entire function `f` on `ℂ^d` with
`‖f z‖ ≤ C (1 + ‖z‖)^N` is (the evaluation of) a polynomial. -/
theorem exists_mvPolynomial_eq_of_norm_le_pow {d : ℕ} {f : (Fin d → ℂ) → ℂ}
    (hf : Differentiable ℂ f) {C : ℝ} {N : ℕ} (hb : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N) :
    ∃ p : MvPolynomial (Fin d) ℂ, ∀ z, f z = MvPolynomial.eval z p := by
  induction d generalizing C with
  | zero =>
    exact ⟨MvPolynomial.C (f 0), fun z ↦ by simp [Subsingleton.elim z 0]⟩
  | succ d ih =>
    have hC : 0 ≤ C := by
      have := (norm_nonneg _).trans (hb 0)
      simpa using this
    -- the interpolation nodes `0, 1, …, N`
    let v : Fin (N + 1) → ℂ := fun i ↦ ((i : ℕ) : ℂ)
    have hv : Set.InjOn v (Finset.univ : Finset (Fin (N + 1))) := fun i _ j _ h ↦ by
      simpa [v, Fin.ext_iff] using h
    -- the values at the nodes are polynomials in the remaining variables
    have hnode : ∀ i : Fin (N + 1), ∃ q : MvPolynomial (Fin d) ℂ,
        ∀ z', f (Fin.cons (v i) z') = MvPolynomial.eval z' q := fun i ↦ by
      refine ih (hf.comp (differentiable_cons_right (v i))) (C := C * (1 + ‖v i‖) ^ N)
        fun z' ↦ ?_
      calc ‖f (Fin.cons (v i) z')‖ ≤ C * (1 + ‖(Fin.cons (v i) z' : Fin (d + 1) → ℂ)‖) ^ N :=
            hb _
        _ ≤ C * ((1 + ‖v i‖) * (1 + ‖z'‖)) ^ N := by
            gcongr
            nlinarith [norm_cons_le (v i) z', norm_nonneg (v i), norm_nonneg z']
        _ = C * (1 + ‖v i‖) ^ N * (1 + ‖z'‖) ^ N := by rw [mul_pow, mul_assoc]
    choose q hq using hnode
    -- in the first variable, `f` is its Lagrange interpolation at the nodes
    have hline : ∀ (t : ℂ) (z' : Fin d → ℂ), f (Fin.cons t z') =
        ∑ i, f (Fin.cons (v i) z') * (Lagrange.basis Finset.univ v i).eval t := by
      intro t z'
      obtain ⟨p, hpdeg, hp⟩ := exists_polynomial_eq_of_norm_le_pow
        (hf.comp (differentiable_cons_left z')) (C := C * (1 + ‖z'‖) ^ N) (N := N) fun s ↦ by
          calc ‖f (Fin.cons s z')‖ ≤ C * (1 + ‖(Fin.cons s z' : Fin (d + 1) → ℂ)‖) ^ N := hb _
            _ ≤ C * ((1 + ‖z'‖) * (1 + ‖s‖)) ^ N := by
                gcongr
                nlinarith [norm_cons_le s z', norm_nonneg s, norm_nonneg z']
            _ = C * (1 + ‖z'‖) ^ N * (1 + ‖s‖) ^ N := by rw [mul_pow, mul_assoc]
      have hint := Lagrange.eq_interpolate_of_eval_eq (r := fun i ↦ f (Fin.cons (v i) z')) hv
        (by simpa using hpdeg) fun i _ ↦ (hp _).symm
      rw [show f (Fin.cons t z') = p.eval t from hp t, hint, Lagrange.interpolate_apply,
        eval_finsetSum]
      simp [mul_comm]
    refine ⟨∑ i, MvPolynomial.rename Fin.succ (q i) *
      Polynomial.aeval (MvPolynomial.X 0) (Lagrange.basis Finset.univ v i), fun z ↦ ?_⟩
    have hz : z = Fin.cons (z 0) (Fin.tail z) := (Fin.cons_self_tail z).symm
    have haeval : ∀ b : ℂ[X], MvPolynomial.eval z (Polynomial.aeval (MvPolynomial.X 0) b) =
        b.eval (z 0) := fun b ↦ by
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, MvPolynomial.eval_X]
      have : (MvPolynomial.eval z).comp (algebraMap ℂ (MvPolynomial (Fin (d + 1)) ℂ)) =
          RingHom.id ℂ := by ext; simp
      rw [this]
      rfl
    rw [hz, hline, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, MvPolynomial.eval_rename, ← hz, haeval, hq]
    rfl

end Differentiable
