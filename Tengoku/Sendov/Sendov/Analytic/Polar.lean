/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Tengoku.Sendov.Sendov.Counterexample.Identities
import Tengoku.Sendov.Sendov.Analytic.Maclaurin
import Tengoku.Sendov.Sendov.Reduction.Setup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The polar inequality, up to the branch point

The polar identity says

  `(∏ q) ∏ⱼ (1 - a zⱼ) = n ∫₀¹ ∏ⱼ (t(1-a²)qⱼ + a) dt`,   `(∏ q) ∏ⱼ (a - zⱼ) = n`.

The Möbius estimate `|a - zⱼ| ≤ |1 - a zⱼ|`, valid because `zⱼ` lies in the closed unit disk
and `a` is real with `|a| ≤ 1`, therefore gives

  `n = |(∏ q) ∏ (a - zⱼ)| ≤ |(∏ q) ∏ (1 - a zⱼ)| = n |∫₀¹ ∏ⱼ (t(1-a²)qⱼ + a) dt|`,

and after the integral triangle inequality

  `1 ≤ ∫₀¹ ∏ⱼ |a + t(1-a²)qⱼ| dt`.                                    (⋆)

**`(⋆)` is the branch point of the whole argument.**  The high-degree route relaxes it by
AM–GM into the raw polar inequality `(1Q)` of `Sendov.Reduction.Setup`; the low-degree route
for `2 ≤ n ≤ 5` (see `docs/plan-low-degrees.md`) instead bounds each factor by `a + (1-a²)t`
and integrates a quartic.  Neither may be folded into the other, so `(⋆)` is stated on its own.

Note that no division occurs anywhere: splitting the blog post's quotient
`∏(1-azⱼ)/(a-zⱼ)` into its numerator and denominator identities is what makes that possible,
and `p'(a) ≠ 0` is never needed.

## Main statements

* `Sendov.norm_sub_le_norm_one_sub_mul`: the Möbius estimate;
* `Sendov.one_le_integral_prod_norm`: the branch point `(⋆)`.
-/

namespace Sendov

open Polynomial MeasureTheory

/-! ### The Möbius estimate -/

/-- `|a - z| ≤ |1 - a z|` for real `a` with `|a| ≤ 1` and `z` in the closed unit disk.  The
difference of squares is `(1-a²)(1-|z|²)`, which is why `a` must be real: for complex `a` the
cross terms contribute `(conj a - a)(z - conj z)`, which need not vanish.
@isnad1 id=le.2h2v.s6.4cba5f072fb0 from=translated src=- shape=246a7dbf vocab=2b5b9466
-/
lemma norm_sub_le_norm_one_sub_mul {a : ℝ} (ha : |a| ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(a : ℂ) - z‖ ≤ ‖1 - (a : ℂ) * z‖ := by
  have hkey : Complex.normSq (1 - (a : ℂ) * z) - Complex.normSq ((a : ℂ) - z)
      = (1 - a ^ 2) * (1 - Complex.normSq z) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have ha2 : a ^ 2 ≤ 1 := by
    have := abs_le.1 ha
    nlinarith [this.1, this.2]
  have hz2 : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hdiff : 0 ≤ Complex.normSq (1 - (a : ℂ) * z) - Complex.normSq ((a : ℂ) - z) := by
    rw [hkey]
    have h1 : (0 : ℝ) ≤ 1 - a ^ 2 := by linarith
    have h2 : (0 : ℝ) ≤ 1 - Complex.normSq z := by linarith
    positivity
  have hsq : ‖(a : ℂ) - z‖ ^ 2 ≤ ‖1 - (a : ℂ) * z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    linarith
  nlinarith [norm_nonneg ((a : ℂ) - z), norm_nonneg (1 - (a : ℂ) * z), hsq]

/-! ### Products of norms over a multiset -/

/--
@isnad1 id=eq.0h1v.s4.ef43deec4677 from=translated src=- shape=40577f78 vocab=452ec4e4
-/
lemma norm_multiset_prod (s : Multiset ℂ) : ‖s.prod‖ = (s.map (fun w => ‖w‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w t ih => simp [ih]

/--
@isnad1 id=le.1h3v.s6.3ffae70e7f4a from=translated src=- shape=5fd55df1 vocab=6d5b3ae9
-/
lemma prod_map_le_of_le {s : Multiset ℂ} {f g : ℂ → ℂ} (h : ∀ w ∈ s, ‖f w‖ ≤ ‖g w‖) :
    (s.map (fun w => ‖f w‖)).prod ≤ (s.map (fun w => ‖g w‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w t ih =>
    have hw := h w (Multiset.mem_cons_self w t)
    have ht : ∀ u ∈ t, ‖f u‖ ≤ ‖g u‖ := fun u hu => h u (Multiset.mem_cons_of_mem hu)
    have hnn : (0 : ℝ) ≤ (t.map (fun u => ‖f u‖)).prod :=
      Multiset.prod_nonneg (by
        intro y hy
        obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
        exact norm_nonneg _)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact mul_le_mul hw (ih ht) hnn (norm_nonneg _)

/-! ### The branch point -/

/-- Norms distribute over a mapped multiset product.
@isnad1 id=eq.0h2v.s5.9170131d886f from=translated src=- shape=966903b0 vocab=452ec4e4
-/
lemma norm_prod_map (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).prod‖ = (s.map (fun w => ‖f w‖)).prod := by
  rw [norm_multiset_prod, Multiset.map_map]
  rfl

/--
@isnad1 id=le.0h2v.s4.60cd63979a93 from=translated src=- shape=4dbe6386 vocab=0c2552fc
-/
lemma prod_map_norm_nonneg (s : Multiset ℂ) (f : ℂ → ℂ) :
    0 ≤ (s.map (fun w => ‖f w‖)).prod := by
  refine Multiset.prod_nonneg ?_
  intro y hy
  obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
  exact norm_nonneg _

/-- **The branch point `(⋆)`.**  `1 ≤ ∫₀¹ ∏ⱼ |a + t(1-a²)qⱼ| dt`.

The high-degree argument relaxes this by AM–GM to the raw polar inequality; the low-degree
argument bounds each factor by `a + (1-a²)t`.  It is stated separately so that neither route
has to reproduce the other's work.
@isnad1 id=le.5h4v.s8.a4cba67f24ac from=translated src=- shape=80c2d911 vocab=c3579716
-/
theorem one_le_integral_prod_norm {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : |a| ≤ 1)
    {z q : Multiset ℂ} (hz : ∀ w ∈ z, ‖w‖ ≤ 1)
    (hpolar : q.prod * (z.map (fun w => 1 - (a : ℂ) * w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod)
    (hdenom : q.prod * (z.map (fun w => (a : ℂ) - w)).prod = (n : ℂ)) :
    1 ≤ ∫ t in (0 : ℝ)..1,
        (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  -- the Möbius estimate, multiplied over the multiset
  have hmob : (z.map (fun w => ‖(a : ℂ) - w‖)).prod
      ≤ (z.map (fun w => ‖1 - (a : ℂ) * w‖)).prod :=
    prod_map_le_of_le (fun w hw => norm_sub_le_norm_one_sub_mul ha (hz w hw))
  -- take norms in the two identities
  have h1 : (n : ℝ) = ‖q.prod‖ * (z.map (fun w => ‖(a : ℂ) - w‖)).prod := by
    have := congrArg (fun w : ℂ => ‖w‖) hdenom
    simpa [norm_mul, norm_prod_map] using this.symm
  have h2 : ‖q.prod‖ * (z.map (fun w => ‖1 - (a : ℂ) * w‖)).prod
      = (n : ℝ) * ‖∫ t in (0 : ℝ)..1,
          (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
    have := congrArg (fun w : ℂ => ‖w‖) hpolar
    simpa [norm_mul, norm_prod_map] using this
  -- so the integral has norm at least one
  have h3 : (1 : ℝ) ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
    have hstep : (n : ℝ) ≤ (n : ℝ) * ‖∫ t in (0 : ℝ)..1,
        (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
      rw [← h2, h1]
      exact mul_le_mul_of_nonneg_left hmob (norm_nonneg _)
    nlinarith [hstep, hnpos]
  -- and the triangle inequality moves the norm inside
  refine h3.trans ?_
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans_eq ?_
  refine intervalIntegral.integral_congr ?_
  intro t _
  simp only []
  exact norm_prod_map q _

/-! ### The AM–GM relaxation to `(1Q)` -/

/-- `‖a + s v‖² = a² + 2 a s Re v + s² ‖v‖²` for real `a`, `s`.
@isnad1 id=eq.0h3v.s7.dc5cf303bf02 from=translated src=- shape=10cb3a3c vocab=0a44e00a
-/
lemma norm_sq_add_real_mul (a s : ℝ) (v : ℂ) :
    ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2 = a ^ 2 + 2 * a * s * v.re + s ^ 2 * ‖v‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/--
@isnad1 id=eq.0h2v.s5.6a43765414b6 from=translated src=- shape=27720804 vocab=a8d38741
-/
lemma prod_map_sq (s : Multiset ℂ) (f : ℂ → ℝ) :
    (s.map (fun v => f v ^ 2)).prod = ((s.map f).prod) ^ 2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, ih]
    ring

/-- Splitting `∑ⱼ ‖a + s qⱼ‖²` into its three pieces.
@isnad1 id=eq.0h3v.s7.4b66d7c8a14c from=translated src=- shape=12f4af95 vocab=cdada048
-/
lemma sum_norm_sq_split (a s : ℝ) (q : Multiset ℂ) :
    (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2)).sum
      = (q.card : ℝ) * a ^ 2 + 2 * a * s * ((q.map (fun v => v.re)).sum)
        + s ^ 2 * ((q.map (fun v => ‖v‖ ^ 2)).sum) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    rw [ih, norm_sq_add_real_mul]
    push_cast
    ring

/--
@isnad1 id=le.1h1v.s6.9995c6a79fa6 from=translated src=- shape=f34c1ba6 vocab=bce1cf0d
-/
lemma sum_norm_sq_le_card (q : Multiset ℂ) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) :
    (q.map (fun v => ‖v‖ ^ 2)).sum ≤ (q.card : ℝ) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    have hv := hq1 v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hq1 u (Multiset.mem_cons_of_mem hu)
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    push_cast
    nlinarith [ih ht, norm_nonneg v]

/--
@isnad1 id=continuo.0h2v.s6.79defcf47f42 from=translated src=- shape=a4842dd5 vocab=456f5776
-/
lemma continuous_prod_norm (a : ℝ) (q : Multiset ℂ) :
    Continuous fun t : ℝ =>
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod := by
  induction q using Multiset.induction_on with
  | empty => simpa using continuous_const
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (by fun_prop : Continuous fun t : ℝ =>
      ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖).mul ih

/-- **The pointwise quadratic-mean bound.**  `∏ⱼ |a + t(1-a²)qⱼ| ≤ P(t)^{(n-1)/2)}`, by AM–GM
on the squares followed by `∑ ‖qⱼ‖² ≤ n-1`.
@isnad1 id=le.4h5v.s7.bfc799a0c94c from=translated src=- shape=5aeba26a vocab=47329b3c
-/
lemma prod_norm_le_Ppolar {n : ℕ} (hn : 2 ≤ n) {a x t : ℝ}
    {q : Multiset ℂ} (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod
      ≤ Ppolar a x t ^ (((n : ℝ) - 1) / 2) := by
  have hNcast : ((q.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard]
    have h1 : (1 : ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hNpos : (0 : ℝ) < (q.card : ℕ) := by
    rw [hNcast]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  set s : ℝ := t * (1 - a ^ 2) with hs
  have hcast : ∀ v : ℂ, (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v = (a : ℂ) + (s : ℂ) * v := by
    intro v
    rw [hs]
    push_cast
    ring
  simp only [hcast]
  -- the product of squares
  set P : ℝ := (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖)).prod with hP
  have hP0 : 0 ≤ P := prod_map_norm_nonneg q _
  have hM0 : ∀ v ∈ q, (0 : ℝ) ≤ ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2 := fun v _ => sq_nonneg _
  have hamgm := Multiset.prod_le_mean_pow (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2))
    (by
      intro y hy
      obtain ⟨v, _, rfl⟩ := Multiset.mem_map.1 hy
      exact sq_nonneg _)
  rw [Multiset.card_map, prod_map_sq] at hamgm
  set M : ℝ := (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2)).sum / (q.card : ℝ) with hM
  -- `M ≤ P(t)`
  have hMle : M ≤ Ppolar a x t := by
    rw [hM, div_le_iff₀ hNpos]
    have hsplit := sum_norm_sq_split a s q
    have hcard2 := sum_norm_sq_le_card q hq1
    rw [hsplit, hx, hNcast]
    have hPp : Ppolar a x t = a ^ 2 + 2 * a * s * x + s ^ 2 := by
      rw [Ppolar, hs]; ring
    rw [hPp]
    nlinarith [hcard2, hNcast, sq_nonneg s, hNpos]
  have hM0' : 0 ≤ M := by
    rw [hM]
    apply div_nonneg _ (le_of_lt hNpos)
    exact Multiset.sum_nonneg (by
      intro y hy
      obtain ⟨v, _, rfl⟩ := Multiset.mem_map.1 hy
      exact sq_nonneg _)
  -- take square roots
  have hexp : ((q.card : ℕ) : ℝ) / 2 = ((n : ℝ) - 1) / 2 := by rw [hNcast]
  have hb : (0 : ℝ) ≤ Ppolar a x t := le_trans hM0' hMle
  have hsq : (Ppolar a x t ^ (((n : ℝ) - 1) / 2)) ^ 2 = Ppolar a x t ^ (q.card : ℕ) := by
    rw [← Real.rpow_natCast (Ppolar a x t ^ (((n : ℝ) - 1) / 2)) 2, ← Real.rpow_mul hb,
      ← Real.rpow_natCast (Ppolar a x t) q.card, hNcast]
    congr 1
    push_cast
    ring
  have hchain : P ^ 2 ≤ Ppolar a x t ^ (q.card : ℕ) := by
    refine hamgm.trans ?_
    exact pow_le_pow_left₀ hM0' hMle _
  rw [← hsq] at hchain
  nlinarith [hchain, hP0, Real.rpow_nonneg (le_trans hM0' hMle) (((n : ℝ) - 1) / 2)]

/-- **The raw polar inequality `(1Q)`.**
@isnad1 id=le.5h4v.s8.02864c0671e6 from=translated src=- shape=58616c6f vocab=5b5a7436
-/
theorem one_le_integral_Ppolar {n : ℕ} (hn : 2 ≤ n) {a x : ℝ}
    {q : Multiset ℂ} (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2) := by
  have he : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  refine hstar.trans (intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_prod_norm a q).intervalIntegrable _ _)
    (((continuous_rpow_const he).comp (continuous_Ppolar a x)).intervalIntegrable _ _) ?_)
  intro u _
  exact prod_norm_le_Ppolar hn hqcard hq1 hx

end Sendov
