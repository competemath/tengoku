import Tengoku.Piirrationalitymeasure.Formalization.ComplexDerivative
import Tengoku.Piirrationalitymeasure.Formalization.EndpointPolynomial
import Tengoku.Piirrationalitymeasure.Formalization.PartialFractionIdentity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The endpoint coefficient formula (2.25), obtained by differentiating the
actual rational function at its numerator zero `t_0=-1-2*i`.
-/

namespace PiIrrationality

open Polynomial

noncomputable def complexRationalFunction (n : ℕ) (t : ℂ) : ℂ :=
  5 * t ^ (2 * 1857 * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (3714 * n) /
    (25 - t ^ 2) ^ (5570 * n + 1)

/--
@isnad1 id=eq.2h2v.s7.2c415c7e09c6 from=translated src=- shape=d39d620b vocab=eb23ea25
-/
theorem endpointCoeff_eq_normalizedComplexDeriv
    (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k < 7430 * n - 1) :
    normalizedComplexDeriv k (fun t : ℂ => aeval t (polynomialPart n))
      (-1 - 2 * Complex.I) = (endpointCoeff n k : ℂ) := by
  have hfun := funext (polynomialPart_endpoint_expansion n hn)
  rw [hfun, normalizedComplexDeriv_sum _ _ _ _ (by intros; fun_prop)]
  simp_rw [normalizedComplexDeriv_const_mul, normalizedComplexDeriv_shift_power]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hik
    simp [Ne.symm hik]
  · intro h
    exact (h (Finset.mem_range.mpr hk)).elim

noncomputable def endpointRegularFactor (n : ℕ) (t : ℂ) : ℂ :=
  5 * t ^ (2 * 1857 * n) * (t - (-1 + 2 * Complex.I)) ^ (3714 * n) *
    ((t - 1) ^ 2 + 4) ^ (3714 * n) / (25 - t ^ 2) ^ (5570 * n + 1)

/--
@isnad1 id=eq.0h2v.s6.ed0287447aad from=translated src=- shape=1c7e5c99 vocab=dbd33598
-/
theorem complexRationalFunction_endpoint_factor (n : ℕ) (t : ℂ) :
    complexRationalFunction n t =
      (t - (-1 - 2 * Complex.I)) ^ (3714 * n) * endpointRegularFactor n t := by
  have hquad : (t - (-1 - 2 * Complex.I)) * (t - (-1 + 2 * Complex.I)) =
      (t + 1) ^ 2 + 4 := by
    linear_combination -4 * Complex.I_sq
  have hquartic : t ^ 4 + 6 * t ^ 2 + 25 =
      ((t - (-1 - 2 * Complex.I)) * (t - (-1 + 2 * Complex.I))) *
        ((t - 1) ^ 2 + 4) := by
    rw [hquad]
    ring
  unfold complexRationalFunction endpointRegularFactor
  rw [hquartic, mul_pow, mul_pow]
  ring

/--
@isnad1 id=ne.0h0v.s6.41757c3828b9 from=translated src=- shape=8bd0c1c0 vocab=0fec222f
-/
theorem endpoint_denominator_ne_zero : (25 : ℂ) - (-1 - 2 * Complex.I) ^ 2 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at this

/--
@isnad1 id=eq.1h2v.s6.0b174b926428 from=translated src=- shape=02e69ff9 vocab=663ba8b6
-/
theorem normalizedComplexDeriv_rationalFunction_endpoint_zero
    (n k : ℕ) (hk : k < 3714 * n) :
    normalizedComplexDeriv k (complexRationalFunction n) (-1 - 2 * Complex.I) = 0 := by
  have hf : ContDiffAt ℂ k (endpointRegularFactor n) (-1 - 2 * Complex.I) := by
    unfold endpointRegularFactor
    fun_prop (disch := exact pow_ne_zero _ endpoint_denominator_ne_zero)
  have hfun := funext (complexRationalFunction_endpoint_factor n)
  unfold normalizedComplexDeriv
  rw [hfun, iteratedDeriv_shift_power_mul_zero k _ hk _ _ hf, zero_div]

/--
@isnad1 id=ne.0h0v.s5.ec460219229a from=translated src=- shape=589bfb3b vocab=2ae7b950
-/
theorem endpoint_left_pole_ne_zero : (5 : ℂ) + (-1 - 2 * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

/--
@isnad1 id=ne.0h0v.s5.2392001b5839 from=translated src=- shape=f6d23e0a vocab=73188b13
-/
theorem endpoint_right_pole_ne_zero : (5 : ℂ) - (-1 - 2 * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

/--
@isnad1 id=eq.2h2v.s9.badd6d60f34f from=translated src=- shape=eaf4a0c8 vocab=7ff0ab25
-/
theorem endpointCoeff_formula (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k < 3714 * n) :
    (endpointCoeff n k : ℂ) =
      -∑ j : Fin (5570 * n + 1), ((j.val + k).choose k : ℂ) *
        (laurentCoeffRat n (j.val : ℤ) : ℂ) *
          ((-1 : ℂ) ^ k / (4 - 2 * Complex.I) ^ (j.val + k + 1) +
            1 / (6 + 2 * Complex.I) ^ (j.val + k + 1)) := by
  let t0 : ℂ := -1 - 2 * Complex.I
  let f (j : Fin (5570 * n + 1)) (t : ℂ) :=
    (laurentCoeffRat n (j.val : ℤ) : ℂ) *
      (1 / (5 + t) ^ (j.val + 1) + 1 / (5 - t) ^ (j.val + 1))
  have hl (j : ℕ) : ContDiffAt ℂ k (fun t : ℂ => 1 / (5 + t) ^ (j + 1)) t0 := by
    dsimp [t0]
    fun_prop (disch := exact pow_ne_zero _ endpoint_left_pole_ne_zero)
  have hr (j : ℕ) : ContDiffAt ℂ k (fun t : ℂ => 1 / (5 - t) ^ (j + 1)) t0 := by
    dsimp [t0]
    fun_prop (disch := exact pow_ne_zero _ endpoint_right_pole_ne_zero)
  have hf (j : Fin (5570 * n + 1)) : ContDiffAt ℂ k (f j) t0 :=
    contDiffAt_const.mul ((hl j.val).add (hr j.val))
  have hs : ContDiffAt ℂ k (fun t : ℂ => ∑ j, f j t) t0 := by
    exact ContDiffAt.sum (fun j _ => hf j)
  have hp : ContDiffAt ℂ k (fun t : ℂ => aeval t (polynomialPart n)) t0 :=
    ((polynomialPart n).contDiff_aeval k).contDiffAt
  have heq : complexRationalFunction n =ᶠ[nhds t0]
      (fun t : ℂ => aeval t (polynomialPart n) + ∑ j, f j t) := by
    have hm5 : t0 ≠ -5 := by
      intro h
      have := congrArg Complex.re h
      norm_num [t0] at this
    have hp5 : t0 ≠ 5 := by
      intro h
      have := congrArg Complex.re h
      norm_num [t0] at this
    filter_upwards [eventually_ne_nhds hm5, eventually_ne_nhds hp5] with t hm hp'
    exact rationalFunction_partialFractions n t (by simpa [add_eq_zero_iff_eq_neg] using hm)
      (sub_ne_zero.mpr hp')
  have hd := congrArg (fun z : ℂ => z / (k.factorial : ℂ)) (heq.iteratedDeriv_eq k)
  change normalizedComplexDeriv k (complexRationalFunction n) t0 =
    normalizedComplexDeriv k (fun t => aeval t (polynomialPart n) + ∑ j, f j t) t0 at hd
  rw [normalizedComplexDeriv_add k _ _ _ hp hs,
    normalizedComplexDeriv_sum _ _ _ _ (fun j _ => hf j)] at hd
  rw [normalizedComplexDeriv_rationalFunction_endpoint_zero n k hk,
    endpointCoeff_eq_normalizedComplexDeriv n hn k (by omega)] at hd
  have hterm (j : Fin (5570 * n + 1)) : normalizedComplexDeriv k (f j) t0 =
      ((j.val + k).choose k : ℂ) * (laurentCoeffRat n (j.val : ℤ) : ℂ) *
        ((-1 : ℂ) ^ k / (4 - 2 * Complex.I) ^ (j.val + k + 1) +
          1 / (6 + 2 * Complex.I) ^ (j.val + k + 1)) := by
    dsimp only [f]
    rw [normalizedComplexDeriv_const_mul, normalizedComplexDeriv_add k _ _ _ (hl _) (hr _),
      normalizedComplexDeriv_inv_add, normalizedComplexDeriv_inv_sub]
    have hleft : 5 + t0 = 4 - 2 * Complex.I := by dsimp [t0]; ring
    have hright : 5 - t0 = 6 + 2 * Complex.I := by dsimp [t0]; ring
    rw [hleft, hright]
    ring
  simp_rw [hterm] at hd
  linear_combination -hd

end PiIrrationality
