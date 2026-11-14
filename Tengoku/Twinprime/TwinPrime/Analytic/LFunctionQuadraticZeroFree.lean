import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionNonquadraticZeroFree
import Tengoku.Twinprime.TwinPrime.Analytic.ZetaLocalExpansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# Quadratic-character zero exclusion away from small heights

The square character is principal, so its zeta pole is retained in the
three-four-one inequality. A height condition bounds that extra pole term.
The possible real zero near one is outside the scope of this theorem.
-/

noncomputable section

namespace TwinPrime.Analytic

/-- The real part of the principal pole at twice the height.
@isnad1 id=eq.0h2v.s6.d670e9b37a02 from=translated src=- shape=60115b54 vocab=8cbd1687
-/
theorem principal_pole_re_at_twice_height (a t : ℝ) :
    (1 / ((a : ℂ) + Complex.I * (2 * t : ℝ))).re = a / (a ^ 2 + 4 * t ^ 2) := by
  simp only [Complex.div_re, Complex.normSq_apply, Complex.one_re, Complex.one_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/--
@isnad1 id=le.2h2v.s6.432d6beefda1 from=translated src=- shape=4e2f511b vocab=a183a737
-/
theorem principal_pole_re_le_one_fifth (a t : ℝ) (ha : 0 < a) (ht : a ≤ |t|) :
    (1 / ((a : ℂ) + Complex.I * (2 * t : ℝ))).re ≤ 1 / (5 * a) := by
  rw [principal_pole_re_at_twice_height]
  have hsq : a ^ 2 ≤ t ^ 2 := by
    have h := mul_self_le_mul_self ha.le ht
    nlinarith [sq_abs t]
  apply (div_le_div_iff₀ (by positivity : 0 < a ^ 2 + 4 * t ^ 2)
    (by positivity : 0 < 5 * a)).mpr
  nlinarith

/-- The numerical contradiction after retaining and bounding the extra pole.
@isnad1 id=not.3h2v.s7.13ceedbd80a4 from=translated src=- shape=378aea26 vocab=70d00927
-/
theorem four_three_one_fifth_pole_contradiction {E δ : ℝ} (hE : 0 < E)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (40 * E)) :
    ¬ 4 / (1 / (4 * E) + δ) ≤
      3 / (1 / (4 * E)) + 1 / (5 * (1 / (4 * E))) + E := by
  have ha : 0 < 1 / (4 * E) := by positivity
  have hden : 0 < 1 / (4 * E) + δ := by linarith
  have hsum : 1 / (4 * E) + 1 / (40 * E) = 11 / (40 * E) := by field_simp; ring
  have hbound : 1 / (4 * E) + δ ≤ 11 / (40 * E) := by linarith
  have hlo : 160 * E / 11 ≤ 4 / (1 / (4 * E) + δ) := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 160 * E / 11)
    have heq : (160 * E / 11) * (11 / (40 * E)) = 4 := by field_simp; ring
    linarith
  have hr : 3 / (1 / (4 * E)) + 1 / (5 * (1 / (4 * E))) + E = 69 * E / 5 := by
    field_simp
    ring
  rw [hr]
  linarith

def quadraticZeroFreeBudget (q : ℕ) (t : ℝ) : ℝ :=
  120 + 4 * primitiveLFunctionLogBudget q t + zetaLogBudget (2 * t) + Real.log q

/--
@isnad1 id=le.0h2v.s4.21f1c3630aeb from=translated src=- shape=787c1379 vocab=e87f135b
-/
theorem quadraticZeroFreeBudget_ge (q : ℕ) (t : ℝ) :
    120 ≤ quadraticZeroFreeBudget q t := by
  have hK := primitiveLFunctionLogBudget_nonneg q t
  have hZ := zetaLogBudget_nonneg (2 * t)
  have hq := Real.log_natCast_nonneg q
  unfold quadraticZeroFreeBudget
  linarith

end TwinPrime.Analytic
