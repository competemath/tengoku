import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The polynomial bound for a bilinear box

These elementary real inequalities isolate the polynomial part of the
large-sieve box estimate. They do not perform the dyadic box assembly or
supply a mean-value theorem.
-/

noncomputable section

namespace TwinPrime.Analytic

/-- A single side of the square-root box polynomial.
@isnad1 id=le.2h2v.s6.3ed758d62fe7 from=translated src=- shape=dda5c098 vocab=339213db
-/
theorem sqrt_mul_add_le (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C) :
    Real.sqrt (M * (M + C)) ≤ M + Real.sqrt C * Real.sqrt M := by
  apply (Real.sqrt_le_left (by positivity)).mpr
  have hs : (Real.sqrt C * Real.sqrt M) ^ 2 = C * M := by
    rw [mul_pow, Real.sq_sqrt hC, Real.sq_sqrt hM]
  nlinarith [mul_nonneg hM (mul_nonneg (Real.sqrt_nonneg C) (Real.sqrt_nonneg M))]

/-- Expansion of the box polynomial into its three types of terms.
@isnad1 id=le.3h3v.s7.14556be01da5 from=translated src=- shape=405e17f6 vocab=339213db
-/
theorem bilinear_box_sqrt_le_expansion (M N C : ℝ)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hC : 0 ≤ C) :
    Real.sqrt (M * N * (M + C) * (N + C)) ≤
      M * N + Real.sqrt C * (M * Real.sqrt N + Real.sqrt M * N) +
        C * Real.sqrt (M * N) := by
  have heq : M * N * (M + C) * (N + C) = (M * (M + C)) * (N * (N + C)) := by ring
  rw [heq, Real.sqrt_mul (mul_nonneg hM (add_nonneg hM hC))]
  calc
    _ ≤ (M + Real.sqrt C * Real.sqrt M) * (N + Real.sqrt C * Real.sqrt N) :=
      mul_le_mul (sqrt_mul_add_le M C hM hC) (sqrt_mul_add_le N C hN hC)
        (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by
      rw [Real.sqrt_mul hM]
      calc
        _ = M * N + Real.sqrt C * (M * Real.sqrt N + Real.sqrt M * N) +
            (Real.sqrt C) ^ 2 * (Real.sqrt M * Real.sqrt N) := by ring
        _ = _ := by rw [Real.sq_sqrt hC]

/-- A mixed side term is controlled by the product bound and the lower
bound for the side appearing under its square root.
@isnad1 id=le.4h4v.s6.e6bfae95f891 from=translated src=- shape=bd4ac70a vocab=4374279d
-/
theorem mul_sqrt_le_div_sqrt (M N V T : ℝ) (hM : 0 ≤ M)
    (hV : 0 < V) (hVN : V ≤ N) (hMN : M * N ≤ T) :
    M * Real.sqrt N ≤ T / Real.sqrt V := by
  have hN : 0 < N := hV.trans_le hVN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hT : 0 ≤ T := (mul_nonneg hM hN.le).trans hMN
  calc
    _ = (M * N) / Real.sqrt N := by
      apply (eq_div_iff hsN.ne').mpr
      rw [mul_assoc, Real.mul_self_sqrt hN.le]
    _ ≤ T / Real.sqrt N := div_le_div_of_nonneg_right hMN hsN.le
    _ ≤ _ := div_le_div_of_nonneg_left hT hsV (Real.sqrt_le_sqrt hVN)

/-- The polynomial bound for a nonempty bilinear box, with explicit
positive lower cutoffs and a nonnegative large-sieve constant.
@isnad1 id=le.6h6v.s7.678cbd837d34 from=translated src=- shape=dbaf057f vocab=a2bb450f
-/
theorem bilinear_box_polynomial_le (M N U V T C : ℝ)
    (hU : 0 < U) (hUM : U ≤ M) (hV : 0 < V) (hVN : V ≤ N)
    (hMN : M * N ≤ T) (hC : 0 ≤ C) :
    Real.sqrt (M * N * (M + C) * (N + C)) ≤
      T + Real.sqrt C * T * (1 / Real.sqrt U + 1 / Real.sqrt V) + C * Real.sqrt T := by
  have hM : 0 ≤ M := (hU.trans_le hUM).le
  have hN : 0 ≤ N := (hV.trans_le hVN).le
  have hmixN := mul_sqrt_le_div_sqrt M N V T hM hV hVN hMN
  have hmixM := mul_sqrt_le_div_sqrt N M U T hN hU hUM (by simpa only [mul_comm] using hMN)
  calc
    _ ≤ M * N + Real.sqrt C * (M * Real.sqrt N + Real.sqrt M * N) +
        C * Real.sqrt (M * N) := bilinear_box_sqrt_le_expansion M N C hM hN hC
    _ ≤ T + Real.sqrt C * (T / Real.sqrt V + T / Real.sqrt U) + C * Real.sqrt T := by
      apply add_le_add
      · exact add_le_add hMN (mul_le_mul_of_nonneg_left
          (add_le_add hmixN (by simpa only [mul_comm] using hmixM)) (Real.sqrt_nonneg C))
      · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hMN) hC
    _ = _ := by ring

/-- Absorb the square-root logarithmic factor into `L ≥ 1` after putting
`C = Q² L`. This isolates the polynomial used by the later Vaughan boxes.
@isnad1 id=le.7h7v.s8.61c674db9d17 from=translated src=- shape=d69c6f3f vocab=d44e7500
-/
theorem bilinear_box_polynomial_le_log_factor (M N U V T Q L : ℝ)
    (hU : 0 < U) (hUM : U ≤ M) (hV : 0 < V) (hVN : V ≤ N)
    (hMN : M * N ≤ T) (hQ : 0 ≤ Q) (hL : 1 ≤ L) :
    Real.sqrt (M * N * (M + Q ^ 2 * L) * (N + Q ^ 2 * L)) ≤
      L * (T + Q * T * (1 / Real.sqrt U + 1 / Real.sqrt V) + Q ^ 2 * Real.sqrt T) := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hT : 0 ≤ T := (mul_nonneg (hU.trans_le hUM).le (hV.trans_le hVN).le).trans hMN
  have hsL : Real.sqrt L ≤ L := Real.sqrt_le_self_iff.mpr (Or.inr hL)
  have hsum : 0 ≤ 1 / Real.sqrt U + 1 / Real.sqrt V := by positivity
  have hsC : Real.sqrt (Q ^ 2 * L) = Q * Real.sqrt L := by
    rw [Real.sqrt_mul (sq_nonneg Q), Real.sqrt_sq hQ]
  calc
    _ ≤ T + Real.sqrt (Q ^ 2 * L) * T * (1 / Real.sqrt U + 1 / Real.sqrt V) +
        (Q ^ 2 * L) * Real.sqrt T :=
      bilinear_box_polynomial_le M N U V T (Q ^ 2 * L) hU hUM hV hVN hMN (by positivity)
    _ ≤ L * T + (Q * L) * T * (1 / Real.sqrt U + 1 / Real.sqrt V) +
        (Q ^ 2 * L) * Real.sqrt T := by
      rw [hsC]
      apply add_le_add _ le_rfl
      exact add_le_add (by nlinarith) (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsL hQ) hT) hsum)
    _ = _ := by ring

end TwinPrime.Analytic
