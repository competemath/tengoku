import Tengoku.Jsp000570Lean.Erdos700.PairA
import Tengoku.Jsp000570Lean.Erdos700.Bounds
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos700.FourPrime.PairADigits

/-- Exact Euclidean quotient and remainder for an already bounded remainder.-/
theorem quotient_remainder (n q t r : ℤ) (hq : 0 < q)
    (hr0 : 0 ≤ r) (hrq : r < q) (hn : n = t * q + r) :
    n % q = r ∧ n / q = t := by
  subst n
  constructor
  · rw [Int.add_emod, Int.mul_emod]
    simp [Int.emod_eq_of_lt hr0 hrq]
  · rw [Int.mul_add_ediv_right _ _ hq.ne', Int.ediv_eq_zero_of_lt hr0 hrq]
    simp

/-- A negative constant coefficient between -q and 0 has remainder q+K.-/
theorem negative_low_remainder (n q u M K : ℤ) (hq : 0 < q)
    (hKlo : -q < K) (hKneg : K < 0)
    (hn : n = u * q ^ 2 + M * q + K) : n % q = q + K := by
  have hr0 : 0 ≤ q + K := by omega
  have hrq : q + K < q := by omega
  apply (quotient_remainder n q (u * q + M - 1) (q + K) hq hr0 hrq ?_).1
  nlinarith only [hn]

/-- The actual three digits when the constant is nonnegative and the
middle coefficient is negative. The second high quotient is repeated
Euclidean division, which equals division by q^2 for positive q.-/
theorem borrow_middle_digits (n q u M K : ℤ) (hq : 0 < q)
    (hK0 : 0 ≤ K) (hKq : K < q)
    (hMlo : -q < M) (hMneg : M < 0)
    (hu0 : 0 < u) (huq : u ≤ q)
    (hn : n = u * q ^ 2 + M * q + K) :
    n % q = K ∧ (n / q) % q = q + M ∧ (n / q / q) % q = u - 1 := by
  have h₁ := quotient_remainder n q (u * q + M) K hq hK0 hKq
    (by nlinarith only [hn])
  have h₂ := quotient_remainder (n / q) q (u - 1) (q + M) hq
    (by omega) (by omega) (by nlinarith only [h₁.2])
  refine ⟨h₁.1, h₂.1, ?_⟩
  rw [h₂.2]
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- Full integer exclusion for the pair `(P+a,P+b)`, with `q=P+b`.

The three target hypotheses are actual Euclidean remainders of `k/q`, not
presupposed normalized coefficients. The four explicit size hypotheses
are weaker than the global `P >= 12*c^3` condition in the paper. The
source divisibility `q | k/(P+a)` is the input obtained from the two
prime divisibilities and coprimality; no primality is used in this lemma.-/
theorem pairAB_actual_digits
    (a b c q u v w k : ℤ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hu0 : 0 ≤ u) (hu : u ≤ b + c - 3 * a)
    (hv0 : 0 ≤ v) (hv : v ≤ b * c - 2 * a * (b + c) + 3 * a ^ 2 - 1)
    (hw0 : 0 ≤ w)
    (hw : w ≤ q - (b - a) - a * (b - a) * (c - a))
    (hsize_u : b + c - 3 * a < q)
    (hsize_M : 3 * (b - a) * (b + c - 3 * a) < q)
    (hsize_K : 2 * (b - a) ^ 2 * (b + c - 3 * a) < q)
    (hsize_low : b * (b - a) * (c - b) +
      (b - a) * (b * c - 2 * a * (b + c) + 3 * a ^ 2) < q)
    (hdiv : q ∣ u * (q - (b - a)) ^ 2 + v * (q - (b - a)) + w)
    (hk : k = (q - (b - a)) *
      (u * (q - (b - a)) ^ 2 + v * (q - (b - a)) + w))
    (hk_ne : k ≠ 0)
    (hlow : (k / q) % q ≤ b * (b - a) * (c - b))
    (hmiddle : (k / q / q) % q ≤
      q - ((2 * b - a) * c + 2 * a * b - 3 * b ^ 2))
    (hhigh : (k / q / q / q) % q ≤ a + c - 3 * b - 1) : False := by
  let d := b - a
  let S := b + c - 3 * a
  let V := b * c - 2 * a * (b + c) + 3 * a ^ 2 - 1
  let C := b * (b - a) * (c - b)
  have hd : 0 < d := by dsimp [d]; omega
  have hC0 : 0 ≤ C := by
    have hb0 : 0 < b := lt_trans ha hab
    have hcb : 0 < c - b := sub_pos.mpr hbc
    dsimp [C]
    exact mul_nonneg (mul_nonneg hb0.le (sub_pos.mpr hab).le) hcb.le
  have hA0 : 0 ≤ a * d * (c - a) := by
    have : 0 < c - a := by omega
    positivity
  change u ≤ S at hu
  change v ≤ V at hv
  change S < q at hsize_u
  change 3 * d * S < q at hsize_M
  change 2 * d ^ 2 * S < q at hsize_K
  have hsize_low : C + d * (V + 1) < q := by
    dsimp [C, d, V]
    nlinarith only [hsize_low]
  change w ≤ q - d - a * d * (c - a) at hw
  have hS0 : 0 ≤ S := le_trans hu0 hu
  have hV0 : 0 ≤ V := le_trans hv0 hv
  have hq : 0 < q := lt_of_le_of_lt hS0 hsize_u
  have hud0 : 0 ≤ u * d ^ 2 := mul_nonneg hu0 (sq_nonneg d)
  have hdv0 : 0 ≤ d * v := mul_nonneg hd.le hv0
  have hdu0 : 0 ≤ d * u := mul_nonneg hd.le hu0
  have hud_upper := mul_le_mul_of_nonneg_left hu (sq_nonneg d)
  have hdv_upper := mul_le_mul_of_nonneg_left hv hd.le
  have hSsquare : 0 ≤ d ^ 2 * S := mul_nonneg (sq_nonneg d) hS0
  have hwq : w < q := by nlinarith only [hw, hd, hA0]
  have hqv : d * V < q := by nlinarith only [hsize_low, hC0, hd]
  have hudq : u * d ^ 2 < q := by nlinarith only [hud_upper, hsize_K, hSsquare]
  obtain ⟨t, ht⟩ := hdiv
  change u * (q - d) ^ 2 + v * (q - d) + w = q * t at ht
  let h := t - u * q - v + 2 * d * u
  have hcarry : u * d ^ 2 - v * d + w = h * q := by
    dsimp [h]
    nlinarith only [ht]
  have hFmin : -q < h * q := by
    nlinarith only [hcarry, hud0, hdv_upper, hqv, hw0]
  have hFmax : h * q < 2 * q := by
    nlinarith only [hcarry, hudq, hwq, hdv0]
  have hh0 : 0 ≤ h := by
    by_contra hn
    have hh : h ≤ -1 := by omega
    have hs := mul_le_mul_of_nonneg_right hh hq.le
    nlinarith only [hs, hFmin]
  have hh1 : h ≤ 1 := by
    by_contra hn
    have hh : 2 ≤ h := by omega
    have hs := mul_le_mul_of_nonneg_right hh hq.le
    nlinarith only [hs, hFmax]
  have hcases : h = 0 ∨ h = 1 := by omega
  let K := d * (2 * d * u - v - h)
  let M := v - 3 * d * u + h
  have hw_eq : w = h * q - u * d ^ 2 + v * d := by
    linarith only [hcarry]
  have hn : k / q = u * q ^ 2 + M * q + K := by
    apply Int.ediv_eq_of_eq_mul_right hq.ne'
    change k = q * (u * q ^ 2 + (v - 3 * d * u + h) * q +
      d * (2 * d * u - v - h))
    change k = (q - d) * (u * (q - d) ^ 2 + v * (q - d) + w) at hk
    rw [hk, hw_eq]
    ring
  have hK_lower : -(d * (V + 1)) ≤ K := by
    have hi : -(V + 1) ≤ 2 * d * u - v - h := by
      nlinarith only [hdu0, hv, hh1]
    have hs := mul_le_mul_of_nonneg_left hi hd.le
    dsimp [K]
    nlinarith only [hs]
  have hK_upper : K < q := by
    have hi : 2 * d * u - v - h ≤ 2 * d * u := by omega
    have hs := mul_le_mul_of_nonneg_left hi hd.le
    dsimp [K]
    nlinarith only [hs, hud_upper, hsize_K]
  have hKlo : -q < K := by
    nlinarith only [hK_lower, hsize_low, hC0]
  have hMlo : -q < M := by
    have hs := mul_le_mul_of_nonneg_left hu
      (show (0 : ℤ) ≤ 3 * d by positivity)
    dsimp [M]
    nlinarith only [hs, hsize_M, hv0, hh0]
  have hK0 : 0 ≤ K := by
    by_contra hneg
    have hneg' : K < 0 := by omega
    have hrem := negative_low_remainder (k / q) q u M K hq hKlo hneg' hn
    change (k / q) % q ≤ C at hlow
    rw [hrem] at hlow
    nlinarith only [hlow, hK_lower, hsize_low]
  have huq : u ≤ q := le_trans hu hsize_u.le
  rcases hcases with hzero | hone
  · have hw_formula : w = d * (v - d * u) := by
      rw [hzero] at hcarry
      nlinarith only [hcarry]
    have hv_lower : d * u ≤ v := by
      have hi : 0 ≤ d * (v - d * u) := by rw [← hw_formula]; exact hw0
      have hh := (mul_nonneg_iff_of_pos_left hd).mp hi
      linarith only [hh]
    have hv_upper : v ≤ 2 * d * u := by
      have hi : 0 ≤ 2 * d * u - v - h :=
        (mul_nonneg_iff_of_pos_left hd).mp hK0
      rw [hzero] at hi
      linarith only [hi]
    have hupos : 0 < u := by
      by_contra hnot
      have hu_eq : u = 0 := by omega
      have hv_eq : v = 0 := by rw [hu_eq] at hv_upper; nlinarith only [hv_upper, hv0]
      have hw_eq0 : w = 0 := by rw [hw_formula, hu_eq, hv_eq]; ring
      apply hk_ne
      rw [hk, hu_eq, hv_eq, hw_eq0]
      ring
    have hMneg : M < 0 := by
      have hp := mul_pos hd hupos
      dsimp [M]
      rw [hzero]
      nlinarith only [hv_upper, hp]
    have hdigits := borrow_middle_digits (k / q) q u M K hq hK0 hK_upper
      hMlo hMneg hupos huq hn
    apply PairA.pairAB_h0_from_digits a b c q u v ha hab hbc
    · simpa [d] using hv_lower
    · rw [hdigits.2.2] at hhigh
      exact hhigh
    · rw [hdigits.2.1] at hmiddle
      simpa only [M, hzero, add_zero, d] using hmiddle
  · have htbound : a * (c - a) + 1 ≤ d * u - v := by
      have hs : d * (a * (c - a) + 1) ≤ d * (d * u - v) := by
        rw [hone] at hcarry
        nlinarith only [hcarry, hw]
      exact (mul_le_mul_iff_right₀ hd).mp hs
    have htpos : 1 < d * u - v := by
      have hp : 0 < a * (c - a) := mul_pos ha (by omega)
      linarith only [htbound, hp]
    have hupos : 0 < u := by
      by_contra hnot
      have hu_eq : u = 0 := by omega
      rw [hu_eq] at htpos
      nlinarith only [htpos, hv0]
    have hMneg : M < 0 := by
      dsimp [M]
      rw [hone]
      nlinarith only [htpos, hdu0]
    have hdigits := borrow_middle_digits (k / q) q u M K hq hK0 hK_upper
      hMlo hMneg hupos huq hn
    apply PairA.pairAB_h1_from_digits a b c q u v hab
    · rw [hdigits.1] at hlow
      simpa only [K, hone, d] using hlow
    · rw [hdigits.2.2] at hhigh
      exact hhigh
    · rw [hdigits.2.1] at hmiddle
      simpa only [M, hone, d] using hmiddle

/-- Full integer exclusion for the pair `(P+a,P+c)`, with `q=P+c`.
Only the actual low and middle target digits are needed. As in the AB
lemma, all carry choices and Euclidean normalizations are proved here.-/
theorem pairAC_actual_digits
    (a b c q u v w k : ℤ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hsep : 0 < c + 3 * a - 2 * b)
    (hu0 : 0 ≤ u) (hu : u ≤ b + c - 3 * a)
    (hv0 : 0 ≤ v) (hv : v ≤ b * c - 2 * a * (b + c) + 3 * a ^ 2 - 1)
    (hw0 : 0 ≤ w)
    (hw : w ≤ q - (c - a) - a * (b - a) * (c - a))
    (hsize_u : b + c - 3 * a < q)
    (hsize_M : 3 * (c - a) * (b + c - 3 * a) < q)
    (hsize_K : 2 * (c - a) ^ 2 * (b + c - 3 * a) < q)
    (hsize_low : (c - a) * (b * c - 2 * a * (b + c) + 3 * a ^ 2) < q)
    (hsize_middle : 3 * (c - a) * (b + c - 3 * a) +
      (3 * c ^ 2 - 2 * c * (a + b) + a * b) - 1 < q)
    (hdiv : q ∣ u * (q - (c - a)) ^ 2 + v * (q - (c - a)) + w)
    (hk : k = (q - (c - a)) *
      (u * (q - (c - a)) ^ 2 + v * (q - (c - a)) + w))
    (hk_ne : k ≠ 0)
    (hlow : (k / q) % q ≤ q - c * (c - a) * (c - b))
    (hmiddle : (k / q / q) % q ≤
      (3 * c ^ 2 - 2 * c * (a + b) + a * b) - 1) : False := by
  let d := c - a
  let S := b + c - 3 * a
  let V := b * c - 2 * a * (b + c) + 3 * a ^ 2 - 1
  let U := 3 * c ^ 2 - 2 * c * (a + b) + a * b
  have hac : a < c := lt_trans hab hbc
  have hd : 0 < d := sub_pos.mpr hac
  have hA0 : 0 ≤ a * (b - a) * d := by
    have hba : 0 < b - a := sub_pos.mpr hab
    positivity
  change u ≤ S at hu
  change v ≤ V at hv
  change S < q at hsize_u
  change 3 * d * S < q at hsize_M
  change 2 * d ^ 2 * S < q at hsize_K
  have hsize_low : d * (V + 1) < q := by
    dsimp [d, V]
    nlinarith only [hsize_low]
  change 3 * d * S + U - 1 < q at hsize_middle
  change w ≤ q - d - a * (b - a) * d at hw
  change (k / q / q) % q ≤ U - 1 at hmiddle
  have hS0 : 0 ≤ S := le_trans hu0 hu
  have hV0 : 0 ≤ V := le_trans hv0 hv
  have hq : 0 < q := lt_of_le_of_lt hS0 hsize_u
  have hud0 : 0 ≤ u * d ^ 2 := mul_nonneg hu0 (sq_nonneg d)
  have hdv0 : 0 ≤ d * v := mul_nonneg hd.le hv0
  have hdu0 : 0 ≤ d * u := mul_nonneg hd.le hu0
  have hud_upper := mul_le_mul_of_nonneg_left hu (sq_nonneg d)
  have hdv_upper := mul_le_mul_of_nonneg_left hv hd.le
  have hSsquare : 0 ≤ d ^ 2 * S := mul_nonneg (sq_nonneg d) hS0
  have hwq : w < q := by nlinarith only [hw, hd, hA0]
  have hqv : d * V < q := by nlinarith only [hsize_low, hd]
  have hudq : u * d ^ 2 < q := by nlinarith only [hud_upper, hsize_K, hSsquare]
  obtain ⟨t, ht⟩ := hdiv
  change u * (q - d) ^ 2 + v * (q - d) + w = q * t at ht
  let h := t - u * q - v + 2 * d * u
  have hcarry : u * d ^ 2 - v * d + w = h * q := by
    dsimp [h]
    nlinarith only [ht]
  have hFmin : -q < h * q := by
    nlinarith only [hcarry, hud0, hdv_upper, hqv, hw0]
  have hFmax : h * q < 2 * q := by
    nlinarith only [hcarry, hudq, hwq, hdv0]
  have hh0 : 0 ≤ h := by
    by_contra hn
    have hh : h ≤ -1 := by omega
    have hs := mul_le_mul_of_nonneg_right hh hq.le
    nlinarith only [hs, hFmin]
  have hh1 : h ≤ 1 := by
    by_contra hn
    have hh : 2 ≤ h := by omega
    have hs := mul_le_mul_of_nonneg_right hh hq.le
    nlinarith only [hs, hFmax]
  let K := d * (2 * d * u - v - h)
  let M := v - 3 * d * u + h
  have hw_eq : w = h * q - u * d ^ 2 + v * d := by
    linarith only [hcarry]
  have hn : k / q = u * q ^ 2 + M * q + K := by
    apply Int.ediv_eq_of_eq_mul_right hq.ne'
    change k = q * (u * q ^ 2 + (v - 3 * d * u + h) * q +
      d * (2 * d * u - v - h))
    change k = (q - d) * (u * (q - d) ^ 2 + v * (q - d) + w) at hk
    rw [hk, hw_eq]
    ring
  have hK_lower : -(d * (V + 1)) ≤ K := by
    have hi : -(V + 1) ≤ 2 * d * u - v - h := by
      nlinarith only [hdu0, hv, hh1]
    have hs := mul_le_mul_of_nonneg_left hi hd.le
    dsimp [K]
    nlinarith only [hs]
  have hK_upper : K < q := by
    have hi : 2 * d * u - v - h ≤ 2 * d * u := by omega
    have hs := mul_le_mul_of_nonneg_left hi hd.le
    dsimp [K]
    nlinarith only [hs, hud_upper, hsize_K]
  have hKlo : -q < K := by
    linarith only [hK_lower, hsize_low]
  have hM_lower : -(3 * d * S) ≤ M := by
    have hs := mul_le_mul_of_nonneg_left hu
      (show (0 : ℤ) ≤ 3 * d by positivity)
    dsimp [M]
    nlinarith only [hs, hv0, hh0]
  have hMlo : -q < M := by linarith only [hM_lower, hsize_M]
  have hK0 : 0 ≤ K := by
    by_contra hneg
    have hneg' : K < 0 := by omega
    have hrem := negative_low_remainder (k / q) q u M K hq hKlo hneg' hn
    rw [hrem] at hlow
    apply PairA.pairAC_negative_low_impossible a b c q u v h hac hsep hu0
    · dsimp [V] at hv
      linarith only [hv, hh1]
    · simpa only [K, d] using hlow
  have hupos : 0 < u := by
    by_contra hnot
    have hu_eq : u = 0 := by omega
    have hk_zero : 0 ≤ (c - a) * (2 * (c - a) * 0 - v - h) := by
      simpa only [K, d, hu_eq] using hK0
    have hzeros := PairA.pairAC_zero_u a c v h hac hv0 hh0 hk_zero
    have hw_zero : w = 0 := by
      rw [hu_eq, hzeros.1, hzeros.2] at hcarry
      nlinarith only [hcarry]
    apply hk_ne
    rw [hk, hu_eq, hzeros.1, hw_zero]
    ring
  have hMneg : M < 0 := by
    exact PairA.pairAC_middle_negative a c u v h hac hupos hK0
  have huq : u ≤ q := le_trans hu hsize_u.le
  have hdigits := borrow_middle_digits (k / q) q u M K hq hK0 hK_upper
    hMlo hMneg hupos huq hn
  rw [hdigits.2.1] at hmiddle
  linarith only [hmiddle, hM_lower, hsize_middle]

/-- All source-A local size requirements follow from the original global
hypotheses, uniformly for every gap `d` between 0 and c.-/
theorem source_a_size_bounds
    (a b c d q : ℤ)
    (ha : 1 ≤ a) (hb : 3 * a ≤ b) (hc : 3 * b - a + 1 ≤ c)
    (hd0 : 0 ≤ d) (hdc : d ≤ c) (hq : 12 * c ^ 3 ≤ q) :
    b + c - 3 * a < q ∧
    3 * d * (b + c - 3 * a) < q ∧
    2 * d ^ 2 * (b + c - 3 * a) < q ∧
    b * (b - a) * (c - b) +
      d * (b * c - 2 * a * (b + c) + 3 * a ^ 2) < q ∧
    d * (b * c - 2 * a * (b + c) + 3 * a ^ 2) < q ∧
    3 * d * (b + c - 3 * a) +
      (3 * c ^ 2 - 2 * c * (a + b) + a * b) - 1 < q := by
  let S := b + c - 3 * a
  let T := b * c - 2 * a * (b + c) + 3 * a ^ 2
  let C := b * (b - a) * (c - b)
  let U := 3 * c ^ 2 - 2 * c * (a + b) + a * b
  have hc9 := Bounds.c_at_least_9 a b c ha hb hc
  have hc1 : 1 ≤ c := by omega
  have hc2 : 2 ≤ c := by omega
  have hc0 : 0 ≤ c := by omega
  have hb_lt_c := Bounds.b_less_c a b c ha hb hc
  have hbc : b ≤ c := by linarith only [hb_lt_c]
  have hS0 : 0 ≤ S := by
    have hs := Bounds.S1_positive a b c ha hb hc
    dsimp [S]
    linarith only [hs]
  have hSupper : S ≤ 2 * c := by
    have hs := Bounds.S1_less_2c a b c ha hb hc
    dsimp [S]
    linarith only [hs]
  have hT0 : 0 ≤ T := by
    have ht := Bounds.T1_positive a b c ha hb hc
    dsimp [T]
    linarith only [ht]
  have hTupper : T ≤ c ^ 2 := by
    have ht := Bounds.T1_less_than_bc a b c ha hb hc
    have hprod := mul_le_mul_of_nonneg_right hbc hc0
    dsimp [T]
    nlinarith only [ht, hprod]
  have hCupper : C < c ^ 3 := by
    have hh := Bounds.C_less_c_cubed a b c ha hb hc
    dsimp [C]
    nlinarith only [hh]
  have hUupper : U < 3 * c ^ 2 := by
    have hh := Bounds.U_less_than_3c_squared a b c ha hb hc
    dsimp [U]
    nlinarith only [hh]
  have hds : d * S ≤ 2 * c ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hdc hS0
    have h₂ := mul_le_mul_of_nonneg_left hSupper hc0
    nlinarith only [h₁, h₂]
  have hd2 : d ^ 2 ≤ c ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hdc) (add_nonneg hc0 hd0)
    nlinarith only [hh]
  have hd2s : d ^ 2 * S ≤ 2 * c ^ 3 := by
    have h₁ := mul_le_mul_of_nonneg_right hd2 hS0
    have h₂ := mul_le_mul_of_nonneg_left hSupper (sq_nonneg c)
    nlinarith only [h₁, h₂]
  have hdt : d * T ≤ c ^ 3 := by
    have h₁ := mul_le_mul_of_nonneg_right hdc hT0
    have h₂ := mul_le_mul_of_nonneg_left hTupper hc0
    nlinarith only [h₁, h₂]
  have hbase := Bounds.large_base_thresholds c q hc2 hq
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos (by omega : 0 < c)
  have hc3 : 0 < c ^ 3 := pow_pos (by omega : 0 < c) 3
  have hcc : c ≤ c ^ 2 := by
    have hh := mul_nonneg hc0 (show (0 : ℤ) ≤ c - 1 by omega)
    nlinarith only [hh]
  change S < q ∧ 3 * d * S < q ∧ 2 * d ^ 2 * S < q ∧
    C + d * T < q ∧ d * T < q ∧ 3 * d * S + U - 1 < q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hSupper, hcc, hbase.2.1, hc2]
  · nlinarith only [hds, hbase.2.1, hc2]
  · nlinarith only [hd2s, hbase.1, hc3]
  · linarith only [hCupper, hdt, hbase.1, hc3]
  · linarith only [hdt, hbase.1, hc3]
  · nlinarith only [hds, hUupper, hbase.2.1, hc2]

/-- AB pair exclusion under the original four-prime parameter bounds.
This theorem still uses integer source/target digits, but no longer has
any auxiliary size hypotheses.-/
theorem pairAB_global_digits
    (a b c q u v w k : ℤ)
    (ha : 1 ≤ a) (hb : 3 * a ≤ b) (hc : 3 * b - a + 1 ≤ c)
    (hq : 12 * c ^ 3 ≤ q)
    (hu0 : 0 ≤ u) (hu : u ≤ b + c - 3 * a)
    (hv0 : 0 ≤ v) (hv : v ≤ b * c - 2 * a * (b + c) + 3 * a ^ 2 - 1)
    (hw0 : 0 ≤ w)
    (hw : w ≤ q - (b - a) - a * (b - a) * (c - a))
    (hdiv : q ∣ u * (q - (b - a)) ^ 2 + v * (q - (b - a)) + w)
    (hk : k = (q - (b - a)) *
      (u * (q - (b - a)) ^ 2 + v * (q - (b - a)) + w))
    (hk_ne : k ≠ 0)
    (hlow : (k / q) % q ≤ b * (b - a) * (c - b))
    (hmiddle : (k / q / q) % q ≤
      q - ((2 * b - a) * c + 2 * a * b - 3 * b ^ 2))
    (hhigh : (k / q / q / q) % q ≤ a + c - 3 * b - 1) : False := by
  have hab' := Bounds.a_less_b a b c ha hb hc
  have hbc' := Bounds.b_less_c a b c ha hb hc
  have hab : a < b := by linarith only [hab']
  have hbc : b < c := by linarith only [hbc']
  have hs := source_a_size_bounds a b c (b - a) q ha hb hc
    (by omega) (by omega) hq
  exact pairAB_actual_digits a b c q u v w k (by omega) hab hbc
    hu0 hu hv0 hv hw0 hw hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1
    hdiv hk hk_ne hlow hmiddle hhigh

/-- AC pair exclusion under the original four-prime parameter bounds.-/
theorem pairAC_global_digits
    (a b c q u v w k : ℤ)
    (ha : 1 ≤ a) (hb : 3 * a ≤ b) (hc : 3 * b - a + 1 ≤ c)
    (hq : 12 * c ^ 3 ≤ q)
    (hu0 : 0 ≤ u) (hu : u ≤ b + c - 3 * a)
    (hv0 : 0 ≤ v) (hv : v ≤ b * c - 2 * a * (b + c) + 3 * a ^ 2 - 1)
    (hw0 : 0 ≤ w)
    (hw : w ≤ q - (c - a) - a * (b - a) * (c - a))
    (hdiv : q ∣ u * (q - (c - a)) ^ 2 + v * (q - (c - a)) + w)
    (hk : k = (q - (c - a)) *
      (u * (q - (c - a)) ^ 2 + v * (q - (c - a)) + w))
    (hk_ne : k ≠ 0)
    (hlow : (k / q) % q ≤ q - c * (c - a) * (c - b))
    (hmiddle : (k / q / q) % q ≤
      (3 * c ^ 2 - 2 * c * (a + b) + a * b) - 1) : False := by
  have hab' := Bounds.a_less_b a b c ha hb hc
  have hbc' := Bounds.b_less_c a b c ha hb hc
  have hab : a < b := by linarith only [hab']
  have hbc : b < c := by linarith only [hbc']
  have hs := source_a_size_bounds a b c (c - a) q ha hb hc
    (by omega) (by omega) hq
  have hsep : 0 < c + 3 * a - 2 * b := by
    have hgap := Bounds.p1_to_p3_low_gap a b c ha hb hc
    have hac : 0 < c - a := by omega
    have heq : 0 < (c - a) * (c + 3 * a - 2 * b) := by
      nlinarith only [hgap]
    exact (mul_pos_iff_of_pos_left hac).mp heq
  exact pairAC_actual_digits a b c q u v w k (by omega) hab hbc hsep
    hu0 hu hv0 hv hw0 hw hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2
    hdiv hk hk_ne hlow hmiddle

end Erdos700.FourPrime.PairADigits
