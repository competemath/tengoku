import Tengoku.Jsp000570Lean.Erdos700.Arithmetic
import Tengoku.Jsp000570Lean.Erdos700.PairADigits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos700.FourPrime.PairPDigits
open PairADigits

theorem carry_zero (q d S T Z u v w : ℤ)
    (hd : 0 ≤ d) (hu0 : 0 ≤ u) (hu : u ≤ S)
    (hv0 : 0 ≤ v) (hv : v ≤ T) (hw0 : 0 ≤ w) (hw : w ≤ Z)
    (hsize1 : d^2*S+Z < q) (hsize2 : d*T < q)
    (hdiv : q ∣ u*(q-d)^2+v*(q-d)+w) : u*d^2-v*d+w = 0 := by
  have hdv := mul_le_mul_of_nonneg_left hv hd
  have hdu := mul_le_mul_of_nonneg_left hu (sq_nonneg d)
  have hu' := mul_nonneg hu0 (sq_nonneg d)
  have hv' := mul_nonneg hv0 hd
  have hlo : -q < u*d^2-v*d+w := by nlinarith only [hdv, hu', hw0, hsize2]
  have hhi : u*d^2-v*d+w < q := by nlinarith only [hdu, hv', hw, hsize1]
  have hdiv' : q ∣ u*d^2-v*d+w := by
    have hid : u*(q-d)^2+v*(q-d)+w - q*(u*q+v-2*u*d) = u*d^2-v*d+w := by ring
    rw [← hid]
    exact dvd_sub hdiv (dvd_mul_right q (u*q+v-2*u*d))
  by_cases hnonneg : 0 ≤ u*d^2-v*d+w
  · exact Int.eq_zero_of_dvd_of_nonneg_of_lt hnonneg hhi hdiv'
  · have hneg : 0 ≤ -(u*d^2-v*d+w) := by omega
    have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt hneg (by omega) (dvd_neg.mpr hdiv')
    omega

theorem quotient_after_zero_carry (q d u v w k : ℤ) (hq : 0 < q)
    (hc : u*d^2-v*d+w = 0)
    (hk : k = (q-d)*(u*(q-d)^2+v*(q-d)+w)) :
    k/q = u*q^2+(v-3*d*u)*q+d*(2*d*u-v) := by
  apply Int.ediv_eq_of_eq_mul_right hq.ne'
  have hw : w = v*d-u*d^2 := by linarith
  rw [hk, hw]
  ring

/-- Full actual-digit exclusion for the pair `(P,P+b)`.-/
theorem pairPB_actual_digits (a b c q u v w k : ℤ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hu0 : 0 ≤ u) (hu : u ≤ a+b+c)
    (hv0 : 0 ≤ v) (hv : v ≤ a*b+a*c+b*c)
    (hw0 : 0 ≤ w) (hw : w ≤ a*b*c)
    (hsize1 : b^2*(a+b+c)+a*b*c < q)
    (hsize2 : b*(b-a)*(c-b)+b*(a*b+a*c+b*c) < q)
    (hsizeM : 2*b*(a+b+c) < q) (hsizeu : a+b+c < q)
    (hdiv : q ∣ u*(q-b)^2+v*(q-b)+w)
    (hk : k = (q-b)*(u*(q-b)^2+v*(q-b)+w)) (hk_ne : k ≠ 0)
    (hlow : (k/q)%q ≤ b*(b-a)*(c-b))
    (hmiddle : (k/q/q)%q ≤ q-((2*b-a)*c+2*a*b-3*b^2))
    (hhigh : (k/q/q/q)%q ≤ a+c-3*b-1) : False := by
  have hb : 0 < b := lt_trans ha hab
  have hc : 0 < c := lt_trans hb hbc
  have hC : 0 ≤ b*(b-a)*(c-b) := by positivity
  have hZ : 0 ≤ a*b*c := by positivity
  have hq : 0 < q := by linarith [mul_nonneg (sq_nonneg b) (by linarith : 0 ≤ a+b+c)]
  have hcarry := carry_zero q b (a+b+c) (a*b+a*c+b*c) (a*b*c) u v w
    hb.le hu0 hu hv0 hv hw0 hw hsize1 (by linarith) hdiv
  let t := v-b*u
  have hwt : w = b*t := by dsimp [t]; nlinarith only [hcarry]
  have ht0 : 0 ≤ t := by nlinarith only [hwt, hw0, hb]
  have ht : t ≤ a*c := by nlinarith only [hwt, hw, hb]
  have hbu := mul_nonneg hb.le hu0
  have htV : t ≤ a*b+a*c+b*c := by dsimp [t]; linarith
  let K := b*(b*u-t)
  let M := t-2*b*u
  have hn : k/q = u*q^2+M*q+K := by
    have hn := quotient_after_zero_carry q b u v w k hq hcarry hk
    dsimp [M, K, t]
    nlinarith only [hn]
  have hKlo : -(b*(a*b+a*c+b*c)) ≤ K := by
    have hs := mul_le_mul_of_nonneg_left htV hb.le
    have hpos := mul_nonneg hb.le hbu
    dsimp [K]
    nlinarith only [hs, hpos]
  have hKmin : -q < K := by linarith
  have hKup : K < q := by
    have hs := mul_le_mul_of_nonneg_left hu (sq_nonneg b)
    have hbt := mul_nonneg hb.le ht0
    dsimp [K]
    nlinarith only [hs, hbt, hsize1, hZ]
  have hMlo : -q < M := by
    have hs := mul_le_mul_of_nonneg_left hu (by positivity : (0:ℤ) ≤ 2*b)
    dsimp [M]
    nlinarith only [hs, ht0, hsizeM]
  have hK0 : 0 ≤ K := by
    by_contra hneg
    have hrem := negative_low_remainder (k/q) q u M K hq hKmin (by omega) hn
    rw [hrem] at hlow
    linarith
  have htbu : t ≤ b*u := by
    have hin := (mul_nonneg_iff_of_pos_left hb).mp hK0
    linarith
  have hupos : 0 < u := by
    by_contra hnot
    have hu_eq : u = 0 := by omega
    have ht_eq : t = 0 := by rw [hu_eq] at htbu; nlinarith
    have hv_eq : v = 0 := by dsimp [t] at ht_eq; simpa [hu_eq] using ht_eq
    have hw_eq : w = 0 := by rw [hwt, ht_eq]; ring
    apply hk_ne
    rw [hk, hu_eq, hv_eq, hw_eq]
    ring
  have hMneg : M < 0 := by
    have hpos := mul_pos hb hupos
    dsimp [M]
    nlinarith only [hpos, htbu]
  have hdigits := borrow_middle_digits (k/q) q u M K hq hK0 hKup hMlo hMneg
    hupos (by linarith : u ≤ q) hn
  rw [hdigits.1] at hlow
  rw [hdigits.2.1] at hmiddle
  rw [hdigits.2.2] at hhigh
  apply Arithmetic.pairPB_impossible a b c u t hb (by linarith)
  · change b*(b*u-t) ≤ b*(b-a)*(c-b) at hlow
    have hh : b*(b*u-t) ≤ b*((b-a)*(c-b)) := by nlinarith only [hlow]
    exact (mul_le_mul_iff_right₀ hb).mp hh
  · dsimp [M] at hmiddle
    linarith

/-- Full actual-digit exclusion for the pair `(P,P+c)`.-/
theorem pairPC_actual_digits (a b c q u v w k : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hsep : a+b < c)
    (hu0 : 0 ≤ u) (hu : u ≤ a+b+c)
    (hv0 : 0 ≤ v) (hv : v ≤ a*b+a*c+b*c)
    (hw0 : 0 ≤ w) (hw : w ≤ a*b*c)
    (hsize1 : c^2*(a+b+c)+a*b*c < q)
    (hsize2 : c*(a*b+a*c+b*c) < q)
    (hsizeM : 2*c*(a+b+c)+(3*c^2-2*c*(a+b)+a*b) < q)
    (hsizeu : a+b+c < q)
    (hU0 : 0 ≤ 3*c^2-2*c*(a+b)+a*b)
    (hdiv : q ∣ u*(q-c)^2+v*(q-c)+w)
    (hk : k = (q-c)*(u*(q-c)^2+v*(q-c)+w)) (hk_ne : k ≠ 0)
    (hlow : (k/q)%q ≤ q-c*(c-a)*(c-b))
    (hmiddle : (k/q/q)%q ≤ 3*c^2-2*c*(a+b)+a*b-1) : False := by
  have hc : 0 < c := by linarith
  have hZ : 0 ≤ a*b*c := by positivity
  have hq : 0 < q := by linarith [mul_nonneg (sq_nonneg c) (by linarith : 0 ≤ a+b+c)]
  have hcarry := carry_zero q c (a+b+c) (a*b+a*c+b*c) (a*b*c) u v w
    hc.le hu0 hu hv0 hv hw0 hw hsize1 hsize2 hdiv
  let t := v-c*u
  have hwt : w = c*t := by dsimp [t]; nlinarith only [hcarry]
  have ht0 : 0 ≤ t := by nlinarith only [hwt, hw0, hc]
  have ht : t ≤ a*b := by nlinarith only [hwt, hw, hc]
  have hcu := mul_nonneg hc.le hu0
  let K := c*(c*u-t)
  let M := t-2*c*u
  have hn : k/q = u*q^2+M*q+K := by
    have hn := quotient_after_zero_carry q c u v w k hq hcarry hk
    dsimp [M, K, t]
    nlinarith only [hn]
  have hKlo : -(a*b*c) ≤ K := by
    have hs := mul_le_mul_of_nonneg_left ht hc.le
    have hpos := mul_nonneg hc.le hcu
    dsimp [K]
    nlinarith only [hs, hpos]
  have hsqS : 0 ≤ c^2*(a+b+c) := mul_nonneg (sq_nonneg c) (by linarith)
  have hKmin : -q < K := by linarith
  have hKup : K < q := by
    have hs := mul_le_mul_of_nonneg_left hu (sq_nonneg c)
    have hct := mul_nonneg hc.le ht0
    dsimp [K]
    nlinarith only [hs, hct, hsize1, hZ]
  have hMlo : -q < M := by
    have hs := mul_le_mul_of_nonneg_left hu (by positivity : (0:ℤ) ≤ 2*c)
    dsimp [M]
    nlinarith only [hs, ht0, hsizeM, hU0]
  have hK0 : 0 ≤ K := by
    by_contra hneg
    have hrem := negative_low_remainder (k/q) q u M K hq hKmin (by omega) hn
    rw [hrem] at hlow
    exact Arithmetic.pairPC_negative_low_impossible a b c q u t hc hsep hu0 ht hlow
  have htcu : t ≤ c*u := by
    have hin := (mul_nonneg_iff_of_pos_left hc).mp hK0
    linarith
  have hupos : 0 < u := by
    by_contra hnot
    have hu_eq : u = 0 := by omega
    have ht_eq : t = 0 := by rw [hu_eq] at htcu; nlinarith
    have hv_eq : v = 0 := by dsimp [t] at ht_eq; simpa [hu_eq] using ht_eq
    have hw_eq : w = 0 := by rw [hwt, ht_eq]; ring
    apply hk_ne
    rw [hk, hu_eq, hv_eq, hw_eq]
    ring
  have hMneg : M < 0 := Arithmetic.pairPC_middle_negative c u t hc hupos hK0
  have hdigits := borrow_middle_digits (k/q) q u M K hq hK0 hKup hMlo hMneg
    hupos (by linarith : u ≤ q) hn
  rw [hdigits.2.1] at hmiddle
  have hs := mul_le_mul_of_nonneg_left hu (by positivity : (0:ℤ) ≤ 2*c)
  dsimp [M] at hmiddle
  nlinarith only [hmiddle, hs, ht0, hsizeM]

end Erdos700.FourPrime.PairPDigits
