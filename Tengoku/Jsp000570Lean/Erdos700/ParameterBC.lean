import Tengoku.Jsp000570Lean.Erdos700.PairBC
import Tengoku.Jsp000570Lean.Erdos700.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The `(P+b,P+c)` exclusion with the boundary-separation parameters and source digit bounds.
All auxiliary size hypotheses of `PairBC.source_pair_exclusion_of_large_base`
are discharged here from the uniform parameter assumptions.
-/

namespace Erdos700.FourPrime.ParameterBC

/-- No positive integer has the source digit bounds for `P+b`, a source
quotient divisible by `P+c`, and the target low and middle digit bounds for
`P+c`, under the four-prime construction's boundary-separation parameter inequalities.

This is an integer arithmetic theorem.  Primality is not needed once the
source representation, divisibility, and target digit inequalities have been
obtained.  No auxiliary normalized-digit or size hypothesis is required.
@isnad1 id=false.15h8v.s9.5ef748806651 from=translated src=- shape=dcdcb01b vocab=82d94ad8
-/
theorem pairBC_actual_digits (a b c p u v w k : ℤ)
    (ha : 1 ≤ a) (hb : 3 * a ≤ b) (hc : 3 * b - a + 1 ≤ c)
    (hp : 12 * c ^ 3 ≤ p)
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hw0 : 0 ≤ w)
    (hu : u ≤ a + c - 3 * b - 1)
    (hv : v ≤ p + b - ((2 * b - a) * c + 2 * a * b - 3 * b ^ 2))
    (hw : w ≤ b * (b - a) * (c - b))
    (hk : 0 < k)
    (hsource : k = (p + b) * (u * (p + b) ^ 2 + v * (p + b) + w))
    (hdiv : (p + c) ∣ u * (p + b) ^ 2 + v * (p + b) + w)
    (hlow : (k / (p + c)) % (p + c) ≤
      p + c - c * (c - a) * (c - b))
    (hmiddle : (k / (p + c) / (p + c)) % (p + c) ≤
      3 * c ^ 2 - 2 * c * (a + b) + a * b - 1) : False := by
  have hbpos : 0 < b := by linarith only [ha, hb]
  have hc9 : 9 ≤ c := by
    have h := Bounds.c_at_least_9 a b c ha hb hc
    omega
  have hc1 : 1 ≤ c := by omega
  have hc2 : 2 ≤ c := by omega
  have hd : 0 < c - b := by
    have h := Bounds.b_less_c a b c ha hb hc
    linarith only [h]
  have hdc : c - b < c := by linarith only [hbpos]
  have hLsize : b * (b - a) ≤ c ^ 2 := by
    have h := Bounds.L_less_c_squared a b c ha hb hc
    nlinarith only [h]
  have huc : u < c := by
    have h := Bounds.R_less_than_c a b c ha hb hc
    linarith only [hu, h]
  have hBpos : 0 < (2 * b - a) * c + 2 * a * b - 3 * b ^ 2 := by
    have h := Bounds.B_positive a b c ha hb hc
    nlinarith only [h]
  have hvq : v < p + c := by nlinarith only [hv, hBpos, hd]
  have hwL : w ≤ (c - b) * (b * (b - a)) := by nlinarith only [hw]
  have hUpos : 0 < 3 * c ^ 2 - 2 * c * (a + b) + a * b := by
    have h := Bounds.U_positive a b c ha hb hc
    nlinarith only [h]
  have hUlo : 1 ≤ 3 * c ^ 2 - 2 * c * (a + b) + a * b := by omega
  have hUhi : 3 * c ^ 2 - 2 * c * (a + b) + a * b ≤ 3 * c ^ 2 := by
    have h := Bounds.U_less_than_3c_squared a b c ha hb hc
    nlinarith only [h]
  have hlarge : 10 * c ^ 3 < p + c := by
    have h := (Bounds.large_base_thresholds c p hc2 hp).1
    have hc3 : 0 ≤ c ^ 3 := pow_nonneg (by omega : 0 ≤ c) 3
    nlinarith only [h, hc3, hc1]
  have hLlow : b * (b - a) < c * (c - a) := by
    have h := Bounds.p2_to_p3_low_gap a b c ha hb hc
    nlinarith only [h]
  have hF : (c - b) * (b * (b - a)) < c * (c - a) * (c - b) := by
    nlinarith only [mul_lt_mul_of_pos_left hLlow hd]
  have hbase : p + c - (c - b) = p + b := by ring
  apply Erdos700.PairBC.source_pair_exclusion_of_large_base
    (q := p + c) (d := c - b) (c := c) (L := b * (b - a))
    (U := 3 * c ^ 2 - 2 * c * (a + b) + a * b)
    (F := c * (c - a) * (c - b)) (u := u) (v := v) (w := w) (k := k)
    hd hdc hLsize hu0 huc hv0 hvq hw0 hwL hUlo hUhi hlarge hF hk
  · simpa only [hbase] using hsource
  · simpa only [hbase] using hdiv
  · exact hlow
  · exact hmiddle

end Erdos700.FourPrime.ParameterBC
