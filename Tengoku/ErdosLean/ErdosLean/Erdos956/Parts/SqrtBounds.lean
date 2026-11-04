import Tengoku.ErdosLean.ErdosLean.Erdos956.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős #956 — Part 1: elementary bounds on `r(t) = √(1+t²)`

Note, Lemma 1, estimate (5) with `u = t²`:
`1 - u/2 ≤ (1+u)^{-1/2} ≤ 1 - u/2 + u²/2` for `u ≥ 0`.
Proof: set `r = rr t`, use `r² = 1 + t²`, `r ≥ 1`,
and reduce to polynomial inequalities (`nlinarith`).
-/

namespace Erdos956

/--
@isnad1 id=eq.0h1v.s5.1389345ae859 from=translated src=- shape=a7460c21 vocab=10a35809
-/
lemma rr_sq (t : ℝ) : rr t ^ 2 = 1 + t ^ 2 := by
  unfold rr
  rw [Real.sq_sqrt (by positivity)]

/--
@isnad1 id=le.0h1v.s3.ea7ffc5ab363 from=translated src=- shape=8a62b088 vocab=79246381
-/
lemma one_le_rr (t : ℝ) : 1 ≤ rr t := by
  have h0 : 0 ≤ rr t := Real.sqrt_nonneg _
  nlinarith [rr_sq t, sq_nonneg t]

/--
@isnad1 id=lt.0h1v.s3.0cd24fb3bb02 from=translated src=- shape=8a62b088 vocab=6e66c496
-/
lemma rr_pos (t : ℝ) : 0 < rr t := by
  linarith [one_le_rr t]

/-- `1 - t²/2 ≤ 1/√(1+t²)`.
@isnad1 id=le.0h1v.s6.afcaea02ce6b from=translated src=- shape=e84f3dde vocab=66352e9d
-/
lemma inv_rr_lower (t : ℝ) : 1 - t ^ 2 / 2 ≤ 1 / rr t := by
  have h1 := rr_sq t
  have h2 := one_le_rr t
  rw [le_div_iff₀ (by linarith)]
  set r := rr t
  set u := t ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  rcases le_or_gt 2 u with h | h
  · nlinarith
  · -- (1 - u/2) r ≤ 1 since ((1-u/2) r)^2 = (1+u)(1-u/2)^2 ≤ 1
    have hp : 0 < 1 - u / 2 := by linarith
    have hsq : ((1 - u / 2) * r) ^ 2 ≤ 1 := by
      rw [mul_pow, h1]
      nlinarith [mul_nonneg hu0 hu0, mul_nonneg (mul_nonneg hu0 hu0) (by linarith : (0:ℝ) ≤ 3 - u)]
    nlinarith [mul_pos hp (by linarith : (0:ℝ) < r)]

/-- `1/√(1+t²) ≤ 1 - t²/2 + t⁴/2`.
@isnad1 id=le.0h1v.s6.d5ecdcb18c54 from=translated src=- shape=fbbfe871 vocab=3381c370
-/
lemma inv_rr_upper (t : ℝ) : 1 / rr t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 2 := by
  have h1 := rr_sq t
  have h2 := one_le_rr t
  rw [div_le_iff₀ (by linarith)]
  set r := rr t
  set u := t ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  have hp : 0 < 1 - u / 2 + u ^ 2 / 2 := by nlinarith [sq_nonneg (u - 1/2)]
  have hpoly : 0 ≤ 1 + 3 * u - u ^ 2 + u ^ 3 := by
    nlinarith [sq_nonneg (u - 1), mul_nonneg hu0 (sq_nonneg (u - 1))]
  have hsq : 1 ≤ ((1 - u / 2 + u ^ 2 / 2) * r) ^ 2 := by
    rw [mul_pow, h1]
    nlinarith [mul_nonneg (sq_nonneg u) hpoly]
  have hpos : 0 < (1 - u / 2 + u ^ 2 / 2) * r := mul_pos hp (by linarith)
  have : t ^ 4 = u ^ 2 := by rw [hu]; ring
  rw [this]
  nlinarith

end Erdos956
