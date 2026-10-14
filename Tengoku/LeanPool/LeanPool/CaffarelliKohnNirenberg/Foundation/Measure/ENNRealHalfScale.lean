/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku

/-!
# ENNReal Half Scale

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped ENNReal

namespace CKN.Foundation.Measure

/-- For `t > 0` and any extended nonnegative real `X`,
`ENNReal.ofReal A * X / ENNReal.ofReal (t/2) = ENNReal.ofReal (2*A/t) * X`.
@isnad1 id=eq.1h3v.s6.2057bcd81011 from=translated src=- shape=ec2fd271 vocab=beb0ea93
-/
theorem ofReal_mul_div_ofReal_half {A t : ℝ} (ht : 0 < t) (X : ℝ≥0∞) :
    ENNReal.ofReal A * X / ENNReal.ofReal (t / 2) = ENNReal.ofReal (2 * A / t) * X := by
  have ht2 : (0 : ℝ) < t / 2 := by linarith only [ht]
  calc ENNReal.ofReal A * X / ENNReal.ofReal (t / 2)
      = (ENNReal.ofReal A / ENNReal.ofReal (t / 2)) * X := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        ring
    _ = ENNReal.ofReal (A / (t / 2)) * X := by rw [ENNReal.ofReal_div_of_pos ht2]
    _ = ENNReal.ofReal (2 * A / t) * X := by
        congr 1
        field_simp

/-- For `t > 0` and any extended nonnegative real `X`,
`ENNReal.ofReal B * X / (ENNReal.ofReal (t/2))^2 = ENNReal.ofReal (4*B/t^2) * X`.
@isnad1 id=eq.1h3v.s7.fd744189b252 from=translated src=- shape=dfeb16f9 vocab=93e72c61
-/
theorem ofReal_mul_div_ofReal_half_sq {B t : ℝ} (ht : 0 < t) (X : ℝ≥0∞) :
    ENNReal.ofReal B * X / (ENNReal.ofReal (t / 2)) ^ 2 =
      ENNReal.ofReal (4 * B / t ^ 2) * X := by
  have ht2 : (0 : ℝ) < t / 2 := by linarith only [ht]
  rw [← ENNReal.ofReal_pow ht2.le]
  have hq : (0 : ℝ) < (t / 2) ^ 2 := by positivity
  calc ENNReal.ofReal B * X / ENNReal.ofReal ((t / 2) ^ 2)
      = (ENNReal.ofReal B / ENNReal.ofReal ((t / 2) ^ 2)) * X := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        ring
    _ = ENNReal.ofReal (B / (t / 2) ^ 2) * X := by rw [ENNReal.ofReal_div_of_pos hq]
    _ = ENNReal.ofReal (4 * B / t ^ 2) * X := by
        congr 1
        have ht_ne : t ≠ 0 := by linarith only [ht]
        field_simp [ht_ne]
        norm_num

end CKN.Foundation.Measure
