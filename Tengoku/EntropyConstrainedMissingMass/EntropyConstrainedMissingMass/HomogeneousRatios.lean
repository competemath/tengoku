import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.CoefficientPartialFractions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The zero-index Turán convention and the exact decreasing-ratio consequences. -/

namespace EntropyConstrainedMissingMass

/--
@isnad1 id=eq.0h4v.s6.9e376e537a67 from=translated src=- shape=3392517a vocab=4db2862c
-/
theorem homogeneous3_turan_all (x y z : ℝ) (n : ℕ) :
    homogeneous3 x y z n ^ 2 - previousHomogeneous3 x y z n * homogeneous3 x y z (n + 1) =
      homogeneous3 (x * y) (x * z) (y * z) n := by
  cases n with
  | zero => simp [previousHomogeneous3]
  | succ n => exact homogeneous3_turan x y z n

/--
@isnad1 id=le.3h4v.s6.b6ac5dc4e779 from=translated src=- shape=f0154d7a vocab=864fe3d4
-/
theorem homogeneous3_turan_nonneg {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ homogeneous3 x y z n ^ 2 - previousHomogeneous3 x y z n * homogeneous3 x y z (n + 1) := by
  rw [homogeneous3_turan_all]
  exact homogeneous3_nonneg (mul_nonneg hx hy) (mul_nonneg hx hz) (mul_nonneg hy hz) n

/-- The sequence here starts at source ratio h₁/h₀.
@isnad1 id=antitone.4h3v.s6.f29060875770 from=translated src=- shape=ce4fa052 vocab=18bac893
-/
theorem homogeneous3_ratio_antitone {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    Antitone (fun n => homogeneous3 x y z (n + 1) / homogeneous3 x y z n) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [div_le_div_iff₀ (homogeneous3_pos_of_ne_zero hx hy hz hne (n + 1))
    (homogeneous3_pos_of_ne_zero hx hy hz hne n)]
  simpa only [Nat.add_assoc, pow_two, mul_comm] using homogeneous3_log_concave hx hy hz n

/--
@isnad1 id=strictan.3h3v.s6.ce7a2d1a1c6e from=translated src=- shape=eb719281 vocab=828b74be
-/
theorem homogeneous3_ratio_strictAnti {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    StrictAnti (fun n => homogeneous3 x y z (n + 1) / homogeneous3 x y z n) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [div_lt_div_iff₀ (homogeneous3_pos hx.le hy.le hz (n + 1))
    (homogeneous3_pos hx.le hy.le hz n)]
  simpa only [Nat.add_assoc, pow_two, mul_comm] using homogeneous3_strict_log_concave hx hy hz n

end EntropyConstrainedMissingMass
