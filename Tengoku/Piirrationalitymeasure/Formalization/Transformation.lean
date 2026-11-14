import Tengoku.Piirrationalitymeasure.Formalization.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxRecDepth 100000

/-!
Power identities for the Mobius substitution used in the coefficient extraction.
-/

namespace PiIrrationality

/--
@isnad1 id=eq.0h2v.s7.4a57e18f1fca from=translated src=- shape=86dccf0e vocab=4b42fb74
-/
theorem mobius_even_power (n : ℕ) (z : ℚ) :
    mobius z ^ (2 * 1857 * n) =
      (5 : ℚ) ^ (2 * 1857 * n) * (1 + z) ^ (2 * 1857 * n) /
        (1 - z) ^ (2 * 1857 * n) := by
  unfold mobius
  rw [div_pow, mul_pow]
  have hsign : (-5 : ℚ) ^ (2 * 1857 * n) = (5 : ℚ) ^ (2 * 1857 * n) := by
    rw [show 2 * 1857 * n = 2 * (1857 * n) by ring]
    simp [pow_mul]
  rw [hsign]

/--
@isnad1 id=eq.2h2v.s7.3cb9959428af from=translated src=- shape=674a1278 vocab=7207a120
-/
theorem mobius_denominator_power (n : ℕ) (z : ℚ)
    (hz : z ≠ 0) (hz1 : z ≠ 1) :
    (25 - mobius z ^ 2) ^ (5570 * n + 1) =
      - ((100 : ℚ) ^ (5570 * n + 1) * z ^ (5570 * n + 1)) /
        (1 - z) ^ (2 * (5570 * n + 1)) := by
  rw [mobius_denominator z hz1]
  have hodd : (-1 : ℚ) ^ (5570 * n + 1) = -1 := by
    rw [show 5570 * n + 1 = 2 * (2785 * n) + 1 by omega]
    norm_num [pow_succ, pow_mul]
  rw [show (-100 : ℚ) * z = (-1 : ℚ) * (100 * z) by ring]
  rw [div_pow, mul_pow, hodd]
  rw [mul_pow, ← pow_mul]
  field_simp [hz, hz1]

/--
@isnad1 id=eq.1h2v.s7.5a90885baa0a from=translated src=- shape=57b213cb vocab=094d52d8
-/
theorem mobius_quartic_power (n : ℕ) (z : ℚ) (hz1 : z ≠ 1) :
    (mobius z ^ 4 + 6 * mobius z ^ 2 + 25) ^ (3714 * n) =
      ((400 : ℚ) ^ (3714 * n) * P z ^ (3714 * n)) /
        (1 - z) ^ (4 * (3714 * n)) := by
  rw [mobius_quartic z hz1, div_pow, mul_pow]
  field_simp [hz1]
  rw [← pow_mul]

noncomputable def transformedDensityFactorized (n : ℕ) (z : ℚ) : ℚ :=
  5 * ((5 : ℚ) ^ (2 * 1857 * n) * (1 + z) ^ (2 * 1857 * n) /
      (1 - z) ^ (2 * 1857 * n)) *
    ((400 : ℚ) ^ (3714 * n) * P z ^ (3714 * n) /
      (1 - z) ^ (4 * (3714 * n))) *
    (-10 / (1 - z) ^ 2) /
    (- ((100 : ℚ) ^ (5570 * n + 1) * z ^ (5570 * n + 1)) /
      (1 - z) ^ (2 * (5570 * n + 1)))

/--
@isnad1 id=eq.2h2v.s6.815284831d88 from=translated src=- shape=03f9a135 vocab=7e7e8e97
-/
theorem transformedDensityFactorized_eq (n : ℕ) (z : ℚ)
    (hz : z ≠ 0) (hz1 : z ≠ 1) :
    rationalFunction n (mobius z) * (-10 / (1 - z)^2) =
      transformedDensityFactorized n z := by
  unfold rationalFunction transformedDensityFactorized
  rw [mobius_even_power n z, mobius_quartic_power n z hz1,
    mobius_denominator_power n z hz hz1]
  ring

end PiIrrationality
