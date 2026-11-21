import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRGInequality

/-- If the spectral gap factor is zero, the target inequality is an equality.-/
theorem target_of_absolute_gap_eq_zero_standalone
    {t k f g v : Real} (ht : t ≠ 0)
    (hv : v = f + g + 1)
    (hgap : t ^ 2 * g * (f + 1) - v * k = 0) :
    v * k / t ^ 2 = g * (v - g) := by
  have hvg : v - g = f + 1 := by linarith [hv]
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  rw [hvg]
  field_simp [ht2]
  nlinarith [hgap]

end SRGInequality
