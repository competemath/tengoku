import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.PositiveCharacteristic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Norms of finite-field elements

A finite field embedded in a normed field has trivial norm: nonzero elements have norm
one, since `c ^ (q - 1) = 1`.
-/

namespace AlternatingAnalytic

variable {κ K : Type*} [Field κ] [Finite κ] [NormedField K]

/-- A nonzero element of a finite field maps to an element of norm one.
@isnad1 id=eq.1h4v.s6.53e7df094d43 from=translated src=- shape=3b3fd7fa vocab=39e11283
-/
theorem norm_finiteField_map (f : κ →+* K) (c : κ) (hc : c ≠ 0) : ‖f c‖ = 1 := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ - 1 ≠ 0 := by
    have := Fintype.one_lt_card (α := κ)
    omega
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) hcard).mp
  rw [← norm_pow, ← map_pow, FiniteField.pow_card_sub_one_eq_one c hc, map_one, norm_one]

/--
@isnad1 id=le.0h4v.s6.5641f23e321a from=translated src=- shape=777b333c vocab=85e8834e
-/
theorem norm_finiteField_map_le_one (f : κ →+* K) (c : κ) : ‖f c‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (norm_finiteField_map f c hc).le

end AlternatingAnalytic
