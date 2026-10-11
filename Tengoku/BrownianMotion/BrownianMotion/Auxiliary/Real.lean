module

public import Tengoku

@[expose] public section

namespace Real

/--
@isnad1 id=eq.3h2v.s5.e6771f719af6 from=translated src=- shape=62086d01 vocab=a2d812b7
-/
lemma inv_rpow_logb {b : ℝ} (hb : 0 < b) (hb' : b ≠ 1) {x : ℝ} (hx : 0 < x) :
    b⁻¹ ^ Real.logb b x = x⁻¹ := by
  rw [inv_eq_one_div, Real.div_rpow (by norm_num) (le_of_lt hb)]
  simpa using Real.rpow_logb hb hb' hx

end Real
