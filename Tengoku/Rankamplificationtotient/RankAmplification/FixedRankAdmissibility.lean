import Tengoku.Rankamplificationtotient.RankAmplification.FixedRankAssembly
import Tengoku.Rankamplificationtotient.RankAmplification.Supplier.Weights

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Fixed-rank cutoff admissibility The supplier argument uses natural cutoffs, while the saddle calculation is expressed with real exponentials. -/

namespace RankAmplification

open Filter
open scoped Topology

noncomputable section

/-! ## The exact floor-to-exponential relation -/

/-- Flooring `exp T_J` loses less than one.-/
theorem fixedRankY_le_natY_add_one (J x : ℕ) :
    fixedRankY J (x : ℝ) ≤ (fixedRankNatY J x + 1 : ℕ) := by
  simpa [fixedRankNatY, Nat.cast_add, Nat.cast_one] using
    (Nat.lt_floor_add_one (fixedRankY J (x : ℝ))).le

/-- The paper's fixed-rank floor satisfies `HasExponentialCutoffScale` exactly.-/
theorem fixedRank_hasExponentialCutoffScale (J x : ℕ) :
    HasExponentialCutoffScale (fixedRankNatY J x)
      (fixedRankT J (x : ℝ)) := by
  unfold HasExponentialCutoffScale
  simpa only [fixedRankY] using fixedRankY_le_natY_add_one J x

/-! ## The upper cutoff is eventually below the ambient range -/

/-- For fixed `J`, the upper exponent `√J G` is `o(L)`.-/
theorem fixedRankUpperExponent_isLittleO_scaleL (J : ℕ) :
    (fun x ↦ Real.sqrt J * scaleG x) =o[atTop] scaleL :=
  scaleG_isLittleO_scaleL.const_mul_left (Real.sqrt J)

/-- Hence `√J G ≤ L` eventually.-/
theorem eventually_fixedRankUpperExponent_le_scaleL (J : ℕ) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt J * scaleG x ≤ scaleL x := by
  have hbound := (fixedRankUpperExponent_isLittleO_scaleL J).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, eventually_scaleL_pos] with x hx hL
  calc
    Real.sqrt J * scaleG x ≤ ‖Real.sqrt J * scaleG x‖ :=
      Real.le_norm_self _
    _ ≤ ‖scaleL x‖ := by simpa using hx
    _ = scaleL x := Real.norm_of_nonneg hL.le

/-- Real upper cutoff `Y_J` is eventually at most `x`.-/
theorem eventually_fixedRankUpperY_le_id (J : ℕ) :
    ∀ᶠ x : ℝ in atTop, fixedRankUpperY J x ≤ x := by
  have hxone : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  filter_upwards [eventually_fixedRankUpperExponent_le_scaleL J, hxone] with x hexp hx
  by_cases hJ : J = 0
  · subst J
    simp only [fixedRankUpperY, Nat.cast_zero, zero_mul, Real.exp_zero]
    exact hx
  · have hJpos : 0 < J := Nat.pos_of_ne_zero hJ
    calc
      fixedRankUpperY J x = Real.exp (Real.sqrt J * scaleG x) :=
        fixedRankUpperY_eq_exp_sqrt_mul_scaleG x hJpos
      _ ≤ Real.exp (scaleL x) := Real.exp_le_exp.mpr hexp
      _ = x := Real.exp_log (zero_lt_one.trans_le hx)

/-- The natural upper cutoff is eventually at most the natural ambient parameter.-/
theorem eventually_fixedRankNatUpperY_le_id (J : ℕ) :
    ∀ᶠ x : ℕ in atTop, fixedRankNatUpperY J x ≤ x := by
  have hreal := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_fixedRankUpperY_le_id J)
  filter_upwards [hreal] with x hx
  have hfloor : (fixedRankNatUpperY J x : ℝ) ≤
      fixedRankUpperY J (x : ℝ) := by
    exact Nat.floor_le (fixedRankUpperY_pos J (x : ℝ)).le
  exact_mod_cast hfloor.trans hx

/-! ## Complete eventual admissibility -/

/-- All elementary natural cutoff conditions required by the fixed-rank supplier argument.-/
structure FixedRankNaturalAdmissibility (J x : ℕ) : Prop where
  rank_pos : 0 < J
  three_le_y : 3 ≤ fixedRankNatY J x
  y_le_upper : fixedRankNatY J x ≤ fixedRankNatUpperY J x
  upper_le_x : fixedRankNatUpperY J x ≤ x
  exponential_scale : HasExponentialCutoffScale (fixedRankNatY J x)
    (fixedRankT J (x : ℝ))

theorem eventually_fixedRankNaturalAdmissibility (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ x : ℕ in atTop, FixedRankNaturalAdmissibility J x := by
  filter_upwards [eventually_three_le_fixedRankNatY J hJ,
    eventually_fixedRankNatY_le_upperY J hJ,
    eventually_fixedRankNatUpperY_le_id J] with x hy hyY hYx
  exact ⟨hJ, hy, hyY, hYx, fixedRank_hasExponentialCutoffScale J x⟩

theorem eventually_fixedRankNatY_le_id (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ x : ℕ in atTop, fixedRankNatY J x ≤ x := by
  filter_upwards [eventually_fixedRankNaturalAdmissibility J hJ] with x hx
  exact hx.y_le_upper.trans hx.upper_le_x

theorem eventually_fixedRankNatUpperY_le_two_mul (J : ℕ) :
    ∀ᶠ x : ℕ in atTop, fixedRankNatUpperY J x ≤ 2 * x := by
  filter_upwards [eventually_fixedRankNatUpperY_le_id J] with x hx
  exact hx.trans (Nat.le_mul_of_pos_left x (by norm_num))

/-- Every shift in the paper's natural range automatically satisfies all convolution cutoffs.-/
theorem FixedRankNaturalAdmissibility.shift_le_ranges
    {J x h : ℕ} (hadmissible : FixedRankNaturalAdmissibility J x)
    (hh : h ≤ fixedRankNatY J x) :
    h ≤ fixedRankNatUpperY J x ∧ h ≤ x :=
  ⟨hh.trans hadmissible.y_le_upper,
    hh.trans (hadmissible.y_le_upper.trans hadmissible.upper_le_x)⟩

end

end RankAmplification
