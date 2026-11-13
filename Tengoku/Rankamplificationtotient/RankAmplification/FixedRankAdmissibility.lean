import Tengoku.Rankamplificationtotient.RankAmplification.FixedRankAssembly
import Tengoku.Rankamplificationtotient.RankAmplification.Supplier.Weights

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Fixed-rank cutoff admissibility The supplier argument uses natural cutoffs, while the saddle calculation is expressed with real exponentials. -/

namespace RankAmplification

open Filter
open scoped Topology

noncomputable section

/-! ## The exact floor-to-exponential relation -/

/-- Flooring `exp T_J` loses less than one.
@isnad1 id=le.0h2v.s4.4a02113982cb from=translated src=- shape=2ee16f4f vocab=7bbb2864
-/
theorem fixedRankY_le_natY_add_one (J x : ℕ) :
    fixedRankY J (x : ℝ) ≤ (fixedRankNatY J x + 1 : ℕ) := by
  simpa [fixedRankNatY, Nat.cast_add, Nat.cast_one] using
    (Nat.lt_floor_add_one (fixedRankY J (x : ℝ))).le

/-- The paper's fixed-rank floor satisfies `HasExponentialCutoffScale` exactly.
@isnad1 id=hasexpon.0h2v.s3.2935ccb581e0 from=translated src=- shape=6452919b vocab=afcc63ed
-/
theorem fixedRank_hasExponentialCutoffScale (J x : ℕ) :
    HasExponentialCutoffScale (fixedRankNatY J x)
      (fixedRankT J (x : ℝ)) := by
  unfold HasExponentialCutoffScale
  simpa only [fixedRankY] using fixedRankY_le_natY_add_one J x

/-! ## The upper cutoff is eventually below the ambient range -/

/-- For fixed `J`, the upper exponent `√J G` is `o(L)`.
@isnad1 id=islittle.0h1v.s4.c771dc304921 from=translated src=- shape=ce229097 vocab=f46e4473
-/
theorem fixedRankUpperExponent_isLittleO_scaleL (J : ℕ) :
    (fun x ↦ Real.sqrt J * scaleG x) =o[atTop] scaleL :=
  scaleG_isLittleO_scaleL.const_mul_left (Real.sqrt J)

/-- Hence `√J G ≤ L` eventually.
@isnad1 id=eventual.0h1v.s4.8248277501ea from=translated src=- shape=41203060 vocab=100e2c21
-/
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

/-- Real upper cutoff `Y_J` is eventually at most `x`.
@isnad1 id=eventual.0h1v.s4.50d94c80b9a3 from=translated src=- shape=4435f604 vocab=b12b3085
-/
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

/-- The natural upper cutoff is eventually at most the natural ambient parameter.
@isnad1 id=eventual.0h1v.s4.b7d10e3ce278 from=translated src=- shape=3d748f88 vocab=78b481e4
-/
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

/--
@isnad1 id=eventual.1h1v.s4.41549dd30285 from=translated src=- shape=b47cba71 vocab=055d4c4b
-/
theorem eventually_fixedRankNaturalAdmissibility (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ x : ℕ in atTop, FixedRankNaturalAdmissibility J x := by
  filter_upwards [eventually_three_le_fixedRankNatY J hJ,
    eventually_fixedRankNatY_le_upperY J hJ,
    eventually_fixedRankNatUpperY_le_id J] with x hy hyY hYx
  exact ⟨hJ, hy, hyY, hYx, fixedRank_hasExponentialCutoffScale J x⟩

/--
@isnad1 id=eventual.1h1v.s4.1ad8300f93fe from=translated src=- shape=6b47d1bf vocab=0784f315
-/
theorem eventually_fixedRankNatY_le_id (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ x : ℕ in atTop, fixedRankNatY J x ≤ x := by
  filter_upwards [eventually_fixedRankNaturalAdmissibility J hJ] with x hx
  exact hx.y_le_upper.trans hx.upper_le_x

/--
@isnad1 id=eventual.0h1v.s4.fa0d47dd916e from=translated src=- shape=ed9f6e81 vocab=f583ca9b
-/
theorem eventually_fixedRankNatUpperY_le_two_mul (J : ℕ) :
    ∀ᶠ x : ℕ in atTop, fixedRankNatUpperY J x ≤ 2 * x := by
  filter_upwards [eventually_fixedRankNatUpperY_le_id J] with x hx
  exact hx.trans (Nat.le_mul_of_pos_left x (by norm_num))

/-- Every shift in the paper's natural range automatically satisfies all convolution cutoffs.
@isnad1 id=and.2h3v.s4.8c13ab2ccea6 from=translated src=- shape=b195b361 vocab=372676f3
-/
theorem FixedRankNaturalAdmissibility.shift_le_ranges
    {J x h : ℕ} (hadmissible : FixedRankNaturalAdmissibility J x)
    (hh : h ≤ fixedRankNatY J x) :
    h ≤ fixedRankNatUpperY J x ∧ h ≤ x :=
  ⟨hh.trans hadmissible.y_le_upper,
    hh.trans (hadmissible.y_le_upper.trans hadmissible.upper_le_x)⟩

end

end RankAmplification
