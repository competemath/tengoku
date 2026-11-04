import Tengoku.Seed.Analysis.Complex.ExponentialBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact calibration and final constants for the standalone `C < 96` proof. -/

namespace stoch_to_det

def eta96Q : ℚ := 221 / 1000
def delta96Q : ℚ := 2 * eta96Q ^ 2
def rho96Q : ℚ := 1 / 2 - eta96Q ^ 2
def floorNat96Q : ℚ := 231 / 10000

noncomputable def eta96 : ℝ := eta96Q
noncomputable def delta96 : ℝ := delta96Q
noncomputable def rho96 : ℝ := rho96Q
noncomputable def floorNat96 : ℝ := floorNat96Q
noncomputable def infoFloor96 : ℝ := floorNat96 / Real.log 2

/-- Coefficient of `M` after the shared-race estimate and mismatch charge.-/
noncomputable def KM96 : ℝ := 1 / infoFloor96

/-- Coefficient of `Sinfo = b_Z` after the shared-race estimate and mismatch charge.-/
noncomputable def KS96 : ℝ := 2 + 2 * Real.log 2 / delta96

/-- The hybrid coefficient before the final deterministic `+1`.-/
noncomputable def KD96 : ℝ :=
  max (3 * KM96) ((3 / 2 : ℝ) * KM96 + 3 * KS96 + 1)

/-- The complete comparison constant delivered by the shared-race route.-/
noncomputable def Cdagger96 : ℝ := KD96 + 1

/--
@isnad1 id=eq.0h0v.s4.140ee5d51e62 from=translated src=- shape=0efb1284 vocab=304fce55
-/
lemma eta96_eq : eta96 = (221 : ℝ) / 1000 := by
  norm_num [eta96, eta96Q]

/--
@isnad1 id=eq.0h0v.s5.d2b4ae4179bb from=translated src=- shape=41d85760 vocab=031fecf7
-/
lemma delta96_eq : delta96 = 2 * eta96 ^ 2 := by
  norm_num [delta96, delta96Q, eta96, eta96Q]

/--
@isnad1 id=eq.0h0v.s4.0d83c2ee840f from=translated src=- shape=0efb1284 vocab=03238b1c
-/
lemma delta96_eq_value : delta96 = (48841 : ℝ) / 500000 := by
  norm_num [delta96, delta96Q, eta96Q]

/--
@isnad1 id=eq.0h0v.s5.45d7d0844552 from=translated src=- shape=f2920ecc vocab=65b02f33
-/
lemma rho96_eq : rho96 = 1 / 2 - eta96 ^ 2 := by
  norm_num [rho96, rho96Q, eta96, eta96Q]

/--
@isnad1 id=eq.0h0v.s4.b9a74e42389b from=translated src=- shape=0efb1284 vocab=be3526ef
-/
lemma rho96_eq_value : rho96 = (451159 : ℝ) / 1000000 := by
  norm_num [rho96, rho96Q, eta96Q]

/--
@isnad1 id=eq.0h0v.s4.cc83f3f5f6be from=translated src=- shape=0efb1284 vocab=eed40420
-/
lemma floorNat96_eq : floorNat96 = (231 : ℝ) / 10000 := by
  norm_num [floorNat96, floorNat96Q]

/--
@isnad1 id=lt.0h0v.s3.349dd7dff11d from=translated src=- shape=ff3a10fc vocab=3f4f7cc5
-/
lemma eta96_pos : 0 < eta96 := by norm_num [eta96_eq]
/--
@isnad1 id=lt.0h0v.s3.40a31884cfab from=translated src=- shape=ff3a10fc vocab=d1ea3700
-/
lemma delta96_pos : 0 < delta96 := by norm_num [delta96_eq_value]
/--
@isnad1 id=lt.0h0v.s3.b9e8fde9b58e from=translated src=- shape=ff3a10fc vocab=6a08f1d9
-/
lemma rho96_pos : 0 < rho96 := by norm_num [rho96_eq_value]
/--
@isnad1 id=lt.0h0v.s3.dd1a66b43fdc from=translated src=- shape=ff3a10fc vocab=47bd50e6
-/
lemma floorNat96_pos : 0 < floorNat96 := by norm_num [floorNat96_eq]

/--
@isnad1 id=lt.0h0v.s5.0da3b5b84fae from=translated src=- shape=2642eee4 vocab=d0ceb66c
-/
lemma two_mul_eta96_sq_lt_one : 2 * eta96 ^ 2 < 1 := by
  norm_num [eta96_eq]

/--
@isnad1 id=lt.0h0v.s3.29123e547981 from=translated src=- shape=ff3a10fc vocab=e23a997e
-/
lemma infoFloor96_pos : 0 < infoFloor96 := by
  exact div_pos floorNat96_pos (Real.log_pos one_lt_two)

/--
@isnad1 id=eq.0h0v.s5.4e02166ce88f from=translated src=- shape=bc85c230 vocab=5488f0f2
-/
theorem KM96_eq : KM96 = Real.log 2 * (10000 / 231 : ℝ) := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold KM96 infoFloor96
  rw [floorNat96_eq]
  field_simp [hlog]

/--
@isnad1 id=eq.0h0v.s5.a56aebfb9450 from=translated src=- shape=1dbbdc9d vocab=be98d115
-/
theorem KS96_eq : KS96 = 2 + Real.log 2 * (1000000 / 48841 : ℝ) := by
  unfold KS96
  rw [delta96_eq_value]
  ring

/--
@isnad1 id=eq.0h0v.s5.f5e258057e6e from=translated src=- shape=f17957eb vocab=5488f0f2
-/
theorem near_branch_96_eq :
    3 * KM96 = Real.log 2 * (10000 / 77 : ℝ) := by
  rw [KM96_eq]
  ring

/--
@isnad1 id=eq.0h0v.s6.9e08d8df0efa from=translated src=- shape=e8e8039e vocab=53c3972b
-/
theorem far_branch_96_eq :
    (3 / 2 : ℝ) * KM96 + 3 * KS96 + 1 =
      7 + Real.log 2 * (475205000 / 3760757 : ℝ) := by
  rw [KM96_eq, KS96_eq]
  ring

/--
@isnad1 id=lt.0h0v.s6.52c4d4952a6d from=translated src=- shape=202b6500 vocab=699f52cf
-/
theorem near_branch_96_lt_far :
    3 * KM96 < (3 / 2 : ℝ) * KM96 + 3 * KS96 + 1 := by
  rw [near_branch_96_eq, far_branch_96_eq]
  have hlog0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2 := Real.log_two_lt_d9
  nlinarith

/--
@isnad1 id=eq.0h0v.s5.5997240527ca from=translated src=- shape=1dbbdc9d vocab=1f8fb8b5
-/
theorem KD96_eq :
    KD96 = 7 + Real.log 2 * (475205000 / 3760757 : ℝ) := by
  unfold KD96
  rw [max_eq_right near_branch_96_lt_far.le, far_branch_96_eq]

/--
@isnad1 id=eq.0h0v.s5.b4b9648130a4 from=translated src=- shape=1dbbdc9d vocab=cdb74326
-/
theorem Cdagger96_eq :
    Cdagger96 = 8 + Real.log 2 * (475205000 / 3760757 : ℝ) := by
  unfold Cdagger96
  rw [KD96_eq]
  ring

/--
@isnad1 id=lt.0h0v.s3.9f2b946882df from=translated src=- shape=ffdda526 vocab=6e610aa1
-/
theorem Cdagger96_lt_96 : Cdagger96 < (96 : ℝ) := by
  rw [Cdagger96_eq]
  nlinarith [Real.log_two_lt_d9]

/--
@isnad1 id=le.0h0v.s3.096d5351ba79 from=translated src=- shape=ff3a10fc vocab=58704161
-/
theorem KM96_nonneg : 0 ≤ KM96 := by
  rw [KM96_eq]
  positivity

/--
@isnad1 id=le.0h0v.s3.1458e2e0dcd5 from=translated src=- shape=ff3a10fc vocab=86bb8a4e
-/
theorem KS96_nonneg : 0 ≤ KS96 := by
  rw [KS96_eq]
  positivity

/--
@isnad1 id=le.0h0v.s5.60dca651496b from=translated src=- shape=0590051e vocab=ea4a1ee3
-/
theorem joint_bZ_coefficient_nonneg : 0 ≤ 3 * KS96 + 1 := by
  rw [KS96_eq]
  positivity

end stoch_to_det
