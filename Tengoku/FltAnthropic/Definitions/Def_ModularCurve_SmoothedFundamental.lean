import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open UpperHalfPlane Set
open scoped MatrixGroups Topology

noncomputable section

namespace ModularCurve.SmoothedFundamental

def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ := num γ z / denom γ z

/--
@isnad1 id=eq.0h2v.s7.7a6ae056d316 from=translated src=- shape=d18f0e4a vocab=d98f6e64
-/
theorem coe_smul (γ : SL(2, ℤ)) (τ : ℍ) : ((γ • τ : ℍ) : ℂ) = mob γ τ := by
  rw [ModularGroup.sl_moeb, coe_smul_of_det_pos (by simp)]; rfl

/--
@isnad1 id=eq.0h3v.s7.47f4e29fcc85 from=translated src=- shape=29485180 vocab=f42d21ec
-/
theorem mob_mob (γ γ' : SL(2, ℤ)) (τ : ℍ) : mob γ (mob γ' τ) = mob (γ * γ') τ := by
  rw [← coe_smul, ← coe_smul, ← coe_smul, mul_smul]

/--
@isnad1 id=eq.0h1v.s6.4e9b0b85a682 from=translated src=- shape=00d93106 vocab=e64e745c
-/
theorem mob_one_apply (z : ℂ) : mob 1 z = z := by
  simp [mob, num, denom]

def pOne (x : ℝ) : ℝ := Real.smoothTransition (x + 1) - Real.smoothTransition x

/--
@isnad1 id=le.0h1v.s3.80d9d5eb1787 from=translated src=- shape=8a62b088 vocab=30cf9692
-/
theorem pOne_nonneg (x : ℝ) : 0 ≤ pOne x :=
  sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))

/--
@isnad1 id=le.0h1v.s3.6174233280ec from=translated src=- shape=b14ee516 vocab=30cf9692
-/
theorem pOne_le_one (x : ℝ) : pOne x ≤ 1 := by
  have := Real.smoothTransition.le_one (x + 1)
  have := Real.smoothTransition.nonneg x
  unfold pOne; linarith

/--
@isnad1 id=eq.1h1v.s4.ac10a390d31b from=translated src=- shape=2efac4f6 vocab=15f574c8
-/
theorem pOne_eq_zero_of_le {x : ℝ} (hx : x ≤ -1) : pOne x = 0 := by
  simp [pOne, Real.smoothTransition.zero_of_nonpos (show x + 1 ≤ 0 by linarith),
    Real.smoothTransition.zero_of_nonpos (show x ≤ 0 by linarith)]

/--
@isnad1 id=eq.1h1v.s4.b8dc96fa005c from=translated src=- shape=97c35add vocab=30cf9692
-/
theorem pOne_eq_zero_of_ge {x : ℝ} (hx : 1 ≤ x) : pOne x = 0 := by
  simp [pOne, Real.smoothTransition.one_of_one_le (show 1 ≤ x + 1 by linarith),
    Real.smoothTransition.one_of_one_le hx]

/--
@isnad1 id=and.1h1v.s5.d8b54068b9c2 from=translated src=- shape=3f31d984 vocab=00e76c7e
-/
theorem mem_Ioo_of_pOne_ne_zero {x : ℝ} (hx : pOne x ≠ 0) : -1 < x ∧ x < 1 := by
  by_contra h
  rcases not_and_or.1 h with h | h <;> push Not at h
  exacts [hx (pOne_eq_zero_of_le h), hx (pOne_eq_zero_of_ge h)]

/--
@isnad1 id=eq.2h1v.s5.d59266bb254a from=translated src=- shape=bc295b5f vocab=225160da
-/
theorem pOne_sub_one_add {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : pOne (u - 1) + pOne u = 1 := by
  unfold pOne
  rw [sub_add_cancel, Real.smoothTransition.zero_of_nonpos (by linarith : u - 1 ≤ 0),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ u + 1)]
  ring

def pTwo (T y : ℝ) : ℝ := Real.smoothTransition (8 * y - 5) * Real.smoothTransition (T + 4 - y)

/--
@isnad1 id=le.0h2v.s4.6ce429ad5703 from=translated src=- shape=a120b2a8 vocab=807fbb75
-/
theorem pTwo_nonneg (T y : ℝ) : 0 ≤ pTwo T y :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

/--
@isnad1 id=le.0h2v.s4.4d9c340f2127 from=translated src=- shape=aa052b1b vocab=807fbb75
-/
theorem pTwo_le_one (T y : ℝ) : pTwo T y ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

/--
@isnad1 id=eq.1h2v.s5.2a926ad34ee8 from=translated src=- shape=f1c1bfae vocab=b2510cd7
-/
theorem pTwo_eq_zero_of_le {T y : ℝ} (hy : y ≤ 5 / 8) : pTwo T y = 0 := by
  simp [pTwo, Real.smoothTransition.zero_of_nonpos (show 8 * y - 5 ≤ 0 by linarith)]

/--
@isnad1 id=eq.1h2v.s5.622ec10e3415 from=translated src=- shape=704e537f vocab=8c5e5570
-/
theorem pTwo_eq_zero_of_ge {T y : ℝ} (hy : T + 4 ≤ y) : pTwo T y = 0 := by
  simp [pTwo, Real.smoothTransition.zero_of_nonpos (show T + 4 - y ≤ 0 by linarith)]

/--
@isnad1 id=eq.2h2v.s6.22a33174dc33 from=translated src=- shape=7ae65a4b vocab=cec4fd76
-/
theorem pTwo_eq_one {T y : ℝ} (h1 : 3 / 4 ≤ y) (h2 : y ≤ T + 3) : pTwo T y = 1 := by
  simp [pTwo, Real.smoothTransition.one_of_one_le (show 1 ≤ 8 * y - 5 by linarith),
    Real.smoothTransition.one_of_one_le (show 1 ≤ T + 4 - y by linarith)]

/--
@isnad1 id=and.1h2v.s6.d0858b8e05b4 from=translated src=- shape=c2ce52c2 vocab=6981ba40
-/
theorem mem_Ioo_of_pTwo_ne_zero {T y : ℝ} (h : pTwo T y ≠ 0) : 5 / 8 < y ∧ y < T + 4 := by
  by_contra h'
  rcases not_and_or.1 h' with h' | h' <;> push Not at h'
  exacts [h (pTwo_eq_zero_of_le h'), h (pTwo_eq_zero_of_ge h')]

def bump (T : ℝ) (z : ℂ) : ℝ := pOne z.re * pTwo T z.im

/--
@isnad1 id=le.0h2v.s4.88dc7ce07fbb from=translated src=- shape=25b8bdde vocab=aa8ebb64
-/
theorem bump_nonneg (T : ℝ) (z : ℂ) : 0 ≤ bump T z := mul_nonneg (pOne_nonneg _) (pTwo_nonneg _ _)

/--
@isnad1 id=le.0h2v.s4.084540eafaf7 from=translated src=- shape=1884bda8 vocab=aa8ebb64
-/
theorem bump_le_one (T : ℝ) (z : ℂ) : bump T z ≤ 1 :=
  mul_le_one₀ (pOne_le_one _) (pTwo_nonneg _ _) (pTwo_le_one _ _)

/--
@isnad1 id=and.1h2v.s6.47832acfa638 from=translated src=- shape=5cc404f5 vocab=87c0c9d1
-/
theorem mem_of_bump_ne_zero {T : ℝ} {z : ℂ} (h : bump T z ≠ 0) :
    (-1 < z.re ∧ z.re < 1) ∧ (5 / 8 < z.im ∧ z.im < T + 4) :=
  ⟨mem_Ioo_of_pOne_ne_zero (left_ne_zero_of_mul h),
    mem_Ioo_of_pTwo_ne_zero (right_ne_zero_of_mul h)⟩

/--
@isnad1 id=lt.1h2v.s4.3bfd302d295c from=translated src=- shape=b09155fb vocab=1a1b4703
-/
theorem im_pos_of_bump_ne_zero {T : ℝ} {z : ℂ} (h : bump T z ≠ 0) : 0 < z.im := by
  have := (mem_of_bump_ne_zero h).2.1; linarith

def box (T : ℝ) : Set ℂ := Icc (-1 : ℝ) 1 ×ℂ Icc (5 / 8 : ℝ) (T + 4)

/--
@isnad1 id=iscompac.0h1v.s4.ba781d3359b2 from=translated src=- shape=1a6c1393 vocab=19151698
-/
theorem isCompact_box (T : ℝ) : IsCompact (box T) := isCompact_Icc.reProdIm isCompact_Icc

/--
@isnad1 id=isclosed.0h1v.s4.eb12657faa1a from=translated src=- shape=1a6c1393 vocab=689ca0d3
-/
theorem isClosed_box (T : ℝ) : IsClosed (box T) := isClosed_Icc.reProdIm isClosed_Icc

/--
@isnad1 id=lt.1h2v.s4.98ae643a6e9a from=translated src=- shape=d9bd9ecf vocab=9ed90e27
-/
theorem im_pos_of_mem_box {T : ℝ} {z : ℂ} (hz : z ∈ box T) : 0 < z.im := by
  have := (Complex.mem_reProdIm.1 hz).2.1; linarith

/--
@isnad1 id=le.0h1v.s3.35128b636c0a from=translated src=- shape=17da43a1 vocab=cb6a04d1
-/
theorem support_bump_subset (T : ℝ) : Function.support (bump T) ⊆ box T := by
  intro z hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_of_bump_ne_zero hz
  exact Complex.mem_reProdIm.2 ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩

/--
@isnad1 id=le.0h1v.s4.7b956e5c431b from=translated src=- shape=17da43a1 vocab=3382209c
-/
theorem tsupport_bump_subset (T : ℝ) : tsupport (bump T) ⊆ box T :=
  closure_minimal (support_bump_subset T) (isClosed_box T)

def recip (t : ℝ) : ℝ := Real.smoothTransition (4 * t - 1) / t

/--
@isnad1 id=le.1h1v.s4.d8d1206e63e0 from=translated src=- shape=35bd48ee vocab=a0fb7d9b
-/
theorem recip_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ recip t :=
  div_nonneg (Real.smoothTransition.nonneg _) ht

/--
@isnad1 id=eq.1h1v.s5.d7865d792303 from=translated src=- shape=af6100ba vocab=e008bb65
-/
theorem mul_recip_of_half_le {t : ℝ} (ht : 1 / 2 ≤ t) : t * recip t = 1 := by
  unfold recip
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  field_simp

/--
@isnad1 id=le.0h1v.s4.4d554d4d0f36 from=translated src=- shape=50069a91 vocab=56fe4ba2
-/
theorem mul_recip_le_one (t : ℝ) : t * recip t ≤ 1 := by
  unfold recip
  by_cases ht : t = 0
  · simp [ht]
  · rw [mul_div_cancel₀ _ ht]; exact Real.smoothTransition.le_one _

def gcut (T : ℝ) (z : ℂ) : ℝ := 1 - Real.smoothTransition (z.im - T)

/--
@isnad1 id=eq.1h2v.s4.d70d153f104d from=translated src=- shape=8dddc791 vocab=01816c0a
-/
theorem gcut_eq_one {T : ℝ} {z : ℂ} (h : z.im ≤ T) : gcut T z = 1 := by
  simp [gcut, Real.smoothTransition.zero_of_nonpos (show z.im - T ≤ 0 by linarith)]

/--
@isnad1 id=eq.1h2v.s5.d87d34908e72 from=translated src=- shape=4a5176b6 vocab=7f43705d
-/
theorem gcut_eq_zero {T : ℝ} {z : ℂ} (h : T + 1 ≤ z.im) : gcut T z = 0 := by
  simp [gcut, Real.smoothTransition.one_of_one_le (show 1 ≤ z.im - T by linarith)]

/--
@isnad1 id=le.0h2v.s4.e478ab8b4cbb from=translated src=- shape=25b8bdde vocab=e2e4321d
-/
theorem gcut_nonneg (T : ℝ) (z : ℂ) : 0 ≤ gcut T z :=
  sub_nonneg.2 (Real.smoothTransition.le_one _)

/--
@isnad1 id=le.0h2v.s4.3281175653d7 from=translated src=- shape=1884bda8 vocab=e2e4321d
-/
theorem gcut_le_one (T : ℝ) (z : ℂ) : gcut T z ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg _)

def cover (T : ℝ) (z : ℂ) : ℝ := ∑ᶠ γ : SL(2, ℤ), bump T (mob γ z)

/--
@isnad1 id=le.0h2v.s4.3ea1cdaf0a15 from=translated src=- shape=25b8bdde vocab=b175ae28
-/
theorem cover_nonneg (T : ℝ) (z : ℂ) : 0 ≤ cover T z := finsum_nonneg fun _ => bump_nonneg _ _

def pu (T : ℝ) (z : ℂ) : ℝ := bump T z * recip (cover T z)

/--
@isnad1 id=le.0h2v.s4.87c253e9f161 from=translated src=- shape=25b8bdde vocab=f704812b
-/
theorem pu_nonneg (T : ℝ) (z : ℂ) : 0 ≤ pu T z :=
  mul_nonneg (bump_nonneg _ _) (recip_nonneg (cover_nonneg _ _))

/--
@isnad1 id=le.0h1v.s4.04f7d8b6b64f from=translated src=- shape=334bc037 vocab=7570a82e
-/
theorem support_pu_subset (T : ℝ) : Function.support (pu T) ⊆ Function.support (bump T) :=
  fun _ hz => left_ne_zero_of_mul hz

/--
@isnad1 id=le.0h1v.s4.b032c50fcb02 from=translated src=- shape=17da43a1 vocab=7f2f2ee6
-/
theorem tsupport_pu_subset (T : ℝ) : tsupport (pu T) ⊆ box T :=
  (closure_mono (support_pu_subset T)).trans (tsupport_bump_subset T)

def puCut (T : ℝ) (z : ℂ) : ℝ := pu T z * gcut T z

/--
@isnad1 id=le.0h2v.s4.9406554a1d3e from=translated src=- shape=25b8bdde vocab=7c1b3b18
-/
theorem puCut_nonneg (T : ℝ) (z : ℂ) : 0 ≤ puCut T z :=
  mul_nonneg (pu_nonneg _ _) (gcut_nonneg _ _)

/--
@isnad1 id=le.0h2v.s3.8667253d216c from=translated src=- shape=6456e7f0 vocab=c2586552
-/
theorem puCut_le_pu (T : ℝ) (z : ℂ) : puCut T z ≤ pu T z :=
  mul_le_of_le_one_right (pu_nonneg _ _) (gcut_le_one _ _)

/--
@isnad1 id=le.0h1v.s3.e3d53b22bac4 from=translated src=- shape=17da43a1 vocab=3dedc6a1
-/
theorem support_puCut_subset (T : ℝ) : Function.support (puCut T) ⊆ box T :=
  fun _ hz => support_bump_subset T (support_pu_subset T (left_ne_zero_of_mul hz))

/--
@isnad1 id=le.0h1v.s4.c66e8b7f6e74 from=translated src=- shape=17da43a1 vocab=0f6dc4a2
-/
theorem tsupport_puCut_subset (T : ℝ) : tsupport (puCut T) ⊆ box T :=
  closure_minimal (support_puCut_subset T) (isClosed_box T)

/--
@isnad1 id=eq.1h2v.s4.aa299a164e72 from=translated src=- shape=5800b206 vocab=91b8eff0
-/
theorem puCut_eq_pu_of_im_le {T : ℝ} {z : ℂ} (h : z.im ≤ T) : puCut T z = pu T z := by
  rw [puCut, gcut_eq_one h, mul_one]

end ModularCurve.SmoothedFundamental

def ModularCurve.smoothedFundamental (Γ : Subgroup SL(2, ℤ)) (T : ℝ) (z : ℂ) : ℝ :=
  ∑ᶠ q : SL(2, ℤ) ⧸ Γ,
    ModularCurve.SmoothedFundamental.puCut T (ModularCurve.SmoothedFundamental.mob (Quotient.out q) z)

namespace ModularCurve.SmoothedFundamental

/--
@isnad1 id=le.0h3v.s5.01e2c3c1cc98 from=translated src=- shape=5a68abd9 vocab=d6b14a7c
-/
theorem smoothedFundamental_nonneg (Γ : Subgroup SL(2, ℤ)) (T : ℝ) (z : ℂ) :
    0 ≤ ModularCurve.smoothedFundamental Γ T z :=
  finsum_nonneg fun _ => puCut_nonneg _ _

/--
@isnad1 id=eq.0h3v.s9.e96c220effdb from=translated src=- shape=df486724 vocab=89124f8d
-/
theorem smoothedFundamental_eq_sum (Γ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Γ)] (T : ℝ)
    (z : ℂ) : ModularCurve.smoothedFundamental Γ T z =
      ∑ q : SL(2, ℤ) ⧸ Γ, puCut T (mob (Quotient.out q) z) :=
  finsum_eq_sum_of_fintype _

end ModularCurve.SmoothedFundamental

end
