import Tengoku.Rankamplificationtotient.RankAmplification.Saddle
import Tengoku.Rankamplificationtotient.RankAmplification.Section5Assembly
import Tengoku.Rankamplificationtotient.RankAmplification.MovingScales

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Optimization consequences of the two saddles This module records the exact and asymptotic optimization statements in Corollary 7.2 and Proposition 10.27. -/

namespace RankAmplification

open Filter
open Asymptotics
open scoped Topology Asymptotics

noncomputable section

/-! ## A reciprocal two-branch profile -/

/-- The scale-free profile underlying the rank-one saddle.-/
def reciprocalSaddleProfile (r : ℝ) : ℝ :=
  min r r⁻¹

/--
@isnad1 id=le.1h1v.s4.bdef4b805cbc from=translated src=- shape=97c35add vocab=0c316f2c
-/
theorem reciprocalSaddleProfile_le_one {r : ℝ} (hr : 0 < r) :
    reciprocalSaddleProfile r ≤ 1 := by
  unfold reciprocalSaddleProfile
  by_cases h : r ≤ 1
  · exact (min_le_left _ _).trans h
  · have hrOne : 1 < r := lt_of_not_ge h
    exact (min_le_right _ _).trans ((inv_le_one₀ hr).2 hrOne.le)

/--
@isnad1 id=iff.1h1v.s5.7e278edffbb9 from=translated src=- shape=a6d5929f vocab=ad9787b1
-/
theorem reciprocalSaddleProfile_eq_one_iff {r : ℝ} (hr : 0 < r) :
    reciprocalSaddleProfile r = 1 ↔ r = 1 := by
  constructor
  · intro heq
    have hleft : 1 ≤ r := heq.ge.trans (min_le_left _ _)
    have hright : 1 ≤ r⁻¹ := heq.ge.trans (min_le_right _ _)
    have hrle : r ≤ 1 := by
      rw [one_le_inv₀ hr] at hright
      exact hright
    exact le_antisymm hrle hleft
  · rintro rfl
    simp [reciprocalSaddleProfile]

/--
@isnad1 id=lt.2h1v.s5.77935a952a1e from=translated src=- shape=d34e1a3e vocab=ad9787b1
-/
theorem reciprocalSaddleProfile_lt_one {r : ℝ}
    (hr : 0 < r) (hne : r ≠ 1) :
    reciprocalSaddleProfile r < 1 :=
  lt_of_le_of_ne (reciprocalSaddleProfile_le_one hr)
    (fun h ↦ hne ((reciprocalSaddleProfile_eq_one_iff hr).mp h))

/-- On a fixed upper window, distance from the saddle and loss in the profile are comparable.
@isnad1 id=and.3h2v.s6.e619eb7c30df from=translated src=- shape=94069923 vocab=3e553117
-/
theorem reciprocalSaddleProfile_loss_bounds
    {r C : ℝ} (hr : 0 < r) (hrC : r ≤ C) (hC : 1 ≤ C) :
    1 - reciprocalSaddleProfile r ≤ |r - 1| ∧
      |r - 1| ≤ C * (1 - reciprocalSaddleProfile r) := by
  unfold reciprocalSaddleProfile
  by_cases hrOne : r ≤ 1
  · have hinv : r ≤ r⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ hr).2
      nlinarith [sq_nonneg (r - 1)]
    rw [min_eq_left hinv, abs_of_nonpos (sub_nonpos.mpr hrOne)]
    constructor
    · linarith
    · have hnonneg : 0 ≤ 1 - r := sub_nonneg.mpr hrOne
      nlinarith
  · have hrOne' : 1 < r := lt_of_not_ge hrOne
    have hinv : r⁻¹ ≤ r := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ hr).2
      nlinarith [sq_nonneg (r - 1)]
    rw [min_eq_right hinv, abs_of_nonneg (sub_nonneg.mpr hrOne'.le)]
    have hloss : 1 - r⁻¹ = (r - 1) / r := by
      field_simp [hr.ne']
    rw [hloss]
    constructor
    · apply (div_le_iff₀ hr).2
      nlinarith
    · rw [show C * ((r - 1) / r) = (C * (r - 1)) / r by ring]
      apply (le_div_iff₀ hr).2
      have hdelta : 0 ≤ r - 1 := sub_nonneg.mpr hrOne'.le
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hrC hdelta

/-- On a fixed positive window, convergence of the reciprocal profile to its maximum is equivalent to convergence of its argument to the unique saddle.
@isnad1 id=iff.2h4v.s6.5d78e18b0ef3 from=translated src=- shape=e7bf7440 vocab=ce21d2b7
-/
theorem tendsto_reciprocalSaddleProfile_one_iff
    {α : Type*} {l : Filter α} {r : α → ℝ} {C : ℝ}
    (hC : 1 ≤ C) (hr : ∀ᶠ x in l, 0 < r x ∧ r x ≤ C) :
    Tendsto (fun x ↦ reciprocalSaddleProfile (r x)) l (nhds 1) ↔
      Tendsto r l (nhds 1) := by
  constructor
  · intro hprofile
    have hloss : Tendsto (fun x ↦ 1 - reciprocalSaddleProfile (r x)) l (nhds 0) := by
      simpa only [sub_self] using
        ((tendsto_const_nhds : Tendsto (fun _ : α ↦ (1 : ℝ)) l (nhds 1)).sub hprofile)
    have hupper : Tendsto
        (fun x ↦ C * (1 - reciprocalSaddleProfile (r x))) l (nhds 0) := by
      simpa only [mul_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : α ↦ C) l (nhds C)).mul hloss)
    have habs : Tendsto (fun x ↦ |r x - 1|) l (nhds 0) := by
      apply squeeze_zero'
      · exact Eventually.of_forall fun x ↦ abs_nonneg (r x - 1)
      · filter_upwards [hr] with x hx
        exact (reciprocalSaddleProfile_loss_bounds hx.1 hx.2 hC).2
      · exact hupper
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simpa only [Real.norm_eq_abs] using habs
  · intro hsaddle
    have habs : Tendsto (fun x ↦ |r x - 1|) l (nhds 0) := by
      simpa only [Real.norm_eq_abs] using
        (tendsto_iff_norm_sub_tendsto_zero.1 hsaddle)
    have hloss : Tendsto (fun x ↦ 1 - reciprocalSaddleProfile (r x)) l (nhds 0) := by
      apply squeeze_zero'
      · filter_upwards [hr] with x hx
        exact sub_nonneg.mpr (reciprocalSaddleProfile_le_one hx.1)
      · filter_upwards [hr] with x hx
        exact (reciprocalSaddleProfile_loss_bounds hx.1 hx.2 hC).1
      · exact habs
    simpa only [sub_sub_cancel, sub_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : α ↦ (1 : ℝ)) l (nhds 1)).sub hloss)

/-! ## Corollary 7.2: exact rank-one optimization -/

/-- The rank-one exponent normalized by `G` is exactly the reciprocal profile of `T/G`.
@isnad1 id=eq.2h2v.s5.56869c9ec9b9 from=translated src=- shape=ee45df13 vocab=efec7a4a
-/
theorem section5SaddleExponent_div_scaleG
    {X T : ℝ} (hG : scaleG X ≠ 0) (hT : T ≠ 0) :
    section5SaddleExponent X T / scaleG X =
      reciprocalSaddleProfile (T / scaleG X) := by
  have hratio : T / scaleG X ≠ 0 := div_ne_zero hT hG
  have hTform : (T / scaleG X) * scaleG X = T := div_mul_cancel₀ T hG
  rw [← hTform, section5SaddleExponent_at_mul_scaleG hG hratio]
  unfold reciprocalSaddleProfile
  field_simp [hG]

/-- Corollary 7.2, exact maximum and unique positive equality case.
@isnad1 id=and.2h2v.s5.32b7c82c879d from=translated src=- shape=94a22d3d vocab=a7ee51fb
-/
theorem corollary7_2_exact_maximum {X T : ℝ}
    (hG : 0 < scaleG X) (hT : 0 < T) :
    section5SaddleExponent X T ≤ scaleG X ∧
      (section5SaddleExponent X T = scaleG X ↔ T = scaleG X) :=
  ⟨section5SaddleExponent_le_scaleG hG.le hT,
    section5SaddleExponent_eq_scaleG_iff hG hT⟩

/-- Corollary 7.2, fixed-ratio formula.
@isnad1 id=eq.2h2v.s5.ada4896949fa from=translated src=- shape=09633025 vocab=0b8b470c
-/
theorem corollary7_2_fixed_ratio
    {X lam : ℝ} (hG : scaleG X ≠ 0) (hlam : lam ≠ 0) :
    section5SaddleExponent X (lam * scaleG X) =
      min lam lam⁻¹ * scaleG X := by
  rw [section5SaddleExponent_at_mul_scaleG hG hlam]
  ring

/-- Loss in the unnormalized rank-one exponent is comparable to distance from the saddle, uniformly on every fixed upper window.
@isnad1 id=and.4h3v.s6.48f42bdfa705 from=translated src=- shape=0adb0fb7 vocab=6eaa4df3
-/
theorem section5SaddleExponent_loss_bounds
    {X T C : ℝ} (hG : 0 < scaleG X) (hT : 0 < T)
    (hTC : T ≤ C * scaleG X) (hC : 1 ≤ C) :
    scaleG X - section5SaddleExponent X T ≤ |T - scaleG X| ∧
      |T - scaleG X| ≤
        C * (scaleG X - section5SaddleExponent X T) := by
  let r := T / scaleG X
  have hr : 0 < r := div_pos hT hG
  have hrC : r ≤ C := by
    apply (div_le_iff₀ hG).2
    simpa [mul_comm] using hTC
  have hprofile := reciprocalSaddleProfile_loss_bounds hr hrC hC
  have hnormalized := section5SaddleExponent_div_scaleG hG.ne' hT.ne'
  have hexponent :
      section5SaddleExponent X T = reciprocalSaddleProfile r * scaleG X :=
    (div_eq_iff hG.ne').mp hnormalized
  have hTform : T = r * scaleG X := by
    exact (div_mul_cancel₀ T hG.ne').symm
  have hloss : scaleG X - section5SaddleExponent X T =
      scaleG X * (1 - reciprocalSaddleProfile r) := by
    rw [hexponent]
    ring
  have hdistance : |T - scaleG X| = scaleG X * |r - 1| := by
    rw [hTform]
    have hfactor : r * scaleG X - scaleG X = (r - 1) * scaleG X := by ring
    rw [hfactor, abs_mul, abs_of_pos hG]
    ring
  constructor
  · rw [hloss, hdistance]
    exact mul_le_mul_of_nonneg_left hprofile.1 hG.le
  · rw [hloss, hdistance]
    calc
      scaleG X * |r - 1| ≤ scaleG X *
          (C * (1 - reciprocalSaddleProfile r)) :=
        mul_le_mul_of_nonneg_left hprofile.2 hG.le
      _ = C * (scaleG X * (1 - reciprocalSaddleProfile r)) := by ring

/-- Corollary 7.2(i): in a fixed positive window, preserving the optimal leading coefficient is equivalent to `T/G → 1`.
@isnad1 id=iff.2h2v.s7.7e375aec787a from=translated src=- shape=bf1468e2 vocab=55676a3d
-/
theorem corollary7_2_leadingCoefficient_iff
    {T : ℝ → ℝ} {C : ℝ} (hC : 1 ≤ C)
    (hwindow : ∀ᶠ x in atTop,
      0 < scaleG x ∧ 0 < T x ∧ T x ≤ C * scaleG x) :
    Tendsto (fun x ↦ section5SaddleExponent x (T x) / scaleG x)
        atTop (nhds 1) ↔
      Tendsto (fun x ↦ T x / scaleG x) atTop (nhds 1) := by
  have hratio : ∀ᶠ x in atTop,
      0 < T x / scaleG x ∧ T x / scaleG x ≤ C := by
    filter_upwards [hwindow] with x hx
    refine ⟨div_pos hx.2.1 hx.1, ?_⟩
    apply (div_le_iff₀ hx.1).2
    simpa [mul_comm] using hx.2.2
  have hnormalized :
      (fun x ↦ section5SaddleExponent x (T x) / scaleG x) =ᶠ[atTop]
        (fun x ↦ reciprocalSaddleProfile (T x / scaleG x)) := by
    filter_upwards [hwindow] with x hx
    exact section5SaddleExponent_div_scaleG hx.1.ne' hx.2.1.ne'
  exact (tendsto_congr' hnormalized).trans
    (tendsto_reciprocalSaddleProfile_one_iff hC hratio)

/-- For a fixed positive ratio, the normalized exponent is eventually the constant `min(lam,lam⁻¹)`.
@isnad1 id=tendsto.1h1v.s5.3a588b7025d6 from=translated src=- shape=0b0aafdb vocab=5314d90a
-/
theorem corollary7_2_fixed_ratio_limit {lam : ℝ} (hlam : 0 < lam) :
    Tendsto
      (fun x ↦ section5SaddleExponent x (lam * scaleG x) / scaleG x)
      atTop (nhds (min lam lam⁻¹)) := by
  apply (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ min lam lam⁻¹)
    atTop (nhds (min lam lam⁻¹))).congr'
  filter_upwards [tendsto_scaleG_atTop.eventually_gt_atTop 0] with x hG
  rw [corollary7_2_fixed_ratio hG.ne' hlam.ne', mul_div_cancel_right₀ _ hG.ne']

/-- Exact one-sided second-order expansion around `T=G`.
@isnad1 id=eq.2h2v.s7.045e56d3fac9 from=translated src=- shape=8098e1c7 vocab=92213b0e
-/
theorem section5SaddleExponent_add_scaleG_exact
    {X Δ : ℝ} (hG : 0 < scaleG X) (hT : 0 < scaleG X + Δ) :
    section5SaddleExponent X (scaleG X + Δ) =
      scaleG X - |Δ| + if Δ ≤ 0 then 0 else Δ ^ 2 / (scaleG X + Δ) := by
  by_cases hΔ : Δ ≤ 0
  · have hTG : scaleG X + Δ ≤ scaleG X := by linarith
    have hleft : scaleG X + Δ ≤
        scaleG X ^ 2 / (scaleG X + Δ) := by
      apply (le_div_iff₀ hT).2
      nlinarith
    rw [section5SaddleExponent, min_eq_left hleft, ite_eq_left hΔ,
      abs_of_nonpos hΔ]
    ring
  · have hΔpos : 0 < Δ := lt_of_not_ge hΔ
    have hGleT : scaleG X ≤ scaleG X + Δ := by linarith
    have hright : scaleG X ^ 2 / (scaleG X + Δ) ≤ scaleG X + Δ := by
      apply (div_le_iff₀ hT).2
      nlinarith
    rw [section5SaddleExponent, min_eq_right hright, ite_eq_right hΔ,
      abs_of_pos hΔpos]
    field_simp [hT.ne']
    ring

/-- The paper's `O(Δ²/G)` remainder, as an explicit inequality with constant one.
@isnad1 id=le.2h2v.s6.f212765ddfa3 from=translated src=- shape=310b09c2 vocab=10b1fd1e
-/
theorem section5SaddleExponent_secondOrder_error
    {X Δ : ℝ} (hG : 0 < scaleG X) (hT : 0 < scaleG X + Δ) :
    |section5SaddleExponent X (scaleG X + Δ) -
        (scaleG X - |Δ|)| ≤ Δ ^ 2 / scaleG X := by
  rw [section5SaddleExponent_add_scaleG_exact hG hT]
  by_cases hΔ : Δ ≤ 0
  · rw [ite_eq_left hΔ]
    simp only [add_zero, sub_self, abs_zero]
    positivity
  · rw [ite_eq_right hΔ]
    have hsimp :
        scaleG X - |Δ| + Δ ^ 2 / (scaleG X + Δ) -
            (scaleG X - |Δ|) = Δ ^ 2 / (scaleG X + Δ) := by
      ring
    rw [hsimp, abs_of_nonneg (div_nonneg (sq_nonneg _) hT.le)]
    apply div_le_div_of_nonneg_left (sq_nonneg _) hG
    linarith

/-- Corollary 7.2(ii), in ratio form: on a fixed window, exponent loss is `o(S)` exactly when displacement from the saddle is `o(S)`.
@isnad1 id=iff.2h3v.s7.1bf534b95d7e from=translated src=- shape=23b2e05c vocab=add83c7f
-/
theorem corollary7_2_secondOrder_iff
    {T S : ℝ → ℝ} {C : ℝ} (hC : 1 ≤ C)
    (hwindow : ∀ᶠ x in atTop,
      0 < scaleG x ∧ 0 < T x ∧ T x ≤ C * scaleG x ∧ 0 < S x) :
    Tendsto
        (fun x ↦ (scaleG x - section5SaddleExponent x (T x)) / S x)
        atTop (nhds 0) ↔
      Tendsto (fun x ↦ (T x - scaleG x) / S x) atTop (nhds 0) := by
  constructor
  · intro hexponent
    have hupper : Tendsto
        (fun x ↦ C *
          ((scaleG x - section5SaddleExponent x (T x)) / S x))
        atTop (nhds 0) := by
      simpa only [mul_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ C) atTop (nhds C)).mul hexponent)
    have habs : Tendsto (fun x ↦ |(T x - scaleG x) / S x|)
        atTop (nhds 0) := by
      refine squeeze_zero'
        (f := fun x ↦ |(T x - scaleG x) / S x|)
        (g := fun x ↦ C *
          ((scaleG x - section5SaddleExponent x (T x)) / S x)) ?_ ?_ hupper
      · exact Eventually.of_forall fun x ↦ abs_nonneg _
      · filter_upwards [hwindow] with x hx
        have hloss := section5SaddleExponent_loss_bounds
          hx.1 hx.2.1 hx.2.2.1 hC
        have hquotient :
          |T x - scaleG x| / S x ≤
              (C * (scaleG x - section5SaddleExponent x (T x))) / S x :=
          div_le_div_of_nonneg_right hloss.2 hx.2.2.2.le
        calc
          |(T x - scaleG x) / S x| = |T x - scaleG x| / S x := by
            rw [abs_div, abs_of_pos hx.2.2.2]
          _ ≤ (C * (scaleG x - section5SaddleExponent x (T x))) / S x :=
            hquotient
          _ = C * ((scaleG x - section5SaddleExponent x (T x)) / S x) := by
            ring
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simpa only [sub_zero, Real.norm_eq_abs] using habs
  · intro hparameter
    have habs : Tendsto (fun x ↦ |(T x - scaleG x) / S x|)
        atTop (nhds 0) := by
      simpa only [sub_zero, Real.norm_eq_abs] using
        (tendsto_iff_norm_sub_tendsto_zero.1 hparameter)
    refine squeeze_zero'
      (f := fun x ↦
        (scaleG x - section5SaddleExponent x (T x)) / S x)
      (g := fun x ↦ |(T x - scaleG x) / S x|) ?_ ?_ habs
    · filter_upwards [hwindow] with x hx
      exact div_nonneg
        (sub_nonneg.mpr (section5SaddleExponent_le_scaleG hx.1.le hx.2.1))
        hx.2.2.2.le
    · filter_upwards [hwindow] with x hx
      have hloss := section5SaddleExponent_loss_bounds
        hx.1 hx.2.1 hx.2.2.1 hC
      calc
        (scaleG x - section5SaddleExponent x (T x)) / S x ≤
            |T x - scaleG x| / S x :=
          div_le_div_of_nonneg_right hloss.1 hx.2.2.2.le
        _ = |(T x - scaleG x) / S x| := by
          rw [abs_div, abs_of_pos hx.2.2.2]

/-- The exact local expansion in Corollary 7.2 implies the stated `O(Delta²/G)` remainder for every perturbation `Delta=o(G)`.
@isnad1 id=isbigo.1h1v.s6.d25b7716aa50 from=translated src=- shape=23d631f9 vocab=e79363b0
-/
theorem corollary7_2_secondOrder_expansion
    {Delta : ℝ → ℝ} (hDelta : Delta =o[atTop] scaleG) :
    (fun x ↦ section5SaddleExponent x (scaleG x + Delta x) -
        (scaleG x - |Delta x|)) =O[atTop]
      (fun x ↦ Delta x ^ 2 / scaleG x) := by
  have hsmall := hDelta.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hpositive : ∀ᶠ x in atTop, 0 < scaleG x + Delta x := by
    filter_upwards [hsmall, tendsto_scaleG_atTop.eventually_gt_atTop 0] with x hx hG
    change |Delta x| ≤ (1 / 2 : ℝ) * |scaleG x| at hx
    rw [abs_of_pos hG] at hx
    have hlower : -|Delta x| ≤ Delta x := neg_abs_le (Delta x)
    nlinarith
  apply IsBigO.of_bound 1
  filter_upwards [hpositive, tendsto_scaleG_atTop.eventually_gt_atTop 0] with x hT hG
  rw [one_mul, Real.norm_eq_abs,
    Real.norm_of_nonneg (div_nonneg (sq_nonneg _) hG.le)]
  exact section5SaddleExponent_secondOrder_error hG hT

/-! ## Proposition 10.27: the moving-rank saddle -/

/-- The two competing transfer exponents in (10.52), before division by `R`.-/
def movingTransferExponent (c x : ℝ) : ℝ :=
  min (c * movingR x) (movingR x / (4 * c))

/-- The outer cutoff `Z=exp(cR)` used in Proposition 10.27.-/
def movingOuterCutoff (c x : ℝ) : ℝ :=
  Real.exp (c * movingR x)

/--
@isnad1 id=eq.0h2v.s4.4427602ef484 from=translated src=- shape=534da806 vocab=37da8cf9
-/
@[simp]
theorem log_movingOuterCutoff (c x : ℝ) :
    Real.log (movingOuterCutoff c x) = c * movingR x := by
  simp [movingOuterCutoff]

/-- The moving profile is a rescaled copy of the reciprocal rank-one profile.
@isnad1 id=eq.1h1v.s6.8e9d44f6a60c from=translated src=- shape=957031a1 vocab=813b7727
-/
theorem movingSaddleExponent_eq_half_mul_reciprocalSaddleProfile
    {c : ℝ} (hc : 0 < c) :
    movingSaddleExponent c =
      (1 / 2 : ℝ) * reciprocalSaddleProfile (2 * c) := by
  unfold movingSaddleExponent reciprocalSaddleProfile
  rw [mul_min_of_nonneg (2 * c) (2 * c)⁻¹ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  · ring
  · field_simp [hc.ne']
    norm_num

/-- The dimensional transfer exponent factors exactly as its coefficient times `R`.
@isnad1 id=eq.0h2v.s4.689c53d9d2c5 from=translated src=- shape=43f21ce9 vocab=d6c7fe94
-/
theorem movingTransferExponent_eq_profile_mul_movingR (c x : ℝ) :
    movingTransferExponent c x = movingSaddleExponent c * movingR x := by
  have hR : 0 ≤ movingR x := Real.sqrt_nonneg _
  have hsecond : movingR x / (4 * c) = (1 / (4 * c)) * movingR x := by ring
  rw [movingTransferExponent, hsecond, movingSaddleExponent]
  simpa [mul_comm] using
    (mul_min_of_nonneg c (1 / (4 * c)) hR).symm

/-- Exact fixed-ratio form of (10.52), normalized by `R`.
@isnad1 id=eq.1h2v.s5.e57af2d2d1f0 from=translated src=- shape=881ac70c vocab=ac1e303d
-/
theorem movingTransferExponent_div_movingR
    {c x : ℝ} (hR : movingR x ≠ 0) :
    movingTransferExponent c x / movingR x = movingSaddleExponent c := by
  rw [movingTransferExponent_eq_profile_mul_movingR,
    mul_div_cancel_right₀ _ hR]

/-- Proposition 10.27: the profile has maximum `1/2`, attained uniquely at `c=1/2`.
@isnad1 id=and.1h1v.s6.cb3b8e49f381 from=translated src=- shape=b50a6f8f vocab=5b89cd29
-/
theorem proposition10_27_exact_maximum {c : ℝ} (hc : 0 < c) :
    movingSaddleExponent c ≤ 1 / 2 ∧
      (movingSaddleExponent c = 1 / 2 ↔ c = 1 / 2) :=
  ⟨movingSaddleExponent_le_half hc,
    movingSaddleExponent_eq_half_iff hc⟩

/-- The corresponding unnormalized transfer exponent is uniquely maximized at `c=1/2`.
@isnad1 id=and.2h2v.s7.1dfe1e10bfe4 from=translated src=- shape=4d3b5aba vocab=5b4ed7f2
-/
theorem proposition10_27_transfer_exact_maximum
    {c x : ℝ} (hc : 0 < c) (hR : 0 < movingR x) :
    movingTransferExponent c x ≤ (1 / 2 : ℝ) * movingR x ∧
      (movingTransferExponent c x = (1 / 2 : ℝ) * movingR x ↔
        c = 1 / 2) := by
  rw [movingTransferExponent_eq_profile_mul_movingR]
  constructor
  · exact mul_le_mul_of_nonneg_right (movingSaddleExponent_le_half hc) hR.le
  · constructor
    · intro heq
      have hcoefficient : movingSaddleExponent c = 1 / 2 := by
        nlinarith
      exact (movingSaddleExponent_eq_half_iff hc).mp hcoefficient
    · intro hcHalf
      rw [hcHalf]
      norm_num [movingSaddleExponent]

/-- Distance from the moving optimum and loss of its coefficient are uniformly comparable on every fixed upper window.
@isnad1 id=and.3h2v.s7.b9f57633846e from=translated src=- shape=173b8028 vocab=62194c3c
-/
theorem movingSaddleExponent_loss_bounds
    {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C) (hC : 1 / 2 ≤ C) :
    1 / 2 - movingSaddleExponent c ≤ |c - 1 / 2| ∧
      |c - 1 / 2| ≤
        2 * C * (1 / 2 - movingSaddleExponent c) := by
  have hscaledPositive : 0 < 2 * c := by positivity
  have hscaledUpper : 2 * c ≤ 2 * C := by linarith
  have hscaledC : (1 : ℝ) ≤ 2 * C := by linarith
  have hprofile := reciprocalSaddleProfile_loss_bounds
    hscaledPositive hscaledUpper hscaledC
  have hfactor := movingSaddleExponent_eq_half_mul_reciprocalSaddleProfile hc
  have hloss :
      1 / 2 - movingSaddleExponent c =
        (1 / 2 : ℝ) * (1 - reciprocalSaddleProfile (2 * c)) := by
    rw [hfactor]
    ring
  have hdistance :
      |c - 1 / 2| = (1 / 2 : ℝ) * |2 * c - 1| := by
    have hrewrite : c - 1 / 2 = (1 / 2 : ℝ) * (2 * c - 1) := by ring
    rw [hrewrite, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  constructor
  · rw [hloss, hdistance]
    exact mul_le_mul_of_nonneg_left hprofile.1 (by norm_num)
  · rw [hloss, hdistance]
    calc
      (1 / 2 : ℝ) * |2 * c - 1| ≤
          (1 / 2 : ℝ) *
            ((2 * C) * (1 - reciprocalSaddleProfile (2 * c))) :=
        mul_le_mul_of_nonneg_left hprofile.2 (by norm_num)
      _ = 2 * C *
          ((1 / 2 : ℝ) * (1 - reciprocalSaddleProfile (2 * c))) := by ring

/-- Uniform uniqueness of the moving saddle: the coefficient tends to `1/2` exactly when `c` tends to `1/2`.
@isnad1 id=iff.2h4v.s7.a8eef6472e34 from=translated src=- shape=ceba1602 vocab=727f3ba8
-/
theorem tendsto_movingSaddleExponent_half_iff
    {α : Type*} {l : Filter α} {c : α → ℝ} {C : ℝ}
    (hC : 1 / 2 ≤ C) (hc : ∀ᶠ x in l, 0 < c x ∧ c x ≤ C) :
    Tendsto (fun x ↦ movingSaddleExponent (c x)) l (nhds (1 / 2)) ↔
      Tendsto c l (nhds (1 / 2)) := by
  constructor
  · intro hprofile
    have hloss : Tendsto
        (fun x ↦ 1 / 2 - movingSaddleExponent (c x)) l (nhds 0) := by
      simpa only [sub_self] using
        ((tendsto_const_nhds : Tendsto (fun _ : α ↦ (1 / 2 : ℝ)) l
          (nhds (1 / 2))).sub hprofile)
    have hupper : Tendsto
        (fun x ↦ 2 * C * (1 / 2 - movingSaddleExponent (c x)))
        l (nhds 0) := by
      simpa only [mul_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : α ↦ (2 * C : ℝ)) l
          (nhds (2 * C))).mul hloss)
    have habs : Tendsto (fun x ↦ |c x - 1 / 2|) l (nhds 0) := by
      refine squeeze_zero' (f := fun x ↦ |c x - 1 / 2|)
        (g := fun x ↦ 2 * C *
          (1 / 2 - movingSaddleExponent (c x))) ?_ ?_ hupper
      · exact Eventually.of_forall fun x ↦ abs_nonneg _
      · filter_upwards [hc] with x hx
        exact (movingSaddleExponent_loss_bounds hx.1 hx.2 hC).2
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simpa only [Real.norm_eq_abs] using habs
  · intro hsaddle
    have habs : Tendsto (fun x ↦ |c x - 1 / 2|) l (nhds 0) := by
      simpa only [Real.norm_eq_abs] using
        (tendsto_iff_norm_sub_tendsto_zero.1 hsaddle)
    have hloss : Tendsto
        (fun x ↦ 1 / 2 - movingSaddleExponent (c x)) l (nhds 0) := by
      refine squeeze_zero'
        (f := fun x ↦ 1 / 2 - movingSaddleExponent (c x))
        (g := fun x ↦ |c x - 1 / 2|) ?_ ?_ habs
      · filter_upwards [hc] with x hx
        exact sub_nonneg.mpr (movingSaddleExponent_le_half hx.1)
      · filter_upwards [hc] with x hx
        exact (movingSaddleExponent_loss_bounds hx.1 hx.2 hC).1
    simpa only [sub_sub_cancel, sub_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : α ↦ (1 / 2 : ℝ)) l
        (nhds (1 / 2))).sub hloss)

/-- Proposition 10.27 in the paper's fixed-`c` normalization.
@isnad1 id=tendsto.0h1v.s5.d8bbf87f6d59 from=translated src=- shape=a4fd65f1 vocab=e3ad1b55
-/
theorem proposition10_27_fixed_ratio_limit {c : ℝ} :
    Tendsto (fun x ↦ movingTransferExponent c x / movingR x)
      atTop (nhds (movingSaddleExponent c)) := by
  apply (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ movingSaddleExponent c)
    atTop (nhds (movingSaddleExponent c))).congr'
  filter_upwards [tendsto_movingR_atTop.eventually_gt_atTop 0] with x hR
  exact (movingTransferExponent_div_movingR hR.ne').symm

/-- A varying cutoff preserves the optimal leading coefficient precisely when `c→1/2`.
@isnad1 id=iff.2h2v.s7.3795881eece6 from=translated src=- shape=6ecd1659 vocab=22fcae83
-/
theorem proposition10_27_leadingCoefficient_iff
    {c : ℝ → ℝ} {C : ℝ} (hC : 1 / 2 ≤ C)
    (hwindow : ∀ᶠ x in atTop, 0 < c x ∧ c x ≤ C) :
    Tendsto (fun x ↦ movingTransferExponent (c x) x / movingR x)
        atTop (nhds (1 / 2)) ↔
      Tendsto c atTop (nhds (1 / 2)) := by
  have hnormalized :
      (fun x ↦ movingTransferExponent (c x) x / movingR x) =ᶠ[atTop]
        (fun x ↦ movingSaddleExponent (c x)) := by
    filter_upwards [tendsto_movingR_atTop.eventually_gt_atTop 0] with x hR
    exact movingTransferExponent_div_movingR hR.ne'
  exact (tendsto_congr' hnormalized).trans
    (tendsto_movingSaddleExponent_half_iff hC hwindow)

/-- Precise interpretation of the `o(1)` in (10.52): adding any coefficient error tending to zero leaves the normalized exponent at the fixed profile value.
@isnad1 id=tendsto.1h2v.s6.905762aea94b from=translated src=- shape=27f1e90a vocab=a632576e
-/
theorem proposition10_27_fixed_ratio_with_vanishing_error
    {c : ℝ} {error : ℝ → ℝ} (herror : Tendsto error atTop (nhds 0)) :
    Tendsto
      (fun x ↦ (movingTransferExponent c x + error x * movingR x) / movingR x)
      atTop (nhds (movingSaddleExponent c)) := by
  have hlimit : Tendsto (fun x ↦ movingSaddleExponent c + error x)
      atTop (nhds (movingSaddleExponent c)) := by
    simpa only [add_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ movingSaddleExponent c)
        atTop (nhds (movingSaddleExponent c))).add herror)
  apply hlimit.congr'
  filter_upwards [tendsto_movingR_atTop.eventually_gt_atTop 0] with x hR
  rw [add_div, movingTransferExponent_div_movingR hR.ne',
    mul_div_cancel_right₀ _ hR.ne']

/-- At the optimizing cutoff `c=1/2`, the preceding statement gives coefficient `1/2`.
@isnad1 id=tendsto.1h1v.s6.44b7fc287dc5 from=translated src=- shape=91827eef vocab=d8ec414e
-/
theorem proposition10_27_optimal_with_vanishing_error
    {error : ℝ → ℝ} (herror : Tendsto error atTop (nhds 0)) :
    Tendsto
      (fun x ↦ (movingTransferExponent (1 / 2) x +
        error x * movingR x) / movingR x)
      atTop (nhds (1 / 2)) := by
  have hhalf : movingSaddleExponent (1 / 2) = (1 / 2 : ℝ) :=
    (movingSaddleExponent_eq_half_iff (by norm_num)).2 rfl
  simpa only [hhalf] using
    (proposition10_27_fixed_ratio_with_vanishing_error
      (c := (1 / 2 : ℝ)) herror)

end

end RankAmplification
