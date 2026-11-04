import Tengoku.Pi2Lean.Row12.BetaFrame

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12EulerSupport.upper_scalarMid_lower` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.upper_radius_le_quarter` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.upper_scalarDenom_lower` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.upper_lambda_norm` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.upper_circle_nonzero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.upper_betaFrameF_lower` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.upper_betaFrameF_nonzero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.upper_betaFrameDenom_lower` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.upper_betaFrameDenom_nonzero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.upper_balanced_argument_norm` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.upper_betaFrame_denominator_lower` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.upper_betaFrame_denominator_nonzero` (it only prints; the queue checks the axioms of every declaration). -/

namespace Row12EulerSupport

/--
@isnad1 id=le.2h1v.s5.0082d2b75879 from=translated src=- shape=8a3ab131 vocab=6052fcad
-/
theorem upper_scalarMid_lower {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 100) :
    x ≤ Row12.scalarMid x := by
  have hq : (1 : ℝ) ≤ 27 * (80 - 99 * x + 27 * x ^ 2) / 1000 := by
    nlinarith [sq_nonneg x]
  calc
    x = x * 1 := by ring
    _ ≤ x * (27 * (80 - 99 * x + 27 * x ^ 2) / 1000) :=
      mul_le_mul_of_nonneg_left hq hx.le
    _ = Row12.scalarMid x := by unfold Row12.scalarMid; ring

/--
@isnad1 id=le.2h1v.s6.b30456db2d6d from=translated src=- shape=37b57f9a vocab=be4c199b
-/
theorem upper_radius_le_quarter {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 100) :
    Real.sqrt (Row12.scalarLambda x) ≤ x / 4 := by
  have hx1 : x ≤ 1 := by linarith
  have hc : x ^ 3 ≤ x ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx1)]
  have hl : Row12.scalarLambda x ≤ (x / 4) ^ 2 := by
    unfold Row12.scalarLambda Row12.rho
    nlinarith [sq_nonneg x]
  have hs := Real.sq_sqrt (Row12.scalarLambda_pos hx).le
  have hr := Real.sqrt_nonneg (Row12.scalarLambda x)
  nlinarith

/--
@isnad1 id=le.2h1v.s6.c14b28f44109 from=translated src=- shape=9d7d8414 vocab=72c26721
-/
theorem upper_scalarDenom_lower {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 100) :
    57624 * x ^ 4 ≤ Row12.scalarDenom x := by
  have hm : (24 : ℝ) ≤ Row12.scalarM x := by unfold Row12.scalarM; linarith
  have hb : (2401 : ℝ) ≤ (99 * x - 50) ^ 2 := by
    have hh : 99 * x - 50 ≤ -49 := by linarith
    nlinarith
  have hp : (24 : ℝ) * 2401 ≤ Row12.scalarM x * (99 * x - 50) ^ 2 :=
    mul_le_mul hm hb (by norm_num) (by linarith)
  calc
    57624 * x ^ 4 = x ^ 4 * (24 * 2401) := by ring
    _ ≤ x ^ 4 * (Row12.scalarM x * (99 * x - 50) ^ 2) :=
      mul_le_mul_of_nonneg_left hp (pow_nonneg hx.le 4)
    _ = Row12.scalarDenom x := by unfold Row12.scalarDenom; ring

/--
@isnad1 id=eq.1h1v.s5.34e60666e759 from=translated src=- shape=0ee19d04 vocab=a1f3bd3f
-/
theorem upper_lambda_norm {x : ℝ} (hx : 0 < x) :
    ‖Row12.betaFrameLambda (x : ℂ)‖ = Real.sqrt (Row12.scalarLambda x) ^ 2 := by
  rw [(Row12.betaFrame_real_agreement x).2.2.2.2.2.2, Complex.norm_real,
    Real.norm_of_nonneg (Row12.scalarLambda_pos hx).le,
    Real.sq_sqrt (Row12.scalarLambda_pos hx).le]

/--
@isnad1 id=ne.2h2v.s5.6f0cd2301ad6 from=translated src=- shape=fcecd1c9 vocab=d96be1d2
-/
theorem upper_circle_nonzero {x : ℝ} {s : ℂ} (hx : 0 < x)
    (hs : ‖s‖ = Real.sqrt (Row12.scalarLambda x)) : s ≠ 0 := by
  apply norm_pos_iff.mp
  rw [hs]
  exact Real.sqrt_pos.2 (Row12.scalarLambda_pos hx)

/-- A direct reverse-triangle estimate, with radius and constants fixed numerically.
@isnad1 id=le.3h2v.s6.77e118e5c2c4 from=translated src=- shape=59a51c8d vocab=eaf430dd
-/
theorem upper_betaFrameF_lower {x : ℝ} {s : ℂ}
    (hx : 0 < x) (hxsmall : x ≤ 1 / 100)
    (hs : ‖s‖ = Real.sqrt (Row12.scalarLambda x)) :
    x * Real.sqrt (Row12.scalarLambda x) ≤ ‖Row12.betaFrameF (x : ℂ) s‖ := by
  let r := Real.sqrt (Row12.scalarLambda x)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hm := upper_scalarMid_lower hx hxsmall
  have hm0 : 0 ≤ Row12.scalarMid x := hx.le.trans hm
  have hmid := (Row12.betaFrame_real_agreement x).2.2.2.1
  have hlinear : ‖(2 : ℂ) * Row12.betaFrameMid (x : ℂ) * s‖ =
      2 * Row12.scalarMid x * r := by
    rw [norm_mul, norm_mul, hmid, Complex.norm_real, Real.norm_of_nonneg hm0, hs]
    norm_num [r]
  have hsmall : ‖s ^ 2 + Row12.betaFrameLambda (x : ℂ)‖ ≤ 2 * r ^ 2 := by
    calc
      _ ≤ ‖s ^ 2‖ + ‖Row12.betaFrameLambda (x : ℂ)‖ := norm_add_le _ _
      _ = 2 * r ^ 2 := by rw [norm_pow, hs, upper_lambda_norm hx]; dsimp [r]; ring
  have hid : (2 : ℂ) * Row12.betaFrameMid (x : ℂ) * s =
      (s ^ 2 + Row12.betaFrameLambda (x : ℂ)) - Row12.betaFrameF (x : ℂ) s := by
    unfold Row12.betaFrameF
    ring
  have ht : 2 * Row12.scalarMid x * r ≤ 2 * r ^ 2 + ‖Row12.betaFrameF (x : ℂ) s‖ := by
    calc
      _ = ‖(2 : ℂ) * Row12.betaFrameMid (x : ℂ) * s‖ := hlinear.symm
      _ = ‖(s ^ 2 + Row12.betaFrameLambda (x : ℂ)) - Row12.betaFrameF (x : ℂ) s‖ := by rw [hid]
      _ ≤ ‖s ^ 2 + Row12.betaFrameLambda (x : ℂ)‖ + ‖Row12.betaFrameF (x : ℂ) s‖ := norm_sub_le _ _
      _ ≤ 2 * r ^ 2 + ‖Row12.betaFrameF (x : ℂ) s‖ := add_le_add hsmall le_rfl
  have hrad : r ≤ x / 4 := upper_radius_le_quarter hx hxsmall
  have hgap : x ≤ 2 * (Row12.scalarMid x - r) := by linarith
  calc
    x * Real.sqrt (Row12.scalarLambda x) = x * r := rfl
    _ ≤ 2 * (Row12.scalarMid x - r) * r := mul_le_mul_of_nonneg_right hgap hr
    _ ≤ ‖Row12.betaFrameF (x : ℂ) s‖ := by nlinarith

/--
@isnad1 id=ne.3h2v.s6.63ad41029a45 from=translated src=- shape=ea8f766e vocab=9b808743
-/
theorem upper_betaFrameF_nonzero {x : ℝ} {s : ℂ}
    (hx : 0 < x) (hxsmall : x ≤ 1 / 100)
    (hs : ‖s‖ = Real.sqrt (Row12.scalarLambda x)) : Row12.betaFrameF (x : ℂ) s ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (mul_pos hx (Real.sqrt_pos.2 (Row12.scalarLambda_pos hx)))
    (upper_betaFrameF_lower hx hxsmall hs)

/--
@isnad1 id=le.2h1v.s6.243ce8cafd86 from=translated src=- shape=4ba0140d vocab=6c9ea48a
-/
theorem upper_betaFrameDenom_lower {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 100) :
    57624 * x ^ 4 ≤ ‖Row12.betaFrameDenom (x : ℂ)‖ := by
  have hd := upper_scalarDenom_lower hx hxsmall
  have hd0 : 0 ≤ Row12.scalarDenom x :=
    (mul_nonneg (by norm_num) (pow_nonneg hx.le 4)).trans hd
  rw [(Row12.betaFrame_real_agreement x).2.2.2.2.2.1,
    Complex.norm_real, Real.norm_of_nonneg hd0]
  exact hd

/--
@isnad1 id=ne.2h1v.s5.dcf18d3edabb from=translated src=- shape=fdb1408a vocab=f04dfddc
-/
theorem upper_betaFrameDenom_nonzero {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 100) :
    Row12.betaFrameDenom (x : ℂ) ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (mul_pos (by norm_num) (pow_pos hx 4))
    (upper_betaFrameDenom_lower hx hxsmall)

/--
@isnad1 id=eq.2h2v.s5.de0a97df5a73 from=translated src=- shape=19eaf34d vocab=12b5d1de
-/
theorem upper_balanced_argument_norm {x : ℝ} {s : ℂ} (hx : 0 < x)
    (hs : ‖s‖ = Real.sqrt (Row12.scalarLambda x)) :
    ‖Row12.betaFrameLambda (x : ℂ) / s‖ = Real.sqrt (Row12.scalarLambda x) := by
  rw [norm_div, upper_lambda_norm hx, hs, pow_two,
    mul_div_cancel_right₀ _ (ne_of_gt (Real.sqrt_pos.2 (Row12.scalarLambda_pos hx)))]

/--
@isnad1 id=le.3h2v.s6.f471649add5c from=translated src=- shape=17623d81 vocab=5cf75350
-/
theorem upper_betaFrame_denominator_lower {x : ℝ} {s : ℂ}
    (hx : 0 < x) (hxsmall : x ≤ 1 / 100)
    (hs : ‖s‖ = Real.sqrt (Row12.scalarLambda x)) :
    57624 * x ^ 5 * Real.sqrt (Row12.scalarLambda x) ≤
      ‖Row12.betaFrameDenom (x : ℂ) * Row12.betaFrameF (x : ℂ) s‖ := by
  calc
    _ = (57624 * x ^ 4) * (x * Real.sqrt (Row12.scalarLambda x)) := by ring
    _ ≤ ‖Row12.betaFrameDenom (x : ℂ)‖ * ‖Row12.betaFrameF (x : ℂ) s‖ :=
      mul_le_mul (upper_betaFrameDenom_lower hx hxsmall) (upper_betaFrameF_lower hx hxsmall hs)
        (mul_nonneg hx.le (Real.sqrt_nonneg _)) (norm_nonneg _)
    _ = _ := (norm_mul _ _).symm

/--
@isnad1 id=ne.3h2v.s6.6c59088ee2f1 from=translated src=- shape=b484ae3b vocab=81133d1f
-/
theorem upper_betaFrame_denominator_nonzero {x : ℝ} {s : ℂ}
    (hx : 0 < x) (hxsmall : x ≤ 1 / 100)
    (hs : ‖s‖ = Real.sqrt (Row12.scalarLambda x)) :
    Row12.betaFrameDenom (x : ℂ) * Row12.betaFrameF (x : ℂ) s ≠ 0 :=
  mul_ne_zero (upper_betaFrameDenom_nonzero hx hxsmall) (upper_betaFrameF_nonzero hx hxsmall hs)

end Row12EulerSupport

