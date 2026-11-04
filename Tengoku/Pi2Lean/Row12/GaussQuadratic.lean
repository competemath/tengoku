import Tengoku.Pi2Lean.Row12.GaussSeries
import Tengoku.Seed.Analysis.SpecialFunctions.Sqrt
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Analytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12.gaussP_norm_lt_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussP_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussG_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussSqrt_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussP_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussSqrt_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussP_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussG_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussG_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussG_deriv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussInvSqrt_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussG_second_deriv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussP_quadratic` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussP_linear` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussG_equation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussG_theta_second` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussG_nativeSecond` (it only prints; the queue checks the axioms of every declaration). -/

open Filter

namespace Row12

noncomputable def gaussP (q : ℝ) : ℝ := (1 - Real.sqrt (1 - q)) / 2

noncomputable def gaussG (q : ℝ) : ℝ := gaussA (gaussP q)

/--
@isnad1 id=lt.2h1v.s5.c85f42091f44 from=translated src=- shape=7e143dca vocab=7e8ae589
-/
theorem gaussP_norm_lt_one (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    ‖gaussP q‖ < 1 := by
  have hs0 : 0 < Real.sqrt (1 - q) := Real.sqrt_pos.2 (by linarith)
  have hs2 : Real.sqrt (1 - q) ^ 2 = 1 - q := Real.sq_sqrt (by linarith)
  have hs3 : Real.sqrt (1 - q) < 3 := by nlinarith
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> dsimp [gaussP] <;> linarith

/--
@isnad1 id=eq.0h0v.s3.7bf3eb036826 from=translated src=- shape=3c26ae4f vocab=8fbb9705
-/
theorem gaussP_zero : gaussP 0 = 0 := by norm_num [gaussP]

/--
@isnad1 id=eq.0h0v.s3.5f0912b8a2d0 from=translated src=- shape=3c26ae4f vocab=1b3a6525
-/
theorem gaussG_zero : gaussG 0 = 1 := by
  simp only [gaussG, gaussP_zero, gaussA_zero]

/--
@isnad1 id=hasderiv.1h1v.s6.501960aa5274 from=translated src=- shape=ec5e8311 vocab=8968d1fe
-/
theorem gaussSqrt_hasDerivAt (q : ℝ) (hq : q < 1) :
    HasDerivAt (fun x : ℝ => Real.sqrt (1 - x))
      (-1 / (2 * Real.sqrt (1 - q))) q := by
  simpa only [zero_sub, id_eq] using
    ((hasDerivAt_id q).const_sub 1).sqrt (by linarith : 1 - q ≠ 0)

/--
@isnad1 id=hasderiv.1h1v.s6.2e989792a688 from=translated src=- shape=cf519556 vocab=2bd61ce6
-/
theorem gaussP_hasDerivAt (q : ℝ) (hq : q < 1) :
    HasDerivAt gaussP (1 / (4 * Real.sqrt (1 - q))) q := by
  have hs : Real.sqrt (1 - q) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hd := ((gaussSqrt_hasDerivAt q hq).const_sub 1).div_const 2
  have he : -(-1 / (2 * Real.sqrt (1 - q))) / 2 =
      1 / (4 * Real.sqrt (1 - q)) := by field_simp [hs]; ring
  convert! hd.congr_deriv he using 1

/--
@isnad1 id=analytic.1h1v.s5.66f2d16bc22c from=translated src=- shape=cb89bad8 vocab=174d475b
-/
theorem gaussSqrt_analyticAt (q : ℝ) (hq : q < 1) :
    AnalyticAt ℝ (fun x : ℝ => Real.sqrt (1 - x)) q := by
  have hl : AnalyticAt ℝ (fun x : ℝ => Real.log (1 - x)) q :=
    (analyticAt_log (by linarith : 0 < 1 - q)).comp (by fun_prop)
  have hh : AnalyticAt ℝ (fun x : ℝ => Real.log (1 - x) * (1 / 2)) q := by fun_prop
  have ha : AnalyticAt ℝ (fun x : ℝ => Real.exp (Real.log (1 - x) * (1 / 2))) q := hh.rexp'
  apply ha.congr
  have hn : Set.Iio (1 : ℝ) ∈ nhds q := isOpen_Iio.mem_nhds hq
  filter_upwards [hn] with x hx
  change x < 1 at hx
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith : 0 < 1 - x)]

/--
@isnad1 id=analytic.1h1v.s5.4df4082b1be3 from=translated src=- shape=d04ac3e0 vocab=36da40d3
-/
theorem gaussP_analyticAt (q : ℝ) (hq : q < 1) : AnalyticAt ℝ gaussP q := by
  have hs := gaussSqrt_analyticAt q hq
  unfold gaussP
  fun_prop

/--
@isnad1 id=analytic.2h1v.s5.8fb85936c90c from=translated src=- shape=7c3c738a vocab=60f16c4c
-/
theorem gaussG_analyticAt (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    AnalyticAt ℝ gaussG q :=
  (gaussA_analyticAt (gaussP q) (gaussP_norm_lt_one q hq0 hq1)).comp
    (gaussP_analyticAt q hq1)

/--
@isnad1 id=hasderiv.2h1v.s7.c96bbd632682 from=translated src=- shape=ce7dc107 vocab=546b528c
-/
theorem gaussG_hasDerivAt (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    HasDerivAt gaussG
      (deriv gaussA (gaussP q) / (4 * Real.sqrt (1 - q))) q := by
  have ha := (gaussA_analyticAt (gaussP q)
    (gaussP_norm_lt_one q hq0 hq1)).differentiableAt.hasDerivAt
  have hd := ha.comp q (gaussP_hasDerivAt q hq1)
  have he : deriv gaussA (gaussP q) * (1 / (4 * Real.sqrt (1 - q))) =
      deriv gaussA (gaussP q) / (4 * Real.sqrt (1 - q)) := by ring
  convert! hd.congr_deriv he using 1

/--
@isnad1 id=eq.2h1v.s7.2e041a2677fe from=translated src=- shape=6935dfbb vocab=e50e59c2
-/
theorem gaussG_deriv (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    deriv gaussG q = deriv gaussA (gaussP q) / (4 * Real.sqrt (1 - q)) :=
  (gaussG_hasDerivAt q hq0 hq1).deriv

/--
@isnad1 id=hasderiv.1h1v.s7.a39473a59ec7 from=translated src=- shape=b022c889 vocab=d5c6ffa6
-/
theorem gaussInvSqrt_hasDerivAt (q : ℝ) (hq : q < 1) :
    HasDerivAt (fun x : ℝ => 1 / (4 * Real.sqrt (1 - x)))
      (1 / (8 * Real.sqrt (1 - q) ^ 3)) q := by
  have hs : Real.sqrt (1 - q) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hd := ((gaussSqrt_hasDerivAt q hq).const_mul 4).inv (mul_ne_zero (by norm_num) hs)
  have he : -(4 * (-1 / (2 * Real.sqrt (1 - q)))) / (4 * Real.sqrt (1 - q)) ^ 2 =
      1 / (8 * Real.sqrt (1 - q) ^ 3) := by field_simp [hs]; ring
  convert! hd.congr_deriv he using 1
  funext x
  exact one_div (4 * Real.sqrt (1 - x))

/--
@isnad1 id=eq.2h1v.s8.c68c00d405a2 from=translated src=- shape=32c8f8c9 vocab=1ff0a4d9
-/
theorem gaussG_second_deriv (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    deriv (deriv gaussG) q =
      deriv (deriv gaussA) (gaussP q) / (16 * Real.sqrt (1 - q) ^ 2) +
      deriv gaussA (gaussP q) / (8 * Real.sqrt (1 - q) ^ 3) := by
  have hs : Real.sqrt (1 - q) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have ha := (gaussA_analyticAt (gaussP q)
    (gaussP_norm_lt_one q hq0 hq1)).deriv.differentiableAt.hasDerivAt
  have hd := ((ha.comp q (gaussP_hasDerivAt q hq1)).mul
    (gaussInvSqrt_hasDerivAt q hq1))
  have he : deriv gaussG =ᶠ[nhds q]
      (fun x : ℝ => deriv gaussA (gaussP x) * (1 / (4 * Real.sqrt (1 - x)))) := by
    have hn : Set.Ioo (-8 : ℝ) 1 ∈ nhds q := isOpen_Ioo.mem_nhds ⟨hq0, hq1⟩
    filter_upwards [hn] with x hx
    rw [gaussG_deriv x hx.1 hx.2]
    ring
  rw [(hd.congr_of_eventuallyEq he).deriv]
  simp only [Function.comp_apply]
  field_simp [hs]
  ring

/--
@isnad1 id=eq.1h1v.s5.20d9b207318d from=translated src=- shape=682701f4 vocab=4aacaad8
-/
theorem gaussP_quadratic (q : ℝ) (hq : q < 1) :
    gaussP q * (1 - gaussP q) = q / 4 := by
  have hs : Real.sqrt (1 - q) ^ 2 = 1 - q := Real.sq_sqrt (by linarith)
  dsimp [gaussP]
  nlinarith

/--
@isnad1 id=eq.0h1v.s5.43ea91907b68 from=translated src=- shape=3350891c vocab=03499ec9
-/
theorem gaussP_linear (q : ℝ) : 1 - 2 * gaussP q = Real.sqrt (1 - q) := by
  dsimp [gaussP]
  ring

/--
@isnad1 id=eq.2h1v.s7.51d7d371854c from=translated src=- shape=c498a2fa vocab=051bac95
-/
theorem gaussG_equation (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    q * (1 - q) * deriv (deriv gaussG) q +
      (1 - 3 * q / 2) * deriv gaussG q - (5 / 144 : ℝ) * gaussG q = 0 := by
  have hs0 : Real.sqrt (1 - q) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hs2 : Real.sqrt (1 - q) ^ 2 = 1 - q := Real.sq_sqrt (by linarith)
  have he := gaussA_equation (gaussP q) (gaussP_norm_lt_one q hq0 hq1)
  rw [gaussP_quadratic q hq1, gaussP_linear q] at he
  rw [gaussG_second_deriv q hq0 hq1, gaussG_deriv q hq0 hq1]
  dsimp only [gaussG]
  have hid :
      q * (1 - q) * (deriv (deriv gaussA) (gaussP q) / (16 * Real.sqrt (1 - q) ^ 2) +
        deriv gaussA (gaussP q) / (8 * Real.sqrt (1 - q) ^ 3)) +
        (1 - 3 * q / 2) * (deriv gaussA (gaussP q) / (4 * Real.sqrt (1 - q))) -
        (5 / 144 : ℝ) * gaussA (gaussP q) =
      (q / 4 * deriv (deriv gaussA) (gaussP q) +
        Real.sqrt (1 - q) * deriv gaussA (gaussP q) - 5 / 36 * gaussA (gaussP q)) / 4 := by
    generalize Real.sqrt (1 - q) = s at hs0 hs2 ⊢
    have hq : q = 1 - s ^ 2 := by linarith
    rw [hq]
    field_simp [hs0]
    ring
  rw [hid, he]
  norm_num

/--
@isnad1 id=eq.2h1v.s7.7f6ed8d0f45d from=translated src=- shape=80f0f813 vocab=0f5daf63
-/
theorem gaussG_theta_second (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    nativeTheta (nativeTheta gaussG) q =
      q * deriv gaussG q + q ^ 2 * deriv (deriv gaussG) q := by
  have hg := (gaussG_analyticAt q hq0 hq1).deriv.differentiableAt.hasDerivAt
  have hd := (hasDerivAt_id q).mul hg
  change q * deriv (fun x : ℝ => x * deriv gaussG x) q = _
  have he : deriv (fun x : ℝ => x * deriv gaussG x) q =
      deriv gaussG q + q * deriv (deriv gaussG) q := by
    convert! hd.deriv using 1
    simp only [id_eq, one_mul]
  rw [he]
  ring

/--
@isnad1 id=eq.2h1v.s7.bb4fff114bab from=translated src=- shape=6bcbae74 vocab=77a1ba92
-/
theorem gaussG_nativeSecond (q : ℝ) (hq0 : -8 < q) (hq1 : q < 1) :
    144 * (1 - q) * nativeTheta (nativeTheta gaussG) q -
      72 * q * nativeTheta gaussG q - 5 * q * gaussG q = 0 := by
  rw [gaussG_theta_second q hq0 hq1]
  dsimp only [nativeTheta]
  linear_combination 144 * q * gaussG_equation q hq0 hq1

end Row12

