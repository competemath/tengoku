import Tengoku.Piirrationalitymeasure.Formalization.Saddle
import Tengoku.Piirrationalitymeasure.Formalization.Statements
import Tengoku.Piirrationalitymeasure.Formalization.ScalarImplicitFunction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual parameter-dependent stationary cubic and its real analytic branch. -/

namespace PiIrrationality

open Filter
open scoped Topology

noncomputable def parameterStationary (p : ℝ × ℝ) (y : ℝ) : ℝ :=
  (p.1 + 2 * p.2 - 1) * y ^ 3 - (19 * p.1 + 44 * p.2 + 6) * y ^ 2 -
    (125 * p.1 + 150 * p.2 + 25) * y - 625 * p.1

noncomputable def parameterStationaryDerivative (p : ℝ × ℝ) (y : ℝ) : ℝ :=
  3 * (p.1 + 2 * p.2 - 1) * y ^ 2 - 2 * (19 * p.1 + 44 * p.2 + 6) * y -
    (125 * p.1 + 150 * p.2 + 25)

/--
@isnad1 id=eq.0h1v.s4.435588474088 from=translated src=- shape=59d5760e vocab=95ec9ad7
-/
theorem parameterStationary_candidate (y : ℝ) :
    parameterStationary candidate y = stationaryCubic y / 5570 := by
  dsimp [parameterStationary, candidate, stationaryCubic]
  ring

/--
@isnad1 id=hasderiv.0h2v.s5.b5a9bc46317d from=translated src=- shape=c949b204 vocab=a24ddf84
-/
theorem parameterStationary_hasDerivAt (p : ℝ × ℝ) (y : ℝ) :
    HasDerivAt (parameterStationary p) (parameterStationaryDerivative p y) y := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 y := hasDerivAt_id y
  have h := (((hid.pow 3).const_mul (p.1 + 2 * p.2 - 1)).sub
    ((hid.pow 2).const_mul (19 * p.1 + 44 * p.2 + 6))).sub
      (hid.const_mul (125 * p.1 + 150 * p.2 + 25))
  have h' : HasDerivAt (parameterStationary p)
      ((p.1 + 2 * p.2 - 1) * (3 * y ^ 2) - (19 * p.1 + 44 * p.2 + 6) * (2 * y) -
        (125 * p.1 + 150 * p.2 + 25)) y := by
    simpa only [Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, mul_one, pow_one]
      using! h.sub_const (625 * p.1)
  have he : parameterStationaryDerivative p y =
      (p.1 + 2 * p.2 - 1) * (3 * y ^ 2) - (19 * p.1 + 44 * p.2 + 6) * (2 * y) -
        (125 * p.1 + 150 * p.2 + 25) := by
    dsimp [parameterStationaryDerivative]
    ring
  rwa [he]

/--
@isnad1 id=analytic.0h2v.s7.0aed6a3105c6 from=translated src=- shape=1dd00fc8 vocab=a932632f
-/
theorem analyticAt_parameterStationary (p : ℝ × ℝ) (y : ℝ) :
    AnalyticAt ℝ (fun q : (ℝ × ℝ) × ℝ => parameterStationary q.1 q.2) (p, y) := by
  apply ContDiffAt.analyticAt
  unfold parameterStationary
  fun_prop

/--
@isnad1 id=lt.0h0v.s3.5a3c1bff7020 from=translated src=- shape=7164367e vocab=a49d3cde
-/
theorem parameterStationaryDerivative_candidate_pos :
    0 < parameterStationaryDerivative candidate stationaryRoot := by
  have hr := stationaryRoot_mem.1
  have he : parameterStationaryDerivative candidate stationaryRoot =
      (11145 * stationaryRoot ^ 2 - 464238 * stationaryRoot - 928475) / 5570 := by
    dsimp [parameterStationaryDerivative, candidate]
    ring
  rw [he]
  apply div_pos _ (by norm_num)
  nlinarith [sq_nonneg (stationaryRoot - 66)]

/--
@isnad1 id=ex.0h0v.s7.249e6585694a from=translated src=- shape=377eacd9 vocab=8f8b2723
-/
theorem parameterStationary_real_analytic_branch :
    ∃ g : ℝ × ℝ → ℝ, g candidate = stationaryRoot ∧ AnalyticAt ℝ g candidate ∧
      ∀ᶠ p in 𝓝 candidate, parameterStationary p (g p) = 0 ∧ 25 < g p := by
  obtain ⟨g, hg, hga, hroot⟩ := exists_analytic_scalar_implicit
    (analyticAt_parameterStationary candidate stationaryRoot)
    (parameterStationary_hasDerivAt candidate stationaryRoot)
    parameterStationaryDerivative_candidate_pos.ne'
  refine ⟨g, hg, hga, ?_⟩
  have hy : 25 < g candidate := by rw [hg]; linarith [stationaryRoot_mem.1]
  have hnear := hga.continuousAt.eventually_const_lt hy
  filter_upwards [hroot, hnear] with p hp hyp
  refine ⟨?_, hyp⟩
  simpa only [parameterStationary_candidate, stationaryRoot_eq_zero, zero_div] using hp

noncomputable def parameterRealSaddle : ℝ × ℝ → ℝ :=
  Classical.choose parameterStationary_real_analytic_branch

/--
@isnad1 id=eq.0h0v.s2.bb7d93d531ca from=translated src=- shape=4b736592 vocab=9646c003
-/
theorem parameterRealSaddle_candidate : parameterRealSaddle candidate = stationaryRoot :=
  (Classical.choose_spec parameterStationary_real_analytic_branch).1

/--
@isnad1 id=analytic.0h0v.s5.a244aba0232e from=translated src=- shape=3217f290 vocab=523ea6bd
-/
theorem analyticAt_parameterRealSaddle : AnalyticAt ℝ parameterRealSaddle candidate :=
  (Classical.choose_spec parameterStationary_real_analytic_branch).2.1

/--
@isnad1 id=eventual.0h0v.s5.561168397fb8 from=translated src=- shape=6f25763e vocab=d465db5f
-/
theorem parameterRealSaddle_near_candidate : ∀ᶠ p in 𝓝 candidate,
    parameterStationary p (parameterRealSaddle p) = 0 ∧ 25 < parameterRealSaddle p :=
  (Classical.choose_spec parameterStationary_real_analytic_branch).2.2

end PiIrrationality
