import Tengoku.Seed.Analysis.Analytic.Basic
import Tengoku.Seed.Analysis.Calculus.Deriv.MeanValue
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
import Tengoku.Seed.Dynamics.FixedPoints.Topology
import Tengoku.Seed.Topology.Order.MonotoneConvergence
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analytic Abel functions for `exp x - 1`

This file states the paper's assumptions on the positive real axis and proves
their elementary consequences. A Lean function is total; its values outside the
positive real axis are immaterial to `IsAbel`.
-/

open Set Filter Function
open scoped Topology

namespace AbelFormalization

noncomputable section

/-- The self-map of the positive real axis used in the Abel equation.-/
def E (x : ℝ) : ℝ := Real.exp x - 1

/-- Exactly the analyticity, derivative, normalization and Abel-equation
assumptions in equation (1) of the paper.-/
structure IsAbel (A : ℝ → ℝ) : Prop where
  analytic : AnalyticOnNhd ℝ A (Ioi 0)
  deriv_pos : ∀ x > 0, 0 < deriv A x
  normalized : A 1 = 0
  abel : ∀ x > 0, A (E x) = A x + 1

/--
@isnad1 id=lt.1h1v.s4.e631271cce5e from=translated src=- shape=35bd48ee vocab=4aa3b9a0
-/
theorem E_pos {x : ℝ} (hx : 0 < x) : 0 < E x := by
  exact sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)

/--
@isnad1 id=lt.1h1v.s4.6316a968ef31 from=translated src=- shape=9331e166 vocab=4aa3b9a0
-/
theorem lt_E {x : ℝ} (hx : 0 < x) : x < E x := by
  have h := Real.add_one_lt_exp (ne_of_gt hx)
  dsimp [E]
  linarith

/--
@isnad1 id=strictmo.0h0v.s2.fade54487f8d from=translated src=- shape=e3d48bcb vocab=ba533b16
-/
theorem E_strictMono : StrictMono E := by
  intro x y hxy
  exact sub_lt_sub_right (Real.exp_strictMono hxy) 1

/--
@isnad1 id=continuo.0h0v.s3.7eff7fb3290c from=translated src=- shape=e3d48bcb vocab=e40af797
-/
theorem E_continuous : Continuous E := Real.continuous_exp.sub continuous_const

/--
@isnad1 id=lt.1h2v.s4.83a0945fb256 from=translated src=- shape=adab10c0 vocab=38d077a8
-/
theorem E_iterate_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 < E^[n] x := by
  induction n with
  | zero => simpa using hx
  | succ n ih => simpa only [Function.iterate_succ_apply'] using E_pos ih

/--
@isnad1 id=strictmo.1h1v.s4.faa6e214037a from=translated src=- shape=0b5729fc vocab=bc80fe4d
-/
theorem E_iterate_strictMono {x : ℝ} (hx : 0 < x) :
    StrictMono (fun n : ℕ => E^[n] x) := by
  apply strictMono_nat_of_lt_succ
  intro n
  simpa only [Function.iterate_succ_apply'] using lt_E (E_iterate_pos hx n)

/--
@isnad1 id=tendsto.1h1v.s4.b02a55bb60cb from=translated src=- shape=1fd08995 vocab=6849e49b
-/
theorem E_iterate_tendsto_atTop {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => E^[n] x) atTop atTop := by
  have hm := (E_iterate_strictMono hx).monotone
  rcases tendsto_atTop_of_monotone hm with h | ⟨l, hl⟩
  · exact h
  · have hxl : x ≤ l := by
      apply ge_of_tendsto hl
      exact Filter.Eventually.of_forall (fun n => by simpa using hm (Nat.zero_le n))
    have hfix := isFixedPt_of_tendsto_iterate hl E_continuous.continuousAt
    have hlt := lt_E (lt_of_lt_of_le hx hxl)
    exact False.elim ((ne_of_gt hlt) hfix)

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/--
@isnad1 id=continuo.1h1v.s4.3091c24882df from=translated src=- shape=8b4d7ca8 vocab=65f20971
-/
theorem continuousOn : ContinuousOn A (Ioi 0) := hA.analytic.continuousOn

/--
@isnad1 id=strictmo.1h1v.s4.8dd213a34237 from=translated src=- shape=8b4d7ca8 vocab=c1b70730
-/
theorem strictMonoOn : StrictMonoOn A (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ)) hA.continuousOn
  intro x hx
  exact hA.deriv_pos x (interior_subset hx)

/--
@isnad1 id=injon.1h1v.s4.5a1f90dea45f from=translated src=- shape=8b4d7ca8 vocab=48cf338c
-/
theorem injectiveOn : Set.InjOn A (Ioi 0) := hA.strictMonoOn.injOn

/--
@isnad1 id=eq.2h3v.s5.310c10bed40b from=translated src=- shape=df9e845a vocab=7bf9c882
-/
theorem abel_iterate {x : ℝ} (hx : 0 < x) (n : ℕ) :
    A (E^[n] x) = A x + (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', hA.abel _ (E_iterate_pos hx n), ih]
      simp only [Nat.cast_succ]
      linarith

/--
@isnad1 id=eq.1h2v.s4.e9f84d449b6a from=translated src=- shape=55c7c05d vocab=625d6e8a
-/
theorem abel_iterate_one (n : ℕ) : A (E^[n] 1) = (n : ℝ) := by
  simpa [hA.normalized] using hA.abel_iterate (show (0 : ℝ) < 1 from zero_lt_one) n

/--
@isnad1 id=le.2h2v.s5.c7db3063192b from=translated src=- shape=ce03371a vocab=d00f8622
-/
theorem nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ A x := by
  have hp : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  simpa [hA.normalized] using
    hA.strictMonoOn.monotoneOn (show (0 : ℝ) < 1 from zero_lt_one) hp hx

/--
@isnad1 id=lt.2h2v.s5.645605cea5e1 from=translated src=- shape=ce03371a vocab=8f79f274
-/
theorem pos_of_one_lt {x : ℝ} (hx : 1 < x) : 0 < A x := by
  have hp : (0 : ℝ) < x := lt_trans zero_lt_one hx
  simpa [hA.normalized] using
    hA.strictMonoOn (show (0 : ℝ) < 1 from zero_lt_one) hp hx

/--
@isnad1 id=ex.1h2v.s4.2ca8b0b00942 from=translated src=- shape=7b2010a1 vocab=63fb5fa7
-/
theorem exists_pos_value_gt (b : ℝ) : ∃ x > 0, b < A x := by
  obtain ⟨n, hn⟩ := exists_nat_gt b
  refine ⟨E^[n] 1, E_iterate_pos zero_lt_one n, ?_⟩
  simpa only [hA.abel_iterate_one] using hn

/--
@isnad1 id=tendsto.1h1v.s4.bf5070a451a2 from=translated src=- shape=3576cc78 vocab=29fdc513
-/
theorem tendsto_atTop : Tendsto A atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  obtain ⟨x, hx, hb⟩ := hA.exists_pos_value_gt b
  exact (eventually_ge_atTop x).mono fun y hy =>
    hb.le.trans (hA.strictMonoOn.monotoneOn hx (hx.trans_le hy) hy)

end IsAbel
end
end AbelFormalization
