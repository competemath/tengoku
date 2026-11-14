import Tengoku.Piirrationalitymeasure.Formalization.Coefficient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The logarithmic slope of S and its unique positive real saddle in Section 4.1. -/

namespace PiIrrationality

def PRealPrime (x : ℝ) : ℝ := 6 + 18 * x + 18 * x ^ 2 + 8 * x ^ 3

def PMeanNumerator (x : ℝ) : ℝ :=
  12 + 72 * x + 162 * x ^ 2 + 208 * x ^ 3 + 162 * x ^ 4 + 72 * x ^ 5 + 12 * x ^ 6

noncomputable def coefficientMean (x : ℝ) : ℝ :=
  3714 * x / (1 + x) + 3714 * (x * PRealPrime x) / PReal x + 7430 * x / (1 - x)

noncomputable def coefficientMeanPrime (x : ℝ) : ℝ :=
  3714 / (1 + x) ^ 2 + 3714 * PMeanNumerator x / PReal x ^ 2 + 7430 / (1 - x) ^ 2

theorem PReal_hasDerivAt (x : ℝ) : HasDerivAt PReal (PRealPrime x) x := by
  convert! ((((hasDerivAt_const x (2 : ℝ)).add ((hasDerivAt_id x).const_mul 6)).add
    (((hasDerivAt_id x).pow 2).const_mul 9)).add
    (((hasDerivAt_id x).pow 3).const_mul 6)).add
    (((hasDerivAt_id x).pow 4).const_mul 2) using 1
  dsimp [PReal, PRealPrime]
  ring

theorem PRealPrime_hasDerivAt (x : ℝ) :
    HasDerivAt PRealPrime (18 + 36 * x + 24 * x ^ 2) x := by
  convert! (((hasDerivAt_const x (6 : ℝ)).add ((hasDerivAt_id x).const_mul 18)).add
    (((hasDerivAt_id x).pow 2).const_mul 18)).add
    (((hasDerivAt_id x).pow 3).const_mul 8) using 1
  dsimp [PRealPrime]
  ring

theorem PMeanNumerator_pos {x : ℝ} (hx : 0 ≤ x) : 0 < PMeanNumerator x := by
  dsimp [PMeanNumerator]
  positivity

theorem coefficientMean_hasDerivAt {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasDerivAt coefficientMean (coefficientMeanPrime x) x := by
  have hp : 1 + x ≠ 0 := by linarith
  have hm : 1 - x ≠ 0 := by linarith
  have hP := (PReal_strictPositive x hx0).ne'
  have h := ((((hasDerivAt_id x).const_mul 3714).div
    ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)) hp).add
    ((((hasDerivAt_id x).mul (PRealPrime_hasDerivAt x)).const_mul 3714).div
      (PReal_hasDerivAt x) hP)).add
    (((hasDerivAt_id x).const_mul 7430).div
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) hm)
  convert! h using 1
  dsimp [coefficientMeanPrime, PMeanNumerator, PRealPrime, PReal]
  field_simp
  ring

theorem coefficientMeanPrime_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 < coefficientMeanPrime x := by
  have hp : 0 < 1 + x := by linarith
  have hm : 0 < 1 - x := by linarith
  have hP := PReal_strictPositive x hx0
  have hN := PMeanNumerator_pos hx0
  unfold coefficientMeanPrime
  positivity

theorem coefficientMean_strictMono : StrictMonoOn coefficientMean (Set.Ico 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 1)
  · intro x hx
    exact (coefficientMean_hasDerivAt hx.1 hx.2).continuousAt.continuousWithinAt
  · intro x hx
    have hx' := interior_subset hx
    rw [(coefficientMean_hasDerivAt hx'.1 hx'.2).deriv]
    exact coefficientMeanPrime_pos hx'.1 hx'.2

theorem coefficientMean_unique_saddle :
    ∃! x : ℝ, x ∈ Set.Ioo 0 1 ∧ coefficientMean x = 5570 := by
  have hcont : ContinuousOn coefficientMean (Set.Icc 0 (1 / 2 : ℝ)) := by
    intro x hx
    exact (coefficientMean_hasDerivAt hx.1 (by linarith [hx.2])).continuousAt.continuousWithinAt
  have hb : (5570 : ℝ) ∈ Set.Icc (coefficientMean 0) (coefficientMean (1 / 2)) := by
    norm_num [coefficientMean, PReal, PRealPrime]
  obtain ⟨x, hx, hm⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 / 2 by norm_num) hcont hb
  have hxpos : 0 < x := by
    have hzero : coefficientMean 0 = 0 := by norm_num [coefficientMean, PRealPrime]
    by_contra h
    have hxzero : x = 0 := by linarith [hx.1]
    rw [hxzero, hzero] at hm
    norm_num at hm
  have hx1 : x < 1 := by linarith [hx.2]
  refine ⟨x, ⟨⟨hxpos, hx1⟩, hm⟩, fun y hy => ?_⟩
  exact coefficientMean_strictMono.injOn ⟨hy.1.1.le, hy.1.2⟩ ⟨hxpos.le, hx1⟩
    (hy.2.trans hm.symm)

noncomputable def coefficientSaddle : ℝ := coefficientMean_unique_saddle.exists.choose

theorem coefficientSaddle_mem : coefficientSaddle ∈ Set.Ioo 0 1 :=
  coefficientMean_unique_saddle.exists.choose_spec.1

theorem coefficientSaddle_mean : coefficientMean coefficientSaddle = 5570 :=
  coefficientMean_unique_saddle.exists.choose_spec.2

theorem coefficientSaddle_variance_pos :
    0 < coefficientSaddle * deriv coefficientMean coefficientSaddle := by
  rw [(coefficientMean_hasDerivAt coefficientSaddle_mem.1.le coefficientSaddle_mem.2).deriv]
  exact mul_pos coefficientSaddle_mem.1
    (coefficientMeanPrime_pos coefficientSaddle_mem.1.le coefficientSaddle_mem.2)

end PiIrrationality
