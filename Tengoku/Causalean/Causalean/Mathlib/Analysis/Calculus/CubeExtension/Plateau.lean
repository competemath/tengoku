module
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Calculus.CubeExtension.Glue
public import Tengoku

/-!
# The exact quintic radial plateau

The real extension equals one on the entire half-line `r ≤ 1`, transitions by
the specified quintic on `(1,2)`, and vanishes on `r ≥ 2`. Its real support is
therefore `(-∞,2)`, not a compact interval. On nonnegative radii its support is
contained in `[0,2]`; composition with a norm is treated in `Radial`.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- At [a real radius](hyp:r), [the plateau](goal) is
[one through radius one, the exact quintic until radius two, and zero thereafter](step:1). -/
noncomputable def plateau (r : ℝ) : ℝ :=
  if r ≤ 1 then 1 else
    if r < 2 then 1 - 10 * (r - 1) ^ 3 + 15 * (r - 1) ^ 4 - 6 * (r - 1) ^ 5 else 0

/-- At [a real radius](hyp:r), [the first plateau jet](goal) is
[the quintic derivative in the transition region and zero elsewhere](step:1). -/
noncomputable def plateauD1 (r : ℝ) : ℝ :=
  if 1 < r ∧ r < 2 then -30 * (r - 1) ^ 2 + 60 * (r - 1) ^ 3 - 30 * (r - 1) ^ 4 else 0

/-- At [a real radius](hyp:r), [the second plateau jet](goal) is
[the second quintic derivative in the transition region and zero elsewhere](step:1). -/
noncomputable def plateauD2 (r : ℝ) : ℝ :=
  if 1 < r ∧ r < 2 then -60 * (r - 1) + 180 * (r - 1) ^ 2 - 120 * (r - 1) ^ 3 else 0

/-- At [every real radius](hyp:r), [the transition polynomial has its exact
first derivative](goal), before the constant branches are glued.
@isnad1 id=hasderiv.0h1v.s8.fbc04c0779b2 from=translated src=- shape=56afb807 vocab=982a4af2
-/
theorem plateau_polynomial_hasDerivAt (r : ℝ) :
    HasDerivAt (fun v : ℝ =>
      1 - 10 * (v - 1) ^ 3 + 15 * (v - 1) ^ 4 - 6 * (v - 1) ^ 5)
      (-30 * (r - 1) ^ 2 + 60 * (r - 1) ^ 3 - 30 * (r - 1) ^ 4) r := by
  have ht := (hasDerivAt_id r).sub_const 1
  convert! ((((hasDerivAt_const r (1 : ℝ)).sub ((ht.pow 3).const_mul 10)).add
    ((ht.pow 4).const_mul 15)).sub ((ht.pow 5).const_mul 6)) using 1 <;> (try simp) <;> ring

/-- At [every real radius](hyp:r), [the first transition polynomial has its
exact second derivative](goal), before the constant branches are glued.
@isnad1 id=hasderiv.0h1v.s8.f35ab5a189dd from=translated src=- shape=66e5c696 vocab=982a4af2
-/
theorem plateau_polynomialD1_hasDerivAt (r : ℝ) :
    HasDerivAt (fun v : ℝ =>
      -30 * (v - 1) ^ 2 + 60 * (v - 1) ^ 3 - 30 * (v - 1) ^ 4)
      (-60 * (r - 1) + 180 * (r - 1) ^ 2 - 120 * (r - 1) ^ 3) r := by
  have ht := (hasDerivAt_id r).sub_const 1
  convert! ((((ht.pow 2).const_mul (-30)).add ((ht.pow 3).const_mul 60)).sub
    ((ht.pow 4).const_mul 30)) using 1 <;> (try simp) <;> ring

/-- At [every real radius](hyp:r), [the quintic factors into a cubic boundary
zero and a positive quadratic on the transition interval](goal).
@isnad1 id=eq.0h1v.s8.966458814f57 from=translated src=- shape=3b6f929a vocab=3f072e55
-/
theorem plateau_polynomial_factor (r : ℝ) :
    1 - 10 * (r - 1) ^ 3 + 15 * (r - 1) ^ 4 - 6 * (r - 1) ^ 5 =
      (2 - r) ^ 3 * (1 + 3 * (r - 1) + 6 * (r - 1) ^ 2) := by
  ring

/-- At [every real radius](hyp:r), [the complement of the quintic factors
into a cubic boundary zero and a positive quadratic on the transition interval](goal).
@isnad1 id=eq.0h1v.s8.9a93fe734c7b from=translated src=- shape=f7eabda2 vocab=3f072e55
-/
theorem plateau_polynomial_complement_factor (r : ℝ) :
    1 - (1 - 10 * (r - 1) ^ 3 + 15 * (r - 1) ^ 4 - 6 * (r - 1) ^ 5) =
      (r - 1) ^ 3 * (1 + 3 * (2 - r) + 6 * (2 - r) ^ 2) := by
  ring

/-- At [a radius](hyp:r) [at most one](hyp:hr), [the plateau is one](goal).
@isnad1 id=eq.1h1v.s4.5baa568ffe46 from=translated src=- shape=278e0375 vocab=3a0de68a
-/
theorem plateau_eq_one (r : ℝ) (hr : r ≤ 1) : plateau r = 1 := by
  simp [plateau, hr]

/-- At [a radius](hyp:r) [at least two](hyp:hr), [the plateau vanishes](goal).
@isnad1 id=eq.1h1v.s4.6b164c01b302 from=translated src=- shape=97c35add vocab=d6acbf1d
-/
theorem plateau_eq_zero (r : ℝ) (hr : 2 ≤ r) : plateau r = 0 := by
  simp [plateau, show ¬r ≤ 1 by linarith, show ¬r < 2 by linarith]

/-- [The plateau lies between zero and one](goal) at [every real input](hyp:r).

On the transition region, factor its derivative as
`-30*(r-1)^2*(2-r)^2`, or factor the polynomial and its complement.
@isnad1 id=and.0h1v.s4.01d6d0983ed3 from=translated src=- shape=fd7c5cb5 vocab=3a0de68a
-/
theorem plateau_bounds (r : ℝ) : 0 ≤ plateau r ∧ plateau r ≤ 1 := by
  by_cases h₁ : r ≤ 1
  · simp [plateau, h₁]
  by_cases h₂ : r < 2
  · have ha : 0 ≤ r - 1 := by linarith
    have hb : 0 ≤ 2 - r := by linarith
    have hp : 0 ≤ (2 - r) ^ 3 * (1 + 3 * (r - 1) + 6 * (r - 1) ^ 2) :=
      mul_nonneg (pow_nonneg hb 3) (by positivity)
    have hc : 0 ≤ (r - 1) ^ 3 * (1 + 3 * (2 - r) + 6 * (2 - r) ^ 2) :=
      mul_nonneg (pow_nonneg ha 3) (by positivity)
    rw [← plateau_polynomial_factor] at hp
    rw [← plateau_polynomial_complement_factor] at hc
    simp only [plateau, ite_eq_right h₁, ite_eq_left h₂]
    exact ⟨hp, by linarith⟩
  · simp [plateau, h₁, h₂]

/-- [The nonzero support of the real plateau is the radius-two left half-line](goal).
@isnad1 id=eq.0h0v.s4.cb28317bfaea from=translated src=- shape=af22ce47 vocab=581d3f5b
-/
theorem plateau_support : Function.support plateau = Set.Iio 2 := by
  ext r
  simp only [Function.mem_support, Set.mem_Iio]
  constructor
  · intro h
    by_contra hn
    exact h (plateau_eq_zero r (le_of_not_gt hn))
  · intro h₂
    by_cases h₁ : r ≤ 1
    · simp [plateau_eq_one r h₁]
    · have ha : 0 ≤ r - 1 := by linarith
      have hb : 0 < 2 - r := by linarith
      have hp : 0 < (2 - r) ^ 3 * (1 + 3 * (r - 1) + 6 * (r - 1) ^ 2) :=
        mul_pos (pow_pos hb 3) (by positivity)
      rw [← plateau_polynomial_factor] at hp
      simpa only [plateau, ite_eq_right h₁, ite_eq_left h₂] using ne_of_gt hp

/-- [The support among nonnegative radii is contained in the closed radius-two interval](goal).
@isnad1 id=le.0h0v.s5.966a3e271f58 from=translated src=- shape=306adda9 vocab=9ebe1c7f
-/
theorem plateau_nonnegative_support :
    Function.support plateau ∩ Set.Ici 0 ⊆ Set.Icc 0 2 := by
  intro r hr
  rw [plateau_support] at hr
  exact ⟨hr.2, le_of_lt hr.1⟩

/-- [The plateau is locally constant one near zero](goal).
@isnad1 id=eventual.0h0v.s4.2d5134f0008b from=translated src=- shape=5e27f846 vocab=87b6a69e
-/
theorem plateau_eventually_one : ∀ᶠ r in nhds (0 : ℝ), plateau r = 1 := by
  filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with r hr
  exact plateau_eq_one r (le_of_lt hr)

/-- The plateau agrees with the nested closed-half-line joins; the polynomial
vanishes at two, so the strict transition test is preserved. -/
private theorem plateau_eq_join : plateau =
    joinAt 1 (fun _ => 1) (joinAt 2 (fun r =>
      1 - 10 * (r - 1) ^ 3 + 15 * (r - 1) ^ 4 - 6 * (r - 1) ^ 5) (fun _ => 0)) := by
  funext r
  by_cases h₁ : r ≤ 1
  · simp [plateau, joinAt, h₁]
  by_cases h₂ : r < 2
  · simp [plateau, joinAt, h₁, h₂, h₂.le]
  by_cases he : r = 2
  · subst r; norm_num [plateau, joinAt]
  · have hn : ¬r ≤ 2 := by grind
    simp [plateau, joinAt, h₁, h₂, hn]

/-- The first jet is the nested join of the first polynomial jet with zeros. -/
private theorem plateauD1_eq_join : plateauD1 =
    joinAt 1 (fun _ => 0) (joinAt 2 (fun r =>
      -30 * (r - 1) ^ 2 + 60 * (r - 1) ^ 3 - 30 * (r - 1) ^ 4) (fun _ => 0)) := by
  funext r
  by_cases h₁ : r ≤ 1
  · simp [plateauD1, joinAt, h₁, not_lt_of_ge h₁]
  by_cases h₂ : r < 2
  · simp [plateauD1, joinAt, h₁, h₂, h₂.le, lt_of_not_ge h₁]
  by_cases he : r = 2
  · subst r; norm_num [plateauD1, joinAt]
  · have hn : ¬r ≤ 2 := by grind
    simp [plateauD1, joinAt, h₁, h₂, hn]

/-- The second jet is the nested join of the second polynomial jet with zeros. -/
private theorem plateauD2_eq_join : plateauD2 =
    joinAt 1 (fun _ => 0) (joinAt 2 (fun r =>
      -60 * (r - 1) + 180 * (r - 1) ^ 2 - 120 * (r - 1) ^ 3) (fun _ => 0)) := by
  funext r
  by_cases h₁ : r ≤ 1
  · simp [plateauD2, joinAt, h₁, not_lt_of_ge h₁]
  by_cases h₂ : r < 2
  · simp [plateauD2, joinAt, h₁, h₂, h₂.le, lt_of_not_ge h₁]
  by_cases he : r = 2
  · subst r; norm_num [plateauD2, joinAt]
  · have hn : ¬r ≤ 2 := by grind
    simp [plateauD2, joinAt, h₁, h₂, hn]

/-- At [every radius](hyp:r), [the plateau has the explicit first derivative](goal).

Use `joinAt 1 (fun _ => 1) (joinAt 2 Q (fun _ => 0))`, where Q is the
transition polynomial. Its value, first jet, and second jet at 2 are zero;
at 1 they are one, zero, zero. Equality at 2 is handled by Q(2)=0 rather
than changing the public formula's strict upper test.
@isnad1 id=hasderiv.0h1v.s5.1512e43a8d8c from=translated src=- shape=475e04ea vocab=15590f8c
-/
theorem plateau_hasDerivAt (r : ℝ) : HasDerivAt plateau (plateauD1 r) r := by
  rw [plateau_eq_join, plateauD1_eq_join]
  have hi := joinAt_hasDerivAt 2 plateau_polynomial_hasDerivAt
    (fun x => hasDerivAt_const x (0 : ℝ)) (by norm_num) (by norm_num)
  exact joinAt_hasDerivAt 1 (fun x => hasDerivAt_const x (1 : ℝ)) hi
    (by norm_num [joinAt]) (by norm_num [joinAt]) r

/-- At [every radius](hyp:r), [the first jet has the explicit second derivative](goal).
@isnad1 id=hasderiv.0h1v.s5.a43296ab0128 from=translated src=- shape=475e04ea vocab=b4827e8c
-/
theorem plateauD1_hasDerivAt (r : ℝ) : HasDerivAt plateauD1 (plateauD2 r) r := by
  rw [plateauD1_eq_join, plateauD2_eq_join]
  have hi := joinAt_hasDerivAt 2 plateau_polynomialD1_hasDerivAt
    (fun x => hasDerivAt_const x (0 : ℝ)) (by norm_num) (by norm_num)
  exact joinAt_hasDerivAt 1 (fun x => hasDerivAt_const x (0 : ℝ)) hi
    (by norm_num [joinAt]) (by norm_num [joinAt]) r

/-- [The exact quintic plateau is globally twice continuously differentiable](goal).
@isnad1 id=contdiff.0h0v.s5.95ef7096743b from=translated src=- shape=23a74193 vocab=2fa78b98
-/
theorem plateau_contDiff : ContDiff ℝ 2 plateau := by
  have he₁ : deriv plateau = plateauD1 :=
    funext fun r => (plateau_hasDerivAt r).deriv
  have he₂ : deriv plateauD1 = plateauD2 :=
    funext fun r => (plateauD1_hasDerivAt r).deriv
  apply (contDiff_succ_iff_deriv (n := 1)).2
  refine ⟨fun r => (plateau_hasDerivAt r).differentiableAt, by simp, ?_⟩
  rw [he₁]
  apply contDiff_one_iff_deriv.2
  refine ⟨fun r => (plateauD1_hasDerivAt r).differentiableAt, ?_⟩
  rw [he₂, plateauD2_eq_join]
  apply joinAt_continuous 1 continuous_const
  · apply joinAt_continuous 2
    · fun_prop
    · exact continuous_const
    · norm_num
  · norm_num [joinAt]

/-- [The ordinary derivative of the plateau is its explicit first jet](goal).
@isnad1 id=eq.0h0v.s5.d714d75aa311 from=translated src=- shape=1142214a vocab=c50057ff
-/
theorem plateau_deriv : deriv plateau = plateauD1 := by
  funext r
  exact (plateau_hasDerivAt r).deriv

/-- [The second ordinary derivative of the plateau is its explicit second jet](goal).
@isnad1 id=eq.0h0v.s5.eb95a17b12d1 from=translated src=- shape=d9d6a2dc vocab=c4c3ed82
-/
theorem plateau_deriv_two : deriv (deriv plateau) = plateauD2 := by
  rw [plateau_deriv]
  funext r
  exact (plateauD1_hasDerivAt r).deriv

/-- At [a radius in the transition region](hyp:r,hr),
[the first derivative has the exact quintic derivative formula](goal).
@isnad1 id=eq.1h1v.s7.53634229b374 from=translated src=- shape=e3763b09 vocab=28b829bd
-/
theorem plateau_deriv_of_transition (r : ℝ) (hr : 1 < r ∧ r < 2) :
    deriv plateau r = -30 * (r - 1) ^ 2 + 60 * (r - 1) ^ 3 - 30 * (r - 1) ^ 4 := by
  simp [plateau_deriv, plateauD1, hr]

/-- At [a radius in the transition region](hyp:r,hr),
[the second derivative has the exact quintic second derivative formula](goal).
@isnad1 id=eq.1h1v.s7.85b605f802f6 from=translated src=- shape=b4272131 vocab=28b829bd
-/
theorem plateau_second_deriv_of_transition (r : ℝ) (hr : 1 < r ∧ r < 2) :
    deriv (deriv plateau) r = -60 * (r - 1) + 180 * (r - 1) ^ 2 - 120 * (r - 1) ^ 3 := by
  simp [plateau_deriv_two, plateauD2, hr]

/-- At [a radius](hyp:r) [outside the open transition region](hyp:hr),
[both derivative jets vanish](goal), including radii one and two.
@isnad1 id=and.1h1v.s7.e269d961e49d from=translated src=- shape=cc9c0117 vocab=11231d7f
-/
theorem plateau_jets_zero (r : ℝ) (hr : r ≤ 1 ∨ 2 ≤ r) :
    deriv plateau r = 0 ∧ deriv (deriv plateau) r = 0 := by
  have hn : ¬(1 < r ∧ r < 2) := by
    intro h
    rcases hr with hr | hr <;> linarith [h.1, h.2]
  rw [plateau_deriv_two, plateau_deriv]
  simp [plateauD1, plateauD2, hn]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
