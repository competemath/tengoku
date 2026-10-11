module
public import Tengoku

/-!
# Uniform C1 stability of positive log-ratio derivatives

This module defines explicit uniform `C¹` and `C²` control on a set.  It proves continuity of
reciprocal, quotient, logarithm, and the within-derivative of a positive log ratio under uniform
`C¹` convergence, then packages openness of a strict fixed-sign derivative margin on a compact
real interval.
-/

@[expose] public section

open Set Filter

noncomputable section

namespace Causalean.Mathlib.Analysis

/-- [Uniform convergence on a set](goal) requires every positive error tolerance eventually to
control [the whole function sequence](hyp:f) relative to [its limiting function](hyp:g) at every
point of [that set](hyp:K).

This sequence-specific predicate is retained for compatibility; new developments should use
Mathlib's filter-general `TendstoUniformlyOn`. -/
@[deprecated TendstoUniformlyOn (since := "2026-09-19")]
def UniformlyOn {α : Type*} (K : Set α) (f : ℕ → α → ℝ) (g : α → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x ∈ K, |f n x - g x| < ε

/-- Two real functions are uniformly `C¹`-close on a set when both values and first
within-derivatives differ by less than the same radius everywhere on the set. -/
def C1CloseOn (K : Set ℝ) (ε : ℝ) (f g : ℝ → ℝ) : Prop :=
  (∀ x ∈ K, |f x - g x| < ε) ∧
    ∀ x ∈ K, |derivWithin f K x - derivWithin g K x| < ε

/-- Two real functions are uniformly `C²`-close when they are uniformly `C¹`-close and their
second within-derivatives differ by less than the same radius. -/
def C2CloseOn (K : Set ℝ) (ε : ℝ) (f g : ℝ → ℝ) : Prop :=
  C1CloseOn K ε f g ∧
    ∀ x ∈ K,
      |derivWithin (fun y ↦ derivWithin f K y) K x -
        derivWithin (fun y ↦ derivWithin g K y) K x| < ε

/-- The log ratio of `q` to `p` is the pointwise function `x ↦ log (q x / p x)`. -/
def logRatio (q p : ℝ → ℝ) (x : ℝ) : ℝ := Real.log (q x / p x)

/-- On a nondegenerate compact interval, the within-derivative of a positive log ratio is the
difference of the two logarithmic derivatives. -/
theorem derivWithin_logRatio {a b : ℝ} (hab : a < b)
    {q p : ℝ → ℝ} (hq : DifferentiableOn ℝ q (Icc a b))
    (hp : DifferentiableOn ℝ p (Icc a b))
    (hqpos : ∀ x ∈ Icc a b, 0 < q x) (hppos : ∀ x ∈ Icc a b, 0 < p x)
    {x : ℝ} (hx : x ∈ Icc a b) :
    derivWithin (logRatio q p) (Icc a b) x =
      derivWithin q (Icc a b) x / q x - derivWithin p (Icc a b) x / p x := by
  have hq_at := hq x hx
  have hp_at := hp x hx
  have hqne : q x ≠ 0 := (hqpos x hx).ne'
  have hpne : p x ≠ 0 := (hppos x hx).ne'
  have hunique := (uniqueDiffOn_Icc hab).uniqueDiffWithinAt hx
  have hdiv : DifferentiableWithinAt ℝ (fun y ↦ q y / p y) (Icc a b) x :=
    hq_at.div hp_at hpne
  have hdiv_deriv := derivWithin_div hq_at hp_at hpne
  change derivWithin (fun y ↦ q y / p y) (Icc a b) x = _ at hdiv_deriv
  change derivWithin (fun y ↦ Real.log (q y / p y)) (Icc a b) x = _
  rw [derivWithin.log hdiv (div_ne_zero hqne hpne) hunique]
  rw [hdiv_deriv]
  field_simp

private theorem abs_div_sub_div_lt {m B ε u u' du du' : ℝ}
    (hm : 0 < m) (hB : 0 < B) (hε : 0 < ε) (hεm : ε ≤ m / 2)
    (hu : m ≤ u) (huB : |u| ≤ B) (hduB : |du| ≤ B)
    (huclose : |u' - u| < ε) (hduclose : |du' - du| < ε) :
    |du' / u' - du / u| < (2 * B * ε) / (m ^ 2 / 2) := by
  have hupos : 0 < u := hm.trans_le hu
  have hu'pos : 0 < u' := by
    have := (neg_lt_of_abs_lt huclose)
    nlinarith
  have hden : m ^ 2 / 2 ≤ u' * u := by
    have hu'lower : m / 2 < u' := by
      have := neg_lt_of_abs_lt huclose
      nlinarith
    nlinarith [mul_pos (sub_pos.mpr hu'lower) hupos]
  have hfirst : |du' - du| * |u| < ε * B := by
    calc
      _ < ε * |u| := mul_lt_mul_of_pos_right hduclose (abs_pos.mpr hupos.ne')
      _ ≤ ε * B := mul_le_mul_of_nonneg_left huB hε.le
  have hsecond : |du| * |u - u'| < B * ε := by
    calc
      _ ≤ B * |u - u'| := mul_le_mul_of_nonneg_right hduB (abs_nonneg _)
      _ < B * ε := mul_lt_mul_of_pos_left (by simpa [abs_sub_comm] using huclose) hB
  have hnum : |(du' - du) * u + du * (u - u')| < 2 * B * ε := by
    calc
      _ ≤ |du' - du| * |u| + |du| * |u - u'| := by
        simpa only [abs_mul] using abs_add_le ((du' - du) * u) (du * (u - u'))
      _ < ε * B + B * ε := add_lt_add hfirst hsecond
      _ = 2 * B * ε := by ring
  rw [show du' / u' - du / u = ((du' - du) * u + du * (u - u')) / (u' * u) by
    field_simp [hu'pos.ne', hupos.ne'] <;> ring]
  rw [abs_div, abs_of_pos (mul_pos hu'pos hupos)]
  exact div_lt_div₀ hnum hden (by positivity) (by positivity)

/-- A [nondegenerate compact interval and positive lower and derivative margins](hyp:a,b,m,margin,hab,hm,hmargin),
[two continuously differentiable center functions](hyp:q,p,hq,hp), [their shared lower bounds](hyp:hqlower,hplower),
[a chosen orientation](hyp:sign,hsign), and [a derivative margin in that orientation](hyp:hfixed)
ensure [a positive uniform C¹ neighborhood in which both perturbed functions stay positive and
their log-ratio derivative retains that orientation](goal). -/
theorem logRatioDerivative_fixedSign_open_C1 {a b m margin : ℝ}
    (hab : a < b) (hm : 0 < m) (hmargin : 0 < margin)
    {q p : ℝ → ℝ} (hq : ContDiffOn ℝ 1 q (Icc a b))
    (hp : ContDiffOn ℝ 1 p (Icc a b))
    (hqlower : ∀ x ∈ Icc a b, m ≤ q x)
    (hplower : ∀ x ∈ Icc a b, m ≤ p x)
    (sign : ℝ) (hsign : sign = 1 ∨ sign = -1)
    (hfixed : ∀ x ∈ Icc a b,
      margin ≤ sign * derivWithin (logRatio q p) (Icc a b) x) :
    ∃ ε > 0, ∀ q' p' : ℝ → ℝ,
      DifferentiableOn ℝ q' (Icc a b) →
      DifferentiableOn ℝ p' (Icc a b) →
      C1CloseOn (Icc a b) ε q' q → C1CloseOn (Icc a b) ε p' p →
      (∀ x ∈ Icc a b, 0 < q' x ∧ 0 < p' x ∧
        0 < sign * derivWithin (logRatio q' p') (Icc a b) x) := by
  have hunique := uniqueDiffOn_Icc hab
  have hqderiv_cont : ContinuousOn (fun x ↦ derivWithin q (Icc a b) x) (Icc a b) :=
    hq.continuousOn_derivWithin hunique (by norm_num)
  have hpderiv_cont : ContinuousOn (fun x ↦ derivWithin p (Icc a b) x) (Icc a b) :=
    hp.continuousOn_derivWithin hunique (by norm_num)
  obtain ⟨Cq, hCq⟩ := isCompact_Icc.exists_bound_of_continuousOn hq.continuousOn
  obtain ⟨Cp, hCp⟩ := isCompact_Icc.exists_bound_of_continuousOn hp.continuousOn
  obtain ⟨Dq, hDq⟩ := isCompact_Icc.exists_bound_of_continuousOn hqderiv_cont
  obtain ⟨Dp, hDp⟩ := isCompact_Icc.exists_bound_of_continuousOn hpderiv_cont
  let B := |Cq| + |Cp| + |Dq| + |Dp| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hqB : ∀ x ∈ Icc a b, |q x| ≤ B := by
    intro x hx
    calc
      |q x| ≤ Cq := hCq x hx
      _ ≤ |Cq| := le_abs_self Cq
      _ ≤ B := by
        dsimp [B]
        linarith [abs_nonneg Cp, abs_nonneg Dq, abs_nonneg Dp]
  have hpB : ∀ x ∈ Icc a b, |p x| ≤ B := by
    intro x hx
    calc
      |p x| ≤ Cp := hCp x hx
      _ ≤ |Cp| := le_abs_self Cp
      _ ≤ B := by
        dsimp [B]
        linarith [abs_nonneg Cq, abs_nonneg Dq, abs_nonneg Dp]
  have hDqB : ∀ x ∈ Icc a b, |derivWithin q (Icc a b) x| ≤ B := by
    intro x hx
    calc
      |derivWithin q (Icc a b) x| ≤ Dq := hDq x hx
      _ ≤ |Dq| := le_abs_self Dq
      _ ≤ B := by
        dsimp [B]
        linarith [abs_nonneg Cq, abs_nonneg Cp, abs_nonneg Dp]
  have hDpB : ∀ x ∈ Icc a b, |derivWithin p (Icc a b) x| ≤ B := by
    intro x hx
    calc
      |derivWithin p (Icc a b) x| ≤ Dp := hDp x hx
      _ ≤ |Dp| := le_abs_self Dp
      _ ≤ B := by
        dsimp [B]
        linarith [abs_nonneg Cq, abs_nonneg Cp, abs_nonneg Dq]
  let L := (2 * B) / (m ^ 2 / 2)
  have hL : 0 < L := by dsimp [L]; positivity
  let ε := min (m / 2) (margin / (4 * L))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεm : ε ≤ m / 2 := min_le_left _ _
  have hεmargin : 2 * L * ε ≤ margin / 2 := by
    have hεL : ε ≤ margin / (4 * L) := min_le_right _ _
    have hL4 : 0 < 4 * L := by positivity
    calc
      2 * L * ε ≤ 2 * L * (margin / (4 * L)) := by gcongr
      _ = margin / 2 := by field_simp; ring
  refine ⟨ε, hε, ?_⟩
  intro q' p' hq'diff hp'diff hqclose hpclose x hx
  have hqpos : 0 < q x := hm.trans_le (hqlower x hx)
  have hppos : 0 < p x := hm.trans_le (hplower x hx)
  have hq'pos : 0 < q' x := by
    have hneg := neg_lt_of_abs_lt (hqclose.1 x hx)
    linarith [hqlower x hx, hεm, hm]
  have hp'pos : 0 < p' x := by
    have hneg := neg_lt_of_abs_lt (hpclose.1 x hx)
    linarith [hplower x hx, hεm, hm]
  refine ⟨hq'pos, hp'pos, ?_⟩
  have hqfrac := abs_div_sub_div_lt hm hB hε hεm (hqlower x hx) (hqB x hx)
    (hDqB x hx) (hqclose.1 x hx) (hqclose.2 x hx)
  have hpfrac := abs_div_sub_div_lt hm hB hε hεm (hplower x hx) (hpB x hx)
    (hDpB x hx) (hpclose.1 x hx) (hpclose.2 x hx)
  have hqfrac' :
      |derivWithin q' (Icc a b) x / q' x - derivWithin q (Icc a b) x / q x| < L * ε := by
    convert hqfrac using 1 <;> dsimp [L] <;> ring
  have hpfrac' :
      |derivWithin p' (Icc a b) x / p' x - derivWithin p (Icc a b) x / p x| < L * ε := by
    convert hpfrac using 1 <;> dsimp [L] <;> ring
  have hderivdiff :
      |derivWithin (logRatio q' p') (Icc a b) x -
        derivWithin (logRatio q p) (Icc a b) x| < 2 * L * ε := by
    rw [derivWithin_logRatio hab hq'diff hp'diff (fun y hy ↦ by
        have hneg := neg_lt_of_abs_lt (hqclose.1 y hy)
        nlinarith [hqlower y hy]) (fun y hy ↦ by
        have hneg := neg_lt_of_abs_lt (hpclose.1 y hy)
        nlinarith [hplower y hy]) hx,
      derivWithin_logRatio hab (hq.differentiableOn (by norm_num))
        (hp.differentiableOn (by norm_num))
        (fun y hy ↦ hm.trans_le (hqlower y hy))
        (fun y hy ↦ hm.trans_le (hplower y hy)) hx]
    calc
      |(derivWithin q' (Icc a b) x / q' x - derivWithin p' (Icc a b) x / p' x) -
          (derivWithin q (Icc a b) x / q x - derivWithin p (Icc a b) x / p x)| =
          |(derivWithin q' (Icc a b) x / q' x - derivWithin q (Icc a b) x / q x) -
            (derivWithin p' (Icc a b) x / p' x - derivWithin p (Icc a b) x / p x)| := by
            congr 1 <;> ring
      _ ≤ |derivWithin q' (Icc a b) x / q' x - derivWithin q (Icc a b) x / q x| +
          |derivWithin p' (Icc a b) x / p' x - derivWithin p (Icc a b) x / p x| := by
            simpa only [sub_eq_add_neg, Real.norm_eq_abs, norm_neg] using
              norm_add_le
                (derivWithin q' (Icc a b) x / q' x - derivWithin q (Icc a b) x / q x)
                (-(derivWithin p' (Icc a b) x / p' x - derivWithin p (Icc a b) x / p x))
      _ < L * ε + L * ε := add_lt_add hqfrac' hpfrac'
      _ = 2 * L * ε := by ring
  have hsignabs : |sign| = 1 := by rcases hsign with rfl | rfl <;> norm_num
  have hsignedDiff :
      |sign * derivWithin (logRatio q' p') (Icc a b) x -
        sign * derivWithin (logRatio q p) (Icc a b) x| < margin / 2 := by
    rw [← mul_sub, abs_mul, hsignabs, one_mul]
    exact hderivdiff.trans_le hεmargin
  have hlowerSigned := hfixed x hx
  have hneg := neg_lt_of_abs_lt hsignedDiff
  nlinarith

/-- The same strict fixed-sign derivative property is open under uniform `C²` perturbations,
because uniform `C²` control includes the required uniform `C¹` control. -/
theorem logRatioDerivative_fixedSign_open_C2 {a b m margin : ℝ}
    (hab : a < b) (hm : 0 < m) (hmargin : 0 < margin)
    {q p : ℝ → ℝ} (hq : ContDiffOn ℝ 1 q (Icc a b))
    (hp : ContDiffOn ℝ 1 p (Icc a b))
    (hqlower : ∀ x ∈ Icc a b, m ≤ q x)
    (hplower : ∀ x ∈ Icc a b, m ≤ p x)
    (sign : ℝ) (hsign : sign = 1 ∨ sign = -1)
    (hfixed : ∀ x ∈ Icc a b,
      margin ≤ sign * derivWithin (logRatio q p) (Icc a b) x) :
    ∃ ε > 0, ∀ q' p' : ℝ → ℝ,
      DifferentiableOn ℝ q' (Icc a b) →
      DifferentiableOn ℝ p' (Icc a b) →
      C2CloseOn (Icc a b) ε q' q → C2CloseOn (Icc a b) ε p' p →
      (∀ x ∈ Icc a b, 0 < q' x ∧ 0 < p' x ∧
        0 < sign * derivWithin (logRatio q' p') (Icc a b) x) := by
  obtain ⟨ε, hε, hopen⟩ := logRatioDerivative_fixedSign_open_C1 hab hm hmargin hq hp
    hqlower hplower sign hsign hfixed
  refine ⟨ε, hε, ?_⟩
  intro q' p' hq'diff hp'diff hqclose hpclose
  exact hopen q' p' hq'diff hp'diff hqclose.1 hpclose.1

end Causalean.Mathlib.Analysis
