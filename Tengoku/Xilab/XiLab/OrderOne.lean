import Tengoku
import Tengoku.Xilab.XiLab.HolomorphicLog

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms eq_exp_affine_of_order_le_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_poly_mul_exp_of_finite_zeros` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_zero_of_not_eq_exp_affine` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# XiLab.OrderOne

Hadamard factorization at order `≤ 1`, nonvanishing case.

The main result is `XiLab.eq_exp_affine_of_order_le_one`: an entire function of order at
most one with no zeros is `exp` of an affine function.

## Route

1. `f` entire and nowhere zero admits an entire logarithm `g` with `f = exp ∘ g`.
   *This is `XiLab.exists_entire_log`, owned by `XiLab/HolomorphicLog.lean`.*
2. `‖f z‖ ≤ A * exp (B * ‖z‖)` and `‖exp (g z)‖ = exp (Re (g z))` give
   `Re (g z) ≤ log A + B * ‖z‖`: `Re g` has at most linear growth.
3. `Complex.borelCaratheodory` upgrades a one-sided bound on `Re g` over `ball 0 R` to a
   two-sided bound on `‖g‖` over a smaller ball. Taking `R = 2‖z‖ + 2` gives a *global*
   linear bound `‖g z‖ ≤ a + b * ‖z‖`.
4. Cauchy's estimate `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` on the circle of
   radius `R` about `w` gives `‖deriv g w‖ ≤ (a + b * (‖w‖ + R)) / R`, and letting `R → ∞`
   gives `‖deriv g w‖ ≤ b` uniformly in `w`. So `deriv g` is a bounded entire function,
   Liouville makes it constant, and `g` is affine.

Step 4 is done on the *first* derivative rather than on `g''`: bounding `‖g'‖` needs only
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` (which does not even require
completeness of the codomain), and the resulting bound `b` is already uniform in `w`, so
Liouville applies directly. The `g'' ≡ 0` route would need
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` plus a separate argument that
a function with vanishing second derivative is affine; the first-derivative route reuses
`Differentiable.exists_const_forall_eq_of_bounded` and `is_const_of_deriv_eq_zero`, both of
which are directly available.
-/

namespace XiLab

open Metric Set Bornology

/-! ## Cross-file dependency

`XiLab.exists_entire_log` — a nowhere-vanishing entire function is `exp` of an entire
function — is owned by `XiLab/HolomorphicLog.lean` and is imported above. It was developed
concurrently with this file; while it was unavailable it stood here as a `sorry`-ed
FRONTIER with exactly this signature:

```
theorem exists_entire_log {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnz : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z)
```

That frontier is now discharged by the real import, so this file contains no `sorry`.
-/

/-! ## From a linear bound on `Re g` to a linear bound on `‖g‖` -/

/-- **Borel–Carathéodory, global form.** If `g` is entire and `Re (g z) ≤ L + B * ‖z‖`
with `B ≥ 0`, then `‖g‖` itself grows at most linearly.

Applying `Complex.borelCaratheodory` on `ball 0 (2‖z‖ + 2)` at the point `z`, where the
majorant of `Re g` on that ball is `M = |L| + B * (2‖z‖+2) + 1`, gives
`‖g z‖ ≤ 2M + 3‖g 0‖`, which is exactly the stated affine function of `‖z‖`.-/
theorem norm_le_linear_of_re_le_linear {g : ℂ → ℂ} (hg : Differentiable ℂ g) {L B : ℝ}
    (hB : 0 ≤ B) (hre : ∀ z, (g z).re ≤ L + B * ‖z‖) (z : ℂ) :
    ‖g z‖ ≤ (2 * |L| + 4 * B + 2 + 3 * ‖g 0‖) + 4 * B * ‖z‖ := by
  have ht : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hL : (0 : ℝ) ≤ |L| := abs_nonneg L
  have h0 : (0 : ℝ) ≤ ‖g 0‖ := norm_nonneg _
  have hR : (0 : ℝ) < 2 * ‖z‖ + 2 := by linarith
  have hM : (0 : ℝ) < |L| + B * (2 * ‖z‖ + 2) + 1 := by
    have : 0 ≤ B * (2 * ‖z‖ + 2) := mul_nonneg hB hR.le
    linarith
  have hmaps : Set.MapsTo g (ball 0 (2 * ‖z‖ + 2))
      {w : ℂ | w.re ≤ |L| + B * (2 * ‖z‖ + 2) + 1} := by
    intro x hx
    have hx' : ‖x‖ < 2 * ‖z‖ + 2 := mem_ball_zero_iff.mp hx
    have h1 : (g x).re ≤ L + B * ‖x‖ := hre x
    have h2 : B * ‖x‖ ≤ B * (2 * ‖z‖ + 2) :=
      mul_le_mul_of_nonneg_left hx'.le hB
    have h3 : L ≤ |L| := le_abs_self L
    simp only [Set.mem_ofPred_eq]
    linarith
  have hz : z ∈ ball (0 : ℂ) (2 * ‖z‖ + 2) := by
    rw [mem_ball_zero_iff]; linarith
  have hbc := Complex.borelCaratheodory hM hg.differentiableOn hmaps hR hz
  have hden : (0 : ℝ) < 2 * ‖z‖ + 2 - ‖z‖ := by linarith
  refine hbc.trans ?_
  rw [← add_div, div_le_iff₀ hden]
  nlinarith [mul_nonneg hB ht, mul_nonneg h0 ht, mul_nonneg hL ht]

/-! ## From a linear bound on `‖g‖` to a bounded derivative -/

/-- **Cauchy estimate, letting the radius run to infinity.** If `g` is entire with
`‖g z‖ ≤ a + b * ‖z‖` then `‖deriv g w‖ ≤ b` for every `w` — the slope of the bound, with
no dependence on `w` at all.-/
theorem norm_deriv_le_of_linear_growth {g : ℂ → ℂ} (hg : Differentiable ℂ g) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hgrow : ∀ z, ‖g z‖ ≤ a + b * ‖z‖) (w : ℂ) :
    ‖deriv g w‖ ≤ b := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  set ε : ℝ := c - b with hε_def
  have hε : 0 < ε := by simp only [hε_def]; linarith
  have hnum : (0 : ℝ) ≤ a + b * ‖w‖ := add_nonneg ha (mul_nonneg hb (norm_nonneg w))
  set R : ℝ := (a + b * ‖w‖) / ε + 1 with hR_def
  have hR : 0 < R := by
    have : (0 : ℝ) ≤ (a + b * ‖w‖) / ε := div_nonneg hnum hε.le
    simp only [hR_def]; linarith
  have hC : ∀ x ∈ sphere w R, ‖g x‖ ≤ a + b * (‖w‖ + R) := by
    intro x hx
    have hxw : ‖x - w‖ = R := mem_sphere_iff_norm.1 hx
    have hxn : ‖x‖ ≤ ‖w‖ + R := by
      have := norm_add_le (x - w) w
      rw [hxw] at this
      simpa [sub_add_cancel] using this.trans_eq (by ring)
    calc ‖g x‖ ≤ a + b * ‖x‖ := hgrow x
      _ ≤ a + b * (‖w‖ + R) := by gcongr
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hg.diffContOnCl hC
  refine hd.trans ?_
  rw [div_le_iff₀ hR]
  have hkey : ε * R = (a + b * ‖w‖) + ε := by
    simp only [hR_def]
    field_simp
  have hcε : c = b + ε := by simp only [hε_def]; ring
  rw [hcε]
  nlinarith [hkey]

/-! ## Liouville: linear growth forces affine -/

/-- An entire function with at most linear growth is affine.-/
theorem eq_affine_of_linear_growth {g : ℂ → ℂ} (hg : Differentiable ℂ g) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hgrow : ∀ z, ‖g z‖ ≤ a + b * ‖z‖) :
    ∃ c : ℂ, ∀ z, g z = c * z + g 0 := by
  have hdd : Differentiable ℂ (deriv g) := hg.deriv
  have hbdd : IsBounded (Set.range (deriv g)) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨b, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact norm_deriv_le_of_linear_growth hg ha hb hgrow w
  obtain ⟨c, hc⟩ := hdd.exists_const_forall_eq_of_bounded hbdd
  refine ⟨c, fun z => ?_⟩
  have hdiff : Differentiable ℂ fun t : ℂ => g t - c * t := by fun_prop
  have hzero : ∀ x : ℂ, deriv (fun t : ℂ => g t - c * t) x = 0 := by
    intro x
    have h1 : HasDerivAt g (deriv g x) x := (hg x).hasDerivAt
    have h2 : HasDerivAt (fun t : ℂ => c * t) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have h3 : HasDerivAt (fun t : ℂ => g t - c * t) (deriv g x - c) x := h1.sub h2
    rw [h3.deriv, hc x]
    ring
  have h := is_const_of_deriv_eq_zero hdiff hzero z 0
  simp only [mul_zero, sub_zero] at h
  linear_combination h

/-! ## Main theorem -/

/-- An entire function of order at most one with no zeros is `exp` of an affine function.-/
theorem eq_exp_affine_of_order_le_one {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnz : ∀ z, f z ≠ 0) {A B : ℝ} (hA : 0 < A)
    (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖)) :
    ∃ a b : ℂ, ∀ z, f z = Complex.exp (a * z + b) := by
  obtain ⟨g, hg, hfg⟩ := exists_entire_log hf hnz
  -- Replace `B` by `max B 0`, so that the exponent slope is nonnegative.
  set B' : ℝ := max B 0 with hB'_def
  have hB' : 0 ≤ B' := le_max_right _ _
  have hgrowth' : ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B' * ‖z‖) := by
    intro z
    refine (hgrowth z).trans ?_
    have hmul : B * ‖z‖ ≤ B' * ‖z‖ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg z)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmul) hA.le
  -- `Re g` grows at most linearly.
  have hre : ∀ z : ℂ, (g z).re ≤ Real.log A + B' * ‖z‖ := by
    intro z
    have h1 : Real.exp ((g z).re) ≤ A * Real.exp (B' * ‖z‖) := by
      have h := hgrowth' z
      rwa [hfg z, Complex.norm_exp] at h
    have h2 : A * Real.exp (B' * ‖z‖) = Real.exp (Real.log A + B' * ‖z‖) := by
      rw [Real.exp_add, Real.exp_log hA]
    rw [h2] at h1
    exact Real.exp_le_exp.mp h1
  -- Borel–Carathéodory: `‖g‖` grows at most linearly.
  have hlin : ∀ z : ℂ, ‖g z‖ ≤
      (2 * |Real.log A| + 4 * B' + 2 + 3 * ‖g 0‖) + 4 * B' * ‖z‖ :=
    fun z => norm_le_linear_of_re_le_linear hg hB' hre z
  have ha : (0 : ℝ) ≤ 2 * |Real.log A| + 4 * B' + 2 + 3 * ‖g 0‖ := by
    have := abs_nonneg (Real.log A)
    have := norm_nonneg (g 0)
    linarith
  have hb : (0 : ℝ) ≤ 4 * B' := by linarith
  -- Cauchy estimate + Liouville: `g` is affine.
  obtain ⟨c, hc⟩ := eq_affine_of_linear_growth hg ha hb hlin
  exact ⟨c, g 0, fun z => by rw [hfg z, hc z]⟩

/-! ## Dividing out a zero, preserving the order-one growth bound -/

/-- **The division step.** If `f` is entire with `‖f z‖ ≤ A * exp (B‖z‖)` (`B ≥ 0`) and
`f z₀ = 0`, then `f z = (z - z₀) * g z` for an entire `g` obeying a growth bound of the same
shape (same `B`, a possibly larger constant).

`g` is `dslope f z₀`; entirety is the removable-singularity theorem
`Complex.differentiableOn_dslope`, and the growth bound splits into `‖z - z₀‖ ≥ 1`, where
`‖g z‖ ≤ ‖f z‖`, and the compact disc `closedBall z₀ 1`, where `g` is bounded by
continuity.-/
theorem exists_entire_div_of_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A B : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖))
    {z₀ : ℂ} (hz₀ : f z₀ = 0) :
    ∃ (g : ℂ → ℂ) (A' : ℝ), Differentiable ℂ g ∧ 0 < A' ∧
      (∀ z : ℂ, ‖g z‖ ≤ A' * Real.exp (B * ‖z‖)) ∧ (∀ z, f z = (z - z₀) * g z) := by
  have hgd : Differentiable ℂ (dslope f z₀) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (by simp)).mpr (differentiableOn_univ.mpr hf)
  have hfac : ∀ z, f z = (z - z₀) * dslope f z₀ z := by
    intro z
    have h := sub_smul_dslope f z₀ z
    rw [hz₀, sub_zero, smul_eq_mul] at h
    exact h.symm
  obtain ⟨C, hC⟩ := (isCompact_closedBall z₀ 1).exists_bound_of_continuousOn
    hgd.continuous.continuousOn
  refine ⟨dslope f z₀, max A (max C 1), hgd, lt_max_of_lt_left hA, fun z => ?_, hfac⟩
  have hexp : (1 : ℝ) ≤ Real.exp (B * ‖z‖) :=
    Real.one_le_exp (mul_nonneg hB (norm_nonneg z))
  have hAle : A ≤ max A (max C 1) := le_max_left _ _
  have hCle : C ≤ max A (max C 1) := (le_max_left C 1).trans (le_max_right _ _)
  have hpos : (0 : ℝ) < max A (max C 1) := lt_max_of_lt_left hA
  rcases le_or_gt 1 ‖z - z₀‖ with h | h
  · have hnorm : ‖z - z₀‖ * ‖dslope f z₀ z‖ = ‖f z‖ := by
      rw [hfac z, norm_mul]
    have hle : ‖dslope f z₀ z‖ ≤ ‖f z‖ := by
      nlinarith [norm_nonneg (dslope f z₀ z)]
    calc ‖dslope f z₀ z‖ ≤ ‖f z‖ := hle
      _ ≤ A * Real.exp (B * ‖z‖) := hgrowth z
      _ ≤ max A (max C 1) * Real.exp (B * ‖z‖) := by gcongr
  · have hmem : z ∈ Metric.closedBall z₀ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact h.le
    calc ‖dslope f z₀ z‖ ≤ C := hC z hmem
      _ ≤ max A (max C 1) := hCle
      _ = max A (max C 1) * 1 := (mul_one _).symm
      _ ≤ max A (max C 1) * Real.exp (B * ‖z‖) := by gcongr

/-! ## Stripping a zero to its full multiplicity -/

/-- Iterating the division step: if the vanishing order of `f` at `z₀` is at most `m`, then
`f z = (z - z₀) ^ j * g z` globally for some `j` and some entire `g` with `g z₀ ≠ 0`, still
of order at most one with the same exponential rate `B`.

The induction is on `m`; the vanishing order drops by exactly one at each division because
`analyticOrderAt (· - z₀) z₀ = 1` and the order is additive on products.-/
theorem exists_pow_mul_of_order_le {B : ℝ} (hB : 0 ≤ B) (z₀ : ℂ) :
    ∀ (m : ℕ) (f : ℂ → ℂ) (A : ℝ), Differentiable ℂ f → 0 < A →
      (∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖)) →
      analyticOrderAt f z₀ ≤ (m : ℕ∞) →
      ∃ (j : ℕ) (g : ℂ → ℂ) (A' : ℝ), Differentiable ℂ g ∧ 0 < A' ∧
        (∀ z : ℂ, ‖g z‖ ≤ A' * Real.exp (B * ‖z‖)) ∧ g z₀ ≠ 0 ∧
        (∀ z, f z = (z - z₀) ^ j * g z) := by
  intro m
  induction m with
  | zero =>
    intro f A hf hA hgrow hord
    have h0 : analyticOrderAt f z₀ = 0 := le_antisymm (by simpa using hord) (by simp)
    exact ⟨0, f, A, hf, hA, hgrow, (hf.analyticAt z₀).analyticOrderAt_eq_zero.mp h0, by simp⟩
  | succ m ih =>
    intro f A hf hA hgrow hord
    by_cases hz₀ : f z₀ = 0
    · obtain ⟨h, A', hh, hA', hhgrow, hfac⟩ := exists_entire_div_of_zero hf hA hB hgrow hz₀
      have hprod : f = (fun z : ℂ => z - z₀) * h := funext fun z => by simpa using hfac z
      have hmono : analyticOrderAt (fun z : ℂ => z - z₀) z₀ = 1 := by
        simpa using analyticOrderAt_centeredMonomial (𝕜 := ℂ) (z₀ := z₀) (n := 1)
      have hsum : analyticOrderAt f z₀ = 1 + analyticOrderAt h z₀ := by
        rw [hprod, analyticOrderAt_mul (by fun_prop) (hh.analyticAt z₀), hmono]
      have hordh : analyticOrderAt h z₀ ≤ (m : ℕ∞) := by
        refine (ENat.add_le_add_iff_left (k := 1) (by simp)).mp ?_
        rw [← hsum]
        refine hord.trans (le_of_eq ?_)
        push_cast
        ring
      obtain ⟨j, g, A'', hg, hA'', hggrow, hgz, hgfac⟩ := ih h A' hh hA' hhgrow hordh
      refine ⟨j + 1, g, A'', hg, hA'', hggrow, hgz, fun z => ?_⟩
      rw [hfac z, hgfac z]
      ring
    · exact ⟨0, f, A, hf, hA, hgrow, hz₀, by simp⟩

/-! ## Hadamard factorization at order `≤ 1`, finitely many zeros -/

/-- Induction on the number of distinct zeros.-/
theorem exists_poly_mul_exp_aux {B : ℝ} (hB : 0 ≤ B) :
    ∀ (k : ℕ) (f : ℂ → ℂ) (A : ℝ), Differentiable ℂ f → 0 < A →
      (∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖)) →
      {z : ℂ | f z = 0}.Finite → {z : ℂ | f z = 0}.ncard = k →
      ∃ (P : Polynomial ℂ) (a b : ℂ), ∀ z, f z = P.eval z * Complex.exp (a * z + b) := by
  intro k
  induction k with
  | zero =>
    intro f A hf hA hgrow hfin hcard
    have hempty : {z : ℂ | f z = 0} = ∅ := (Set.ncard_eq_zero hfin).mp hcard
    have hnz : ∀ z, f z ≠ 0 := by
      intro z hz
      have : z ∈ ({z : ℂ | f z = 0}) := hz
      rw [hempty] at this
      exact this
    obtain ⟨a, b, hab⟩ := eq_exp_affine_of_order_le_one hf hnz hA hgrow
    exact ⟨1, a, b, fun z => by rw [hab z]; simp⟩
  | succ k ih =>
    intro f A hf hA hgrow hfin hcard
    have hne : {z : ℂ | f z = 0}.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hc
      rw [hc] at hcard
      simp at hcard
    obtain ⟨z₀, hz₀⟩ := hne
    have hfne : ¬ (f = 0) := by
      rintro rfl
      have huniv : {z : ℂ | (0 : ℂ → ℂ) z = 0} = Set.univ := by ext; simp
      rw [huniv] at hfin
      exact Set.infinite_univ hfin
    have hordne : analyticOrderAt f z₀ ≠ ⊤ := by
      rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z₀ fun w => hf.analyticAt w]
      exact hfne
    have hle : analyticOrderAt f z₀ ≤ (((analyticOrderAt f z₀).toNat : ℕ) : ℕ∞) :=
      le_of_eq (ENat.natCast_toNat hordne).symm
    obtain ⟨j, g, A', hg, hA', hggrow, hgz, hgfac⟩ :=
      exists_pow_mul_of_order_le hB z₀ _ f A hf hA hgrow hle
    have hzero : {z : ℂ | g z = 0} = {z : ℂ | f z = 0} \ {z₀} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · intro hw
        refine ⟨by rw [hgfac w, hw, mul_zero], ?_⟩
        rintro rfl
        exact hgz hw
      · rintro ⟨hw, hnew⟩
        have hz := hgfac w
        rw [hw] at hz
        have hpow : (w - z₀) ^ j ≠ 0 := pow_ne_zero _ (sub_ne_zero_of_ne hnew)
        exact (mul_eq_zero.mp hz.symm).resolve_left hpow
    have hfin' : {z : ℂ | g z = 0}.Finite := by
      rw [hzero]; exact hfin.sdiff
    have hcard' : {z : ℂ | g z = 0}.ncard = k := by
      have h1 : ({z : ℂ | f z = 0} \ {z₀}).ncard + 1 = {z : ℂ | f z = 0}.ncard :=
        Set.ncard_sdiff_singleton_add_one hz₀ hfin
      rw [hcard] at h1
      rw [hzero]
      omega
    obtain ⟨Q, a, b, hQ⟩ := ih g A' hg hA' hggrow hfin' hcard'
    refine ⟨(Polynomial.X - Polynomial.C z₀) ^ j * Q, a, b, fun z => ?_⟩
    rw [hgfac z, hQ z]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    ring

/-- **Hadamard factorization at order `≤ 1`, finitely many zeros.** An entire function of
order at most one with only finitely many zeros equals `P(z) * exp (a * z + b)` for a
polynomial `P`.-/
theorem exists_poly_mul_exp_of_finite_zeros {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A B : ℝ}
    (hA : 0 < A) (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖))
    (hfin : {z : ℂ | f z = 0}.Finite) :
    ∃ (P : Polynomial ℂ) (a b : ℂ), ∀ z, f z = P.eval z * Complex.exp (a * z + b) := by
  have hB : (0 : ℝ) ≤ max B 0 := le_max_right _ _
  have hgrowth' : ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (max B 0 * ‖z‖) := by
    intro z
    refine (hgrowth z).trans ?_
    have hmul : B * ‖z‖ ≤ max B 0 * ‖z‖ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg z)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmul) hA.le
  exact exists_poly_mul_exp_aux hB _ f A hf hA hgrowth' hfin rfl

/-- Contrapositive form: an entire function of order at most one that is *not* `exp` of an
affine function must have a zero. This is the shape the application consumes.-/
theorem exists_zero_of_not_eq_exp_affine {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A B : ℝ}
    (hA : 0 < A) (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖))
    (hne : ¬ ∃ a b : ℂ, ∀ z, f z = Complex.exp (a * z + b)) :
    ∃ z, f z = 0 := by
  by_contra hc
  exact hne (eq_exp_affine_of_order_le_one hf (fun z hz => hc ⟨z, hz⟩) hA hgrowth)

end XiLab
