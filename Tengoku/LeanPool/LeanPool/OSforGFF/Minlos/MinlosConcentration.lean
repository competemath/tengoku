/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
module

public import Tengoku.LeanPool.LeanPool.OSforGFF.Minlos.NuclearSpace
public import Tengoku
import Tengoku.LeanPool.LeanPool.OSforGFF.Minlos.PietschBridge
import Tengoku.LeanPool.LeanPool.OSforGFF.Minlos.SazonovTightness

/-!
# Minlos Concentration Bound

Proves `nuclear_cylindrical_concentration` — the concentration bound for
nuclear cylindrical measures. `minlos_concentration` is a convenience wrapper.

## Architecture

1. **Helper lemmas** (proved): pointwise CF estimates (`cf_norm_le_one`,
   `cf_nhds_ball`, `one_sub_re_nonneg`, `quadratic_bound_outside`).

2. **Monotonicity lemmas** (proved): `seminorm_mono_of_le`, `finset_sup_le_of_mono`
   derive seminorm monotonicity from consecutive HS embeddings.

3. **Core bounds** (proved):
   - `joint_kernel_bound_finite`: Gaussian averaging on kernel elements
   - `tail_bound_uniform`: Dimension-free Gaussian averaging + Gram matrix + Chebyshev
   - `gram_schmidt_seminorm`: ONB construction for Hilbertian seminorms

4. **Theorem** `nuclear_cylindrical_concentration`: fully proved via
   Gram-Schmidt ONB, kernel concentration, tail bound, and continuity from below.

5. **Theorem** `minlos_concentration`: wrapper applying the above.

## References

- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, §3.3
- Bogachev, "Gaussian Measures", Ch. 2-3
- Trèves, "Topological Vector Spaces", Ch. 50-51
-/

@[expose] public section

open BigOperators MeasureTheory Complex TopologicalSpace Finsupp

noncomputable section

private lemma real_inner_eq_mul (a b : ℝ) : @inner ℝ ℝ _ a b = b * a :=
  RCLike.inner_apply a b

/-! ## CF constantly 1 implies random variable is 0 a.e. -/

/-- If X : Ω → ℝ is measurable and ∫ exp(I * ↑(t * X(ω))) dν = 1 for all t ∈ ℝ,
    then X = 0 ν-a.e.

    Proof sketch: Re(1 - ∫ exp(itX)) = ∫ (1 - cos(tX)) = 0. Since 1 - cos ≥ 0,
    cos(tX) = 1 a.e. for each t. Over countably many t ∈ ℚ simultaneously,
    this forces X = 0.
@isnad1 id=eventual.2h3v.s6.1fe15ba715f6 from=translated src=- shape=f432f1ec vocab=2cc9ee4d
-/
lemma ae_eq_zero_of_charfun_eq_one {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → ℝ} (hX : Measurable X)
    (hcf : ∀ t : ℝ, ∫ ω, exp (I * ↑(t * X ω)) ∂ν = 1) :
    ∀ᵐ ω ∂ν, X ω = 0 := by
  -- Step 1: Show ν.map X = dirac 0 via charFun equality
  have h_eq : ν.map X = Measure.dirac (0 : ℝ) := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_dirac]
    simp only [inner_zero_left]
    rw [charFun_apply, integral_map hX.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x => cexp (@inner ℝ ℝ _ x t * I)) _)]
    have h_inner : ∀ ω, cexp (@inner ℝ ℝ _ (X ω) t * I) = exp (I * ↑(t * X ω)) := by
      intro ω
      have : @inner ℝ ℝ _ (X ω) t = t * X ω := by
        change t * starRingEnd ℝ (X ω) = t * X ω; simp
      rw [this]; push_cast; ring_nf
    simp_all
  -- Step 2: Deduce X = 0 a.e.
  have h_ae : ∀ᵐ y ∂(ν.map X), y = 0 := by
    rw [h_eq]; exact ae_dirac_iff (measurableSet_singleton 0) |>.mpr rfl
  rwa [show (∀ᵐ ω ∂ν, X ω = 0) ↔ ∀ᵐ y ∂(ν.map X), y = 0 from
    (ae_map_iff hX.aemeasurable (measurableSet_singleton 0)).symm]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-! ## Helper lemmas -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The characteristic functional satisfies `‖Φ(x)‖ ≤ 1`, as the integral
    of a unit-modulus function against a probability measure.
@isnad1 id=le.1h4v.s7.422d0953a0d8 from=translated src=- shape=55059c14 vocab=6f4fdf5b
-/
lemma cf_norm_le_one
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (x : E) : ‖Φ x‖ ≤ 1 := by
  have h := h_cf_joint 1 (fun _ => 1) (fun _ => x)
  simp only [Fin.sum_univ_one, one_smul, one_mul] at h
  rw [← h]
  calc ‖∫ ω, exp (I * ↑(ω x)) ∂ν‖
      ≤ ∫ ω, ‖exp (I * ↑(ω x))‖ ∂ν := norm_integral_le_integral_norm _
    _ = ∫ ω, 1 ∂ν := by
        simp_all
    _ = 1 := by simp

/-- `1 - Re(z) ≤ 2` when `‖z‖ ≤ 1`.
@isnad1 id=le.1h1v.s5.c51ca3b5f1c4 from=translated src=- shape=4919c83f vocab=d23eafbc
-/
lemma one_sub_re_le_two_of_norm_le (z : ℂ) (hz : ‖z‖ ≤ 1) : 1 - z.re ≤ 2 := by
  have h1 : |z.re| ≤ ‖z‖ := abs_re_le_norm z
  have h2 : -1 ≤ z.re := by linarith [abs_le.mp (h1.trans hz)]
  linarith

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- Quadratic bound outside a seminorm ball: if `q(x) ≥ δ > 0` and `‖Φ(x)‖ ≤ 1`,
    then `1 - Re(Φ(x)) ≤ (2/δ²) · q(x)²`.
@isnad1 id=le.3h5v.s8.3e6d3a380c25 from=translated src=- shape=7583d1eb vocab=89fbc091
-/
lemma quadratic_bound_outside
    (Φ : E → ℂ) (h_norm_le : ∀ x : E, ‖Φ x‖ ≤ 1)
    (q : Seminorm ℝ E) (δ : ℝ) (hδ : 0 < δ)
    (x : E) (hx : δ ≤ q x) :
    1 - (Φ x).re ≤ (2 / δ ^ 2) * q x ^ 2 := by
  have h_re : 1 - (Φ x).re ≤ 2 := one_sub_re_le_two_of_norm_le _ (h_norm_le x)
  calc 1 - (Φ x).re ≤ 2 := h_re
    _ = (2 / δ ^ 2) * δ ^ 2 := by field_simp
    _ ≤ (2 / δ ^ 2) * q x ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sq_le_sq' (by linarith) hx

omit [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- CF norm bound gives `1 - Re(Φ(x)) ≥ 0`.
@isnad1 id=le.1h3v.s5.84c215480a5c from=translated src=- shape=37b53f89 vocab=6e795470
-/
lemma one_sub_re_nonneg
    (Φ : E → ℂ) (h_norm_le : ∀ x : E, ‖Φ x‖ ≤ 1) (x : E) :
    0 ≤ 1 - (Φ x).re := by
  have h1 : |Complex.re (Φ x)| ≤ ‖Φ x‖ := abs_re_le_norm _
  have h2 : (Φ x).re ≤ 1 := by linarith [abs_le.mp (h1.trans (h_norm_le x))]
  linarith

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- From `Continuous Φ`, `Φ 0 = 1`, and `WithSeminorms p`: extract a finite set
    of seminorm indices s and radius r > 0 such that `(s.sup p)(x) < r`
    implies `‖1 - Φ(x)‖ < ε`.
@isnad1 id=ex.4h4v.s8.b08c77434001 from=translated src=- shape=067b50bd vocab=c5cf7600
-/
lemma cf_nhds_ball
    (Φ : E → ℂ) (h_cf_cont : Continuous Φ) (h_normalized : Φ 0 = 1)
    (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset ℕ) (r : ℝ), 0 < r ∧
      ∀ x, (s.sup p) x < r → ‖1 - Φ x‖ < ε := by
  have h_cont_at : ContinuousAt Φ 0 := h_cf_cont.continuousAt
  rw [ContinuousAt, h_normalized] at h_cont_at
  have h_nhds : {x | ‖1 - Φ x‖ < ε} ∈ nhds (0 : E) := by
    have hsub : Φ ⁻¹' Metric.ball 1 ε ⊆ {x : E | ‖1 - Φ x‖ < ε} := by
      intro x hx; simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hx
      simp only [Set.mem_ofPred_eq]; rwa [norm_sub_rev]
    exact Filter.mem_of_superset
      (h_cont_at (Metric.isOpen_ball.mem_nhds (by simp [Metric.mem_ball, dist_self, hε]))) hsub
  rw [hp_top.hasBasis_zero_ball.mem_iff] at h_nhds
  obtain ⟨⟨s, r⟩, hr, h_sub⟩ := h_nhds
  refine ⟨s, r, hr, fun x hx => h_sub ?_⟩
  rw [Seminorm.ball_zero_eq]; exact hx

/-! ## Monotonicity from consecutive HS embeddings -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- From consecutive HS embeddings, `p n ≤ p m` whenever `n ≤ m`.
@isnad1 id=le.2h4v.s8.2daa2779ebc2 from=translated src=- shape=d9ec05c0 vocab=e4a47d06
-/
lemma seminorm_mono_of_le (p : ℕ → Seminorm ℝ E)
    (hp_hs : ∀ n, (p (n + 1)).IsHilbertSchmidtEmbedding (p n))
    {n m : ℕ} (h : n ≤ m) : p n ≤ p m := by
  induction m with
  | zero => simp [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_refl _
    · exact le_trans (ih (Nat.lt_succ_iff.mp hlt)) (hp_hs k).1

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- For a finite set of indices, `s.sup p ≤ p m` when `m` dominates every index in `s`
    (which holds when `m ≥ max s`, given monotonicity).
@isnad1 id=le.2h4v.s8.bf3b85a24b57 from=translated src=- shape=ee9188bc vocab=d700b7e9
-/
lemma finset_sup_le_of_mono (p : ℕ → Seminorm ℝ E)
    (hp_hs : ∀ n, (p (n + 1)).IsHilbertSchmidtEmbedding (p n))
    (s : Finset ℕ) (m : ℕ) (hm : ∀ n ∈ s, n ≤ m) :
    s.sup p ≤ p m := by
  apply Finset.sup_le
  intro n hn
  exact seminorm_mono_of_le p hp_hs (hm n hn)

/-! ## Combined quadratic bound -/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- **Combined quadratic bound** from CF continuity: for any ε > 0, there exist m₀ : ℕ
    and K ≥ 0 such that `1 - Re(Φ(x)) ≤ ε + K · (p m₀)(x)²` for all x.
@isnad1 id=ex.6h5v.s9.6e01049c43b1 from=translated src=- shape=a28bd046 vocab=96f18ddc
-/
lemma combined_quadratic_bound
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_cont : Continuous Φ) (h_normalized : Φ 0 = 1)
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (hp_hs : ∀ n, (p (n + 1)).IsHilbertSchmidtEmbedding (p n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m₀ : ℕ) (K : ℝ), 0 ≤ K ∧
      ∀ x : E, 1 - (Φ x).re ≤ ε + K * (p m₀) x ^ 2 := by
  obtain ⟨s, r, hr, h_ball⟩ := cf_nhds_ball Φ h_cf_cont h_normalized p hp_top ε hε
  have h_norm_le : ∀ x : E, ‖Φ x‖ ≤ 1 := cf_norm_le_one Φ ν h_cf_joint
  set m₀ := s.sup id
  have hm₀ : ∀ n ∈ s, n ≤ m₀ := fun n hn => Finset.le_sup (f := id) hn
  have h_mono : s.sup p ≤ p m₀ := finset_sup_le_of_mono p hp_hs s m₀ hm₀
  refine ⟨m₀, 2 / r ^ 2, by positivity, fun x => ?_⟩
  by_cases hx : (s.sup p) x < r
  · -- Inside ball: ‖1 - Φ(x)‖ < ε, so 1 - Re(Φ(x)) < ε
    have h1 : 1 - (Φ x).re ≤ ‖1 - Φ x‖ := by
      have := abs_re_le_norm (1 - Φ x)
      simp only [Complex.sub_re, Complex.one_re] at this
      linarith [abs_le.mp this]
    have h3 : (0 : ℝ) ≤ 2 / r ^ 2 * (p m₀) x ^ 2 := by positivity
    linarith [h_ball x hx]
  · -- Outside ball: use quadratic_bound_outside with q = p m₀
    push Not at hx
    have hx' : r ≤ (p m₀) x := le_trans hx (h_mono x)
    have := quadratic_bound_outside Φ h_norm_le (p m₀) r hr x hx'
    linarith

/-! ## CF vanishes on seminorm kernel -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- If `q(z) = 0` and `q` dominates the CF near 0 (i.e., for any ε > 0, there's a q-ball
    where `‖1 - Φ‖ < ε`), then `Φ(t • z) = 1` for all `t`.

    Proof: `q(t•z) = |t| · q(z) = 0 < r` for any `r > 0`, so `‖1 - Φ(t•z)‖ < ε`
    for all `ε > 0`.
@isnad1 id=eq.2h5v.s8.b3cf3b357735 from=translated src=- shape=a49cc5c9 vocab=bbc4a115
-/
lemma cf_kernel_of_ball_bound
    (Φ : E → ℂ)
    (q : Seminorm ℝ E) (z : E) (hz : q z = 0)
    (h_dom : ∀ ε > 0, ∃ r > 0, ∀ x, q x < r → ‖1 - Φ x‖ < ε) (t : ℝ) :
    Φ (t • z) = 1 := by
  by_contra h_ne
  have h_pos : 0 < ‖1 - Φ (t • z)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm h_ne))
  obtain ⟨r, hr, h_bound⟩ := h_dom _ h_pos
  have h_qtz : q (t • z) < r := by
    calc q (t • z) = ‖t‖ * q z := map_smul_eq_mul q t z
      _ = ‖t‖ * 0 := by rw [hz]
      _ = 0 := mul_zero _
      _ < r := hr
  linarith [h_bound (t • z) h_qtz]

/-! ## Linear combination a.e. from joint CF -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- If `x = ∑ j, β j • e j` in E (real coefficients), then `ω(x) = ∑ j, β j * ω(e j)`
    for ν-a.e. ω. Uses `h_cf_joint` directly — no linearity of ω assumed.

    This is the key trick: the joint CF condition forces the "linear decomposition"
    to hold a.e. even for real (not just rational) coefficients.
@isnad1 id=eventual.2h6v.s8.9c13595b0db0 from=translated src=- shape=fdf415e9 vocab=caf1a4c0
-/
lemma linear_combination_ae
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    {k : ℕ} (e : Fin k → E) (β : Fin k → ℝ) :
    ∀ᵐ ω ∂ν, ω (∑ j, β j • e j) = ∑ j, β j * ω (e j) := by
  set x := ∑ j, β j • e j with x_def
  set X : (E → ℝ) → ℝ := fun ω => ω x - ∑ j, β j * ω (e j)
  have hX_meas : Measurable X := by
    apply Measurable.sub (measurable_pi_apply x)
    exact Finset.measurable_sum _ (fun j _ => (measurable_pi_apply (e j)).const_mul _)
  have hX_cf : ∀ t : ℝ, ∫ ω, exp (I * ↑(t * X ω)) ∂ν = 1 := by
    intro t
    let s' : Fin (k + 1) → ℝ := Fin.cons t (fun j => -t * β j)
    let x' : Fin (k + 1) → E := Fin.cons x e
    have h := h_cf_joint (k + 1) s' x'
    have h_sum_x : ∑ i : Fin (k + 1), s' i • x' i = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, s', x']
      rw [show ∑ j : Fin k, (-t * β j) • e j = -(t • ∑ j, β j • e j) from by
        rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
        congr 1; ext j; simp [neg_smul, neg_mul, smul_smul]]
      simp [x_def]
    have h_sum_ω : ∀ ω', (∑ i : Fin (k + 1), s' i * ω' (x' i)) = t * X ω' := by
      intro ω'
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, s', x', X, mul_sub]
      congr 1
      rw [show ∑ j : Fin k, -t * β j * ω' (e j) =
          -(t * ∑ j, β j * ω' (e j)) from by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]; congr 1; ext j; ring]
    simp_all
  have := ae_eq_zero_of_charfun_eq_one hX_meas hX_cf
  filter_upwards [this] with ω hω
  linarith [show X ω = 0 from hω]

/-! ## Pushforward CF for finite evaluation maps -/

/-! ## Concentration on good set via Cauchy-Schwarz + Parseval -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- **Cauchy-Schwarz + Parseval concentration bound**: if ω is linear on combinations of
    a p-orthonormal sequence `{eⱼ}` and `∑ ω(eⱼ)² ≤ R²`, then for any linear combination
    `x = ∑ βⱼ eⱼ`, we have `|ω(x)| ≤ R · p(x)`.

    This is the pointwise bound at the heart of the concentration argument:
    ω in the "good set" (bounded evaluation norm) respects the seminorm.
@isnad1 id=le.5h7v.s9.5dd7b96543f5 from=translated src=- shape=47e78161 vocab=a815e4e5
-/
lemma bound_on_good_set
    (p : Seminorm ℝ E) (hp : p.IsHilbertian)
    {k : ℕ} (e : Fin k → E) (he : p.IsOrthonormalSeq e)
    (R : ℝ) (hR : 0 < R)
    (ω : E → ℝ)
    (h_linear : ∀ (β : Fin k → ℝ), ω (∑ j, β j • e j) = ∑ j, β j * ω (e j))
    (h_norm : ∑ j : Fin k, (ω (e j)) ^ 2 ≤ R ^ 2)
    (β : Fin k → ℝ) :
    |ω (∑ j, β j • e j)| ≤ R * p (∑ j, β j • e j) := by
  rw [h_linear]
  -- Parseval: p(∑ βⱼ eⱼ)² = ∑ βⱼ²
  have h_parseval := Seminorm.sq_sum_orthonormal p hp e he β
  -- Cauchy-Schwarz: (∑ βⱼ ω(eⱼ))² ≤ (∑ βⱼ²)(∑ ω(eⱼ)²)
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ β (fun j => ω (e j))
  -- Combined: (∑ βⱼ ω(eⱼ))² ≤ (R · p(x))²
  have h_sq : (∑ j : Fin k, β j * ω (e j)) ^ 2 ≤ (R * p (∑ j, β j • e j)) ^ 2 := by
    calc (∑ j : Fin k, β j * ω (e j)) ^ 2
        ≤ (∑ j, β j ^ 2) * (∑ j, (ω (e j)) ^ 2) := h_cs
      _ = p (∑ j, β j • e j) ^ 2 * (∑ j, (ω (e j)) ^ 2) := by rw [h_parseval]
      _ ≤ p (∑ j, β j • e j) ^ 2 * R ^ 2 :=
          mul_le_mul_of_nonneg_left h_norm (sq_nonneg _)
      _ = (R * p (∑ j, β j • e j)) ^ 2 := by ring
  exact abs_le_of_sq_le_sq h_sq (by positivity)

/-! ## Kernel elements vanish a.e. -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- If `p(z) = 0` and `p` dominates the CF (i.e., the CF at multiples of z
    is always 1), then `ω(z) = 0` for ν-a.e. ω. Proof: the CF of ω(z)
    is constantly 1, so ω(z) = 0 a.e. by `ae_eq_zero_of_charfun_eq_one`.
@isnad1 id=eventual.4h5v.s9.2cfe2bef772d from=translated src=- shape=1a67c18c vocab=c02f2ad4
-/
lemma kernel_eval_ae_zero
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (_h_normalized : Φ 0 = 1)
    (p : Seminorm ℝ E) (z : E) (_hz : p z = 0)
    (h_cf_kernel : ∀ t : ℝ, Φ (t • z) = 1) :
    ∀ᵐ ω ∂ν, ω z = 0 := by
  apply ae_eq_zero_of_charfun_eq_one (measurable_pi_apply z)
  intro t
  have h := h_cf_joint 1 (fun _ => t) (fun _ => z)
  simp_all

/-! ## ℚ-linearity for all Finsupp simultaneously -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- For ν-a.e. ω, the evaluation `ω(x_c)` equals the ℚ-linear combination
    `∑ cᵢ ω(dᵢ)` for **all** `c : ℕ →₀ ℚ` simultaneously.

    Uses countable intersection (`eventually_countable_forall`) since `ℕ →₀ ℚ`
    is countable, plus `linear_combination_ae` for each individual `c`.
@isnad1 id=eventual.2h4v.s8.e4daeebe3c82 from=translated src=- shape=2f59ca42 vocab=5c0ca576
-/
lemma q_linear_ae_all
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    (d : ℕ → E) :
    ∀ᵐ ω ∂ν, ∀ c : ℕ →₀ ℚ,
      ω (c.sum fun i a => (a : ℝ) • d i) = c.sum fun i a => (a : ℝ) * ω (d i) := by
  rw [eventually_countable_forall]
  intro c
  -- Enumerate support: Fin-indexed vectors and coefficients
  let e : Fin c.support.card → E := fun j => d (c.support.equivFin.symm j)
  let β : Fin c.support.card → ℝ := fun j => (c (c.support.equivFin.symm j) : ℝ)
  -- Apply linear_combination_ae with the Fin-indexed data
  have := linear_combination_ae Φ ν h_cf_joint h_normalized e β
  filter_upwards [this] with ω hω
  -- Both sides equal the Fin-indexed sum, via sum_coe_sort + Equiv.sum_comp
  change ω (∑ a ∈ c.support, (↑(c a) : ℝ) • d a) =
    ∑ a ∈ c.support, (↑(c a) : ℝ) * ω (d a)
  have h1 : (∑ a ∈ c.support, (↑(c a) : ℝ) • d a : E) = ∑ j, β j • e j := by
    rw [← c.support.sum_coe_sort]; exact (Equiv.sum_comp c.support.equivFin.symm _).symm
  have h2 : (∑ a ∈ c.support, (↑(c a) : ℝ) * ω (d a) : ℝ) = ∑ j, β j * ω (e j) := by
    rw [← c.support.sum_coe_sort]; exact (Equiv.sum_comp c.support.equivFin.symm _).symm
  rw [h1, h2]; exact hω

/-! ## Bad set definitions for continuity from below -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The "bad set" for the concentration bound: the set of ω where some
    ℚ-linear combination of dense vectors violates the seminorm bound.
-/
def concentrationBadSet (d : ℕ → E) (p : Seminorm ℝ E) (C : ℝ) :
    Set (E → ℝ) :=
  {ω | ∃ c : ℕ →₀ ℚ,
    ¬ (|ω (c.sum fun i a => (a : ℝ) • d i)| ≤
      C * p (c.sum fun i a => (a : ℝ) • d i))}

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The "restricted bad set" B_N: bad set restricted to ℚ-linear combinations
    with support in `{0, ..., N-1}`.
-/
def concentrationBadSetN (d : ℕ → E) (p : Seminorm ℝ E) (C : ℝ) (N : ℕ) :
    Set (E → ℝ) :=
  {ω | ∃ c : ℕ →₀ ℚ, c.support ⊆ Finset.range N ∧
    ¬ (|ω (c.sum fun i a => (a : ℝ) • d i)| ≤
      C * p (c.sum fun i a => (a : ℝ) • d i))}

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- B_N ⊆ B_M when N ≤ M.
@isnad1 id=le.1h6v.s6.9a83c0af5703 from=translated src=- shape=3e1b35df vocab=1c20cb85
-/
lemma concentrationBadSetN_mono (d : ℕ → E) (p : Seminorm ℝ E) (C : ℝ)
    {N M : ℕ} (h : N ≤ M) :
    concentrationBadSetN d p C N ⊆ concentrationBadSetN d p C M := by
  intro ω hω
  obtain ⟨c, hc_supp, hc_bad⟩ := hω
  exact ⟨c, hc_supp.trans (Finset.range_mono h), hc_bad⟩

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The full bad set equals the union of the restricted bad sets.
    Every `c : ℕ →₀ ℚ` has finite support contained in some `Finset.range N`.
@isnad1 id=eq.0h4v.s6.f75a3a83bf48 from=translated src=- shape=18f7746f vocab=a8db9123
-/
lemma concentrationBadSet_eq_iUnion (d : ℕ → E) (p : Seminorm ℝ E) (C : ℝ) :
    concentrationBadSet d p C = ⋃ N, concentrationBadSetN d p C N := by
  ext ω
  simp only [concentrationBadSet, concentrationBadSetN, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c.support.sup id + 1, c, ?_, hc⟩
    intro i hi
    exact Finset.mem_range.mpr (by
      have : i ≤ c.support.sup id := Finset.le_sup (f := id) hi
      omega)
  · rintro ⟨_, c, _, hc⟩
    exact ⟨c, hc⟩

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- If `ν(B_N) ≤ δ` for all N, then `ν(full bad set) ≤ δ`.
    Uses continuity of measure from below (`tendsto_measure_iUnion`).
@isnad1 id=le.1h6v.s7.2c2f967d3580 from=translated src=- shape=d75429cd vocab=28db274b
-/
lemma concentrationBadSet_measure_le (d : ℕ → E) (p : Seminorm ℝ E) (C : ℝ)
    (ν : Measure (E → ℝ)) (δ : ENNReal)
    (h_bound : ∀ N, ν (concentrationBadSetN d p C N) ≤ δ) :
    ν (concentrationBadSet d p C) ≤ δ := by
  rw [concentrationBadSet_eq_iUnion]
  exact le_of_tendsto' (tendsto_measure_iUnion_atTop
    (fun _ _ h => concentrationBadSetN_mono d p C h)) h_bound

/-! ## Seminorm Gram-Schmidt (proved) -/

section GramSchmidt

variable {F : Type*} [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
/-- If `p(z) = 0`, then `p(x + z) = p(x)`. -/
private lemma gs_seminorm_add_kernel (p : Seminorm ℝ F) (x z : F) (hz : p z = 0) :
    p (x + z) = p x := by
  apply le_antisymm
  · calc p (x + z) ≤ p x + p z := map_add_le_add p x z
    _ = p x := by rw [hz, add_zero]
  · calc p x = p (x + z + (-z)) := by congr 1; abel
    _ ≤ p (x + z) + p (-z) := map_add_le_add p _ _
    _ = p (x + z) := by rw [map_neg_eq_map, hz, add_zero]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
private lemma gs_innerProd_sub_left (p : Seminorm ℝ F) (hp : p.IsHilbertian)
    (x₁ x₂ y : F) :
    p.innerProd (x₁ - x₂) y = p.innerProd x₁ y - p.innerProd x₂ y := by
  rw [sub_eq_add_neg, p.innerProd_add_left hp x₁ (-x₂) y, p.innerProd_neg_left]
  ring

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
private lemma gs_innerProd_smul_right (p : Seminorm ℝ F) (hp : p.IsHilbertian)
    (a : ℝ) (x y : F) :
    p.innerProd x (a • y) = a * p.innerProd x y := by
  rw [p.innerProd_comm, p.innerProd_smul_left hp, p.innerProd_comm]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
private lemma gs_innerProd_sum_right (p : Seminorm ℝ F) (hp : p.IsHilbertian)
    {ι : Type*} (s : Finset ι) (x : F) (f : ι → F) :
    p.innerProd x (∑ j ∈ s, f j) = ∑ j ∈ s, p.innerProd x (f j) := by
  rw [p.innerProd_comm, p.innerProd_sum_left hp]
  congr 1; ext j; rw [p.innerProd_comm]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
/-- Pythagorean theorem: if `ip(x, y) = 0` then `p(x+y)^2 = p(x)^2 + p(y)^2`. -/
private lemma gs_pythagoras (p : Seminorm ℝ F)
    (hp : p.IsHilbertian) (x y : F) (hxy : p.innerProd x y = 0) :
    p (x + y) ^ 2 = p x ^ 2 + p y ^ 2 := by
  have h1 : p (x + y) ^ 2 = p (x - y) ^ 2 := by
    simp only [Seminorm.innerProd] at hxy; linarith
  linarith [hp x y]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
/-- **Gram-Schmidt for Hilbertian seminorms**: given N vectors in F and a Hilbertian
    seminorm p, there exist k orthonormal vectors such that every element of
    the span of the original vectors decomposes as a p-ONB combination plus a kernel
    element (where p vanishes).
@isnad1 id=ex.1h4v.s9.11688e8d4673 from=translated src=- shape=d573b3e2 vocab=ab68b0c6
-/
lemma gram_schmidt_seminorm_aux (p : Seminorm ℝ F) (hp : p.IsHilbertian)
    (N : ℕ) (d : Fin N → F) :
    ∃ (k : ℕ) (e : Fin k → F),
      p.IsOrthonormalSeq e ∧
      (∀ (β : Fin N → ℝ), ∃ (α : Fin k → ℝ),
        p (∑ i, β i • d i - ∑ j, α j • e j) = 0 ∧
        p (∑ i, β i • d i) ^ 2 = ∑ j, α j ^ 2) := by
  induction N with
  | zero =>
    exact ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun β => ⟨Fin.elim0, by simp, by simp⟩⟩
  | succ n ih =>
    obtain ⟨k, e, he_orth, he_decomp⟩ := ih (fun i => d (Fin.castSucc i))
    -- v = d(last n), projection coefficients c_j = ip(v, e_j)
    set v := d (Fin.last n) with hv_def
    set c : Fin k → ℝ := fun j => p.innerProd v (e j) with hc_def
    -- u = v - Σ c_j e_j is the residual
    set u := v - ∑ j : Fin k, c j • e j with hu_def
    -- u ⊥ e_j for all j
    have hu_orth : ∀ j : Fin k, p.innerProd u (e j) = 0 := by
      intro j; change p.innerProd (v - ∑ i : Fin k, c i • e i) (e j) = 0
      rw [gs_innerProd_sub_left p hp, p.innerProd_sum_left hp]
      simp_rw [p.innerProd_smul_left hp]
      suffices h : ∑ i : Fin k, c i * p.innerProd (e i) (e j) = c j by linarith
      conv_lhs => arg 2; ext i; rw [he_orth i j]
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    -- u ⊥ (Σ c_j e_j)
    have hu_proj_orth : p.innerProd u (∑ j : Fin k, c j • e j) = 0 := by
      rw [gs_innerProd_sum_right p hp]
      simp_rw [gs_innerProd_smul_right p hp]; simp [hu_orth]
    -- Pythagoras: u + proj = v
    have hv_eq : u + ∑ j : Fin k, c j • e j = v := sub_add_cancel v _
    have h_pyth := gs_pythagoras p hp u (∑ j : Fin k, c j • e j) hu_proj_orth
    -- p(proj)^2 = Σ c_j^2
    have h_proj_sq : p (∑ j : Fin k, c j • e j) ^ 2 = ∑ j : Fin k, c j ^ 2 :=
      p.sq_sum_orthonormal hp e he_orth c
    -- Splitting Fin (n+1) sums
    have h_split : ∀ β : Fin (n + 1) → ℝ,
        ∑ i : Fin (n + 1), β i • d i =
        (∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i)) +
        β (Fin.last n) • v := by
      intro β; rw [Fin.sum_univ_castSucc]
    -- Helper: decompose the ONB sum
    have h_onb_decomp : ∀ (α' : Fin k → ℝ) (b : ℝ),
        ∑ j : Fin k, (α' j + b * c j) • e j =
        (∑ j, α' j • e j) + b • ∑ j : Fin k, c j • e j := by
      intro α' b
      simp_rw [add_smul, Finset.sum_add_distrib, mul_smul, Finset.smul_sum]
    -- Helper: b • v = b • proj + b • u
    have hv_decomp : ∀ b' : ℝ,
        b' • v = b' • (∑ j : Fin k, c j • e j) + b' • u := by
      intro b'; change b' • v = b' • (∑ j : Fin k, c j • e j) +
        b' • (v - ∑ j : Fin k, c j • e j)
      rw [← smul_add]; congr 1; abel
    -- Case split on whether p(u) = 0 or p(u) > 0
    by_cases hu0 : p u = 0
    · -- Case 1: u is in the kernel. Same ONB works.
      refine ⟨k, e, he_orth, ?_⟩
      intro β
      obtain ⟨α', hα'_ker, hα'_parseval⟩ := he_decomp (fun i => β (Fin.castSucc i))
      let b := β (Fin.last n)
      have hbu : p (b • u) = 0 := by rw [map_smul_eq_mul, hu0, mul_zero]
      refine ⟨fun j => α' j + b * c j, ?_, ?_⟩
      · -- p(full sum - ONB combination) = 0
        have h_eq : ∑ i : Fin (n + 1), β i • d i -
            ∑ j : Fin k, (α' j + b * c j) • e j =
            (∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i) -
              ∑ j, α' j • e j) + b • u := by
          rw [h_split β, h_onb_decomp α' b, hu_def, smul_sub]; abel
        rw [h_eq, gs_seminorm_add_kernel p _ _ hbu, hα'_ker]
      · -- p(full sum)^2 = Σ (α'j + b*cj)^2
        rw [h_split β]
        conv_lhs =>
          rw [show β (Fin.last n) = b from rfl,
              show v = (∑ j : Fin k, c j • e j) +
                (v - ∑ j : Fin k, c j • e j) from (add_sub_cancel _ _).symm]
        rw [show (∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i)) +
            b • ((∑ j : Fin k, c j • e j) + (v - ∑ j : Fin k, c j • e j)) =
            (∑ j : Fin k, (α' j + b * c j) • e j) +
            ((∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i) -
              ∑ j, α' j • e j) +
            b • (v - ∑ j : Fin k, c j • e j)) from by
          rw [h_onb_decomp, smul_add]; abel]
        have h_ker :
            p ((∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i) -
              ∑ j, α' j • e j) +
            b • (v - ∑ j : Fin k, c j • e j)) = 0 :=
          (gs_seminorm_add_kernel p _ _ hbu).trans hα'_ker
        rw [gs_seminorm_add_kernel p _ _ h_ker, p.sq_sum_orthonormal hp e he_orth]
    · -- Case 2: p(u) > 0. Extend ONB with normalized u.
      have hpu_pos : 0 < p u := lt_of_le_of_ne (apply_nonneg p u) (Ne.symm hu0)
      let e_new := (p u)⁻¹ • u
      have he_new_norm : p e_new = 1 := by
        change p ((p u)⁻¹ • u) = 1
        rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpu_pos),
            inv_mul_cancel₀ (ne_of_gt hpu_pos)]
      have he_new_orth_e : ∀ j : Fin k, p.innerProd e_new (e j) = 0 := by
        intro j; change p.innerProd ((p u)⁻¹ • u) (e j) = 0
        rw [p.innerProd_smul_left hp]; simp [hu_orth j]
      have hu_eq_smul : u = p u • e_new := by
        change u = p u • ((p u)⁻¹ • u)
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpu_pos), one_smul]
      -- Extended ONB: e_new at index 0, old e at indices 1..k
      let e' : Fin (k + 1) → F := Fin.cons e_new e
      have he'_orth : p.IsOrthonormalSeq e' := by
        intro i j
        refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
        · -- (0,0)
          change p.innerProd e_new e_new = if (0 : Fin (k + 1)) = 0 then 1 else 0
          rw [ite_eq_left rfl, p.innerProd_self, he_new_norm, one_pow]
        · -- (0, succ j')
          change p.innerProd e_new (e j') = if (0 : Fin (k + 1)) = j'.succ then 1 else 0
          rw [ite_eq_right (Fin.succ_ne_zero j').symm, he_new_orth_e j']
        · -- (succ i', 0)
          change p.innerProd (e i') e_new = if i'.succ = (0 : Fin (k + 1)) then 1 else 0
          rw [ite_eq_right (Fin.succ_ne_zero i'), p.innerProd_comm, he_new_orth_e i']
        · -- (succ i', succ j')
          change p.innerProd (e i') (e j') = if i'.succ = j'.succ then 1 else 0
          rw [show (if i'.succ = j'.succ then (1:ℝ) else 0) =
            if i' = j' then 1 else 0 from by simp [Fin.ext_iff]]
          exact he_orth i' j'
      refine ⟨k + 1, e', he'_orth, ?_⟩
      intro β
      obtain ⟨α', hα'_ker, hα'_parseval⟩ := he_decomp (fun i => β (Fin.castSucc i))
      let b := β (Fin.last n)
      let α_new : Fin (k + 1) → ℝ := Fin.cons (b * p u) (fun j => α' j + b * c j)
      -- Key identity: the extended ONB sum equals old ONB sum + b•v
      have h_ext_sum : ∑ j : Fin (k + 1), α_new j • e' j =
          (∑ j, α' j • e j) + b • v := by
        change ∑ j : Fin (k + 1),
            (Fin.cons (b * p u) (fun j => α' j + b * c j) : Fin (k + 1) → ℝ) j •
            (Fin.cons e_new e : Fin (k + 1) → F) j =
          (∑ j, α' j • e j) + b • v
        rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]
        rw [h_onb_decomp α' b]
        -- Goal: (b*pu)•e_new + (Σ α'j•ej + b•Σ cj•ej) = Σ α'j•ej + b•v
        -- Since e_new = pu⁻¹•u, (b*pu)•(pu⁻¹•u) = b•u
        -- And b•v = b•Σ cj•ej + b•u (from hv_decomp)
        conv_rhs => rw [show b • v = b • (∑ j : Fin k, c j • e j) + b • u from hv_decomp b]
        change (β (Fin.last n) * p u) • ((p u)⁻¹ • u) +
            (∑ j, α' j • e j + β (Fin.last n) • ∑ j : Fin k, c j • e j) =
          ∑ j, α' j • e j +
            (β (Fin.last n) • ∑ j : Fin k, c j • e j +
              β (Fin.last n) • (v - ∑ j : Fin k, c j • e j))
        rw [smul_smul, mul_assoc, mul_inv_cancel₀ (ne_of_gt hpu_pos), mul_one]
        abel
      refine ⟨α_new, ?_, ?_⟩
      · -- kernel: p(full sum - extended ONB sum) = 0
        rw [show ∑ i : Fin (n + 1), β i • d i - ∑ j : Fin (k + 1), α_new j • e' j =
            ∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i) -
              ∑ j, α' j • e j from by rw [h_ext_sum, h_split]; abel]
        exact hα'_ker
      · -- Parseval: p(full sum)^2 = Σ α_new(j)^2
        rw [h_split]
        -- Rearrange: Σ β'i d(ci) + b•v = (Σ α'j ej + b•v) + kernel_residual
        have h_rearr :
            (∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i)) +
              β (Fin.last n) • v =
            (∑ j : Fin (k + 1), α_new j • e' j) +
            (∑ i : Fin n, β (Fin.castSucc i) • d (Fin.castSucc i) -
              ∑ j, α' j • e j) := by
          rw [h_ext_sum]; abel
        rw [h_rearr, gs_seminorm_add_kernel p _ _ hα'_ker,
            p.sq_sum_orthonormal hp e' he'_orth]

end GramSchmidt

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/--
@isnad1 id=ex.1h4v.s9.11688e8d4673 from=translated src=- shape=d573b3e2 vocab=ab68b0c6
-/
lemma gram_schmidt_seminorm (p : Seminorm ℝ E) (hp : p.IsHilbertian)
    (N : ℕ) (d : Fin N → E) :
    ∃ (k : ℕ) (e : Fin k → E),
      p.IsOrthonormalSeq e ∧
      (∀ (β : Fin N → ℝ), ∃ (α : Fin k → ℝ),
        p (∑ i, β i • d i - ∑ j, α j • e j) = 0 ∧
        p (∑ i, β i • d i) ^ 2 = ∑ j, α j ^ 2) :=
  gram_schmidt_seminorm_aux p hp N d

/-! ## Per-N concentration bound -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- For each N, the restricted bad set B_N has measure bounded by the tail probability
    of the squared evaluation norm on a p-ONB.

    Key argument: on the a.e. set where all decompositions hold,
    Cauchy-Schwarz + Parseval gives |ω(x_c)| ≤ R · p(x_c) whenever Σ ω(eⱼ)² ≤ R².
    So B_N ⊆ {Σ ω(eⱼ)² > R²} ∪ (null set).
@isnad1 id=le.7h9v.s10.ec1f13d72a40 from=translated src=- shape=9d9a7ef8 vocab=ff97d9cc
-/
lemma concentrationBadSetN_measure_bound
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    (d : ℕ → E) (p : Seminorm ℝ E) (_hp : p.IsHilbertian)
    (h_cf_kernel : ∀ z, p z = 0 → ∀ t : ℝ, Φ (t • z) = 1)
    {k : ℕ} (e : Fin k → E) (_he : p.IsOrthonormalSeq e)
    (h_decomp : ∀ c : ℕ →₀ ℚ, ∃ (α : Fin k → ℝ),
      p (c.sum (fun i a => (a : ℝ) • d i) - ∑ j, α j • e j) = 0 ∧
      p (c.sum (fun i a => (a : ℝ) • d i)) ^ 2 = ∑ j, α j ^ 2)
    (R : ℝ) (hR : 0 < R) (N : ℕ) :
    ν (concentrationBadSetN d p R N) ≤
      ν {ω : E → ℝ | R ^ 2 < ∑ j : Fin k, (ω (e j)) ^ 2} := by
  -- Choose decomposition coefficients for each c
  choose α hα_ker hα_parseval using h_decomp
  -- Step 1: For a.e. ω, for all c, ω(x_c) = Σ α(c)_j ω(e_j)
  have h_ae_decomp : ∀ᵐ ω ∂ν, ∀ c : ℕ →₀ ℚ,
      ω (c.sum (fun i a => (a : ℝ) • d i)) = ∑ j, (α c) j * ω (e j) := by
    rw [eventually_countable_forall]; intro c
    -- z_c = x_c - Σ α_j e_j is in the kernel of p
    set z_c := c.sum (fun i a => (a : ℝ) • d i) - ∑ j, (α c) j • e j
    -- ω(z_c) = 0 a.e. via kernel_eval_ae_zero + h_cf_kernel
    have h_z_zero := kernel_eval_ae_zero Φ ν h_cf_joint h_normalized p z_c
      (hα_ker c) (h_cf_kernel z_c (hα_ker c))
    -- x_c = z_c + Σ α_j e_j, so linear_combination_ae with (z_c, e₁,...,eₖ)
    -- and coefficients (1, α₁,...,αₖ) gives ω(x_c) = ω(z_c) + Σ α_j ω(e_j) a.e.
    let e' : Fin (k + 1) → E := Fin.cons z_c e
    let β' : Fin (k + 1) → ℝ := Fin.cons 1 (α c)
    have h_sum_eq : (∑ j, β' j • e' j) = c.sum (fun i a => (a : ℝ) • d i) := by
      rw [Fin.sum_univ_succ]
      simp only [e', β', Fin.cons_zero, Fin.cons_succ, one_smul]
      exact sub_add_cancel _ _
    have h_lin := linear_combination_ae Φ ν h_cf_joint h_normalized e' β'
    filter_upwards [h_z_zero, h_lin] with ω h_z h_xc
    -- h_xc: ω(Σ β'_j • e'_j) = Σ β'_j * ω(e'_j)
    rw [h_sum_eq] at h_xc; rw [h_xc, Fin.sum_univ_succ]
    simp only [e', β', Fin.cons_zero, Fin.cons_succ, one_mul, h_z, zero_add]
  -- Step 2: concentrationBadSetN ⊆ {R² < Σ ω(e_j)²} ∪ (null set)
  set tail := {ω : E → ℝ | R ^ 2 < ∑ j : Fin k, (ω (e j)) ^ 2}
  set null_set := {ω : E → ℝ | ¬∀ c : ℕ →₀ ℚ,
    ω (c.sum (fun i a => (a : ℝ) • d i)) = ∑ j, (α c) j * ω (e j)}
  have h_null : ν null_set = 0 := ae_iff.mp h_ae_decomp
  have h_sub : concentrationBadSetN d p R N ⊆ tail ∪ null_set := by
    intro ω hω
    by_contra h_not
    simp only [Set.mem_union, not_or] at h_not
    obtain ⟨h_not_tail, h_not_null⟩ := h_not
    simp only [tail, null_set, Set.mem_ofPred_eq, not_lt, not_not] at h_not_tail h_not_null
    -- h_not_tail: Σ ω(e_j)² ≤ R²
    -- h_not_null: ∀ c, ω(x_c) = Σ α(c)_j ω(e_j)
    obtain ⟨c, _, hc_bad⟩ := hω
    apply hc_bad
    rw [h_not_null c]
    -- |Σ α(c)_j ω(e_j)| ≤ R · p(x_c) by Cauchy-Schwarz + Parseval
    have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (α c) (fun j => ω (e j))
    have h_sq : (∑ j, (α c) j * ω (e j)) ^ 2 ≤
        (R * p (c.sum fun i a => (a : ℝ) • d i)) ^ 2 := by
      calc (∑ j, (α c) j * ω (e j)) ^ 2
          ≤ (∑ j, (α c) j ^ 2) * (∑ j, ω (e j) ^ 2) := h_cs
        _ = p (c.sum fun i a => (a : ℝ) • d i) ^ 2 * (∑ j, ω (e j) ^ 2) := by
            rw [hα_parseval c]
        _ ≤ p (c.sum fun i a => (a : ℝ) • d i) ^ 2 * R ^ 2 :=
            mul_le_mul_of_nonneg_left h_not_tail (sq_nonneg _)
        _ = (R * p (c.sum fun i a => (a : ℝ) • d i)) ^ 2 := by ring
    exact abs_le_of_sq_le_sq h_sq (by positivity)
  calc ν (concentrationBadSetN d p R N)
      ≤ ν (tail ∪ null_set) := measure_mono h_sub
    _ ≤ ν tail + ν null_set := measure_union_le _ _
    _ = ν tail := by rw [h_null, add_zero]

/-! ## Nuclear cylindrical concentration -/

/- **Nuclear cylindrical concentration** (Gel'fand-Vilenkin Vol.4, Ch.IV §3.3).

Given:
- A separable, nonempty locally convex space `E`,
- Hilbertian seminorms `p` with consecutive Hilbert-Schmidt embeddings
  (`(p (n+1)).IsHilbertSchmidtEmbedding (p n)`) generating the topology,
- A cylindrical probability measure `ν` with continuous characteristic
  functional `Φ` satisfying `Φ(0) = 1` and the joint CF condition
  `∫ exp(i ∑ sⱼ ω(xⱼ)) dν = Φ(∑ sⱼ xⱼ)`,
- A dense sequence `d : ℕ → E`,

the conclusion is: for any `ε > 0`, there exist `m, C : ℕ` such that
  `ν {ω | ∃ c : ℕ →₀ ℚ, |ω(x_c)| > C · (p m)(x_c)} < ε`.

**Proof**:
1. CF continuity at 0 → seminorm ball where `‖1 - Φ‖ < ε/2`.
2. Quadratic bound: `1 - Re Φ(x) ≤ ε/2 + (2/r²) · (p m₀)(x)²`.
3. Gaussian averaging on `(p m₁)`-orthonormal `{eⱼ}`:
   `𝔼[1 - exp(-σ² ω(eⱼ)²/2)] ≤ ε/2 + 2σ²(2/r²)(p m₀)(eⱼ)²`.
4. Sum over `j` using HS bound `∑ (p m₀)(eⱼ)² ≤ C_HS` → tail control.
5. Chebyshev + Bessel inequality for ℚ-linear combinations.

**References:**
- Gel'fand & Vilenkin, *Generalized Functions* Vol. 4, Ch. IV, §3.3
- Bogachev, *Gaussian Measures*, Ch. 2–3
- Minlos, *Generalized Random Processes*, Theorems 2.1–2.3 -/
/-! ### Kernel evaluation a.e. bound -/

/-! ### Tail bound for evaluation on ONB (key step) -/

/-! ### Restricted bad set bound with kernel contribution -/

/-! ### Main theorem -/

/-! ## Main theorem -/

end
