import Tengoku.Twinprime.TwinPrime.Analytic.ZetaTruncation
import Tengoku.Seed.Analysis.Complex.LocallyUniformLimit
import Tengoku.Seed.Analysis.Complex.Convex
import Tengoku.Seed.Analysis.Analytic.Uniqueness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pole-corrected zeta truncation on the positive half-plane

Multiplying the ordered pole-corrected approximations by `s - 1` gives
entire approximants with value one at the pole. Quantitative locally uniform
convergence and analytic uniqueness identify their limit with the existing
regularized zeta function. Dividing away from the pole recovers the sharp
unregularized truncation bound. No absolute convergence in `0 < s.re ≤ 1`
is asserted.
-/

noncomputable section

open Finset Filter
open scoped Topology

namespace TwinPrime.Analytic

/-- An entire regularized approximation when the natural cutoff is positive.-/
def regularizedZetaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  (s - 1) * (∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s)

/--
@isnad1 id=eq.0h1v.s4.abe866504918 from=translated src=- shape=004a7881 vocab=84a1fc06
-/
@[simp] theorem regularizedZetaPartialSum_one (N : ℕ) :
    regularizedZetaPartialSum 1 N = 1 := by
  simp [regularizedZetaPartialSum]

/--
@isnad1 id=eq.1h2v.s5.c5e97d3c1349 from=translated src=- shape=c22ca360 vocab=6a02812a
-/
theorem regularizedZetaPartialSum_eq_mul (s : ℂ) (hs1 : s ≠ 1) (N : ℕ) :
    regularizedZetaPartialSum s N = (s - 1) * zetaPolePartialSum s N := by
  unfold regularizedZetaPartialSum zetaPolePartialSum
  have h : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp

/-- The finite regularized tail bound also holds at the pole.
@isnad1 id=le.3h3v.s6.16c62dc6e066 from=translated src=- shape=ed83effd vocab=6a6f521a
-/
theorem norm_regularizedZetaPartialSum_sub_le (M N : ℕ)
    (hM : 1 ≤ M) (hMN : M ≤ N) (s : ℂ) (hs : 0 < s.re) :
    ‖regularizedZetaPartialSum s N - regularizedZetaPartialSum s M‖ ≤
      ‖s - 1‖ * (‖s‖ / s.re) * (M : ℝ) ^ (-s.re) := by
  by_cases hs1 : s = 1
  · subst s
    simp
  · rw [regularizedZetaPartialSum_eq_mul s hs1 N,
      regularizedZetaPartialSum_eq_mul s hs1 M, ← mul_sub, norm_mul]
    calc
      _ ≤ ‖s - 1‖ * ((‖s‖ / s.re) * (M : ℝ) ^ (-s.re)) :=
        mul_le_mul_of_nonneg_left
          (norm_zetaPolePartialSum_sub_le_left M N hM hMN s hs hs1) (norm_nonneg _)
      _ = _ := by ring

/--
@isnad1 id=cauchyse.1h1v.s4.4a7d19569388 from=translated src=- shape=7c99636a vocab=b39f5f5a
-/
theorem cauchySeq_regularizedZetaPartialSum (s : ℂ) (hs : 0 < s.re) :
    CauchySeq (regularizedZetaPartialSum s) := by
  by_cases hs1 : s = 1
  · subst s
    change CauchySeq (fun N : ℕ => regularizedZetaPartialSum 1 N)
    simpa only [regularizedZetaPartialSum_one] using (cauchySeq_const (β := ℕ) (1 : ℂ))
  · obtain ⟨L, hL, _⟩ := exists_zetaPolePartialSum_limit s hs hs1
    exact ((hL.const_mul (s - 1)).congr
      (fun N => (regularizedZetaPartialSum_eq_mul s hs1 N).symm)).cauchySeq

/-- The ordered regularized limit, defined independently of convergence proofs.-/
def regularizedZetaLimit (s : ℂ) : ℂ := limUnder atTop (regularizedZetaPartialSum s)

/--
@isnad1 id=tendsto.1h1v.s5.36e6c59102b1 from=translated src=- shape=e044ba58 vocab=cdc327cf
-/
theorem tendsto_regularizedZetaPartialSum_limit (s : ℂ) (hs : 0 < s.re) :
    Tendsto (regularizedZetaPartialSum s) atTop (𝓝 (regularizedZetaLimit s)) :=
  (cauchySeq_regularizedZetaPartialSum s hs).tendsto_limUnder

/--
@isnad1 id=le.2h2v.s6.05a2d02ba29b from=translated src=- shape=7b220764 vocab=c3195a4b
-/
theorem norm_regularizedZetaLimit_sub_partialSum_le (M : ℕ) (hM : 1 ≤ M)
    (s : ℂ) (hs : 0 < s.re) :
    ‖regularizedZetaLimit s - regularizedZetaPartialSum s M‖ ≤
      ‖s - 1‖ * (‖s‖ / s.re) * (M : ℝ) ^ (-s.re) := by
  apply le_of_tendsto (((tendsto_regularizedZetaPartialSum_limit s hs).sub
    tendsto_const_nhds).norm)
  filter_upwards [eventually_ge_atTop M] with N hMN
  exact norm_regularizedZetaPartialSum_sub_le M N hM hMN s hs

/-- A common budget on bounded portions of the positive half-plane.
@isnad1 id=le.4h4v.s6.362c61999375 from=translated src=- shape=f871faa7 vocab=37ae6797
-/
theorem norm_regularizedZetaLimit_sub_partialSum_le_uniform (M : ℕ) (hM : 1 ≤ M)
    (δ H : ℝ) (hδ : 0 < δ) (s : ℂ) (hσ : δ ≤ s.re) (hH : ‖s‖ ≤ H) :
    ‖regularizedZetaLimit s - regularizedZetaPartialSum s M‖ ≤
      (H + 1) * (H / δ) * (M : ℝ) ^ (-δ) := by
  have hs := hδ.trans_le hσ
  have hH0 : 0 ≤ H := (norm_nonneg s).trans hH
  have hsub : ‖s - 1‖ ≤ H + 1 := by
    calc
      _ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ _ := by simpa using add_le_add_right hH 1
  apply (norm_regularizedZetaLimit_sub_partialSum_le M hM s hs).trans
  apply mul_le_mul
  · exact mul_le_mul hsub (div_le_div₀ hH0 hH hδ hσ) (by positivity) (by positivity)
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM) (neg_le_neg hσ)
  · positivity
  · positivity

/--
@isnad1 id=tendstou.1h2v.s5.f573fcdf5bdb from=translated src=- shape=cfec39c9 vocab=af7d6a3e
-/
theorem tendstoUniformlyOn_regularizedZetaPartialSum_limit (δ H : ℝ) (hδ : 0 < δ) :
    TendstoUniformlyOn (fun N s => regularizedZetaPartialSum s N)
      regularizedZetaLimit atTop {s : ℂ | δ ≤ s.re ∧ ‖s‖ ≤ H} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (-δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun N : ℕ => (H + 1) * (H / δ) * (N : ℝ) ^ (-δ)) atTop (𝓝 0) := by
    simpa using hp.const_mul ((H + 1) * (H / δ))
  filter_upwards [eventually_ge_atTop 1, hb.eventually (gt_mem_nhds hε)] with N hN hbN
  intro s hs
  rw [dist_eq_norm]
  exact (norm_regularizedZetaLimit_sub_partialSum_le_uniform N hN δ H hδ s hs.1 hs.2).trans_lt hbN

/--
@isnad1 id=tendstol.0h0v.s5.ea7df31c1950 from=translated src=- shape=6b0e006c vocab=63c7502a
-/
theorem tendstoLocallyUniformlyOn_regularizedZetaPartialSum_limit :
    TendstoLocallyUniformlyOn (fun N s => regularizedZetaPartialSum s N)
      regularizedZetaLimit atTop {s : ℂ | 0 < s.re} := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  change 0 < z.re at hz
  let δ : ℝ := z.re / 2
  let H : ℝ := ‖z‖ + 1
  have hδ : 0 < δ := by dsimp [δ]; exact half_pos hz
  have hlo : {s : ℂ | δ < s.re} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp [δ]; linarith)
  have hhi : {s : ℂ | ‖s‖ < H} ∈ 𝓝 z :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by dsimp [H]; linarith)
  refine ⟨{s : ℂ | δ ≤ s.re ∧ ‖s‖ ≤ H}, mem_nhdsWithin_of_mem_nhds ?_,
    tendstoUniformlyOn_regularizedZetaPartialSum_limit δ H hδ⟩
  exact mem_of_superset (inter_mem hlo hhi) (fun s hs => ⟨hs.1.le, hs.2.le⟩)

/--
@isnad1 id=differen.1h1v.s6.f56c30663191 from=translated src=- shape=4aa06753 vocab=03beb577
-/
theorem differentiable_regularizedZetaPartialSum (N : ℕ) (hN : 1 ≤ N) :
    Differentiable ℂ (fun s => regularizedZetaPartialSum s N) := by
  have hsum : Differentiable ℂ (fun s : ℂ => ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s)) := by
    apply Differentiable.fun_sum
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Ioc.mp hn).1)
    exact differentiable_id.neg.const_cpow (Or.inl hn0)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  exact ((differentiable_id.sub_const 1).mul hsum).add
    ((differentiable_const 1).sub differentiable_id |>.const_cpow (Or.inl hN0))

/--
@isnad1 id=differen.0h0v.s6.e9afa10c1a5a from=translated src=- shape=71829fdc vocab=126670f8
-/
theorem differentiableOn_regularizedZetaLimit :
    DifferentiableOn ℂ regularizedZetaLimit {s : ℂ | 0 < s.re} := by
  apply tendstoLocallyUniformlyOn_regularizedZetaPartialSum_limit.differentiableOn
    _ (isOpen_lt continuous_const Complex.continuous_re)
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (differentiable_regularizedZetaPartialSum N hN).differentiableOn

/-- Mathlib's entire pole regularization at conductor one, with value one at `1`.-/
def regularizedRiemannZeta : ℂ → ℂ := DirichletCharacter.LFunctionTrivChar₁ 1

/--
@isnad1 id=eq.0h0v.s3.779b04b36851 from=translated src=- shape=3c26ae4f vocab=8902d808
-/
@[simp] theorem regularizedRiemannZeta_one : regularizedRiemannZeta 1 = 1 := by
  simp [regularizedRiemannZeta, DirichletCharacter.LFunctionTrivChar₁]

/--
@isnad1 id=eq.1h1v.s5.d40e71031d92 from=translated src=- shape=c9d62150 vocab=d0eeea20
-/
theorem regularizedRiemannZeta_apply_of_ne_one (s : ℂ) (hs1 : s ≠ 1) :
    regularizedRiemannZeta s = (s - 1) * riemannZeta s := by
  simp [regularizedRiemannZeta, DirichletCharacter.LFunctionTrivChar₁, hs1,
    DirichletCharacter.LFunctionTrivChar]

/--
@isnad1 id=differen.0h0v.s6.5e448685756f from=translated src=- shape=aa9fb30a vocab=d7a7ceb0
-/
theorem differentiable_regularizedRiemannZeta : Differentiable ℂ regularizedRiemannZeta :=
  DirichletCharacter.differentiable_LFunctionTrivChar₁ 1

/-- Analytic uniqueness retains the pole's correct regularized value.
@isnad1 id=eqon.0h0v.s4.e54694c1c628 from=translated src=- shape=3d5ac373 vocab=9eaa631b
-/
theorem regularizedZetaLimit_eqOn_regularizedRiemannZeta :
    Set.EqOn regularizedZetaLimit regularizedRiemannZeta {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf := differentiableOn_regularizedZetaLimit.analyticOnNhd hopen
  have hg := differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd hopen
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := (2 : ℂ)) (by norm_num)
  have htwo : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [htwo] with s hs
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hR : Tendsto (regularizedZetaPartialSum s) atTop
      (𝓝 ((s - 1) * riemannZeta s)) :=
    ((tendsto_zetaPolePartialSum_riemannZeta s hs).const_mul (s - 1)).congr
      (fun N => (regularizedZetaPartialSum_eq_mul s hs1 N).symm)
  rw [← regularizedRiemannZeta_apply_of_ne_one s hs1] at hR
  exact tendsto_nhds_unique
    (tendsto_regularizedZetaPartialSum_limit s (lt_trans zero_lt_one hs)) hR

/--
@isnad1 id=tendstol.0h0v.s5.cb218e70d808 from=translated src=- shape=6b0e006c vocab=370a3316
-/
theorem tendstoLocallyUniformlyOn_regularizedZetaPartialSum_regularizedRiemannZeta :
    TendstoLocallyUniformlyOn (fun N s => regularizedZetaPartialSum s N)
      regularizedRiemannZeta atTop {s : ℂ | 0 < s.re} :=
  tendstoLocallyUniformlyOn_regularizedZetaPartialSum_limit.congr_right
    regularizedZetaLimit_eqOn_regularizedRiemannZeta

/-- The regularized truncation estimate includes `s=1`.
@isnad1 id=le.2h2v.s6.3a348c0fbda6 from=translated src=- shape=7b220764 vocab=f06492fc
-/
theorem norm_regularizedRiemannZeta_sub_partialSum_le (M : ℕ) (hM : 1 ≤ M)
    (s : ℂ) (hs : 0 < s.re) :
    ‖regularizedRiemannZeta s - regularizedZetaPartialSum s M‖ ≤
      ‖s - 1‖ * (‖s‖ / s.re) * (M : ℝ) ^ (-s.re) := by
  rw [← regularizedZetaLimit_eqOn_regularizedRiemannZeta hs]
  exact norm_regularizedZetaLimit_sub_partialSum_le M hM s hs

/-- Ordered convergence of the actual pole-corrected zeta sums away from `1`.
@isnad1 id=tendsto.2h1v.s5.1630a52002a2 from=translated src=- shape=1fa88813 vocab=801b4cb1
-/
theorem tendsto_zetaPolePartialSum_riemannZeta_of_re_pos (s : ℂ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (zetaPolePartialSum s) atTop (𝓝 (riemannZeta s)) := by
  have hR := tendsto_regularizedZetaPartialSum_limit s hs
  rw [regularizedZetaLimit_eqOn_regularizedRiemannZeta hs,
    regularizedRiemannZeta_apply_of_ne_one s hs1] at hR
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  simpa only [regularizedZetaPartialSum_eq_mul s hs1, mul_div_cancel_left₀ _ hne] using
    hR.div_const (s - 1)

/-- The sharp pole-corrected truncation error on `0 < s.re`, with the
principal pole excluded explicitly.
@isnad1 id=le.3h2v.s7.2c47a58ccdae from=translated src=- shape=53991c8a vocab=ed19306b
-/
theorem norm_riemannZeta_sub_sum_sub_pole_le_of_re_pos (M : ℕ) (hM : 1 ≤ M)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - (∑ n ∈ Ioc 0 M, (n : ℂ) ^ (-s)) -
        (M : ℂ) ^ (1 - s) / (s - 1)‖ ≤
      (‖s‖ / s.re) * (M : ℝ) ^ (-s.re) := by
  have heq : riemannZeta s - (∑ n ∈ Ioc 0 M, (n : ℂ) ^ (-s)) -
      (M : ℂ) ^ (1 - s) / (s - 1) = riemannZeta s - zetaPolePartialSum s M := by
    unfold zetaPolePartialSum
    ring
  rw [heq]
  apply le_of_tendsto (((tendsto_zetaPolePartialSum_riemannZeta_of_re_pos s hs hs1).sub
    tendsto_const_nhds).norm)
  filter_upwards [eventually_ge_atTop M] with N hMN
  exact norm_zetaPolePartialSum_sub_le_left M N hM hMN s hs hs1

end TwinPrime.Analytic
