import Tengoku.Twinprime.TwinPrime.Analytic.PowerDirichletTail
import Tengoku.Seed.Analysis.Complex.LocallyUniformLimit
import Tengoku.Seed.Analysis.Complex.Convex
import Tengoku.Seed.Analysis.Analytic.Uniqueness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Holomorphic ordered Dirichlet limits from a power bound

The proved finite tail estimate implies locally uniform ordered convergence
on `α < Re(s)`. Finite partial sums are entire, so this limit is holomorphic.
An identity theorem identifies it with a separately given holomorphic
continuation when they agree farther to the right. No unconditional
summability is asserted in the enlarged half-plane.
-/

noncomputable section

open Finset Filter
open scoped Topology

namespace TwinPrime.Analytic

/-- Defined independently of the exponent and the bounds used to prove convergence.-/
def powerDirichletLimit (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  limUnder atTop (powerDirichletPartialSum a s)

/--
@isnad1 id=tendsto.4h4v.s6.e11fc0f5235e from=translated src=- shape=7e15d961 vocab=0a70e55d
-/
theorem tendsto_powerDirichletPartialSum_limit (α : ℝ) (hα : 0 ≤ α)
    (a : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ t : ℕ, ‖∑ n ∈ Ioc 0 t, a n‖ ≤ C * (t : ℝ) ^ α)
    (s : ℂ) (hs : α < s.re) :
    Tendsto (powerDirichletPartialSum a s) atTop (𝓝 (powerDirichletLimit a s)) :=
  (cauchySeq_powerDirichletPartialSum α hα s hs a C hC hA).tendsto_limUnder

/--
@isnad1 id=le.5h5v.s7.e4ff188b0eec from=translated src=- shape=bb61567f vocab=0e55ea9e
-/
theorem norm_powerDirichletLimit_sub_partialSum_le (α : ℝ) (hα : 0 ≤ α)
    (a : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ t : ℕ, ‖∑ n ∈ Ioc 0 t, a n‖ ≤ C * (t : ℝ) ^ α)
    (M : ℕ) (hM : 1 ≤ M) (s : ℂ) (hs : α < s.re) :
    ‖powerDirichletLimit a s - powerDirichletPartialSum a s M‖ ≤
      (2 * C) * (M : ℝ) ^ (α - s.re) * (1 + ‖s‖ / (s.re - α)) := by
  have hL := tendsto_powerDirichletPartialSum_limit α hα a C hC hA s hs
  apply le_of_tendsto ((hL.sub tendsto_const_nhds).norm)
  filter_upwards [eventually_ge_atTop M] with N hMN
  rw [powerDirichletPartialSum_sub a s hMN]
  exact norm_sum_Ioc_cpow_mul_le_of_power_partial_sums M N hM hMN α hα s hs a C hC hA

/-- The exponent gap `δ` makes a common quantitative tail bound available.
@isnad1 id=le.7h7v.s7.24efa2f6827e from=translated src=- shape=c01a2a47 vocab=a1888685
-/
theorem norm_powerDirichletLimit_sub_partialSum_le_uniform (α : ℝ) (hα : 0 ≤ α)
    (a : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ t : ℕ, ‖∑ n ∈ Ioc 0 t, a n‖ ≤ C * (t : ℝ) ^ α)
    (M : ℕ) (hM : 1 ≤ M) (δ H : ℝ) (hδ : 0 < δ)
    (s : ℂ) (hσ : α + δ ≤ s.re) (hH : ‖s‖ ≤ H) :
    ‖powerDirichletLimit a s - powerDirichletPartialSum a s M‖ ≤
      (2 * C) * (M : ℝ) ^ (-δ) * (1 + H / δ) := by
  have hs : α < s.re := by linarith
  have hgap : δ ≤ s.re - α := by linarith
  have hH0 : 0 ≤ H := (norm_nonneg s).trans hH
  apply (norm_powerDirichletLimit_sub_partialSum_le α hα a C hC hA M hM s hs).trans
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * C)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM) (by linarith)
  · exact add_le_add le_rfl (div_le_div₀ hH0 hH hδ hgap)
  · positivity
  · positivity

/--
@isnad1 id=tendstou.4h5v.s7.91d55d460d53 from=translated src=- shape=b937949a vocab=b581106a
-/
theorem tendstoUniformlyOn_powerDirichletPartialSum_limit (α : ℝ) (hα : 0 ≤ α)
    (a : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ t : ℕ, ‖∑ n ∈ Ioc 0 t, a n‖ ≤ C * (t : ℝ) ^ α)
    (δ H : ℝ) (hδ : 0 < δ) :
    TendstoUniformlyOn (fun N s => powerDirichletPartialSum a s N)
      (powerDirichletLimit a) atTop {s : ℂ | α + δ ≤ s.re ∧ ‖s‖ ≤ H} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (-δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun N : ℕ => (2 * C) * (N : ℝ) ^ (-δ) * (1 + H / δ))
      atTop (𝓝 0) := by
    simpa using (hp.const_mul (2 * C)).mul_const (1 + H / δ)
  filter_upwards [eventually_ge_atTop 1, hb.eventually (gt_mem_nhds hε)] with N hN hbN
  intro s hs
  rw [dist_eq_norm]
  exact (norm_powerDirichletLimit_sub_partialSum_le_uniform α hα a C hC hA N hN
    δ H hδ s hs.1 hs.2).trans_lt hbN

/--
@isnad1 id=tendstol.3h3v.s7.e8753036db75 from=translated src=- shape=2c64eb7f vocab=34207284
-/
theorem tendstoLocallyUniformlyOn_powerDirichletPartialSum_limit (α : ℝ) (hα : 0 ≤ α)
    (a : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ t : ℕ, ‖∑ n ∈ Ioc 0 t, a n‖ ≤ C * (t : ℝ) ^ α) :
    TendstoLocallyUniformlyOn (fun N s => powerDirichletPartialSum a s N)
      (powerDirichletLimit a) atTop {s : ℂ | α < s.re} := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  change α < z.re at hz
  let δ : ℝ := (z.re - α) / 2
  let H : ℝ := ‖z‖ + 1
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hlo : {s : ℂ | α + δ < s.re} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp [δ]; linarith)
  have hhi : {s : ℂ | ‖s‖ < H} ∈ 𝓝 z :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by dsimp [H]; linarith)
  refine ⟨{s : ℂ | α + δ ≤ s.re ∧ ‖s‖ ≤ H}, mem_nhdsWithin_of_mem_nhds ?_,
    tendstoUniformlyOn_powerDirichletPartialSum_limit α hα a C hC hA δ H hδ⟩
  exact mem_of_superset (inter_mem hlo hhi) (fun s hs => ⟨hs.1.le, hs.2.le⟩)

/--
@isnad1 id=differen.0h2v.s6.fee01e9d81c6 from=translated src=- shape=a4babc60 vocab=c745867c
-/
theorem differentiable_powerDirichletPartialSum (a : ℕ → ℂ) (N : ℕ) :
    Differentiable ℂ (fun s => powerDirichletPartialSum a s N) := by
  unfold powerDirichletPartialSum
  apply Differentiable.fun_sum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Ioc.mp hn).1)
  exact (differentiable_id.neg.const_cpow (Or.inl hn0)).mul_const (a n)

/--
@isnad1 id=differen.3h3v.s7.749c1b53ff46 from=translated src=- shape=57f811c3 vocab=25076f85
-/
theorem differentiableOn_powerDirichletLimit (α : ℝ) (hα : 0 ≤ α)
    (a : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ t : ℕ, ‖∑ n ∈ Ioc 0 t, a n‖ ≤ C * (t : ℝ) ^ α) :
    DifferentiableOn ℂ (powerDirichletLimit a) {s : ℂ | α < s.re} :=
  (tendstoLocallyUniformlyOn_powerDirichletPartialSum_limit α hα a C hC hA).differentiableOn
    (Eventually.of_forall (fun N => (differentiable_powerDirichletPartialSum a N).differentiableOn))
    (isOpen_lt continuous_const Complex.continuous_re)

/-- Agreement on a farther right half-plane identifies the holomorphic limit.
@isnad1 id=eqon.5h4v.s7.9d09e469f492 from=translated src=- shape=ea0b5978 vocab=b7289ea6
-/
theorem powerDirichletLimit_eqOn_of_eqOn_right (α : ℝ) (hα : 0 ≤ α)
    (a : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ t : ℕ, ‖∑ n ∈ Ioc 0 t, a n‖ ≤ C * (t : ℝ) ^ α)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f {s : ℂ | α < s.re})
    (hEq : Set.EqOn (powerDirichletLimit a) f {s : ℂ | max α 1 < s.re}) :
    Set.EqOn (powerDirichletLimit a) f {s : ℂ | α < s.re} := by
  have hopen : IsOpen {s : ℂ | α < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hlim := (differentiableOn_powerDirichletLimit α hα a C hC hA).analyticOnNhd hopen
  apply hlim.eqOn_of_preconnected_of_eventuallyEq (hf.analyticOnNhd hopen)
    (convex_halfSpace_re_gt α).isPreconnected (z₀ := ((max α 1 + 1 : ℝ) : ℂ))
      (by simp only [Set.mem_ofPred_eq, Complex.ofReal_re]; have := le_max_left α 1; linarith)
  have hright : {s : ℂ | max α 1 < s.re} ∈ 𝓝 ((max α 1 + 1 : ℝ) : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simp only [Set.mem_ofPred_eq, Complex.ofReal_re]; exact lt_add_one _)
  filter_upwards [hright] with s hs
  exact hEq hs

/--
@isnad1 id=eqon.5h4v.s7.c02debc2b337 from=translated src=- shape=e42a9e7e vocab=16198c01
-/
theorem powerDirichletLimit_eqOn_of_tendsto_right (α : ℝ) (hα : 0 ≤ α)
    (a : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ t : ℕ, ‖∑ n ∈ Ioc 0 t, a n‖ ≤ C * (t : ℝ) ^ α)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f {s : ℂ | α < s.re})
    (hT : ∀ s : ℂ, max α 1 < s.re →
      Tendsto (powerDirichletPartialSum a s) atTop (𝓝 (f s))) :
    Set.EqOn (powerDirichletLimit a) f {s : ℂ | α < s.re} := by
  apply powerDirichletLimit_eqOn_of_eqOn_right α hα a C hC hA f hf
  intro s hs
  exact tendsto_nhds_unique (tendsto_powerDirichletPartialSum_limit α hα a C hC hA s
    ((le_max_left α 1).trans_lt hs)) (hT s hs)

/-- Absolute summability, where separately available, identifies the ordered sums.
@isnad1 id=tendsto.1h2v.s5.a3e971396678 from=translated src=- shape=a6b408c8 vocab=ad9a454c
-/
theorem tendsto_powerDirichletPartialSum_LSeries (a : ℕ → ℂ) (s : ℂ)
    (hS : LSeriesSummable a s) :
    Tendsto (powerDirichletPartialSum a s) atTop (𝓝 (LSeries a s)) := by
  have heq (N : ℕ) : (∑ n ∈ range (N + 1), LSeries.term a s n) =
      powerDirichletPartialSum a s N := by
    have hset : range (N + 1) = insert 0 (Ioc 0 N) := by
      ext n
      simp only [mem_range, mem_insert, mem_Ioc]
      omega
    rw [hset, sum_insert (by simp), LSeries.term_zero, zero_add]
    apply sum_congr rfl
    intro n hn
    rw [LSeries.term_of_ne_zero (Nat.ne_of_gt (mem_Ioc.mp hn).1),
      div_eq_mul_inv, ← Complex.cpow_neg]
    ring
  exact (hS.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr heq

/--
@isnad1 id=eqon.6h4v.s7.357d1b6bf22a from=translated src=- shape=3b2ab65e vocab=361e4318
-/
theorem powerDirichletLimit_eqOn_of_LSeries_right (α : ℝ) (hα : 0 ≤ α)
    (a : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ t : ℕ, ‖∑ n ∈ Ioc 0 t, a n‖ ≤ C * (t : ℝ) ^ α)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f {s : ℂ | α < s.re})
    (hS : ∀ s : ℂ, max α 1 < s.re → LSeriesSummable a s)
    (hEq : Set.EqOn (LSeries a) f {s : ℂ | max α 1 < s.re}) :
    Set.EqOn (powerDirichletLimit a) f {s : ℂ | α < s.re} := by
  apply powerDirichletLimit_eqOn_of_tendsto_right α hα a C hC hA f hf
  intro s hs
  rw [← hEq hs]
  exact tendsto_powerDirichletPartialSum_LSeries a s (hS s hs)

/-- Quantitative truncation after identification with an actual continuation.
@isnad1 id=le.6h6v.s7.3a9942751e93 from=translated src=- shape=935fa031 vocab=e03ddefa
-/
theorem norm_sub_powerDirichletPartialSum_le_of_eqOn (α : ℝ) (hα : 0 ≤ α)
    (a : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ t : ℕ, ‖∑ n ∈ Ioc 0 t, a n‖ ≤ C * (t : ℝ) ^ α)
    (f : ℂ → ℂ) (hEq : Set.EqOn (powerDirichletLimit a) f {s : ℂ | α < s.re})
    (M : ℕ) (hM : 1 ≤ M) (s : ℂ) (hs : α < s.re) :
    ‖f s - powerDirichletPartialSum a s M‖ ≤
      (2 * C) * (M : ℝ) ^ (α - s.re) * (1 + ‖s‖ / (s.re - α)) := by
  rw [← hEq hs]
  exact norm_powerDirichletLimit_sub_partialSum_le α hα a C hC hA M hM s hs

end TwinPrime.Analytic
