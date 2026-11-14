import Tengoku.Twinprime.TwinPrime.Analytic.CharacterLogInterval
import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Asymptotics
import Tengoku.Seed.NumberTheory.LSeries.DirichletContinuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite Dirichlet-weighted primitive-character tails

Complex power variation and finite Abel summation transfer the proved
Pólya--Vinogradov bound to tails in the half-plane `0 < s.re`.
These are bounds for ordered finite sums, with no assertion of absolute
or unconditional summability in that half-plane.
-/

noncomputable section

open Finset MeasureTheory Filter
open scoped Interval Topology

namespace TwinPrime.Analytic

/-- The variation of a complex Dirichlet weight is controlled by the
decrease of its real absolute-value weight.
@isnad1 id=le.3h3v.s7.12fc233f35d7 from=translated src=- shape=ccc73028 vocab=363b6b69
-/
theorem norm_cpow_neg_sub_le (s : ℂ) (hs : 0 < s.re)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖(b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ ≤
      (‖s‖ / s.re) * (a ^ (-s.re) - b ^ (-s.re)) := by
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (Complex.ne_zero_of_re_pos hs)
  have hd (x : ℝ) (hx : a ≤ x) :
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
        ((-s) * (x : ℂ) ^ (-s - 1)) x :=
    hasDerivAt_ofReal_cpow_const (ha.trans_le hx).ne' hs0
  have hz : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    exact ha.not_ge h.1
  have hi : IntervalIntegrable (fun x : ℝ => ‖s‖ * x ^ (-s.re - 1)) volume a b :=
    (intervalIntegral.intervalIntegrable_rpow (Or.inr hz)).const_mul ‖s‖
  have hbound := norm_sub_le_integral_of_norm_deriv_le_of_le hab
    (show ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Set.Icc a b) from
      fun x hx => (hd x hx.1).continuousAt.continuousWithinAt)
    (show DifferentiableOn ℝ (fun x : ℝ => (x : ℂ) ^ (-s)) (Set.Ioo a b) from
      fun x hx => (hd x hx.1.le).differentiableAt.differentiableWithinAt)
    (B := fun x : ℝ => ‖s‖ * x ^ (-s.re - 1))
    (Filter.Eventually.of_forall (fun x hx => by
      rw [(hd x hx.1.le).deriv, norm_mul, norm_neg,
        Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans hx.1)]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, le_refl])) hi
  apply hbound.trans_eq
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨by linarith, hz⟩)]
  have he : -s.re - 1 + 1 = -s.re := by ring
  rw [he]
  field_simp
  ring

/-- Abel summation with a bound for each partial sum anchored at `M`.
The right endpoint may coincide with the left endpoint.
@isnad1 id=le.5h5v.s7.a06fbf9f5a2f from=translated src=- shape=5f9b9c63 vocab=aca5868f
-/
theorem norm_sum_Ioc_cpow_mul_le_of_partial_sums (M N : ℕ)
    (hM : 1 ≤ M) (hMN : M ≤ N) (s : ℂ) (hs : 0 < s.re)
    (e : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ t ∈ Icc M N, ‖∑ n ∈ Ioc M t, e n‖ ≤ C) :
    ‖∑ n ∈ Ioc M N, (n : ℂ) ^ (-s) * e n‖ ≤
      C * (M : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hN0 := hM0.trans_le hMN'
  have hratio : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have hvar : (∑ t ∈ Ico M N,
      ‖((t + 1 : ℕ) : ℂ) ^ (-s) - (t : ℂ) ^ (-s)‖) ≤
      (‖s‖ / s.re) * ((M : ℝ) ^ (-s.re) - (N : ℝ) ^ (-s.re)) := by
    calc
      _ ≤ ∑ t ∈ Ico M N, (‖s‖ / s.re) *
          ((t : ℝ) ^ (-s.re) - ((t + 1 : ℕ) : ℝ) ^ (-s.re)) := by
        apply sum_le_sum
        intro t ht
        have ht0 : (0 : ℝ) < t := hM0.trans_le (by exact_mod_cast (mem_Ico.mp ht).1)
        exact norm_cpow_neg_sub_le s hs ht0 (by exact_mod_cast Nat.le_succ t)
      _ = _ := by
        rw [← mul_sum]
        congr 1
        simpa only [neg_sub_neg] using
          (sum_Ico_sub (fun t : ℕ => -(t : ℝ) ^ (-s.re)) hMN)
  rw [discrete_abel_Ioc_complex M N hMN (fun n => (n : ℂ) ^ (-s)) e]
  calc
    _ ≤ ‖(N : ℂ) ^ (-s) * (∑ n ∈ Ioc M N, e n)‖ +
        ‖∑ t ∈ Ico M N,
          (((t + 1 : ℕ) : ℂ) ^ (-s) - (t : ℂ) ^ (-s)) *
            (∑ n ∈ Ioc M t, e n)‖ := norm_sub_le _ _
    _ ≤ (N : ℝ) ^ (-s.re) * C +
        (∑ t ∈ Ico M N,
          ‖((t + 1 : ℕ) : ℂ) ^ (-s) - (t : ℂ) ^ (-s)‖) * C := by
      apply add_le_add
      · rw [norm_mul, ← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos hN0, Complex.neg_re]
        exact mul_le_mul_of_nonneg_left (hE N (mem_Icc.mpr ⟨hMN, le_rfl⟩))
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      · apply (norm_sum_le _ _).trans
        rw [sum_mul]
        apply sum_le_sum
        intro t ht
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (hE t (mem_Icc.mpr ⟨(mem_Ico.mp ht).1, (mem_Ico.mp ht).2.le⟩))
          (norm_nonneg _)
    _ ≤ (N : ℝ) ^ (-s.re) * C +
        ((‖s‖ / s.re) * ((M : ℝ) ^ (-s.re) - (N : ℝ) ^ (-s.re))) * C :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hvar hC)
    _ ≤ _ := by
      have hpow := Real.rpow_le_rpow_of_nonpos hM0 hMN' (neg_nonpos.mpr hs.le)
      have hNpow := Real.rpow_nonneg (Nat.cast_nonneg N) (-s.re)
      nlinarith [mul_nonneg hratio hNpow]

/-- A primitive-character Dirichlet tail bound valid on `0 < s.re`.
This concerns a finite ordered sum and does not assert absolute summability.
@isnad1 id=le.5h5v.s7.99b8c8fd4345 from=translated src=- shape=54031fea vocab=eb7ea704
-/
theorem norm_sum_primitive_character_dirichlet_Ioc_le {q : ℕ}
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (M N : ℕ) (hM : 1 ≤ M) (hMN : M ≤ N) (s : ℂ) (hs : 0 < s.re) :
    ‖∑ n ∈ Ioc M N, (n : ℂ) ^ (-s) * χ (n : ZMod q)‖ ≤
      (Real.sqrt q * (1 + Real.log q)) * (M : ℝ) ^ (-s.re) *
        (1 + ‖s‖ / s.re) := by
  have hC : 0 ≤ Real.sqrt (q : ℝ) * (1 + Real.log q) := by
    have := Real.log_natCast_nonneg q
    positivity
  apply norm_sum_Ioc_cpow_mul_le_of_partial_sums M N hM hMN s hs
    (fun n => χ (n : ZMod q)) _ hC
  intro t _
  have hI : Ioc M t = Ico (M + 1) (t + 1) := by
    ext n
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hI]
  exact norm_sum_primitive_character_Ico_le hq χ hχ (M + 1) (t + 1)

/-- Ordered Dirichlet partial sums, with the zero coefficient omitted.-/
def characterDirichletPartialSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s) * χ (n : ZMod q)

/--
@isnad1 id=eq.1h5v.s7.041c825c550b from=translated src=- shape=e5e5aaf2 vocab=0274a890
-/
theorem characterDirichletPartialSum_sub {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : ℂ) {M N : ℕ} (hMN : M ≤ N) :
    characterDirichletPartialSum χ s N - characterDirichletPartialSum χ s M =
      ∑ n ∈ Ioc M N, (n : ℂ) ^ (-s) * χ (n : ZMod q) := by
  have h := sum_Ioc_consecutive (fun n => (n : ℂ) ^ (-s) * χ (n : ZMod q))
    (Nat.zero_le M) hMN
  unfold characterDirichletPartialSum
  rw [← h]
  ring

/-- Cauchy convergence of the ordered partial sums on the positive half-plane.
@isnad1 id=cauchyse.3h3v.s6.cdeedccc10c1 from=translated src=- shape=a9ae892a vocab=4d7b0abc
-/
theorem cauchySeq_characterDirichletPartialSum {q : ℕ}
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (s : ℂ) (hs : 0 < s.re) : CauchySeq (characterDirichletPartialSum χ s) := by
  apply (cauchySeq_shift 1).mp
  apply cauchySeq_of_le_tendsto_0'
    (fun n : ℕ => (Real.sqrt q * (1 + Real.log q)) *
      ((n + 1 : ℕ) : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re))
  · intro n m hnm
    rw [dist_comm, dist_eq_norm, characterDirichletPartialSum_sub χ s (by omega)]
    exact norm_sum_primitive_character_dirichlet_Ioc_le hq χ hχ
      (n + 1) (m + 1) (by omega) (by omega) s hs
  · have hp : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-s.re)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hs).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    simpa using (hp.const_mul (Real.sqrt q * (1 + Real.log q))).mul_const
      (1 + ‖s‖ / s.re)

/-- An ordered limit exists, with the same quantitative bound on every
tail starting at a positive natural endpoint.
@isnad1 id=ex.3h3v.s7.3b0ccfc2af16 from=translated src=- shape=0ce14fbb vocab=2bc3e270
-/
theorem exists_characterDirichletPartialSum_limit {q : ℕ}
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (s : ℂ) (hs : 0 < s.re) :
    ∃ L : ℂ, Tendsto (characterDirichletPartialSum χ s) atTop (𝓝 L) ∧
      ∀ M : ℕ, 1 ≤ M →
        ‖L - characterDirichletPartialSum χ s M‖ ≤
          (Real.sqrt q * (1 + Real.log q)) * (M : ℝ) ^ (-s.re) *
            (1 + ‖s‖ / s.re) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_characterDirichletPartialSum hq χ hχ s hs)
  refine ⟨L, hL, ?_⟩
  intro M hM
  apply le_of_tendsto ((hL.sub tendsto_const_nhds).norm)
  filter_upwards [eventually_ge_atTop M] with N hMN
  rw [characterDirichletPartialSum_sub χ s hMN]
  exact norm_sum_primitive_character_dirichlet_Ioc_le hq χ hχ M N hM hMN s hs

/-- On the absolutely convergent half-plane the ordered limit agrees with
Mathlib's analytically continued Dirichlet L-function.
@isnad1 id=tendsto.1h3v.s6.2a7dcd7465cd from=translated src=- shape=dd07408e vocab=0730417b
-/
theorem tendsto_characterDirichletPartialSum_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) :
    Tendsto (characterDirichletPartialSum χ s) atTop
      (𝓝 (DirichletCharacter.LFunction χ s)) := by
  have hS : LSeriesSummable (fun n : ℕ => χ (n : ZMod q)) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun _ _ => χ.norm_le_one _) hs
  have heq (N : ℕ) :
      (∑ n ∈ range (N + 1), LSeries.term (fun n : ℕ => χ (n : ZMod q)) s n) =
        characterDirichletPartialSum χ s N := by
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
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact (hS.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr heq

/-- A quantitative truncation of `LFunction` on `1 < s.re`, with conductor
dependence supplied by the proved primitive-character interval estimate.
@isnad1 id=le.4h4v.s7.26c7451eef27 from=translated src=- shape=869f3f7d vocab=edad62a4
-/
theorem norm_LFunction_sub_characterDirichletPartialSum_le {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (M : ℕ) (hM : 1 ≤ M) (s : ℂ) (hs : 1 < s.re) :
    ‖DirichletCharacter.LFunction χ s - characterDirichletPartialSum χ s M‖ ≤
      (Real.sqrt q * (1 + Real.log q)) * (M : ℝ) ^ (-s.re) *
        (1 + ‖s‖ / s.re) := by
  have hL := tendsto_characterDirichletPartialSum_LFunction χ s hs
  apply le_of_tendsto ((hL.sub tendsto_const_nhds).norm)
  filter_upwards [eventually_ge_atTop M] with N hMN
  rw [characterDirichletPartialSum_sub χ s hMN]
  exact norm_sum_primitive_character_dirichlet_Ioc_le hq χ hχ M N hM hMN s
    (lt_trans zero_lt_one hs)

end TwinPrime.Analytic
