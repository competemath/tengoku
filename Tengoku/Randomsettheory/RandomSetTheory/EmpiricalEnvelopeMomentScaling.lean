/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FiniteSupremumStrongMomentEfronStein
import Tengoku.Seed.Analysis.Convex.Integral
import Tengoku.Seed.Analysis.Convex.Mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Moment scaling for empirical replace-one envelopes

This file turns ordinary moments of nonnegative coordinate envelopes into
the two deterministic moment sums consumed by the finite Rio endpoint.

For the empirical normalization

`A_i^(n)(z) = A_i(z) / n`,

the centred replace-one proxy is exactly homogeneous:

`R_k(A_i^(n)) = n^(-k) R_k(A_i)`.

On a probability space, Jensen's inequality and

`(a + b)^k <= 2^(k - 1) (a^k + b^k)`

give the explicit raw-moment comparison

`R_k(A_i) <= 2^k ∫ A_i^k`.

Consequently, if all `n` coordinates satisfy
`∫ A_i^k <= K^k`, then

`sum_i R_k(A_i / n) <= 2^k K^k / n^(k - 1)`.

The constants are therefore `4` at order two and `2^q` at order `q`.
No random-set or model-specific object is used here.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Z : Type*} [MeasurableSpace Z] {nu : Measure Z}

/-- An envelope with the empirical-average normalization `1 / n`.-/
def empiricalNormalizedEnvelope (n : Nat) (A : Z → Real) (z : Z) : Real :=
  ((n : Real)⁻¹) * A z

omit [MeasurableSpace Z] in
/--
@isnad1 id=eq.0h4v.s5.7955493b038c from=translated src=- shape=5de57061 vocab=c9feab77
-/
@[simp]
theorem empiricalNormalizedEnvelope_apply
    (n : Nat) (A : Z → Real) (z : Z) :
    empiricalNormalizedEnvelope n A z = A z / (n : Real) := by
  simp only [empiricalNormalizedEnvelope, div_eq_mul_inv, mul_comm]

/--
@isnad1 id=memlp.1h5v.s6.3e0769e58737 from=translated src=- shape=dc528cbf vocab=d1336fb1
-/
theorem memLp_empiricalNormalizedEnvelope
    (n : Nat) (A : Z → Real) (q : ENNReal) (hA : MemLp A q nu) :
    MemLp (empiricalNormalizedEnvelope n A) q nu := by
  change MemLp (fun z ↦ ((n : Real)⁻¹) * A z) q nu
  exact hA.const_mul ((n : Real)⁻¹)

omit [MeasurableSpace Z] in
/--
@isnad1 id=le.1h4v.s5.76e049c4f0f2 from=translated src=- shape=e70b346e vocab=9646a616
-/
theorem empiricalNormalizedEnvelope_nonneg
    (n : Nat) (A : Z → Real)
    (hA : forall z, 0 ≤ A z) (z : Z) :
    0 ≤ empiricalNormalizedEnvelope n A z := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (hA z)

/-- The centred replace-one envelope is homogeneous under scalar
multiplication.  This identity does not require integrability: the Bochner
integral uses its canonical value on non-integrable functions and commutes
with scalar multiplication.
@isnad1 id=eq.0h5v.s5.970b76566306 from=translated src=- shape=5646c569 vocab=5bc4ed9f
-/
theorem replaceOneCenteredEnvelope_const_mul
    (c : Real) (A : Z → Real) (z : Z) :
    replaceOneCenteredEnvelope nu (fun z ↦ c * A z) z =
      c * replaceOneCenteredEnvelope nu A z := by
  simp only [replaceOneCenteredEnvelope, integral_const_mul]
  ring

/-- Exact degree-`k` homogeneity of the centred replace-one moment.
@isnad1 id=eq.0h5v.s6.461531de1530 from=translated src=- shape=3c17c805 vocab=5f00e5f0
-/
theorem replaceOneCenteredMoment_const_mul
    (c : Real) (A : Z → Real) (k : Nat) :
    replaceOneCenteredMoment nu (fun z ↦ c * A z) k =
      c ^ k * replaceOneCenteredMoment nu A k := by
  unfold replaceOneCenteredMoment
  simp_rw [replaceOneCenteredEnvelope_const_mul (nu := nu), mul_pow,
    integral_const_mul]

/-- Exact empirical normalization of a centred replace-one moment.
@isnad1 id=eq.0h5v.s5.551ac61550d8 from=translated src=- shape=c296a304 vocab=6a850085
-/
theorem replaceOneCenteredMoment_empiricalNormalizedEnvelope
    (n k : Nat) (A : Z → Real) :
    replaceOneCenteredMoment nu (empiricalNormalizedEnvelope n A) k =
      ((n : Real)⁻¹) ^ k * replaceOneCenteredMoment nu A k := by
  change replaceOneCenteredMoment nu (fun z ↦ ((n : Real)⁻¹) * A z) k = _
  exact replaceOneCenteredMoment_const_mul (nu := nu) ((n : Real)⁻¹) A k

/-- Denominator form of exact empirical homogeneity.
@isnad1 id=eq.0h5v.s5.75fe807ff9ad from=translated src=- shape=23835413 vocab=45ee0639
-/
theorem replaceOneCenteredMoment_empiricalNormalizedEnvelope_div
    (n k : Nat) (A : Z → Real) :
    replaceOneCenteredMoment nu (empiricalNormalizedEnvelope n A) k =
      replaceOneCenteredMoment nu A k / (n : Real) ^ k := by
  rw [replaceOneCenteredMoment_empiricalNormalizedEnvelope,
    div_eq_mul_inv, inv_pow]
  ring

/-- A nonnegative envelope's centred replace-one moment is at most `2^k`
times its raw `k`-th moment.  The sole loss is the elementary two-term
power inequality; Jensen controls the constant mean term.
@isnad1 id=le.3h4v.s7.55a6695bae3c from=translated src=- shape=36cfe55c vocab=c0374131
-/
theorem replaceOneCenteredMoment_le_two_pow_mul_integral_pow
    [IsProbabilityMeasure nu]
    (A : Z → Real) (k : Nat) (hk : 1 ≤ k)
    (hAk : MemLp A k nu) (hA : forall z, 0 ≤ A z) :
    replaceOneCenteredMoment nu A k ≤
      (2 : Real) ^ k * ∫ z, A z ^ k ∂nu := by
  have hone : (1 : ENNReal) ≤ (k : ENNReal) := by
    exact_mod_cast hk
  have hAint : Integrable A nu :=
    (hAk.mono_exponent hone).integrable (by norm_num)
  have hpowInt : Integrable (fun z ↦ A z ^ k) nu := by
    have hnorm := hAk.integrable_norm_pow'
    convert hnorm using 1
    funext z
    rw [Real.norm_eq_abs, abs_of_nonneg (hA z)]
  have hmeanNonneg : 0 ≤ ∫ z, A z ∂nu := integral_nonneg hA
  have hJensen : (∫ z, A z ∂nu) ^ k ≤ ∫ z, A z ^ k ∂nu := by
    have h := (convexOn_pow k).map_integral_le
      (continuousOn_pow k) isClosed_Ici (ae_of_all nu hA)
      hAint hpowInt
    simpa only [Function.comp_apply] using h
  have hleft : Integrable
      (fun z ↦ replaceOneCenteredEnvelope nu A z ^ k) nu :=
    integrable_pow_replaceOneCenteredEnvelope A k k le_rfl hAk hA
  have hright : Integrable (fun z ↦
      (2 : Real) ^ (k - 1) *
        (A z ^ k + (∫ z', A z' ∂nu) ^ k)) nu :=
    (hpowInt.add (integrable_const _)).const_mul _
  unfold replaceOneCenteredMoment
  calc
    (∫ z, replaceOneCenteredEnvelope nu A z ^ k ∂nu) ≤
        ∫ z, (2 : Real) ^ (k - 1) *
          (A z ^ k + (∫ z', A z' ∂nu) ^ k) ∂nu := by
      apply integral_mono hleft hright
      intro z
      exact add_pow_le (hA z) hmeanNonneg k
    _ = (2 : Real) ^ (k - 1) *
        ((∫ z, A z ^ k ∂nu) + (∫ z, A z ∂nu) ^ k) := by
      rw [integral_const_mul,
        integral_add hpowInt (integrable_const _), integral_const,
        probReal_univ, one_smul]
    _ ≤ (2 : Real) ^ (k - 1) *
        ((∫ z, A z ^ k ∂nu) + (∫ z, A z ^ k ∂nu)) := by
      gcongr
    _ = (2 : Real) ^ k * ∫ z, A z ^ k ∂nu := by
      have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel hk
      calc
        (2 : Real) ^ (k - 1) *
            ((∫ z, A z ^ k ∂nu) + (∫ z, A z ^ k ∂nu)) =
            ((2 : Real) ^ (k - 1) * 2) * ∫ z, A z ^ k ∂nu := by
          ring
        _ = (2 : Real) ^ k * ∫ z, A z ^ k ∂nu := by
          rw [← pow_succ, hkpred]

/-- General aggregate scaling lemma.  For `n` nonnegative coordinate
envelopes, a uniform raw `k`-th moment bound `K^k` gives the exact rate
`2^k K^k / n^(k-1)` for the sum of centred replace-one proxies after
empirical normalization.
@isnad1 id=le.5h6v.s8.175a2d227489 from=translated src=- shape=1d17118c vocab=118f7fdd
-/
theorem sum_replaceOneCenteredMoment_empiricalNormalizedEnvelope_le
    [IsProbabilityMeasure nu]
    (n k : Nat) (hn : 0 < n) (hk : 1 ≤ k)
    (A : Fin n → Z → Real) (K : Real)
    (hAk : forall i, MemLp (A i) k nu)
    (hA : forall i z, 0 ≤ A i z)
    (hmoment : forall i, (∫ z, A i z ^ k ∂nu) ≤ K ^ k) :
    (∑ i : Fin n,
        replaceOneCenteredMoment nu
          (empiricalNormalizedEnvelope n (A i)) k) ≤
      (2 : Real) ^ k * K ^ k / (n : Real) ^ (k - 1) := by
  have hnReal : (n : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    (∑ i : Fin n,
        replaceOneCenteredMoment nu
          (empiricalNormalizedEnvelope n (A i)) k) =
        ∑ i : Fin n, ((n : Real)⁻¹) ^ k *
          replaceOneCenteredMoment nu (A i) k := by
      apply Finset.sum_congr rfl
      intro i _
      exact replaceOneCenteredMoment_empiricalNormalizedEnvelope
        (nu := nu) n k (A i)
    _ ≤ ∑ _i : Fin n, ((n : Real)⁻¹) ^ k *
        ((2 : Real) ^ k * K ^ k) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (inv_nonneg.mpr
        (Nat.cast_nonneg n)) k)
      exact (replaceOneCenteredMoment_le_two_pow_mul_integral_pow
        (nu := nu) (A i) k hk (hAk i) (hA i)).trans
          (mul_le_mul_of_nonneg_left (hmoment i)
            (pow_nonneg (by norm_num : (0 : Real) ≤ 2) k))
    _ = (n : Real) * (((n : Real)⁻¹) ^ k *
        ((2 : Real) ^ k * K ^ k)) := by
      simp
    _ = (2 : Real) ^ k * K ^ k / (n : Real) ^ (k - 1) := by
      have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel hk
      have hscale : (n : Real) * ((n : Real)⁻¹) ^ k =
          ((n : Real)⁻¹) ^ (k - 1) := by
        calc
          (n : Real) * ((n : Real)⁻¹) ^ k =
              (n : Real) * ((n : Real)⁻¹) ^ (k - 1 + 1) := by
            rw [hkpred]
          _ = (n : Real) *
              (((n : Real)⁻¹) ^ (k - 1) * (n : Real)⁻¹) := by
            rw [pow_succ]
          _ = ((n : Real) * (n : Real)⁻¹) *
              ((n : Real)⁻¹) ^ (k - 1) := by ring
          _ = ((n : Real)⁻¹) ^ (k - 1) := by
            rw [mul_inv_cancel₀ hnReal, one_mul]
      rw [← mul_assoc, hscale, div_eq_mul_inv, inv_pow]
      ring

/-- Order-two specialization: the aggregate normalized proxy is at most
`4 K₂² / n`.
@isnad1 id=le.5h6v.s8.89ea9242acce from=translated src=- shape=0c704aba vocab=64cdecba
-/
theorem sum_replaceOneCenteredMoment_empiricalNormalizedEnvelope_two_le
    [IsProbabilityMeasure nu]
    (n q : Nat) (hn : 0 < n) (hq : 2 ≤ q)
    (A : Fin n → Z → Real) (Ktwo : Real)
    (hAq : forall i, MemLp (A i) q nu)
    (hA : forall i z, 0 ≤ A i z)
    (hsecond : forall i, (∫ z, A i z ^ 2 ∂nu) ≤ Ktwo ^ 2) :
    (∑ i : Fin n,
        replaceOneCenteredMoment nu
          (empiricalNormalizedEnvelope n (A i)) 2) ≤
      4 * Ktwo ^ 2 / (n : Real) := by
  have hA2 : forall i, MemLp (A i) 2 nu := by
    intro i
    exact (hAq i).mono_exponent (by exact_mod_cast hq)
  have h := sum_replaceOneCenteredMoment_empiricalNormalizedEnvelope_le
    (nu := nu) n 2 hn (by norm_num) A Ktwo hA2 hA hsecond
  norm_num at h ⊢
  exact h

/-- Order-`q` specialization: the aggregate normalized proxy is at most
`2^q K_q^q / n^(q-1)`, i.e. `2^q K_q^q n^(1-q)`.
@isnad1 id=le.5h6v.s8.175a2d227489 from=translated src=- shape=1d17118c vocab=118f7fdd
-/
theorem sum_replaceOneCenteredMoment_empiricalNormalizedEnvelope_q_le
    [IsProbabilityMeasure nu]
    (n q : Nat) (hn : 0 < n) (hq : 1 ≤ q)
    (A : Fin n → Z → Real) (Kq : Real)
    (hAq : forall i, MemLp (A i) q nu)
    (hA : forall i z, 0 ≤ A i z)
    (hqmoment : forall i, (∫ z, A i z ^ q ∂nu) ≤ Kq ^ q) :
    (∑ i : Fin n,
        replaceOneCenteredMoment nu
          (empiricalNormalizedEnvelope n (A i)) q) ≤
      (2 : Real) ^ q * Kq ^ q / (n : Real) ^ (q - 1) := by
  exact sum_replaceOneCenteredMoment_empiricalNormalizedEnvelope_le
    n q hn hq A Kq hAq hA hqmoment

end ProbabilityTheory
