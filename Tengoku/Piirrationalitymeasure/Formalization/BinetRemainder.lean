import Tengoku.Piirrationalitymeasure.Formalization.BinetMoments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Signed finite expansions of the Binet kernel with a strict next-term bound. -/

namespace PiIrrationality

noncomputable def binetKernelApprox (u : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.range N, (-1 : ℝ) ^ m * positiveBernoulliCoeff (m + 1) * u ^ (2 * m + 1)

/--
@isnad1 id=eq.0h2v.s7.eb9964498667 from=translated src=- shape=666c52b9 vocab=bb96d899
-/
theorem binetKernelApprox_eq (u : ℝ) (N : ℕ) :
    binetKernelApprox u N = ∑ m ∈ Finset.range N,
      (bernoulli (2 * (m + 1)) : ℝ) / ((2 * (m + 1)).factorial : ℝ) * u ^ (2 * m + 1) := by
  unfold binetKernelApprox
  simp_rw [signed_positiveBernoulliCoeff]

noncomputable def binetRemainderTerm (u : ℝ) (N n : ℕ) : ℝ :=
  2 * u ^ (2 * N + 1) / (binetPole n ^ (2 * N) * (u ^ 2 + binetPole n ^ 2))

/--
@isnad1 id=lt.1h3v.s4.d41fd238460c from=translated src=- shape=f4002352 vocab=f8391182
-/
theorem binetRemainderTerm_pos {u : ℝ} (hu : 0 < u) (N n : ℕ) :
    0 < binetRemainderTerm u N n := by
  have hp := binetPole_pos n
  unfold binetRemainderTerm
  positivity

/--
@isnad1 id=lt.1h3v.s6.4fb930c0b085 from=translated src=- shape=1c257935 vocab=c5d58014
-/
theorem binetRemainderTerm_lt {u : ℝ} (hu : 0 < u) (N n : ℕ) :
    binetRemainderTerm u N n < u ^ (2 * N + 1) * (2 / binetPole n ^ (2 * (N + 1))) := by
  have hp := binetPole_pos n
  unfold binetRemainderTerm
  have heq : u ^ (2 * N + 1) * (2 / binetPole n ^ (2 * (N + 1))) =
      2 * u ^ (2 * N + 1) / (binetPole n ^ (2 * N) * binetPole n ^ 2) := by
    rw [show 2 * (N + 1) = 2 * N + 2 by omega, pow_add (binetPole n)]
    ring
  rw [heq]
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  apply mul_lt_mul_of_pos_left _ (by positivity)
  linarith [sq_pos_of_pos hu]

/--
@isnad1 id=summable.1h2v.s4.c17709537c9c from=translated src=- shape=ee130a8d vocab=d1f77786
-/
theorem binetRemainderTerm_summable {u : ℝ} (hu : 0 < u) (N : ℕ) :
    Summable (binetRemainderTerm u N) := by
  apply Summable.of_nonneg_of_le
    (fun n => (binetRemainderTerm_pos hu N n).le)
    (fun n => (binetRemainderTerm_lt hu N n).le)
  exact (hasSum_binetMoment (Nat.succ_pos N)).summable.mul_left _

private theorem binetPole_finite_expansion {u a : ℝ} (hu : 0 < u) (ha : 0 < a) (N : ℕ) :
    2 * u / (u ^ 2 + a ^ 2) =
      (∑ m ∈ Finset.range N, (-1 : ℝ) ^ m * (2 / a ^ (2 * (m + 1))) * u ^ (2 * m + 1)) +
        (-1 : ℝ) ^ N * (2 * u ^ (2 * N + 1) / (a ^ (2 * N) * (u ^ 2 + a ^ 2))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ]
    have hden : u ^ 2 + a ^ 2 ≠ 0 := by positivity
    simp only [show 2 * (N + 1) = 2 * N + 2 by omega, pow_add, pow_succ (-1 : ℝ)]
    field_simp [ha.ne', hden]
    ring

/--
@isnad1 id=eq.1h2v.s6.d47d6cfcb8c6 from=translated src=- shape=30ad0f8e vocab=64f1094c
-/
theorem binetKernel_finite_expansion {u : ℝ} (hu : 0 < u) (N : ℕ) :
    binetKernel u = binetKernelApprox u N +
      (-1 : ℝ) ^ N * ∑' n : ℕ, binetRemainderTerm u N n := by
  have hs (m : ℕ) : HasSum
      (fun n => (-1 : ℝ) ^ m * (2 / binetPole n ^ (2 * (m + 1))) * u ^ (2 * m + 1))
      ((-1 : ℝ) ^ m * positiveBernoulliCoeff (m + 1) * u ^ (2 * m + 1)) :=
    ((hasSum_binetMoment (Nat.succ_pos m)).mul_left ((-1 : ℝ) ^ m)).mul_right _
  have hsum := (hasSum_sum (fun m (_ : m ∈ Finset.range N) => hs m)).add
    ((binetRemainderTerm_summable hu N).hasSum.mul_left ((-1 : ℝ) ^ N))
  have hactual := hasSum_binetKernel hu
  apply hactual.unique
  convert! hsum using 1
  funext n
  exact binetPole_finite_expansion hu (binetPole_pos n) N

/--
@isnad1 id=and.1h2v.s7.bbd3b4d1fc45 from=translated src=- shape=eec00d91 vocab=f11ccace
-/
theorem binetKernel_remainder_bounds {u : ℝ} (hu : 0 < u) (N : ℕ) :
    0 < (-1 : ℝ) ^ N * (binetKernel u - binetKernelApprox u N) ∧
      (-1 : ℝ) ^ N * (binetKernel u - binetKernelApprox u N) <
        positiveBernoulliCoeff (N + 1) * u ^ (2 * N + 1) := by
  have hsgn : (-1 : ℝ) ^ N * (-1 : ℝ) ^ N = 1 := by
    rw [← mul_pow]
    norm_num
  rw [binetKernel_finite_expansion hu N, add_sub_cancel_left, ← mul_assoc, hsgn, one_mul]
  have hs := binetRemainderTerm_summable hu N
  constructor
  · exact hs.tsum_pos (fun n => (binetRemainderTerm_pos hu N n).le) 0
      (binetRemainderTerm_pos hu N 0)
  · have hupper := (hasSum_binetMoment (Nat.succ_pos N)).mul_left (u ^ (2 * N + 1))
    have hlt := hs.tsum_lt_tsum (fun n => (binetRemainderTerm_lt hu N n).le)
      (binetRemainderTerm_lt hu N 0) hupper.summable
    rw [hupper.tsum_eq] at hlt
    simpa only [mul_comm] using hlt

/--
@isnad1 id=lt.1h2v.s7.138dfbda600a from=translated src=- shape=a536c8ea vocab=db62f5df
-/
theorem binetKernel_remainder_abs_lt {u : ℝ} (hu : 0 < u) (N : ℕ) :
    |binetKernel u - binetKernelApprox u N| <
      |(bernoulli (2 * (N + 1)) : ℝ)| / ((2 * (N + 1)).factorial : ℝ) * u ^ (2 * N + 1) := by
  have h := binetKernel_remainder_bounds hu N
  have heq : |binetKernel u - binetKernelApprox u N| =
      (-1 : ℝ) ^ N * (binetKernel u - binetKernelApprox u N) := by
    calc
      _ = |(-1 : ℝ) ^ N * (binetKernel u - binetKernelApprox u N)| := by simp [abs_mul]
      _ = _ := abs_of_pos h.1
  rw [heq, ← positiveBernoulliCoeff_eq_abs (Nat.succ_pos N)]
  exact h.2

/--
@isnad1 id=lt.1h1v.s5.671ffb884a55 from=translated src=- shape=95757b40 vocab=926403f6
-/
theorem binetKernel_lt_linear {u : ℝ} (hu : 0 < u) : binetKernel u < u / 12 := by
  have h := (binetKernel_remainder_bounds hu 0).2
  norm_num [binetKernelApprox, positiveBernoulliCoeff, bernoulli_eq_bernoulli'_of_ne_one] at h
  linarith

end PiIrrationality
