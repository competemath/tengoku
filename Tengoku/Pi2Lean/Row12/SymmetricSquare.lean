import Tengoku.Pi2Lean.Row12.NativeSeries
import Tengoku.Pi2Lean.Row12.BetaMoments
import Tengoku.Seed.RingTheory.PowerSeries.Derivative
import Tengoku.Seed.Analysis.Normed.Ring.InfiniteSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12.formalTheta_add` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.formalTheta_sub` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.formalTheta_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.formalTheta_nat` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.formalTheta_X` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.formalTheta_C` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.formalTheta_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.formalTheta_coeff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.formal_symmetric_square_identity` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.halfGaussCoefficient_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.halfGaussCoefficient_succ_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.formalHalfGauss_second` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.formalThird_coeff_succ` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.formalNative_third` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.formalThird_unique` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.formalNative_eq_square` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeCoefficient_clausen` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.halfGaussCoefficient_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.halfGaussCoefficient_le_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.halfGaussCoefficient_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.halfGaussCoefficient_cast` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.halfGauss_eq_tsum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.halfGauss_summable_norm` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeF_eq_halfGauss_square` (it only prints; the queue checks the axioms of every declaration). -/

namespace Row12

noncomputable def formalTheta (f : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.X * PowerSeries.derivative ℝ f

/--
@isnad1 id=eq.0h2v.s5.549a0bf5ccbb from=translated src=- shape=5de3d10d vocab=b88a6547
-/
theorem formalTheta_add (f g : PowerSeries ℝ) :
    formalTheta (f + g) = formalTheta f + formalTheta g := by
  simp [formalTheta, map_add, mul_add]

/--
@isnad1 id=eq.0h2v.s5.4cef0702d1a2 from=translated src=- shape=5de3d10d vocab=677c97d6
-/
theorem formalTheta_sub (f g : PowerSeries ℝ) :
    formalTheta (f - g) = formalTheta f - formalTheta g := by
  simp [formalTheta, map_sub, mul_sub]

/--
@isnad1 id=eq.0h2v.s6.399ac6b7f888 from=translated src=- shape=ecde3437 vocab=6de08d1d
-/
theorem formalTheta_mul (f g : PowerSeries ℝ) :
    formalTheta (f * g) = f * formalTheta g + g * formalTheta f := by
  simp only [formalTheta, Derivation.leibniz, smul_eq_mul]
  ring

/--
@isnad1 id=eq.0h1v.s4.3fbd38a61bd5 from=translated src=- shape=b38c0055 vocab=a0a8c88f
-/
theorem formalTheta_nat (m : ℕ) : formalTheta (m : PowerSeries ℝ) = 0 := by
  simp [formalTheta, Derivation.map_natCast]

/--
@isnad1 id=eq.0h0v.s3.07cb566d40d4 from=translated src=- shape=9b1c3ca8 vocab=18a8342c
-/
theorem formalTheta_X : formalTheta (PowerSeries.X : PowerSeries ℝ) = PowerSeries.X := by
  simp [formalTheta]

/--
@isnad1 id=eq.0h1v.s5.d7e8a94162e3 from=translated src=- shape=ac1a6262 vocab=b38b9e1c
-/
theorem formalTheta_C (c : ℝ) : formalTheta (PowerSeries.C c) = 0 := by
  simp [formalTheta]

/--
@isnad1 id=eq.0h0v.s4.7fa5f3e9ee9c from=translated src=- shape=e467432f vocab=19c0ecca
-/
theorem formalTheta_one : formalTheta (1 : PowerSeries ℝ) = 0 := by
  simp [formalTheta]

/--
@isnad1 id=eq.0h2v.s7.d8d4e0bb86be from=translated src=- shape=1a6918fc vocab=a3f33e21
-/
theorem formalTheta_coeff (f : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff n (formalTheta f) = (n : ℝ) * PowerSeries.coeff n f := by
  cases n with
  | zero => simp [formalTheta]
  | succ n =>
    rw [formalTheta, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast
    ring

noncomputable def formalSecond (g : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.C 144 * ((1-PowerSeries.X) * formalTheta (formalTheta g)) -
    PowerSeries.C 72 * (PowerSeries.X * formalTheta g) -
    PowerSeries.C 5 * (PowerSeries.X * g)

noncomputable def formalThird (f : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.C 72 * ((1-PowerSeries.X) * formalTheta (formalTheta (formalTheta f))) -
    PowerSeries.X * (PowerSeries.C 108 * formalTheta (formalTheta f) +
      PowerSeries.C 46 * formalTheta f + PowerSeries.C 5 * f)

/--
@isnad1 id=eq.0h1v.s6.afd7a1783b37 from=translated src=- shape=3d238674 vocab=574695e9
-/
theorem formal_symmetric_square_identity (g : PowerSeries ℝ) :
    formalThird (g^2) = g * formalTheta (formalSecond g) +
      3 * formalTheta g * formalSecond g := by
  simp only [formalThird, formalSecond, pow_two, formalTheta_mul, formalTheta_add,
    formalTheta_sub, formalTheta_C, formalTheta_one, formalTheta_X]
  norm_num only [map_ofNat]
  ring

noncomputable def halfGaussCoefficient (n : ℕ) : ℝ :=
  gammaMoment (1/12) n * gammaMoment (5/12) n

/--
@isnad1 id=eq.0h0v.s3.991df6aaaa08 from=translated src=- shape=1ac31801 vocab=e750c75c
-/
theorem halfGaussCoefficient_zero : halfGaussCoefficient 0 = 1 := by
  norm_num [halfGaussCoefficient, gammaMoment_zero]

/--
@isnad1 id=eq.0h1v.s7.20e856e4c38e from=translated src=- shape=512baa57 vocab=7040bbaf
-/
theorem halfGaussCoefficient_succ_mul (n : ℕ) :
    ((n : ℝ)+1)^2 * halfGaussCoefficient (n+1) =
      ((n : ℝ)+1/12) * ((n : ℝ)+5/12) * halfGaussCoefficient n := by
  have ha := gammaMoment_succ (by norm_num : (0:ℝ)<1/12) n
  have hb := gammaMoment_succ (by norm_num : (0:ℝ)<5/12) n
  unfold halfGaussCoefficient
  calc
    _ = (((n : ℝ)+1) * gammaMoment (1/12) (n+1)) *
      (((n : ℝ)+1) * gammaMoment (5/12) (n+1)) := by ring
    _ = _ := by rw [ha, hb]; ring

noncomputable def formalHalfGauss : PowerSeries ℝ := PowerSeries.mk halfGaussCoefficient

noncomputable def formalNative : PowerSeries ℝ := PowerSeries.mk coefficient3

private theorem formalSecond_coeff_zero (g : PowerSeries ℝ) :
    PowerSeries.coeff 0 (formalSecond g) = 0 := by
  rw [formalSecond]
  simp only [map_sub, PowerSeries.coeff_C_mul, sub_mul, one_mul,
    PowerSeries.coeff_zero_X_mul, formalTheta_coeff, Nat.cast_zero, zero_mul,
    mul_zero, sub_self]

private theorem formalSecond_coeff_succ (g : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff (n+1) (formalSecond g) =
      144*((n:ℝ)+1)^2 * PowerSeries.coeff (n+1) g -
        (144*(n:ℝ)^2+72*(n:ℝ)+5)*PowerSeries.coeff n g := by
  rw [formalSecond]
  simp only [map_sub, PowerSeries.coeff_C_mul, sub_mul, one_mul,
    PowerSeries.coeff_succ_X_mul, formalTheta_coeff, Nat.cast_add, Nat.cast_one]
  ring

/--
@isnad1 id=eq.0h0v.s4.4458cd0d44df from=translated src=- shape=8c4e12ea vocab=b96d8a9a
-/
theorem formalHalfGauss_second : formalSecond formalHalfGauss = 0 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp only [formalSecond_coeff_zero, map_zero]
  | succ n =>
    rw [formalSecond_coeff_succ]
    simp only [formalHalfGauss, PowerSeries.coeff_mk, map_zero]
    have h := halfGaussCoefficient_succ_mul n
    linear_combination (144:ℝ)*h

private theorem formalThird_coeff_zero (f : PowerSeries ℝ) :
    PowerSeries.coeff 0 (formalThird f) = 0 := by
  rw [formalThird]
  simp only [map_sub, PowerSeries.coeff_C_mul, sub_mul, one_mul,
    PowerSeries.coeff_zero_X_mul, formalTheta_coeff, Nat.cast_zero, zero_mul,
    sub_zero, mul_zero]

/--
@isnad1 id=eq.0h2v.s8.4c937ecad468 from=translated src=- shape=a648af7d vocab=f8d4cadb
-/
theorem formalThird_coeff_succ (f : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff (n+1) (formalThird f) =
      72*((n:ℝ)+1)^3 * PowerSeries.coeff (n+1) f -
        (72*(n:ℝ)^3+108*(n:ℝ)^2+46*(n:ℝ)+5)*PowerSeries.coeff n f := by
  rw [formalThird]
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, sub_mul, one_mul,
    PowerSeries.coeff_succ_X_mul, formalTheta_coeff, Nat.cast_add, Nat.cast_one]
  ring

/--
@isnad1 id=eq.0h0v.s4.881272a2ce60 from=translated src=- shape=8c4e12ea vocab=85655dfd
-/
theorem formalNative_third : formalThird formalNative = 0 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp only [formalThird_coeff_zero, map_zero]
  | succ n =>
    rw [formalThird_coeff_succ]
    simp only [formalNative, PowerSeries.coeff_mk, map_zero]
    have h := coefficient3_succ_mul n
    linear_combination (72:ℝ)*h

/--
@isnad1 id=eq.3h2v.s7.b120d9c6dadd from=translated src=- shape=1bd2c7e0 vocab=b6bb7853
-/
theorem formalThird_unique {f g : PowerSeries ℝ} (hf : formalThird f = 0)
    (hg : formalThird g = 0) (h0 : PowerSeries.coeff 0 f = PowerSeries.coeff 0 g) : f = g := by
  apply PowerSeries.ext
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    have hfc := congrArg (PowerSeries.coeff (n+1)) hf
    have hgc := congrArg (PowerSeries.coeff (n+1)) hg
    rw [formalThird_coeff_succ, map_zero] at hfc hgc
    rw [ih] at hfc
    have hnonzero : (72:ℝ)*((n:ℝ)+1)^3 ≠ 0 := by positivity
    apply mul_left_cancel₀ hnonzero
    linarith

/--
@isnad1 id=eq.0h0v.s5.4aed992dc8c6 from=translated src=- shape=03a03c6f vocab=6a97a568
-/
theorem formalNative_eq_square : formalNative = formalHalfGauss^2 := by
  apply formalThird_unique formalNative_third
  · rw [formal_symmetric_square_identity, formalHalfGauss_second]
    simp [formalTheta]
  · simp [formalNative, formalHalfGauss, PowerSeries.coeff_mul, pow_two,
      PowerSeries.coeff_mk, coefficient3_zero, halfGaussCoefficient_zero]

/--
@isnad1 id=eq.0h1v.s5.aacb3a8774c1 from=translated src=- shape=c1588e4d vocab=79e690dc
-/
theorem nativeCoefficient_clausen (n : ℕ) :
    coefficient3 n = ∑ ij ∈ Finset.antidiagonal n,
      halfGaussCoefficient ij.1 * halfGaussCoefficient ij.2 := by
  have h := congrArg (PowerSeries.coeff n) formalNative_eq_square
  simpa only [formalNative, formalHalfGauss, pow_two, PowerSeries.coeff_mul,
    PowerSeries.coeff_mk] using h

/--
@isnad1 id=lt.0h1v.s3.c35f946eb9e2 from=translated src=- shape=b9369acb vocab=0b36919e
-/
theorem halfGaussCoefficient_pos (n : ℕ) : 0 < halfGaussCoefficient n := by
  exact mul_pos (gammaMoment_pos (by norm_num) n) (gammaMoment_pos (by norm_num) n)

/--
@isnad1 id=le.0h1v.s3.06d118383a7d from=translated src=- shape=a311c14d vocab=71df7306
-/
theorem halfGaussCoefficient_le_one (n : ℕ) : halfGaussCoefficient n ≤ 1 := by
  have ha := gammaMoment_le_one (by norm_num : (0:ℝ)<1/12) (by norm_num) n
  have hb := gammaMoment_le_one (by norm_num : (0:ℝ)<5/12) (by norm_num) n
  simpa only [halfGaussCoefficient, one_mul] using
    mul_le_mul ha hb (gammaMoment_pos (by norm_num) n).le zero_le_one

/--
@isnad1 id=eq.0h1v.s6.ea29857af24f from=translated src=- shape=513b4e81 vocab=d91d420d
-/
theorem halfGaussCoefficient_eq (n : ℕ) : halfGaussCoefficient n =
    ordinaryHypergeometricCoefficient (1/12:ℝ) (5/12) 1 n := by
  unfold halfGaussCoefficient ordinaryHypergeometricCoefficient
  rw [gammaMoment_eq_ascPochhammer (by norm_num : (0:ℝ)<1/12),
    gammaMoment_eq_ascPochhammer (by norm_num : (0:ℝ)<5/12), ascPochhammer_eval_one]
  ring

section ActualSquare

variable {𝕜 : Type*} [RCLike 𝕜]

private theorem halfPochhammer_cast (a : ℝ) (n : ℕ) :
    (algebraMap ℝ 𝕜) ((ascPochhammer ℝ n).eval a) =
      (ascPochhammer 𝕜 n).eval ((algebraMap ℝ 𝕜) a) := by
  rw [ascPochhammer_eval₂ (algebraMap ℝ 𝕜), Polynomial.eval₂_at_apply]

/--
@isnad1 id=eq.0h2v.s7.cfe3d70d95d1 from=translated src=- shape=3afe36e0 vocab=fe1c6a63
-/
theorem halfGaussCoefficient_cast (n : ℕ) : (halfGaussCoefficient n : 𝕜) =
    ordinaryHypergeometricCoefficient (1/12:𝕜) (5/12) 1 n := by
  change (algebraMap ℝ 𝕜) (halfGaussCoefficient n) = _
  rw [halfGaussCoefficient_eq]
  simp only [ordinaryHypergeometricCoefficient, map_mul, map_inv₀, map_natCast]
  rw [halfPochhammer_cast (𝕜 := 𝕜) (1/12:ℝ) n,
    halfPochhammer_cast (𝕜 := 𝕜) (5/12:ℝ) n,
    halfPochhammer_cast (𝕜 := 𝕜) 1 n]
  simp only [map_one, map_div₀, map_ofNat]

noncomputable def halfGauss (q : 𝕜) : 𝕜 :=
  ordinaryHypergeometric (1/12:𝕜) (5/12) 1 q

/--
@isnad1 id=eq.0h2v.s6.38c4e6fc967d from=translated src=- shape=bdc1796d vocab=ef9bf3b6
-/
theorem halfGauss_eq_tsum (q : 𝕜) :
    halfGauss q = ∑' n : ℕ, (halfGaussCoefficient n : 𝕜)*q^n := by
  simp only [halfGauss, ordinaryHypergeometric_eq_tsum, smul_eq_mul]
  apply tsum_congr
  intro n
  rw [halfGaussCoefficient_cast]

/--
@isnad1 id=summable.1h2v.s6.f20cefb9b357 from=translated src=- shape=d6607e12 vocab=13745f11
-/
theorem halfGauss_summable_norm {q : 𝕜} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ‖(halfGaussCoefficient n : 𝕜)*q^n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (summable_geometric_of_norm_lt_one
      (show ‖‖q‖‖ < 1 by simpa only [Real.norm_eq_abs, abs_norm] using hq))
  intro n
  simp only [norm_mul, norm_pow, RCLike.norm_of_nonneg (halfGaussCoefficient_pos n).le]
  exact (mul_le_mul_of_nonneg_right (halfGaussCoefficient_le_one n)
    (pow_nonneg (norm_nonneg q) n)).trans_eq (one_mul _)

/--
@isnad1 id=eq.1h2v.s6.8be6d0671c57 from=translated src=- shape=f28efdd2 vocab=48fad5b9
-/
theorem nativeF_eq_halfGauss_square (q : 𝕜) (hq : ‖q‖ < 1) :
    nativeF q = halfGauss q ^ 2 := by
  have hs := halfGauss_summable_norm hq
  have hc := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs hs
  rw [halfGauss_eq_tsum, pow_two, hc, nativeF_eq_tsum]
  symm
  apply tsum_congr
  intro n
  have hcoeff : (coefficient3 n : 𝕜) = ∑ ij ∈ Finset.antidiagonal n,
      (halfGaussCoefficient ij.1 : 𝕜) * (halfGaussCoefficient ij.2 : 𝕜) := by
    have h := congrArg (algebraMap ℝ 𝕜) (nativeCoefficient_clausen n)
    simpa only [map_sum, map_mul] using h
  rw [hcoeff, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hijsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [mul_mul_mul_comm, ← pow_add, hijsum]

end ActualSquare

end Row12

