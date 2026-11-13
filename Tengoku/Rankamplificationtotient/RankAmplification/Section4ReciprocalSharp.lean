import Tengoku.Rankamplificationtotient.RankAmplification.Section4Assembly
import Tengoku.Seed.Analysis.SumIntegralComparisons

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The sharp partial-summation form of (4.5) `RankAmplification.Section4Assembly` bounds the reciprocal portion `Σ₁` of the nonsmooth transfer by evaluating the Mertens factor `1 + log p` at the *top* endpoint `p = ⌊√(2xy)⌋`, which yields a majorant of size `x (log x)^2 / y`. -/

namespace RankAmplification

open Finset MeasureTheory

noncomputable section

/-! ## The Abel kernel and its elementary primitive -/

/-- The Abel kernel `(1 + log t)^2 / t^2` whose sum over primes in `(y,P]` is the tail appearing in the paper's display for `Σ₁`.-/
def logSqReciprocalKernel (t : ℝ) : ℝ := (1 + Real.log t) ^ 2 / t ^ 2

/-- The explicit elementary primitive `-((log t)^2 + 4 log t + 5)/t` of `logSqReciprocalKernel` on the positive half line.-/
def logSqReciprocalPrimitive (t : ℝ) : ℝ :=
  -((Real.log t ^ 2 + 4 * Real.log t + 5) / t)

/--
@isnad1 id=hasderiv.1h1v.s5.7a225899885e from=translated src=- shape=111225e6 vocab=fe6e3b9f
-/
theorem hasDerivAt_logSqReciprocalPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt logSqReciprocalPrimitive (logSqReciprocalKernel t) t := by
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht.ne'
  have h1 : HasDerivAt (fun s : ℝ ↦ Real.log s ^ 2) (2 * Real.log t * t⁻¹) t := by
    have h : HasDerivAt (fun s : ℝ ↦ Real.log s * Real.log s)
        (t⁻¹ * Real.log t + Real.log t * t⁻¹) t := hlog.mul hlog
    have heq : t⁻¹ * Real.log t + Real.log t * t⁻¹ = 2 * Real.log t * t⁻¹ := by ring
    rw [heq] at h
    simpa only [pow_two] using h
  have h2 : HasDerivAt (fun s : ℝ ↦ 4 * Real.log s) (4 * t⁻¹) t := hlog.const_mul 4
  have hnum : HasDerivAt (fun s : ℝ ↦ Real.log s ^ 2 + 4 * Real.log s + 5)
      (2 * Real.log t * t⁻¹ + 4 * t⁻¹) t := (h1.add h2).add_const 5
  have hid : HasDerivAt (fun s : ℝ ↦ s) 1 t := hasDerivAt_id t
  have hdiv := hnum.div hid ht.ne'
  have hres := hdiv.neg
  have hval : -(((2 * Real.log t * t⁻¹ + 4 * t⁻¹) * t
      - (Real.log t ^ 2 + 4 * Real.log t + 5) * 1) / t ^ 2)
      = logSqReciprocalKernel t := by
    unfold logSqReciprocalKernel
    field_simp
    ring
  rw [hval] at hres
  exact hres

/--
@isnad1 id=continuo.1h1v.s5.1389fa9b3960 from=translated src=- shape=d95d17de vocab=382d56e3
-/
theorem continuousOn_logSqReciprocalKernel {s : Set ℝ} (hs : s ⊆ {(0 : ℝ)}ᶜ) :
    ContinuousOn logSqReciprocalKernel s := by
  unfold logSqReciprocalKernel
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (continuousOn_const.add (Real.continuousOn_log.mono hs)).pow 2
  · exact continuousOn_id.pow 2
  · intro t ht
    exact pow_ne_zero 2 (by simpa using hs ht)

/-- The Abel kernel is decreasing on `[1,∞)`; this is what makes the sum-versus-integral comparison legitimate.
@isnad1 id=antitone.0h0v.s3.85a4fc893ea4 from=translated src=- shape=f2a09be3 vocab=70bb1403
-/
theorem antitoneOn_logSqReciprocalKernel :
    AntitoneOn logSqReciprocalKernel (Set.Ici (1 : ℝ)) := by
  intro s hs t ht hst
  have hs1 : (1 : ℝ) ≤ s := hs
  have ht1 : (1 : ℝ) ≤ t := ht
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs1
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg hs1
  have hkey : (1 + Real.log t) * s ≤ (1 + Real.log s) * t := by
    have hdiv : Real.log (t / s) ≤ t / s - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div ht0.ne' hs0.ne'] at hdiv
    have h1 : s * (Real.log t - Real.log s) ≤ t - s := by
      have h2 := mul_le_mul_of_nonneg_left hdiv hs0.le
      have h3 : s * (t / s - 1) = t - s := by field_simp
      linarith [h2, h3.le, h3.ge]
    nlinarith [mul_nonneg (sub_nonneg.mpr hst) hlogs]
  have hquot : (1 + Real.log t) / t ≤ (1 + Real.log s) / s := by
    rw [div_le_div_iff₀ ht0 hs0]
    exact hkey
  have hnn : 0 ≤ (1 + Real.log t) / t :=
    div_nonneg (by linarith [Real.log_nonneg ht1]) ht0.le
  have hsq : ((1 + Real.log t) / t) ^ 2 ≤ ((1 + Real.log s) / s) ^ 2 := by
    nlinarith [hquot, hnn]
  unfold logSqReciprocalKernel
  rw [← div_pow, ← div_pow]
  exact hsq

/-- Fundamental theorem of calculus for the Abel kernel.
@isnad1 id=eq.2h2v.s5.7389aadfa9e7 from=translated src=- shape=03104f1f vocab=ccde0344
-/
theorem integral_logSqReciprocalKernel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, logSqReciprocalKernel t) =
      logSqReciprocalPrimitive b - logSqReciprocalPrimitive a := by
  have hsub : Set.uIcc a b ⊆ {(0 : ℝ)}ᶜ := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    simpa using htpos.ne'
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ ?_)
    ((continuousOn_logSqReciprocalKernel hsub).intervalIntegrable)
  refine hasDerivAt_logSqReciprocalPrimitive ?_
  rw [Set.uIcc_of_le hab] at ht
  exact lt_of_lt_of_le ha ht.1

/-! ## Partial summation: the logarithm moves to the lower endpoint -/

/-- **Abel/partial summation for the reciprocal-square tail, exact primitive form.** Summing the Abel kernel over the integers in `(y,P]` and comparing with `∫_y^P` leaves the logarithm at the *lower* endpoint `y`, uniformly in the upper endpoint `P`.
@isnad1 id=le.1h2v.s6.dd121427a277 from=translated src=- shape=3ec17ae1 vocab=af912db7
-/
theorem sum_Ioc_logSqReciprocalKernel_le_primitive {y P : ℕ} (hy : 1 ≤ y) :
    (∑ n ∈ Finset.Ioc y P, logSqReciprocalKernel n) ≤
      (Real.log y ^ 2 + 4 * Real.log y + 5) / y := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg hy1
  have hstep : -logSqReciprocalPrimitive (y : ℝ)
      = (Real.log (y : ℝ) ^ 2 + 4 * Real.log y + 5) / y := by
    unfold logSqReciprocalPrimitive
    rw [neg_neg]
  rcases lt_or_ge P y with hPy | hyP
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    apply div_nonneg _ hy0.le
    nlinarith [sq_nonneg (Real.log (y : ℝ) + 2)]
  · have hanti : AntitoneOn logSqReciprocalKernel (Set.Icc (y : ℝ) (P : ℝ)) := by
      refine antitoneOn_logSqReciprocalKernel.mono ?_
      intro t ht
      exact le_trans hy1 ht.1
    have hshift : (∑ i ∈ Finset.Ico y P, logSqReciprocalKernel ((i + 1 : ℕ) : ℝ))
        = ∑ n ∈ Finset.Ioc y P, logSqReciprocalKernel (n : ℝ) := by
      have h := Finset.sum_Ico_add' (fun n : ℕ ↦ logSqReciprocalKernel (n : ℝ)) y P 1
      have hrange : Finset.Ico (y + 1) (P + 1) = Finset.Ioc y P := by
        ext n
        simp only [Finset.mem_Ico, Finset.mem_Ioc]
        omega
      rw [hrange] at h
      exact h
    have hsum := AntitoneOn.sum_le_integral_Ico hyP hanti
    rw [hshift, integral_logSqReciprocalKernel hy0 (by exact_mod_cast hyP)] at hsum
    have hPprim : logSqReciprocalPrimitive (P : ℝ) ≤ 0 := by
      have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
      have hnum : 0 ≤ (Real.log (P : ℝ) ^ 2 + 4 * Real.log P + 5) / P := by
        apply div_nonneg _ hP0.le
        nlinarith [sq_nonneg (Real.log (P : ℝ) + 2)]
      unfold logSqReciprocalPrimitive
      linarith
    linarith

/-- The same partial summation in the `5 (1 + log y)^2 / y` normalisation.
@isnad1 id=le.1h2v.s6.5601743a7579 from=translated src=- shape=f0bff4f2 vocab=af912db7
-/
theorem sum_Ioc_logSqReciprocalKernel_le {y P : ℕ} (hy : 1 ≤ y) :
    (∑ n ∈ Finset.Ioc y P, logSqReciprocalKernel n) ≤
      5 * (1 + Real.log y) ^ 2 / y := by
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg hy1
  refine (sum_Ioc_logSqReciprocalKernel_le_primitive (P := P) hy).trans ?_
  gcongr
  nlinarith [hlogy]

/-- **The sharp reciprocal-square prime tail, exact primitive form.** The best constant this elementary partial summation gives: the right-hand side is the exact value at `y` of the primitive of `(1 + log t)^2 / t^2`.
@isnad1 id=le.1h2v.s7.0d52a7664524 from=translated src=- shape=336c8d85 vocab=72462ccf
-/
theorem sum_squareSourcePrimeRange_one_add_log_sq_le_primitive {y P : ℕ} (hy : 1 ≤ y) :
    (∑ p ∈ squareSourcePrimeRange y P, (1 + Real.log p) ^ 2 / (p : ℝ) ^ 2) ≤
      (Real.log y ^ 2 + 4 * Real.log y + 5) / y := by
  have hsub : (∑ p ∈ squareSourcePrimeRange y P, logSqReciprocalKernel p) ≤
      ∑ n ∈ Finset.Ioc y P, logSqReciprocalKernel n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (squareSourcePrimeRange_subset_Ioc y P) ?_
    intro n _ _
    unfold logSqReciprocalKernel
    positivity
  exact hsub.trans (sum_Ioc_logSqReciprocalKernel_le_primitive hy)

/-- **The sharp reciprocal-square prime tail.** This is the missing partial-summation step of the paper's `Σ₁ ≪ x ∑_{p>y} (log p)^2/p^2 ≪ x (log y)^2 / y`: the logarithm is evaluated at the running prime on the left and only at the lower endpoint `y` on the right, uniformly in `P`.
@isnad1 id=le.1h2v.s7.4ea2db9ef626 from=translated src=- shape=09d42ea6 vocab=72462ccf
-/
theorem sum_squareSourcePrimeRange_one_add_log_sq_le {y P : ℕ} (hy : 1 ≤ y) :
    (∑ p ∈ squareSourcePrimeRange y P, (1 + Real.log p) ^ 2 / (p : ℝ) ^ 2) ≤
      5 * (1 + Real.log y) ^ 2 / y := by
  have hsub : (∑ p ∈ squareSourcePrimeRange y P, logSqReciprocalKernel p) ≤
      ∑ n ∈ Finset.Ioc y P, logSqReciprocalKernel n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (squareSourcePrimeRange_subset_Ioc y P) ?_
    intro n _ _
    unfold logSqReciprocalKernel
    positivity
  exact hsub.trans (sum_Ioc_logSqReciprocalKernel_le hy)

/-- The literal shape displayed in the paper: `∑_{y < p ≤ P} (log p)^2/p^2 ≪ (log y)^2/y`, with the absolute constant `5` and the harmless `1 +` guarding `y = 1`.
@isnad1 id=le.1h2v.s7.f2649c61de82 from=translated src=- shape=5721d52b vocab=72462ccf
-/
theorem sum_squareSourcePrimeRange_log_sq_le {y P : ℕ} (hy : 1 ≤ y) :
    (∑ p ∈ squareSourcePrimeRange y P, Real.log p ^ 2 / (p : ℝ) ^ 2) ≤
      5 * (1 + Real.log y) ^ 2 / y := by
  refine le_trans (Finset.sum_le_sum ?_) (sum_squareSourcePrimeRange_one_add_log_sq_le (P := P) hy)
  intro p hp
  obtain ⟨_, _, hpprime⟩ := mem_squareSourcePrimeRange.mp hp
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le)
  have hnum : Real.log (p : ℝ) ^ 2 ≤ (1 + Real.log (p : ℝ)) ^ 2 := by nlinarith [hlogp]
  have hinv : (0 : ℝ) ≤ ((p : ℝ) ^ 2)⁻¹ := by positivity
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum hinv

/-! ## The per-prime Mertens factor at the running prime -/

/-- The per-prime input to (4.5) with the Mertens logarithm kept at the running prime `p`, rather than pushed up to the top endpoint of the range.
@isnad1 id=le.1h2v.s7.caf8bef34ca2 from=translated src=- shape=11e7a443 vocab=eb9ea5ad
-/
theorem smoothProviderPairReciprocalSum_le_running {p X : ℕ} (hp : 3 ≤ p) :
    smoothProviderPairReciprocalSum p X ≤
      Real.exp (4 * Real.log 4) ^ 2 * ((1 + Real.log p) ^ 2 / (p : ℝ) ^ 2) := by
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  have hbase := finiteProviderReciprocalSum_le_log p X hp
  have hnonneg : 0 ≤ finiteProviderReciprocalSum p X := by
    unfold finiteProviderReciprocalSum
    exact Finset.sum_nonneg fun k _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)
  have hrhs : 0 ≤ (p : ℝ)⁻¹ * (Real.exp (4 * Real.log 4) * (1 + Real.log p)) :=
    mul_nonneg (by positivity) (mul_nonneg (Real.exp_pos _).le (by linarith))
  have hsq : finiteProviderReciprocalSum p X ^ 2 ≤
      ((p : ℝ)⁻¹ * (Real.exp (4 * Real.log 4) * (1 + Real.log p))) ^ 2 := by
    nlinarith [hbase, hnonneg, hrhs]
  have heq : ((p : ℝ)⁻¹ * (Real.exp (4 * Real.log 4) * (1 + Real.log p))) ^ 2
      = Real.exp (4 * Real.log 4) ^ 2 * ((1 + Real.log p) ^ 2 / (p : ℝ) ^ 2) := by
    rw [mul_pow, mul_pow, inv_pow, div_eq_mul_inv]
    ring
  exact ((smoothProviderPairReciprocalSum_le_sq p X).trans hsq).trans (le_of_eq heq)

/-! ## The sharp form of (4.5) and of Theorem 1.6 -/

/-- The explicit absolute constant `5 · 4^8` in the sharp form of (4.5).-/
def section4SharpConstant : ℝ := 5 * Real.exp (4 * Real.log 4) ^ 2

/--
@isnad1 id=le.0h0v.s3.b1867c59e455 from=translated src=- shape=ff3a10fc vocab=e9af56cd
-/
theorem section4SharpConstant_nonneg : 0 ≤ section4SharpConstant := by
  unfold section4SharpConstant
  positivity

/-- **Sharp (4.5).** The same left-hand side as `section4ReciprocalSum_le`, but with the logarithm at the *lower* endpoint `y` and an absolute constant, instead of the Mertens factor evaluated at the top endpoint `⌊√(2xy)⌋`.
@isnad1 id=le.2h2v.s6.b47b133cd7fc from=translated src=- shape=6cf1e217 vocab=95d38317
-/
theorem section4ReciprocalSum_le_sharp {x y : ℕ} (hy : 2 ≤ y) (_hxy : y ≤ x) :
    section4ReciprocalSum x y ≤
      section4SharpConstant * (x : ℝ) * (1 + Real.log y) ^ 2 / (y : ℝ) := by
  have hC : (0 : ℝ) ≤ Real.exp (4 * Real.log 4) ^ 2 := sq_nonneg _
  have hy1 : 1 ≤ y := by omega
  calc
    section4ReciprocalSum x y ≤
        (x : ℝ) * ∑ p ∈ section5PrimeRange x y,
          (Real.exp (4 * Real.log 4) ^ 2 * ((1 + Real.log p) ^ 2 / (p : ℝ) ^ 2)) := by
      unfold section4ReciprocalSum
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg x)
      refine Finset.sum_le_sum ?_
      intro p hp
      obtain ⟨hyp, _, _⟩ := mem_section5PrimeRange.mp hp
      exact smoothProviderPairReciprocalSum_le_running (by omega)
    _ = (x : ℝ) * Real.exp (4 * Real.log 4) ^ 2 *
        ∑ p ∈ section5PrimeRange x y, ((1 + Real.log p) ^ 2 / (p : ℝ) ^ 2) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (x : ℝ) * Real.exp (4 * Real.log 4) ^ 2 * (5 * (1 + Real.log y) ^ 2 / y) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Nat.cast_nonneg x) hC)
      exact sum_squareSourcePrimeRange_one_add_log_sq_le hy1
    _ = section4SharpConstant * (x : ℝ) * (1 + Real.log y) ^ 2 / (y : ℝ) := by
      unfold section4SharpConstant
      ring

/-- The sharp (4.5) estimate in the `(y : ℝ)⁻¹` normalisation used by the assembly modules.
@isnad1 id=le.2h2v.s6.9fe0d0119e01 from=translated src=- shape=e120a321 vocab=d843299c
-/
theorem section4ReciprocalSum_le_sharp' {x y : ℕ} (hy : 2 ≤ y) (hxy : y ≤ x) :
    section4ReciprocalSum x y ≤
      section4SharpConstant * (x : ℝ) * (1 + Real.log y) ^ 2 * (y : ℝ)⁻¹ := by
  simpa only [div_eq_mul_inv] using section4ReciprocalSum_le_sharp hy hxy

/-- **Sharp outer estimate.** The Section 4 + Section 5 outer sum with the sharp reciprocal term; this is the sharp analogue of `nonsquare_outer_sum_le`.
@isnad1 id=le.3h3v.s8.ee40dbc0c70f from=translated src=- shape=3dbc266c vocab=84460c69
-/
theorem nonsquare_outer_sum_le_sharp {x y : ℕ} {saving : ℝ}
    (hy : 2 ≤ y) (hxy : y ≤ x)
    (hRankin : HasSection5IntermediateRankinSaving x y saving) :
    (∑ p ∈ squareSourcePrimeRange y (2 * x * y).sqrt,
      smoothProviderPairMajorant x p ((2 * x * y) / p ^ 2)) ≤
      section4SharpConstant * (x : ℝ) * (1 + Real.log y) ^ 2 * (y : ℝ)⁻¹ +
        2 * (x : ℝ) * Real.exp (-saving) +
        2 * (x : ℝ) * (1 + Real.log (section5Ambient x y)) * (y : ℝ)⁻¹ := by
  rw [nonsquare_outer_sum_eq_section4_add_B4]
  simpa only [add_assoc] using
    add_le_add (section4ReciprocalSum_le_sharp' hy hxy)
      (smoothMultiplierB4Sum_le_exp_add_upper (by omega) hxy hRankin)

end

end RankAmplification
