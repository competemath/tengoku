import Tengoku.Rankamplificationtotient.RankAmplification.PrimeSums
import Tengoku.Rankamplificationtotient.RankAmplification.Rankin
import Tengoku.Seed.NumberTheory.EulerProduct.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Explicit divisor-weighted smooth-number tails This file combines the finite Rankin inequality, an exact Euler product over smooth numbers, and the explicit Chebyshev prime-sum estimate. -/

namespace RankAmplification

open Finset
open scoped Nat.Prime

noncomputable section

/-- The project's weak smoothness cutoff agrees with Mathlib's strict cutoff after adding one.-/
theorem isSmooth_iff_mem_smoothNumbers_succ {R n : ℕ} :
    IsSmooth R n ↔ n ∈ (R + 1).smoothNumbers := by
  rw [Nat.mem_smoothNumbers_iff_primeFactors_subset]
  constructor
  · rintro ⟨hn, hs⟩
    refine ⟨hn, fun p hp ↦ Nat.mem_primesBelow.mpr ⟨?_, Nat.prime_of_mem_primeFactors hp⟩⟩
    exact Nat.lt_succ_of_le (hs p hp)
  · rintro ⟨hn, hs⟩
    refine ⟨hn, fun p hp ↦ ?_⟩
    exact Nat.le_of_lt_succ (Nat.lt_of_mem_primesBelow (hs hp))

/-- The positive divisor Dirichlet kernel used in Lemma 2.5.-/
def divisorRankinWeight (s : ℝ) (n : ℕ) : ℝ :=
  (orderedDivisorCount 2 n : ℝ) * (n : ℝ) ^ (-s)

theorem divisorRankinWeight_nonneg (s : ℝ) (n : ℕ) :
    0 ≤ divisorRankinWeight s n := by
  exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

@[simp]
theorem divisorRankinWeight_one (s : ℝ) : divisorRankinWeight s 1 = 1 := by
  simp only [divisorRankinWeight, orderedDivisorCount, Nat.cast_one, Real.one_rpow, mul_one]
  exact_mod_cast (ArithmeticFunction.isMultiplicative_zeta.pow (k := 2)).map_one

/-- The divisor Rankin kernel is multiplicative on coprime inputs.-/
theorem divisorRankinWeight_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) (s : ℝ) :
    divisorRankinWeight s (m * n) =
      divisorRankinWeight s m * divisorRankinWeight s n := by
  have htau := (ArithmeticFunction.isMultiplicative_zeta.pow (k := 2)).map_mul_of_coprime h
  simp only [divisorRankinWeight, orderedDivisorCount]
  rw [
    htau, Nat.cast_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

/-- The ordered rank-two divisor count on a prime power.-/
theorem orderedDivisorCount_two_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    orderedDivisorCount 2 (p ^ a) = a + 1 := by
  rw [orderedDivisorCount_two, Nat.card_divisors (pow_ne_zero a hp.ne_zero)]
  rcases a with _ | a
  · simp
  · rw [Nat.primeFactors_prime_pow (Nat.succ_ne_zero a) hp, Finset.prod_singleton,
      Nat.factorization_pow_self hp]

/-- The local divisor Rankin series is the square of the geometric Euler factor.-/
theorem hasSum_divisorRankinWeight_prime_pow {p : ℕ} (hp : p.Prime) {s : ℝ}
    (hs : 0 < s) :
    HasSum (fun a : ℕ ↦ divisorRankinWeight s (p ^ a))
      ((1 - rankinEulerRatio p s)⁻¹ ^ 2) := by
  have hp1 : 1 < p := hp.one_lt
  have hqpos : 0 < rankinEulerRatio p s :=
    rankinEulerRatio_pos hp.pos s
  have hqlt : rankinEulerRatio p s < 1 :=
    rankinEulerRatio_lt_one hp1 hs
  have hqnorm : ‖rankinEulerRatio p s‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]
    exact hqlt
  have hterm (a : ℕ) : divisorRankinWeight s (p ^ a) =
      ((a : ℝ) + 1) * rankinEulerRatio p s ^ a := by
    simp only [divisorRankinWeight, orderedDivisorCount_two_prime_pow hp, Nat.cast_add,
      Nat.cast_one, rankinEulerRatio]
    rw [Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg p) (-s) a]
  have hseries : HasSum (fun a : ℕ ↦
      ((a : ℝ) + 1) * rankinEulerRatio p s ^ a)
      (1 / (1 - rankinEulerRatio p s) ^ 2) := by
    simpa using hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hqnorm
  have hseries' : HasSum (fun a : ℕ ↦ divisorRankinWeight s (p ^ a))
      (1 / (1 - rankinEulerRatio p s) ^ 2) :=
    hseries.congr_fun hterm
  simpa [one_div] using hseries'

/-- Exact Euler product for the divisor kernel over all positive `R`-smooth integers.-/
theorem hasSum_divisorRankinWeight_smooth (R : ℕ) {s : ℝ} (hs : 0 < s) :
    HasSum (fun m : (R + 1).smoothNumbers ↦ divisorRankinWeight s m)
      (rankinEulerMajorant (Nat.primesLE R) 2 s) := by
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun a : ℕ ↦ ‖divisorRankinWeight s (p ^ a)‖) := by
    intro p hp
    exact (hasSum_divisorRankinWeight_prime_pow hp hs).summable.norm
  have heuler := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := divisorRankinWeight s) (divisorRankinWeight_one s)
      (fun {_m _n} h ↦ divisorRankinWeight_mul_of_coprime h s) hlocal (R + 1)
  have hprod :
      (∏ p ∈ (R + 1).primesBelow,
        ∑' a : ℕ, divisorRankinWeight s (p ^ a)) =
        rankinEulerMajorant (Nat.primesLE R) 2 s := by
    rw [rankinEulerMajorant]
    change (∏ p ∈ Nat.primesLE R,
      ∑' a : ℕ, divisorRankinWeight s (p ^ a)) =
        ∏ p ∈ Nat.primesLE R, ((1 - rankinEulerRatio p s)⁻¹) ^ 2
    apply Finset.prod_congr rfl
    intro p hp
    exact (hasSum_divisorRankinWeight_prime_pow
      (Nat.prime_of_mem_primesLE hp) hs).tsum_eq
  exact hprod ▸ heuler.2

/-- The finite divisor Rankin sum is bounded by the full smooth Euler product.-/
theorem finiteDivisorRankinSum_le_eulerMajorant {R X : ℕ} {s : ℝ} (hs : 0 < s) :
    finiteSmoothRpowSum (fun m ↦ orderedDivisorCount 2 m) R X (-s) ≤
      rankinEulerMajorant (Nat.primesLE R) 2 s := by
  let e : {m : ℕ // m ∈ finiteSmoothSet R X} ↪ (R + 1).smoothNumbers :=
    { toFun := fun m ↦
        ⟨m.1, isSmooth_iff_mem_smoothNumbers_succ.mp
          (mem_finiteSmoothSet.mp m.2).2.2⟩
      inj' := fun a b hab ↦ Subtype.ext <|
        congrArg (fun z : (R + 1).smoothNumbers ↦ (z : ℕ)) hab }
  let A : Finset ((R + 1).smoothNumbers) := Finset.univ.map e
  have hsmooth := hasSum_divisorRankinWeight_smooth R hs
  have hle : (∑ m ∈ A, divisorRankinWeight s m) ≤
      rankinEulerMajorant (Nat.primesLE R) 2 s := by
    calc
      (∑ m ∈ A, divisorRankinWeight s m) ≤
          ∑' m : (R + 1).smoothNumbers, divisorRankinWeight s m :=
        hsmooth.summable.sum_le_tsum A (fun m _ ↦ divisorRankinWeight_nonneg s m)
      _ = rankinEulerMajorant (Nat.primesLE R) 2 s := hsmooth.tsum_eq
  have hfinite :
      finiteSmoothRpowSum (fun m ↦ orderedDivisorCount 2 m) R X (-s) =
        ∑ m : {m : ℕ // m ∈ finiteSmoothSet R X}, divisorRankinWeight s m := by
    rw [finiteSmoothRpowSum, ← Finset.sum_attach, Finset.attach_eq_univ]
    rfl
  have hmap :
      (∑ m : {m : ℕ // m ∈ finiteSmoothSet R X}, divisorRankinWeight s m) =
        ∑ m ∈ A, divisorRankinWeight s m := by
    change (∑ m : {m : ℕ // m ∈ finiteSmoothSet R X}, divisorRankinWeight s m) =
      ∑ m ∈ Finset.univ.map e, divisorRankinWeight s m
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro m _
    rfl
  rw [hfinite, hmap]
  exact hle

/-- The explicit loss from replacing every local Euler denominator by the worst prime `2`.-/
def divisorEulerLoss (s : ℝ) : ℝ :=
  2 / (1 - (2 : ℝ) ^ (-s))

theorem divisorEulerLoss_pos {s : ℝ} (hs : 0 < s) : 0 < divisorEulerLoss s := by
  rw [divisorEulerLoss]
  exact div_pos (by norm_num) (sub_pos.mpr <|
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hs))

/-- The logarithm of the rank-two Euler majorant is controlled by the weighted prime sum.-/
theorem log_rankinEulerMajorant_le_divisorEulerLoss_mul_primeRankinSum
    {R : ℕ} {δ : ℝ} (hδ1 : δ < 1) :
    Real.log (rankinEulerMajorant (Nat.primesLE R) 2 (1 - δ)) ≤
      divisorEulerLoss (1 - δ) * primeRankinSum R δ := by
  have hs : 0 < 1 - δ := sub_pos.mpr hδ1
  have hP : ∀ p ∈ Nat.primesLE R, 1 < p := fun p hp ↦
    (Nat.prime_of_mem_primesLE hp).one_lt
  have hlog := log_rankinEulerMajorant_le_sum (j := 2) hP hs
  let ρ : ℝ := (2 : ℝ) ^ (-(1 - δ))
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρlt : ρ < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hs)
  have hlocal (p : ℕ) (hp : p ∈ Nat.primesLE R) :
      rankinEulerRatio p (1 - δ) / (1 - rankinEulerRatio p (1 - δ)) ≤
        rankinEulerRatio p (1 - δ) / (1 - ρ) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesLE hp
    have hqpos : 0 < rankinEulerRatio p (1 - δ) :=
      rankinEulerRatio_pos (Nat.zero_lt_of_lt (hP p hp)) _
    have hqlt : rankinEulerRatio p (1 - δ) < 1 :=
      rankinEulerRatio_lt_one (hP p hp) hs
    have hqρ : rankinEulerRatio p (1 - δ) ≤ ρ := by
      rw [rankinEulerRatio]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (neg_nonpos.mpr hs.le)
    apply (div_le_div_iff₀ (sub_pos.mpr hqlt) (sub_pos.mpr hρlt)).2
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hqρ 1) hqpos.le
  calc
    Real.log (rankinEulerMajorant (Nat.primesLE R) 2 (1 - δ)) ≤
        (2 : ℝ) * ∑ p ∈ Nat.primesLE R,
          rankinEulerRatio p (1 - δ) / (1 - rankinEulerRatio p (1 - δ)) := hlog
    _ ≤ 2 * ∑ p ∈ Nat.primesLE R,
        rankinEulerRatio p (1 - δ) / (1 - ρ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun p hp ↦ hlocal p hp
    _ = divisorEulerLoss (1 - δ) * primeRankinSum R δ := by
      have hexp : -(1 - δ) = -1 + δ := by ring
      dsimp [ρ]
      rw [divisorEulerLoss, primeRankinSum]
      simp_rw [rankinEulerRatio, hexp]
      rw [← Finset.sum_div]
      ring

theorem rankinEulerMajorant_primes_pos {R : ℕ} {s : ℝ} (hs : 0 < s) :
    0 < rankinEulerMajorant (Nat.primesLE R) 2 s := by
  rw [rankinEulerMajorant]
  apply Finset.prod_pos
  intro p hp
  have hqlt := rankinEulerRatio_lt_one
    (Nat.prime_of_mem_primesLE hp).one_lt hs
  positivity

/-- Exponential form of the preceding logarithmic Euler-product estimate.-/
theorem rankinEulerMajorant_le_exp_primeRankinSum {R : ℕ} {δ : ℝ}
    (hδ1 : δ < 1) :
    rankinEulerMajorant (Nat.primesLE R) 2 (1 - δ) ≤
      Real.exp (divisorEulerLoss (1 - δ) * primeRankinSum R δ) := by
  rw [← Real.exp_log (rankinEulerMajorant_primes_pos (sub_pos.mpr hδ1))]
  exact Real.exp_le_exp.mpr
    (log_rankinEulerMajorant_le_divisorEulerLoss_mul_primeRankinSum hδ1)

/-! ## The chosen Rankin exponent -/

/-- A strict version of `rankinDelta_le_one`, useful because convergence of the Euler product requires a strictly positive Dirichlet exponent.-/
theorem rankinDelta_lt_one {H R : ℕ} (hR : 1 < R)
    (huR : rankinU H R < R) (hu : 0 < rankinU H R) :
    rankinDelta H R < 1 := by
  rw [rankinDelta, div_lt_one (Real.log_pos (by exact_mod_cast hR))]
  exact Real.log_lt_log hu huR

/-- The defining identity `δ log R = log u`.-/
theorem rankinDelta_mul_log_base {H R : ℕ} (hR : 1 < R) :
    rankinDelta H R * Real.log R = Real.log (rankinU H R) := by
  rw [rankinDelta, div_mul_cancel₀]
  exact (Real.log_pos (by exact_mod_cast hR)).ne'

/-- The paper's condition `u ≤ R^(1/2)` puts the chosen exponent in `δ ≤ 1/2`.-/
theorem rankinDelta_le_half_of_u_le_sqrt {H R : ℕ} (hR : 1 < R)
    (hu : 0 < rankinU H R) (huSqrt : rankinU H R ≤ Real.sqrt R) :
    rankinDelta H R ≤ 1 / 2 := by
  have hRpos : 0 < (R : ℝ) := by positivity
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  rw [rankinDelta, div_le_iff₀ hlogR]
  calc
    Real.log (rankinU H R) ≤ Real.log (Real.sqrt R) :=
      Real.log_le_log hu huSqrt
    _ = Real.log R / 2 := Real.log_sqrt hRpos.le
    _ = (1 / 2) * Real.log R := by ring

/-- Unconditional finite form of the Rankin/Euler-product argument for Lemma 2.5.-/
theorem finiteDivisorWeightedSmoothCount_le_exp_primeRankinSum {R X : ℕ}
    (hX : 0 < X) (hR : 1 < R) (hu : 1 ≤ rankinU X R)
    (huR : rankinU X R < R) :
    finiteDivisorWeightedSmoothCount R X ≤
      (X : ℝ) * Real.exp
        (-rankinU X R * Real.log (rankinU X R) +
          divisorEulerLoss (1 - rankinDelta X R) *
            primeRankinSum R (rankinDelta X R)) := by
  have hδ0 : 0 ≤ rankinDelta X R := rankinDelta_nonneg hR hu
  have hδ1 : rankinDelta X R < 1 :=
    rankinDelta_lt_one hR huR (zero_lt_one.trans_le hu)
  have hfinite :
      finiteSmoothRpowSum (fun m ↦ orderedDivisorCount 2 m) R X
          (rankinDelta X R - 1) ≤
        rankinEulerMajorant (Nat.primesLE R) 2 (1 - rankinDelta X R) := by
    simpa only [neg_sub] using
      finiteDivisorRankinSum_le_eulerMajorant (R := R) (X := X)
        (sub_pos.mpr hδ1)
  have heuler := rankinEulerMajorant_le_exp_primeRankinSum
    (R := R) (δ := rankinDelta X R) hδ1
  have hxpow : (X : ℝ) ^ (1 - rankinDelta X R) =
      (X : ℝ) * Real.exp
        (-rankinU X R * Real.log (rankinU X R)) := by
    rw [show 1 - rankinDelta X R = 1 + (-rankinDelta X R) by ring,
      Real.rpow_add (by exact_mod_cast hX), Real.rpow_one,
      rankin_cutoff_rpow hX hR]
  calc
    finiteDivisorWeightedSmoothCount R X ≤
        (X : ℝ) ^ (1 - rankinDelta X R) *
          finiteSmoothRpowSum (fun m ↦ orderedDivisorCount 2 m) R X
            (rankinDelta X R - 1) :=
      finiteDivisorWeightedSmoothCount_le_chosen_rankin hR hu huR.le
    _ ≤ (X : ℝ) ^ (1 - rankinDelta X R) *
        rankinEulerMajorant (Nat.primesLE R) 2 (1 - rankinDelta X R) :=
      mul_le_mul_of_nonneg_left hfinite (Real.rpow_nonneg (by positivity) _)
    _ ≤ (X : ℝ) ^ (1 - rankinDelta X R) *
        Real.exp (divisorEulerLoss (1 - rankinDelta X R) *
          primeRankinSum R (rankinDelta X R)) :=
      mul_le_mul_of_nonneg_left heuler (Real.rpow_nonneg (by positivity) _)
    _ = (X : ℝ) * Real.exp
        (-rankinU X R * Real.log (rankinU X R) +
          divisorEulerLoss (1 - rankinDelta X R) *
            primeRankinSum R (rankinDelta X R)) := by
      rw [hxpow, Real.exp_add]
      ring

/-! ## Fully explicit Chebyshev specialization -/

/-- The explicit small-exponent prime-sum bound supplied by `PrimeSums`.-/
def smallPrimeRankinError (R : ℕ) (δ : ℝ) : ℝ :=
  Real.log 4 *
      (Real.log (Real.log (3 * (R : ℝ))) - Real.log (Real.log 2) +
        (Real.log 2)⁻¹) +
    2 * δ * (Real.log 4 * (1 + Real.log R))

/-- The resulting explicit logarithmic error in the divisor-weighted smooth-number estimate.-/
def divisorSmoothError (R X : ℕ) : ℝ :=
  divisorEulerLoss (1 - rankinDelta X R) *
    smallPrimeRankinError R (rankinDelta X R)

/-- Prime-sum error in the conventional `log log (3R) + u / log u` shape.-/
def uLogUPrimeError (R X : ℕ) : ℝ :=
  Real.log 4 *
      (Real.log (Real.log (3 * (R : ℝ))) - Real.log (Real.log 2) +
        (Real.log 2)⁻¹) +
    2 * Real.log 4 * (1 + (Real.log 2)⁻¹) *
      (rankinU X R / Real.log (rankinU X R))

/-- In the small-exponent range, the explicit Chebyshev error has the paper's conventional `log log (3R) + u / log u` form.-/
theorem smallPrimeRankinError_le_uLogUPrimeError {R X : ℕ}
    (hR : 2 ≤ R) (hu : 1 < rankinU X R)
    (hsmall : rankinDelta X R * Real.log R ≤ 1) :
    smallPrimeRankinError R (rankinDelta X R) ≤ uLogUPrimeError R X := by
  have hR' : 1 < R := lt_of_lt_of_le (by norm_num) hR
  have hlogRpos : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR')
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2le : Real.log (2 : ℝ) ≤ Real.log R :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hR)
  have hδ0 : 0 ≤ rankinDelta X R := rankinDelta_nonneg hR' hu.le
  have hlogu : 0 < Real.log (rankinU X R) := Real.log_pos hu
  have hδlog : rankinDelta X R * Real.log R = Real.log (rankinU X R) :=
    rankinDelta_mul_log_base hR'
  have hlogu_le_one : Real.log (rankinU X R) ≤ 1 := hδlog ▸ hsmall
  have hδlog2 : rankinDelta X R * Real.log 2 ≤ Real.log (rankinU X R) := by
    calc
      rankinDelta X R * Real.log 2 ≤ rankinDelta X R * Real.log R :=
        mul_le_mul_of_nonneg_left hlog2le hδ0
      _ = Real.log (rankinU X R) := hδlog
  have hδle : rankinDelta X R ≤
      Real.log (rankinU X R) / Real.log 2 :=
    (le_div_iff₀ hlog2pos).2 hδlog2
  have hlogu_le_frac : Real.log (rankinU X R) ≤
      rankinU X R / Real.log (rankinU X R) := by
    apply (le_div_iff₀ hlogu).2
    nlinarith [hlogu.le]
  have hkernel : rankinDelta X R * (1 + Real.log R) ≤
      (1 + (Real.log 2)⁻¹) *
        (rankinU X R / Real.log (rankinU X R)) := by
    calc
      rankinDelta X R * (1 + Real.log R) =
          rankinDelta X R + Real.log (rankinU X R) := by
        rw [← hδlog]
        ring
      _ ≤ Real.log (rankinU X R) / Real.log 2 +
          Real.log (rankinU X R) := add_le_add_left hδle _
      _ = (1 + (Real.log 2)⁻¹) * Real.log (rankinU X R) := by ring
      _ ≤ (1 + (Real.log 2)⁻¹) *
          (rankinU X R / Real.log (rankinU X R)) :=
        mul_le_mul_of_nonneg_left hlogu_le_frac (by positivity)
  rw [smallPrimeRankinError, uLogUPrimeError]
  apply add_le_add_right _ _
  calc
    2 * rankinDelta X R * (Real.log 4 * (1 + Real.log R)) =
        (2 * Real.log 4) * (rankinDelta X R * (1 + Real.log R)) := by ring
    _ ≤ (2 * Real.log 4) * ((1 + (Real.log 2)⁻¹) *
        (rankinU X R / Real.log (rankinU X R))) :=
      mul_le_mul_of_nonneg_left hkernel (by positivity)
    _ = 2 * Real.log 4 * (1 + (Real.log 2)⁻¹) *
        (rankinU X R / Real.log (rankinU X R)) := by ring

/-- Prime Rankin sum with an explicit `log log (3R) + u / log u` upper bound.-/
theorem primeRankinSum_le_uLogUPrimeError {R X : ℕ}
    (hR : 2 ≤ R) (hu : 1 < rankinU X R)
    (hsmall : rankinDelta X R * Real.log R ≤ 1) :
    primeRankinSum R (rankinDelta X R) ≤ uLogUPrimeError R X := by
  exact (primeRankinSum_le_loglog_three_mul hR
    (rankinDelta_nonneg (lt_of_lt_of_le (by norm_num) hR) hu.le) hsmall).trans
      (smallPrimeRankinError_le_uLogUPrimeError hR hu hsmall)

/-- A fixed loss valid whenever `δ ≤ 1/2`, as in the paper's range `u ≤ √R`.-/
def divisorEulerHalfLoss : ℝ :=
  2 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))

theorem divisorEulerHalfLoss_pos : 0 < divisorEulerHalfLoss := by
  rw [divisorEulerHalfLoss]
  exact div_pos (by norm_num) (sub_pos.mpr <|
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))

/-- Monotonicity of the Euler-factor loss on the half-exponent range.-/
theorem divisorEulerLoss_le_half {δ : ℝ} (hδ : δ ≤ 1 / 2) :
    divisorEulerLoss (1 - δ) ≤ divisorEulerHalfLoss := by
  have hs : 0 < 1 - δ := by linarith
  have hp := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
    (show -(1 - δ) ≤ -(1 / 2 : ℝ) by linarith)
  have hden : 0 < 1 - (2 : ℝ) ^ (-(1 - δ)) := sub_pos.mpr <|
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hs)
  have hdenHalf : 0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) := sub_pos.mpr <|
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  rw [divisorEulerLoss, divisorEulerHalfLoss]
  apply (div_le_div_iff₀ hden hdenHalf).2
  nlinarith

/-- Fully numerical multiplier times the `log log (3R) + u / log u` error.-/
def paperDivisorError (R X : ℕ) : ℝ :=
  divisorEulerHalfLoss * uLogUPrimeError R X

/-- Explicit unconditional version of Lemma 2.5 in the range where `δ log R ≤ 1`.-/
theorem finiteDivisorWeightedSmoothCount_le_explicit {R X : ℕ}
    (hX : 0 < X) (hR : 2 ≤ R) (hu : 1 ≤ rankinU X R)
    (huR : rankinU X R < R)
    (hsmall : rankinDelta X R * Real.log R ≤ 1) :
    finiteDivisorWeightedSmoothCount R X ≤
      (X : ℝ) * Real.exp
        (-rankinU X R * Real.log (rankinU X R) + divisorSmoothError R X) := by
  have hR' : 1 < R := lt_of_lt_of_le (by norm_num) hR
  have hδ0 : 0 ≤ rankinDelta X R := rankinDelta_nonneg hR' hu
  have hprime : primeRankinSum R (rankinDelta X R) ≤
      smallPrimeRankinError R (rankinDelta X R) := by
    simpa only [smallPrimeRankinError] using
      primeRankinSum_le_loglog_three_mul hR hδ0 hsmall
  have hloss : 0 ≤ divisorEulerLoss (1 - rankinDelta X R) :=
    (divisorEulerLoss_pos (sub_pos.mpr <| rankinDelta_lt_one hR' huR
      (zero_lt_one.trans_le hu))).le
  have herror :
      divisorEulerLoss (1 - rankinDelta X R) *
          primeRankinSum R (rankinDelta X R) ≤ divisorSmoothError R X := by
    rw [divisorSmoothError]
    exact mul_le_mul_of_nonneg_left hprime hloss
  calc
    finiteDivisorWeightedSmoothCount R X ≤
        (X : ℝ) * Real.exp
          (-rankinU X R * Real.log (rankinU X R) +
            divisorEulerLoss (1 - rankinDelta X R) *
              primeRankinSum R (rankinDelta X R)) :=
      finiteDivisorWeightedSmoothCount_le_exp_primeRankinSum hX hR' hu huR
    _ ≤ (X : ℝ) * Real.exp
        (-rankinU X R * Real.log (rankinU X R) + divisorSmoothError R X) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (add_le_add_right herror _)

/-- Clean exponential tail.-/
theorem finiteDivisorWeightedSmoothCount_le_half_u_log_u {R X : ℕ}
    (hX : 0 < X) (hR : 2 ≤ R) (hu : 1 ≤ rankinU X R)
    (huR : rankinU X R < R)
    (hsmall : rankinDelta X R * Real.log R ≤ 1)
    (hdom : divisorSmoothError R X ≤
      rankinU X R * Real.log (rankinU X R) / 2) :
    finiteDivisorWeightedSmoothCount R X ≤
      (X : ℝ) * Real.exp
        (-(rankinU X R * Real.log (rankinU X R)) / 2) := by
  calc
    finiteDivisorWeightedSmoothCount R X ≤
        (X : ℝ) * Real.exp
          (-rankinU X R * Real.log (rankinU X R) + divisorSmoothError R X) :=
      finiteDivisorWeightedSmoothCount_le_explicit hX hR hu huR hsmall
    _ ≤ (X : ℝ) * Real.exp
        (-(rankinU X R * Real.log (rankinU X R)) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      linarith

/-! ## Paper-shaped formulation -/

/-- The divisor-weighted census is positive as soon as the cutoff contains `1`.-/
theorem finiteDivisorWeightedSmoothCount_pos {R X : ℕ} (hX : 0 < X) :
    0 < finiteDivisorWeightedSmoothCount R X := by
  have hmem : 1 ∈ finiteSmoothSet R X := by
    rw [mem_finiteSmoothSet]
    exact ⟨le_rfl, hX, by simp [IsSmooth]⟩
  have hone : (orderedDivisorCount 2 1 : ℝ) = 1 := by
    simpa [divisorRankinWeight] using divisorRankinWeight_one (1 : ℝ)
  rw [finiteDivisorWeightedSmoothCount, finiteTauSmoothCount]
  have hle : (orderedDivisorCount 2 1 : ℝ) ≤
      ∑ m ∈ finiteSmoothSet R X, (orderedDivisorCount 2 m : ℝ) := by
    exact Finset.single_le_sum (fun m _ ↦ Nat.cast_nonneg (orderedDivisorCount 2 m)) hmem
  rw [hone] at hle
  exact zero_lt_one.trans_le hle

/-- Paper-shaped exponential form of the general estimate (2.6), with a fixed Euler multiplier and the explicit error `log log (3R) + u / log u`.-/
theorem finiteDivisorWeightedSmoothCount_le_paper_error {R X : ℕ}
    (hX : 0 < X) (hR : 2 ≤ R) (hu : 1 < rankinU X R)
    (huSqrt : rankinU X R ≤ Real.sqrt R)
    (hsmall : rankinDelta X R * Real.log R ≤ 1) :
    finiteDivisorWeightedSmoothCount R X ≤
      (X : ℝ) * Real.exp
        (-rankinU X R * Real.log (rankinU X R) + paperDivisorError R X) := by
  have hR' : 1 < R := lt_of_lt_of_le (by norm_num) hR
  have huR : rankinU X R < R :=
    huSqrt.trans_lt (Real.sqrt_lt_self_iff.mpr (by exact_mod_cast hR'))
  have hδhalf : rankinDelta X R ≤ 1 / 2 :=
    rankinDelta_le_half_of_u_le_sqrt hR' (zero_lt_one.trans hu) huSqrt
  have hprime : primeRankinSum R (rankinDelta X R) ≤ uLogUPrimeError R X :=
    primeRankinSum_le_uLogUPrimeError hR hu hsmall
  have hloss : divisorEulerLoss (1 - rankinDelta X R) ≤ divisorEulerHalfLoss :=
    divisorEulerLoss_le_half hδhalf
  have herror : divisorEulerLoss (1 - rankinDelta X R) *
      primeRankinSum R (rankinDelta X R) ≤ paperDivisorError R X := by
    rw [paperDivisorError]
    exact mul_le_mul hloss hprime (primeRankinSum_nonneg R (rankinDelta X R))
      divisorEulerHalfLoss_pos.le
  calc
    finiteDivisorWeightedSmoothCount R X ≤
        (X : ℝ) * Real.exp
          (-rankinU X R * Real.log (rankinU X R) +
            divisorEulerLoss (1 - rankinDelta X R) *
              primeRankinSum R (rankinDelta X R)) :=
      finiteDivisorWeightedSmoothCount_le_exp_primeRankinSum hX hR' hu.le huR
    _ ≤ (X : ℝ) * Real.exp
        (-rankinU X R * Real.log (rankinU X R) + paperDivisorError R X) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (add_le_add_right herror _)

/-- Log-normalized form of (2.6).-/
theorem log_divisorWeightedSmoothCount_div_le_paper_error {R X : ℕ}
    (hX : 0 < X) (hR : 2 ≤ R) (hu : 1 < rankinU X R)
    (huSqrt : rankinU X R ≤ Real.sqrt R)
    (hsmall : rankinDelta X R * Real.log R ≤ 1) :
    Real.log (finiteDivisorWeightedSmoothCount R X / X) ≤
      -rankinU X R * Real.log (rankinU X R) + paperDivisorError R X := by
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
  have hbound := finiteDivisorWeightedSmoothCount_le_paper_error
    hX hR hu huSqrt hsmall
  have hdiv : finiteDivisorWeightedSmoothCount R X / X ≤
      Real.exp (-rankinU X R * Real.log (rankinU X R) +
        paperDivisorError R X) := by
    apply (div_le_iff₀ hXreal).2
    simpa [mul_comm] using hbound
  have hdivpos : 0 < finiteDivisorWeightedSmoothCount R X / X :=
    div_pos (finiteDivisorWeightedSmoothCount_pos hX) hXreal
  simpa only [Real.log_exp] using Real.log_le_log hdivpos hdiv

/-- Clean form of Lemma 2.5 under one explicit dominance inequality.-/
theorem finiteDivisorWeightedSmoothCount_le_paper_half_u_log_u {R X : ℕ}
    (hX : 0 < X) (hR : 2 ≤ R) (hu : 1 < rankinU X R)
    (huSqrt : rankinU X R ≤ Real.sqrt R)
    (hsmall : rankinDelta X R * Real.log R ≤ 1)
    (hdom : paperDivisorError R X ≤
      rankinU X R * Real.log (rankinU X R) / 2) :
    finiteDivisorWeightedSmoothCount R X ≤
      (X : ℝ) * Real.exp
        (-(rankinU X R * Real.log (rankinU X R)) / 2) := by
  calc
    finiteDivisorWeightedSmoothCount R X ≤
        (X : ℝ) * Real.exp
          (-rankinU X R * Real.log (rankinU X R) + paperDivisorError R X) :=
      finiteDivisorWeightedSmoothCount_le_paper_error hX hR hu huSqrt hsmall
    _ ≤ (X : ℝ) * Real.exp
        (-(rankinU X R * Real.log (rankinU X R)) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      linarith

end

end RankAmplification
