import Tengoku
import Tengoku.Twinprime.TwinPrime.Basic
import Tengoku.Twinprime.TwinPrime.Sieve.TwinSieve

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A lower bound: twin rough numbers via Legendre's sieve

The Selberg sieve gives *upper* bounds.  The exact inclusion–exclusion identity (Legendre)

  `siftedSum = ∑_{d ∣ P} μ(d) · A_d = X ∏_{p ∣ P} (1 - ν p) + ∑_{d ∣ P} μ(d) R_d`

gives a *lower* bound as soon as the (exponentially many) remainders are under control, i.e. for
sifting levels `z` of size `log x`.  For the twin sequence `n (n + 2)` sifted by all primes
`p ≤ z` (including `2`, with `ν(2) = 1/2`) this yields

  `#{n ≤ x : every prime factor of n(n+2) exceeds z} ≥ (x+1)/z² − 3^{z+1}`,

and with `z = ⌊log x / (2 log 3)⌋` the right-hand side is `≫ x/(log x)²`.  Consequently
(`twinRough_infinite`) there are infinitely many `n` such that **both `n` and `n + 2` have all
their prime factors larger than `log n / (2 log 3)`**.  This is the first lower-bound statement
about "twin-like" pairs in the library; it is far weaker than Brun's 1920 theorem (nine prime
factors) or Chen's theorem, but it is elementary and fully checked.
-/

noncomputable section

open Finset Real Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace TwinPrime.Sieve

/-! ### Legendre's identity for a bounding sieve -/

/-- Legendre's identity: `siftedSum = ∑_{d ∣ P} μ(d) A_d`.
@isnad1 id=eq.0h1v.s5.4de175680574 from=translated src=- shape=addd44c2 vocab=df63e931
-/
theorem siftedSum_eq_sum_moebius_multSum (s : BoundingSieve) :
    s.siftedSum = ∑ d ∈ s.prodPrimes.divisors, (μ d : ℝ) * s.multSum d := by
  calc s.siftedSum
      = ∑ n ∈ s.support, s.weights n * ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, (μ d : ℝ) := by
        rw [siftedSum_eq_sum_support_mul_ite]
        apply sum_congr rfl
        intro n _
        rw [sum_divisors_moebius_real]
    _ = ∑ n ∈ s.support, ∑ d ∈ s.prodPrimes.divisors,
          if d ∣ n then s.weights n * μ d else 0 := by
        apply sum_congr rfl
        intro n _
        rw [mul_sum, ← sum_filter,
          ← Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero (Nat.gcd_dvd_left _ _)]
        apply sum_congr
        · ext x
          simp +contextual [dvd_gcd_iff]
        · intros; rfl
    _ = ∑ d ∈ s.prodPrimes.divisors, (μ d : ℝ) * s.multSum d := by
        rw [sum_comm]
        apply sum_congr rfl
        intro d _
        simp only [multSum]
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        split_ifs <;> ring

/-- The main term of Legendre's identity is `X ∏_{p ∣ P} (1 - ν p)`, and the sifted sum is at
least that minus the sum of all remainders.
@isnad1 id=le.0h1v.s6.95859f71fc2c from=translated src=- shape=2ebc89d5 vocab=da2500af
-/
theorem siftedSum_ge_of_legendre (s : BoundingSieve) :
    s.totalMass * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) -
        ∑ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ s.siftedSum := by
  rw [siftedSum_eq_sum_moebius_multSum,
    IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree s.nu s.nu_mult s.prodPrimes_squarefree]
  simp only [multSum_eq_main_err]
  rw [mul_sum, sub_le_iff_le_add, ← sum_add_distrib]
  apply sum_le_sum
  intro d _
  have habs : -(|s.rem d|) ≤ (μ d : ℝ) * s.rem d := by
    have hμ : |(μ d : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs, abs_moebius]
      split_ifs <;> norm_num
    have h1 : |(μ d : ℝ) * s.rem d| ≤ |s.rem d| := by
      rw [abs_mul]
      calc |(μ d : ℝ)| * |s.rem d| ≤ 1 * |s.rem d| :=
            mul_le_mul_of_nonneg_right hμ (abs_nonneg _)
        _ = |s.rem d| := one_mul _
    linarith [neg_abs_le ((μ d : ℝ) * s.rem d)]
  nlinarith [habs]

/-! ### The twin sieve with all primes `p ≤ z` (including `2`) -/

/--
@isnad1 id=eq.0h0v.s3.4414d8bef76b from=translated src=- shape=3c26ae4f vocab=7fbdda8a
-/
theorem twinRoots_two : twinRoots 2 = 1 := by
  unfold twinRoots
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

/--
@isnad1 id=lt.1h1v.s4.61d6f5eb1e98 from=translated src=- shape=2b511f7f vocab=265d7331
-/
theorem twinRoots_pos {d : ℕ} (hd : d ≠ 0) : 0 < twinRoots d := by
  haveI : NeZero d := ⟨hd⟩
  unfold twinRoots
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff]
  exact ⟨⟨0, by simp⟩⟩

/--
@isnad1 id=le.1h1v.s3.6963a245157f from=translated src=- shape=fdf4e94d vocab=f152f780
-/
theorem twinRoots_prime_le_two {p : ℕ} (hp : p.Prime) : twinRoots p ≤ 2 := by
  by_cases h2 : p = 2
  · subst h2; rw [twinRoots_two]; norm_num
  · rw [twinRoots_prime hp h2]

/-- `ν₂ d = ρ(d)/d` where `ρ(d)` is the number of roots of `r(r+2)` mod `d`.-/
def twinNu2 : ArithmeticFunction ℝ :=
  ⟨fun d => if d = 0 then 0 else (twinRoots d : ℝ) / d, by simp⟩

/--
@isnad1 id=eq.0h1v.s5.091bf573901a from=translated src=- shape=99ce8af2 vocab=8768124a
-/
theorem twinNu2_apply' (d : ℕ) : twinNu2 d = if d = 0 then 0 else (twinRoots d : ℝ) / d := rfl

/--
@isnad1 id=eq.1h1v.s5.629d5550df25 from=translated src=- shape=08262418 vocab=95786454
-/
theorem twinNu2_apply {d : ℕ} (hd : d ≠ 0) : twinNu2 d = (twinRoots d : ℝ) / d := by
  rw [twinNu2_apply', ite_eq_right hd]

/--
@isnad1 id=ismultip.0h0v.s2.086e279afef3 from=translated src=- shape=25b03439 vocab=65229982
-/
theorem twinNu2_isMultiplicative : twinNu2.IsMultiplicative := by
  refine ⟨by simp [twinNu2_apply', twinRoots_one], ?_⟩
  intro m n hmn
  by_cases hm : m = 0
  · simp [twinNu2_apply', hm]
  by_cases hn : n = 0
  · simp [twinNu2_apply', hn]
  rw [twinNu2_apply (mul_ne_zero hm hn), twinNu2_apply hm, twinNu2_apply hn, twinRoots_mul hmn]
  push_cast
  field_simp

/-- The Legendre twin sieve: support `{n(n+2) : n ≤ x}`, all primes `≤ z`.-/
def twinSieveL (x z : ℕ) : BoundingSieve where
  support := (Finset.range (x + 1)).image fun n => n * (n + 2)
  prodPrimes := primorial z
  prodPrimes_squarefree := squarefree_primorial z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := x + 1
  nu := twinNu2
  nu_mult := twinNu2_isMultiplicative
  nu_pos_of_prime := fun p hp _ => by
    rw [twinNu2_apply hp.ne_zero]
    have h1 : (0 : ℝ) < twinRoots p := by exact_mod_cast twinRoots_pos hp.ne_zero
    have h2 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  nu_lt_one_of_prime := fun p hp _ => by
    rw [twinNu2_apply hp.ne_zero, div_lt_one (by exact_mod_cast hp.pos)]
    by_cases h2 : p = 2
    · subst h2; rw [twinRoots_two]; norm_num
    · rw [twinRoots_prime hp h2]
      have := hp.two_le
      exact_mod_cast (by omega : 2 < p)

/--
@isnad1 id=eq.0h3v.s6.47877b68e7c5 from=translated src=- shape=6457a146 vocab=e57cb5ef
-/
theorem twinSieveL_multSum (x z d : ℕ) :
    (twinSieveL x z).multSum d = #{n ∈ range (x + 1) | d ∣ n * (n + 2)} := by
  simp only [multSum, twinSieveL]
  rw [sum_image (fun a _ b _ h => mul_add_two_injective h), ← sum_filter, sum_const,
    nsmul_eq_mul, mul_one]

/-- `|#{n < N : d ∣ n(n+2)} − ρ(d) N / d| ≤ ρ(d)` for every `d ≥ 1`.
@isnad1 id=le.1h2v.s6.305d7e4061e6 from=translated src=- shape=6810bc39 vocab=cd8b724c
-/
theorem abs_card_filter_dvd_sub_le' {N d : ℕ} (hd : d ≠ 0) :
    |((#{n ∈ range N | d ∣ n * (n + 2)} : ℕ) : ℝ) - (twinRoots d : ℝ) * N / d| ≤ twinRoots d := by
  haveI : NeZero d := ⟨hd⟩
  rw [card_filter_dvd_mul_add_two_eq_sum]
  set R := (Finset.univ.filter fun r : ZMod d => r * (r + 2) = 0) with hR
  have hcard : (#R : ℝ) = (twinRoots d : ℝ) := by
    rw [hR, card_twinRoots_filter]
  have : (twinRoots d : ℝ) * N / d = ∑ _r ∈ R, (N : ℝ) / d := by
    rw [sum_const, nsmul_eq_mul, hcard, mul_div_assoc]
  rw [this]
  push_cast
  rw [← sum_sub_distrib]
  calc |∑ r ∈ R, (((#(filter (fun n : ℕ => (n : ZMod d) = r) (range N)) : ℕ) : ℝ) - (N : ℝ) / d)|
      ≤ ∑ r ∈ R, |((#(filter (fun n : ℕ => (n : ZMod d) = r) (range N)) : ℕ) : ℝ) - (N : ℝ) / d| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ R, (1 : ℝ) := sum_le_sum fun r _ => abs_count_residue_sub_le r
    _ = twinRoots d := by rw [sum_const, nsmul_eq_mul, mul_one, hcard]

/--
@isnad1 id=le.1h3v.s5.b1b2261ccf85 from=translated src=- shape=7f1b9b34 vocab=f71958a3
-/
theorem twinSieveL_abs_rem_le (x z : ℕ) {d : ℕ} (hd : d ≠ 0) :
    |(twinSieveL x z).rem d| ≤ twinRoots d := by
  simp only [rem]
  rw [twinSieveL_multSum]
  show |((#{n ∈ range (x + 1) | d ∣ n * (n + 2)} : ℕ) : ℝ) - twinNu2 d * ((x : ℝ) + 1)| ≤ _
  rw [twinNu2_apply hd]
  have := abs_card_filter_dvd_sub_le' (N := x + 1) hd
  push_cast at this
  convert this using 2
  ring

/-! ### Summing the remainders: `∑_{d ∣ P} ρ(d) = ∏_{p ∣ P} (1 + ρ(p)) ≤ 3^{ω P}` -/

/-- `ρ` as an arithmetic function.-/
def twinRhoA : ArithmeticFunction ℝ := ⟨fun d => if d = 0 then 0 else (twinRoots d : ℝ), by simp⟩

/--
@isnad1 id=eq.1h1v.s4.1a503e08ed90 from=translated src=- shape=1dc874df vocab=12744f61
-/
theorem twinRhoA_apply {d : ℕ} (hd : d ≠ 0) : twinRhoA d = twinRoots d := by
  show (if d = 0 then (0 : ℝ) else (twinRoots d : ℝ)) = _
  rw [ite_eq_right hd]

/--
@isnad1 id=ismultip.0h0v.s2.e9ed2263ecee from=translated src=- shape=25b03439 vocab=2829eaa4
-/
theorem twinRhoA_isMultiplicative : twinRhoA.IsMultiplicative := by
  refine ⟨by simp [twinRhoA_apply, twinRoots_one], ?_⟩
  intro m n hmn
  by_cases hm : m = 0
  · simp [twinRhoA, hm]
  by_cases hn : n = 0
  · simp [twinRhoA, hn]
  rw [twinRhoA_apply (mul_ne_zero hm hn), twinRhoA_apply hm, twinRhoA_apply hn, twinRoots_mul hmn]
  push_cast
  ring

/--
@isnad1 id=le.1h1v.s5.3e5e4f1ae5cc from=translated src=- shape=700f51f1 vocab=725f2f8f
-/
theorem sum_divisors_twinRoots_le {P : ℕ} (hP : Squarefree P) :
    (∑ d ∈ P.divisors, (twinRoots d : ℝ)) ≤ 3 ^ #P.primeFactors := by
  have hmul : (ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) twinRhoA).IsMultiplicative :=
    isMultiplicative_moebius.intCast.pmul twinRhoA_isMultiplicative
  have hid := IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree _ hmul hP
  have hleft : ∀ d ∈ P.divisors,
      (μ d : ℝ) * (ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) twinRhoA) d =
        twinRoots d := by
    intro d hd
    have hdsq : Squarefree d := hP.squarefree_of_dvd (dvd_of_mem_divisors hd)
    rw [pmul_apply, intCoe_apply, twinRhoA_apply hdsq.ne_zero, ← mul_assoc]
    have hμ : ((μ d : ℝ)) * (μ d : ℝ) = 1 := by
      have := moebius_sq_eq_one_of_squarefree hdsq
      rw [sq] at this
      exact_mod_cast this
    rw [hμ, one_mul]
  rw [← sum_congr rfl hleft, ← hid]
  calc ∏ p ∈ P.primeFactors, (1 - (ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) twinRhoA) p)
      ≤ ∏ _p ∈ P.primeFactors, (3 : ℝ) := by
        apply prod_le_prod
        · intro p hp
          have hpp := Nat.prime_of_mem_primeFactors hp
          rw [pmul_apply, intCoe_apply, moebius_apply_prime hpp, twinRhoA_apply hpp.ne_zero]
          push_cast
          have : (0 : ℝ) ≤ twinRoots p := by positivity
          linarith
        · intro p hp
          have hpp := Nat.prime_of_mem_primeFactors hp
          rw [pmul_apply, intCoe_apply, moebius_apply_prime hpp, twinRhoA_apply hpp.ne_zero]
          push_cast
          have : (twinRoots p : ℝ) ≤ 2 := by exact_mod_cast twinRoots_prime_le_two hpp
          linarith
    _ = 3 ^ #P.primeFactors := prod_const _

/-! ### The main term: `∏_{p ≤ z} (1 - ν₂ p) ≥ 1 / z²` -/

/-- Telescoping: `∏_{m=3}^{z} (1 - 2/m) = 2 / ((z - 1) z)` for `z ≥ 2`.
@isnad1 id=eq.1h1v.s6.26ab3a3eebe0 from=translated src=- shape=d7688c9b vocab=fcdb32bc
-/
theorem prod_one_sub_two_div (z : ℕ) (hz : 2 ≤ z) :
    ∏ m ∈ Finset.Icc 3 z, (1 - 2 / (m : ℝ)) = 2 / (((z : ℝ) - 1) * z) := by
  induction z with
  | zero => omega
  | succ z ih =>
    rcases Nat.lt_or_ge z 2 with h | h
    · have : z = 1 := by omega
      subst this
      rw [Finset.Icc_eq_empty (by norm_num), prod_empty]
      norm_num
    · rw [Finset.prod_Icc_succ_top (by omega), ih h]
      have hz1 : (z : ℝ) - 1 ≠ 0 := by
        have : (2 : ℝ) ≤ z := by exact_mod_cast h
        linarith
      have hz0 : (z : ℝ) ≠ 0 := by positivity
      have hz2 : (z : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      rw [show ((z : ℝ) + 1 - 1) = z by ring]
      field_simp
      ring

/--
@isnad1 id=le.1h1v.s6.bdd43a3b10e5 from=translated src=- shape=48a28c64 vocab=4cfe5a66
-/
theorem prod_primesLE_one_sub_nu_ge (z : ℕ) (hz : 3 ≤ z) :
    1 / ((z : ℝ) ^ 2) ≤ ∏ p ∈ primesLE z, (1 - twinNu2 p) := by
  have h2mem : 2 ∈ primesLE z := by rw [mem_primesLE]; exact ⟨by omega, Nat.prime_two⟩
  rw [← Finset.mul_prod_erase _ _ h2mem, twinNu2_apply two_ne_zero, twinRoots_two]
  have hodd : ∏ m ∈ Finset.Icc 3 z, (1 - 2 / (m : ℝ)) ≤
      ∏ p ∈ (primesLE z).erase 2, (1 - twinNu2 p) := by
    have hsub : (primesLE z).erase 2 ⊆ Finset.Icc 3 z := by
      intro p hp
      rw [mem_erase, mem_primesLE] at hp
      rw [mem_Icc]
      have := hp.2.2.two_le
      exact ⟨by omega, hp.2.1⟩
    calc ∏ m ∈ Finset.Icc 3 z, (1 - 2 / (m : ℝ))
        = (∏ m ∈ (primesLE z).erase 2, (1 - 2 / (m : ℝ))) *
            ∏ m ∈ Finset.Icc 3 z \ (primesLE z).erase 2, (1 - 2 / (m : ℝ)) := by
          rw [← Finset.prod_sdiff hsub, mul_comm]
      _ ≤ ∏ m ∈ (primesLE z).erase 2, (1 - 2 / (m : ℝ)) := by
          apply mul_le_of_le_one_right
          · apply prod_nonneg
            intro m hm
            rw [mem_erase, mem_primesLE] at hm
            have h3 : (3 : ℝ) ≤ m := by
              have := hm.2.2.two_le
              exact_mod_cast (by omega : 3 ≤ m)
            have : 2 / (m : ℝ) ≤ 2 / 3 := by
              apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3
            linarith
          · apply Finset.prod_le_one
            · intro m hm
              rw [mem_sdiff, mem_Icc] at hm
              have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm.1.1
              have : 2 / (m : ℝ) ≤ 2 / 3 := by
                apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3
              linarith
            · intro m hm
              rw [mem_sdiff, mem_Icc] at hm
              have : (0 : ℝ) ≤ 2 / m := by positivity
              linarith
      _ = ∏ p ∈ (primesLE z).erase 2, (1 - twinNu2 p) := by
          apply prod_congr rfl
          intro p hp
          rw [mem_erase, mem_primesLE] at hp
          rw [twinNu2_apply hp.2.2.ne_zero, twinRoots_prime hp.2.2 hp.1]
          push_cast
          ring
  rw [prod_one_sub_two_div z (by omega)] at hodd
  have hz1 : (1 : ℝ) ≤ (z : ℝ) - 1 := by
    have : (3 : ℝ) ≤ z := by exact_mod_cast hz
    linarith
  have hzpos : (0 : ℝ) < z := by positivity
  calc 1 / ((z : ℝ) ^ 2) = (1 - (1 : ℝ) / 2) * (2 / ((z : ℝ) * z)) := by
        field_simp; ring
    _ ≤ (1 - (1 : ℝ) / 2) * (2 / (((z : ℝ) - 1) * z)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith
    _ ≤ (1 - (1 : ℝ) / 2) * ∏ p ∈ (primesLE z).erase 2, (1 - twinNu2 p) := by
        apply mul_le_mul_of_nonneg_left hodd (by norm_num)
    _ = _ := by norm_num

/-! ### The counting lower bound -/

/-- `Nat.Coprime (primorial z) m ↔ m` has no prime factor `≤ z`.
@isnad1 id=iff.0h2v.s4.1e1b6d670162 from=translated src=- shape=c2a5370c vocab=9bee2ec9
-/
theorem coprime_primorial_iff {z m : ℕ} :
    Nat.Coprime (primorial z) m ↔ ∀ p, p.Prime → p ≤ z → ¬ p ∣ m := by
  constructor
  · intro h p hp hpz hpm
    have h1 : p ∣ primorial z := hp.dvd_primorial_iff.mpr hpz
    have h2 : p ∣ Nat.gcd (primorial z) m := Nat.dvd_gcd h1 hpm
    rw [Nat.Coprime.gcd_eq_one h] at h2
    exact hp.not_dvd_one h2
  · intro h
    rw [primorial_eq_prod_primesLE]
    apply Nat.Coprime.prod_left
    intro p hp
    rw [mem_primesLE] at hp
    exact (Nat.Prime.coprime_iff_not_dvd hp.2).mpr (h p hp.2 hp.1)

end TwinPrime.Sieve
