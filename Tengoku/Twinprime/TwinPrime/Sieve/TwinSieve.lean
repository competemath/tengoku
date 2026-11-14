import Tengoku
import Tengoku.Twinprime.TwinPrime.Basic
import Tengoku.Twinprime.TwinPrime.Sieve.Fundamental
import Tengoku.Twinprime.TwinPrime.Sieve.ErrorSum
import Tengoku.Twinprime.TwinPrime.Sieve.Expansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Selberg sieve for twin primes: setup and remainder bound

We sift the set `{n (n + 2) : 0 ≤ n ≤ x}` by the odd primes `p ≤ z`.  The relevant density is
`ν(d) = 2^{ω(d)} / d` for odd squarefree `d`, because `r (r + 2) ≡ 0 (mod d)` has exactly
`2^{ω(d)}` solutions mod `d` (Chinese remainder theorem; two roots `0, -2` modulo each odd prime).

Main results of this file:

* `twinRoots_eq` : the number of solutions of `r (r + 2) = 0` in `ZMod d` is `2^{ω d}` for odd
  squarefree `d`;
* `twinSieve x z hz : SelbergSieve` with support the values `n (n + 2)`, `P = ∏_{3 ≤ p ≤ z} p`,
  `X = x + 1`, `ν = twinNu`, level `z²`;
* `twinSieve_abs_rem_le` : `|R_d| ≤ 2^{ω d}` for every `d ∣ P`.
-/

noncomputable section

open Finset Real Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace TwinPrime.Sieve

/-! ### The odd primorial -/

/-- The product of the odd primes `≤ z`.-/
def oddPrimorial (z : ℕ) : ℕ := ∏ p ∈ (primesLE z).erase 2, p

theorem oddPrimorial_dvd_primorial (z : ℕ) : oddPrimorial z ∣ primorial z := by
  rw [primorial_eq_prod_primesLE]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (erase_subset _ _)

theorem oddPrimorial_squarefree (z : ℕ) : Squarefree (oddPrimorial z) :=
  (squarefree_primorial z).squarefree_of_dvd (oddPrimorial_dvd_primorial z)

theorem oddPrimorial_ne_zero (z : ℕ) : oddPrimorial z ≠ 0 := (oddPrimorial_squarefree z).ne_zero

/-- A prime divides the odd primorial iff it is an odd prime `≤ z`.-/
theorem prime_dvd_oddPrimorial_iff {p z : ℕ} (hp : p.Prime) :
    p ∣ oddPrimorial z ↔ p ≠ 2 ∧ p ≤ z := by
  unfold oddPrimorial
  rw [hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, hq, hpq⟩
    rw [mem_erase, mem_primesLE] at hq
    rw [Nat.prime_dvd_prime_iff_eq hp hq.2.2] at hpq
    subst hpq
    exact ⟨hq.1, hq.2.1⟩
  · rintro ⟨h2, hz⟩
    exact ⟨p, by rw [mem_erase, mem_primesLE]; exact ⟨h2, hz, hp⟩, dvd_rfl⟩

theorem not_two_dvd_of_dvd_oddPrimorial {d z : ℕ} (hd : d ∣ oddPrimorial z) : ¬ 2 ∣ d := by
  intro h2
  have := (prime_dvd_oddPrimorial_iff Nat.prime_two).mp (h2.trans hd)
  exact this.1 rfl

theorem three_le_of_prime_dvd_oddPrimorial {p z : ℕ} (hp : p.Prime) (hpP : p ∣ oddPrimorial z) :
    3 ≤ p := by
  have h := (prime_dvd_oddPrimorial_iff hp).mp hpP
  have := hp.two_le
  omega

/-! ### The density `ν d = 2^{ω d} / d` -/

/-- `twinNu d = 2^{ω d} / d` for `d ≠ 0`, and `twinNu 0 = 0`.-/
def twinNu : ArithmeticFunction ℝ :=
  ⟨fun d => if d = 0 then 0 else (2 : ℝ) ^ (ω d) / d, by simp⟩

theorem twinNu_apply' (d : ℕ) : twinNu d = if d = 0 then 0 else (2 : ℝ) ^ (ω d) / d := rfl

theorem twinNu_apply {d : ℕ} (hd : d ≠ 0) : twinNu d = (2 : ℝ) ^ (ω d) / d := by
  rw [twinNu_apply', ite_eq_right hd]

theorem twinNu_prime {p : ℕ} (hp : p.Prime) : twinNu p = 2 / p := by
  rw [twinNu_apply hp.ne_zero, cardDistinctFactors_apply_prime hp, pow_one]

theorem twinNu_isMultiplicative : twinNu.IsMultiplicative := by
  refine ⟨by simp [twinNu_apply'], ?_⟩
  intro m n hmn
  by_cases hm : m = 0
  · simp [twinNu_apply', hm]
  by_cases hn : n = 0
  · simp [twinNu_apply', hn]
  rw [twinNu_apply (mul_ne_zero hm hn), twinNu_apply hm, twinNu_apply hn,
    cardDistinctFactors_mul hmn, pow_add]
  push_cast
  field_simp

/-! ### Roots of `r (r + 2)` modulo `d` -/

/-- The number of solutions of `r (r + 2) = 0` in `ZMod d`.-/
def twinRoots (d : ℕ) : ℕ := Nat.card {r : ZMod d // r * (r + 2) = 0}

theorem twinRoots_mul {m n : ℕ} (h : m.Coprime n) :
    twinRoots (m * n) = twinRoots m * twinRoots n := by
  unfold twinRoots
  let e := ZMod.chineseRemainder h
  have key : ∀ r : ZMod (m * n),
      r * (r + 2) = 0 ↔ (e r).1 * ((e r).1 + 2) = 0 ∧ (e r).2 * ((e r).2 + 2) = 0 := by
    intro r
    constructor
    · intro hr
      have h0 : e (r * (r + 2)) = 0 := by rw [hr, _root_.map_zero]
      rw [map_mul, map_add, map_ofNat] at h0
      rw [Prod.ext_iff] at h0
      simpa using h0
    · rintro ⟨h1, h2⟩
      apply e.injective
      rw [map_mul, map_add, map_ofNat, _root_.map_zero]
      rw [Prod.ext_iff]
      simpa using ⟨h1, h2⟩
  have e' : {r : ZMod (m * n) // r * (r + 2) = 0} ≃
      {q : ZMod m × ZMod n // q.1 * (q.1 + 2) = 0 ∧ q.2 * (q.2 + 2) = 0} :=
    e.toEquiv.subtypeEquiv key
  rw [Nat.card_congr e',
    Nat.card_congr (Equiv.subtypeProdEquivProd (p := fun a : ZMod m => a * (a + 2) = 0)
      (q := fun b : ZMod n => b * (b + 2) = 0)),
    Nat.card_prod]

theorem twinRoots_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : twinRoots p = 2 := by
  haveI := Fact.mk hp
  unfold twinRoots
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  have hset : (Finset.univ.filter fun r : ZMod p => r * (r + 2) = 0) = {0, -2} := by
    ext r
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    · rintro (h | h)
      · rw [h]; ring
      · rw [h]; ring
  rw [hset, Finset.card_pair_eq_two_iff]
  intro h
  apply h2
  linear_combination h

theorem twinRoots_one : twinRoots 1 = 1 := by
  unfold twinRoots
  have : ∀ r : ZMod 1, r * (r + 2) = 0 := fun r => Subsingleton.elim _ _
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv this), Nat.card_eq_fintype_card, ZMod.card]

/-- For odd squarefree `d`, `r (r + 2) = 0` has exactly `2^{ω d}` solutions in `ZMod d`.-/
theorem twinRoots_eq {d : ℕ} (hd : Squarefree d) (hodd : ¬ 2 ∣ d) : twinRoots d = 2 ^ (ω d) := by
  induction d using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    have hn1 : n = 1 := by
      by_contra h
      have h2 : 2 ≤ n := by omega
      have hpp : p * p ∣ p ^ n := by
        rw [← sq]; exact pow_dvd_pow p h2
      exact hp.ne_one (Nat.isUnit_iff.mp (hd p hpp))
    subst hn1
    rw [pow_one] at hodd ⊢
    rw [twinRoots_prime hp (by rintro rfl; exact hodd dvd_rfl),
      cardDistinctFactors_apply_prime hp, pow_one]
  | zero => exact absurd hd not_squarefree_zero
  | one => rw [twinRoots_one, cardDistinctFactors_one, pow_zero]
  | coprime a b _ _ hab iha ihb =>
    rw [twinRoots_mul hab, cardDistinctFactors_mul hab, pow_add,
      iha (hd.squarefree_of_dvd (dvd_mul_right a b))
        (fun h => hodd (h.trans (dvd_mul_right a b))),
      ihb (hd.squarefree_of_dvd (dvd_mul_left b a))
        (fun h => hodd (h.trans (dvd_mul_left b a)))]

/-! ### Counting `n < N` with `d ∣ n (n + 2)` -/

/-- Number of `n < N` in a fixed residue class mod `d`, as a real number, differs from `N / d`
by at most one.-/
theorem abs_count_residue_sub_le {N d : ℕ} [NeZero d] (r : ZMod d) :
    |((#(filter (fun n : ℕ => (n : ZMod d) = r) (range N)) : ℕ) : ℝ) - (N : ℝ) / d| ≤ 1 := by
  have hd : 0 < d := NeZero.pos d
  have hcount : #(filter (fun n : ℕ => (n : ZMod d) = r) (range N)) =
      N / d + if r.val % d < N % d then 1 else 0 := by
    rw [← Nat.count_modEq_card N hd r.val, Nat.count_eq_card_filter_range]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro n _
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  rw [hcount]
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hfloor_le : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
  have hfloor_gt : (N : ℝ) / d - 1 < ((N / d : ℕ) : ℝ) := by
    have hmod : N % d < d := Nat.mod_lt N hd
    have hdiv : (N : ℝ) = d * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod N d).symm
    have hmod' : ((N % d : ℕ) : ℝ) < d := by exact_mod_cast hmod
    rw [div_sub_one hdr.ne', div_lt_iff₀ hdr]
    nlinarith
  push_cast
  rw [abs_le]
  split_ifs <;> constructor <;> linarith

/-- For `d > 0`, the number of `n < N` with `d ∣ n (n + 2)` is a sum over the roots `r` of
`r (r + 2) = 0` in `ZMod d` of the number of `n < N` with `n ≡ r`.-/
theorem card_filter_dvd_mul_add_two_eq_sum {N d : ℕ} [NeZero d] :
    #{n ∈ range N | d ∣ n * (n + 2)} =
      ∑ r ∈ (Finset.univ.filter fun r : ZMod d => r * (r + 2) = 0),
        #(filter (fun n : ℕ => (n : ZMod d) = r) (range N)) := by
  have hcast : ∀ n : ℕ, d ∣ n * (n + 2) ↔ (n : ZMod d) * ((n : ZMod d) + 2) = 0 := by
    intro n
    rw [← CharP.cast_eq_zero_iff (ZMod d) d]
    push_cast
    rfl
  rw [Finset.card_eq_sum_card_fiberwise (f := fun n : ℕ => (n : ZMod d))
    (t := Finset.univ.filter fun r : ZMod d => r * (r + 2) = 0)]
  · apply sum_congr rfl
    intro r hr
    rw [mem_filter] at hr
    apply congrArg Finset.card
    ext n
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rw [hcast, h3]
      exact hr.2
  · intro n hn
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hn ⊢
    exact (hcast n).mp hn.2

theorem card_twinRoots_filter {d : ℕ} [NeZero d] :
    #(Finset.univ.filter fun r : ZMod d => r * (r + 2) = 0) = twinRoots d := by
  unfold twinRoots
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **Key counting estimate.** For odd squarefree `d`,
`| #{n < N : d ∣ n (n + 2)} - 2^{ω d} N / d | ≤ 2^{ω d}`.-/
theorem abs_card_filter_dvd_sub_le {N d : ℕ} (hd : Squarefree d) (hodd : ¬ 2 ∣ d) :
    |((#{n ∈ range N | d ∣ n * (n + 2)} : ℕ) : ℝ) - (2 : ℝ) ^ (ω d) * N / d| ≤ 2 ^ (ω d) := by
  haveI : NeZero d := ⟨hd.ne_zero⟩
  rw [card_filter_dvd_mul_add_two_eq_sum]
  set R := (Finset.univ.filter fun r : ZMod d => r * (r + 2) = 0) with hR
  have hcard : (#R : ℝ) = (2 : ℝ) ^ (ω d) := by
    rw [hR, card_twinRoots_filter, twinRoots_eq hd hodd]
    push_cast
    rfl
  have : (2 : ℝ) ^ (ω d) * N / d = ∑ _r ∈ R, (N : ℝ) / d := by
    rw [sum_const, nsmul_eq_mul, hcard, mul_div_assoc]
  rw [this]
  push_cast
  rw [← sum_sub_distrib]
  calc |∑ r ∈ R, (((#(filter (fun n : ℕ => (n : ZMod d) = r) (range N)) : ℕ) : ℝ) - (N : ℝ) / d)|
      ≤ ∑ r ∈ R, |((#(filter (fun n : ℕ => (n : ZMod d) = r) (range N)) : ℕ) : ℝ) - (N : ℝ) / d| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ R, (1 : ℝ) := sum_le_sum fun r _ => abs_count_residue_sub_le r
    _ = 2 ^ (ω d) := by rw [sum_const, nsmul_eq_mul, mul_one, hcard]

/-! ### The sieve -/

/-- The Selberg sieve for twin primes: support `{n (n + 2) : n ≤ x}`, sifting primes the odd
primes `≤ z`, level `z²`.-/
def twinSieve (x z : ℕ) (hz : 1 ≤ z) : SelbergSieve where
  support := (Finset.range (x + 1)).image fun n => n * (n + 2)
  prodPrimes := oddPrimorial z
  prodPrimes_squarefree := oddPrimorial_squarefree z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := x + 1
  nu := twinNu
  nu_mult := twinNu_isMultiplicative
  nu_pos_of_prime := fun p hp _ => by
    rw [twinNu_prime hp]
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  nu_lt_one_of_prime := fun p hp hpP => by
    rw [twinNu_prime hp, div_lt_one (by exact_mod_cast hp.pos)]
    have := three_le_of_prime_dvd_oddPrimorial hp hpP
    exact_mod_cast (by omega : 2 < p)
  level := (z : ℝ) ^ 2
  one_le_level := by
    have : (1 : ℝ) ≤ z := by exact_mod_cast hz
    nlinarith

theorem twinSieve_prodPrimes (x z : ℕ) (hz : 1 ≤ z) :
    (twinSieve x z hz).prodPrimes = oddPrimorial z := rfl

theorem twinSieve_level (x z : ℕ) (hz : 1 ≤ z) : (twinSieve x z hz).level = (z : ℝ) ^ 2 := rfl

theorem twinSieve_totalMass (x z : ℕ) (hz : 1 ≤ z) :
    (twinSieve x z hz).totalMass = x + 1 := rfl

theorem twinSieve_nu (x z : ℕ) (hz : 1 ≤ z) : (twinSieve x z hz).nu = twinNu := rfl

theorem mul_add_two_injective : Function.Injective fun n : ℕ => n * (n + 2) := by
  intro a b h
  have h' : (a + 1) ^ 2 = (b + 1) ^ 2 := by
    rw [show (a + 1) ^ 2 = a * (a + 2) + 1 by ring, show (b + 1) ^ 2 = b * (b + 2) + 1 by ring]
    simp only at h
    rw [h]
  have := Nat.pow_left_injective two_ne_zero h'
  omega

theorem twinSieve_multSum (x z : ℕ) (hz : 1 ≤ z) (d : ℕ) :
    (twinSieve x z hz).multSum d = #{n ∈ range (x + 1) | d ∣ n * (n + 2)} := by
  simp only [multSum, twinSieve]
  rw [sum_image (fun a _ b _ h => mul_add_two_injective h), ← sum_filter, sum_const,
    nsmul_eq_mul, mul_one]

/-- The remainder bound `|R_d| ≤ 2^{ω d}` for `d ∣ P`.-/
theorem twinSieve_abs_rem_le (x z : ℕ) (hz : 1 ≤ z) {d : ℕ} (hd : d ∣ oddPrimorial z) :
    |(twinSieve x z hz).rem d| ≤ (2 : ℝ) ^ (ω d) := by
  have hsq : Squarefree d := (oddPrimorial_squarefree z).squarefree_of_dvd hd
  have hodd := not_two_dvd_of_dvd_oddPrimorial hd
  simp only [rem]
  rw [twinSieve_multSum, twinSieve_nu, twinSieve_totalMass, twinNu_apply hsq.ne_zero]
  have := abs_card_filter_dvd_sub_le (N := x + 1) hsq hodd
  push_cast at this ⊢
  convert this using 2
  ring

end TwinPrime.Sieve
