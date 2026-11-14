import Tengoku
import Tengoku.Twinprime.TwinPrime.Sieve.BrunLower
import Tengoku.Twinprime.TwinPrime.Brun
import Tengoku.Twinprime.TwinPrime.Conditional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brun's theorem on twin almost-primes (weak form)

With the sifting level `z(x) = ⌊exp (log x / (1000 log log x))⌋`, the exact Brun inequality
`brun_count_ge` gives, for all large `x`,

  `#{n ≤ x : n(n+2) has no prime factor ≤ z(x)} ≥ x / (4 (log x)^96)`

(`brun_count_ge_eventually`).  Every such `n ≥ √x` satisfies
`Ω(n) + Ω(n+2) = Ω(n(n+2)) ≤ 2 log(x+2)/log(z+1) ≤ 3000 log log x ≤ 6000 log log n`.  Hence
(`brun_almostPrime_infinite`): **there are infinitely many `n` such that `n` and `n + 2` together
have at most `6000 log log n` prime factors (with multiplicity).**

This is a (quantitatively very weak) form of Brun's 1920 theorem; Brun obtained a bounded number
of prime factors, and Chen's theorem gives `p + 2 = P₂`.  The constants here are dictated by the
crude Mertens bound of `Sieve/Mertens.lean` and were not optimised.
-/

noncomputable section

open Finset Real Filter Topology
open TwinPrime.Sieve
open scoped ArithmeticFunction.Omega

namespace TwinPrime

/-- The Brun sifting level `z(x) = ⌊exp (log x / (1000 log log x))⌋`.-/
def zB (x : ℕ) : ℕ := ⌊Real.exp (Real.log x / (1000 * Real.log (Real.log x)))⌋₊

/-- The exponent `u(x) = log x / (1000 log log x)`.-/
def uB (x : ℕ) : ℝ := Real.log x / (1000 * Real.log (Real.log x))

/-! ### Eventual estimates -/

theorem eventually_loglog_ge (C : ℝ) : ∀ᶠ x : ℕ in atTop, C ≤ Real.log (Real.log x) := by
  have h : Tendsto (fun x : ℕ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact h.eventually (eventually_ge_atTop C)

theorem eventually_log_ge (C : ℝ) : ∀ᶠ x : ℕ in atTop, C ≤ Real.log x := by
  have h : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact h.eventually (eventually_ge_atTop C)

theorem eventually_loglog_le_mul_log {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, Real.log (Real.log x) ≤ ε * Real.log x := by
  have h1 : (fun y : ℝ => Real.log y) =o[atTop] (fun y => y) := Real.isLittleO_log_id_atTop
  have h2 := h1.comp_tendsto (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h3 := h2.def hε
  filter_upwards [h3, eventually_log_ge 0] with x hx hx0
  simp only [Function.comp] at hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0] at hx
  exact le_trans (le_abs_self _) hx

theorem eventually_rpow_ge (C : ℝ) {y : ℝ} (hy : 0 < y) :
    ∀ᶠ x : ℕ in atTop, C ≤ (x : ℝ) ^ y := by
  have h : Tendsto (fun x : ℕ => (x : ℝ) ^ y) atTop atTop :=
    (tendsto_rpow_atTop hy).comp tendsto_natCast_atTop_atTop
  exact h.eventually (eventually_ge_atTop C)

/-- The basic estimates at `z = zB x`, for large `x`.-/
theorem zB_estimates : ∀ᶠ x : ℕ in atTop,
    2 ≤ zB x ∧
    ell (zB x) ≤ 32 * Real.log (Real.log x) ∧
    (zB x : ℝ) ^ (mLevel (zB x)) ≤ Real.exp (Real.log x / 5) ∧
    uB x ≤ Real.log ((zB x : ℝ) + 1) := by
  filter_upwards [eventually_loglog_ge 1, eventually_loglog_le_mul_log (by norm_num : (0 : ℝ) < 1 / 2000),
    eventually_log_ge 1] with x hℓ hLℓ hL
  set ℓ := Real.log (Real.log x) with hℓdef
  set L := Real.log x with hLdef
  have hℓpos : 0 < ℓ := by linarith
  have hu : 2 ≤ uB x := by
    unfold uB
    rw [← hLdef, ← hℓdef, le_div_iff₀ (by positivity)]
    linarith
  have hupos : 0 < uB x := by linarith
  -- `z ≥ 7`
  have hz7 : 7 ≤ zB x := by
    unfold zB
    apply Nat.le_floor
    have he : Real.exp 2 ≤ Real.exp (uB x) := Real.exp_le_exp.mpr hu
    have he2 : (7 : ℝ) ≤ Real.exp 2 := by
      have := Real.exp_one_gt_d9
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    push_cast
    show (7 : ℝ) ≤ Real.exp (uB x)
    linarith
  have hz2 : 2 ≤ zB x := by omega
  have hzpos : (0 : ℝ) < zB x := by exact_mod_cast (by omega : 0 < zB x)
  -- `log z ≤ u`
  have hlogz : Real.log (zB x) ≤ uB x := by
    have : (zB x : ℝ) ≤ Real.exp (uB x) := Nat.floor_le (Real.exp_pos _).le
    calc Real.log (zB x) ≤ Real.log (Real.exp (uB x)) := Real.log_le_log hzpos this
      _ = uB x := Real.log_exp _
  -- `log₂ z ≤ 2 u`
  have hlog2z : (Nat.log 2 (zB x) : ℝ) ≤ 2 * uB x := by
    have h1 : (2 : ℕ) ^ Nat.log 2 (zB x) ≤ zB x := Nat.pow_log_le_self 2 (by omega)
    have h2 : (Nat.log 2 (zB x) : ℝ) * Real.log 2 ≤ Real.log (zB x) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast h1)
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    nlinarith
  -- `ℓ(z) ≤ 32 ℓ`
  have hell : ell (zB x) ≤ 32 * ℓ := by
    unfold ell
    have h1 : (Nat.log 2 (zB x) : ℝ) + 1 ≤ L := by
      have : (2 * uB x + 1) ≤ 3 * uB x := by linarith
      have hu' : 3 * uB x ≤ L := by
        unfold uB
        rw [← hLdef, ← hℓdef]
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    have h2 : Real.log ((Nat.log 2 (zB x) : ℝ) + 1) ≤ ℓ := by
      rw [hℓdef, hLdef]
      exact Real.log_le_log (by positivity) (by rw [← hLdef]; exact h1)
    linarith
  -- `z^m ≤ exp(L/5)`
  have hzm : (zB x : ℝ) ^ (mLevel (zB x)) ≤ Real.exp (L / 5) := by
    have hm : (mLevel (zB x) : ℝ) ≤ 6 * ell (zB x) + 3 := by
      unfold mLevel
      push_cast
      have := Nat.ceil_lt_add_one (by linarith [ell_pos (zB x)] : (0 : ℝ) ≤ 3 * ell (zB x))
      linarith
    have hm' : (mLevel (zB x) : ℝ) ≤ 195 * ℓ := by linarith
    have hmu : (mLevel (zB x) : ℝ) * uB x ≤ L / 5 := by
      calc (mLevel (zB x) : ℝ) * uB x ≤ 195 * ℓ * uB x :=
            mul_le_mul_of_nonneg_right hm' hupos.le
        _ = 195 * ℓ * (L / (1000 * ℓ)) := by rfl
        _ = L * (195 / 1000) := by field_simp
        _ ≤ L / 5 := by nlinarith
    calc (zB x : ℝ) ^ (mLevel (zB x)) = Real.exp ((mLevel (zB x) : ℝ) * Real.log (zB x)) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos hzpos, mul_comm]
      _ ≤ Real.exp ((mLevel (zB x) : ℝ) * uB x) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left hlogz (by positivity)
      _ ≤ Real.exp (L / 5) := Real.exp_le_exp.mpr hmu
  -- `u ≤ log (z + 1)`
  have hlogz1 : uB x ≤ Real.log ((zB x : ℝ) + 1) := by
    have : Real.exp (uB x) < (zB x : ℝ) + 1 := by
      unfold zB
      exact Nat.lt_floor_add_one _
    calc uB x = Real.log (Real.exp (uB x)) := (Real.log_exp _).symm
      _ ≤ Real.log ((zB x : ℝ) + 1) := Real.log_le_log (Real.exp_pos _) this.le
  exact ⟨hz2, hell, hzm, hlogz1⟩

/-! ### From roughness to few prime factors -/

/-- If every prime factor of `N ≥ 1` exceeds `z`, then `(z+1)^{Ω N} ≤ N`.-/
theorem pow_cardFactors_le {N z : ℕ} (hN : N ≠ 0) (h : ∀ p, p.Prime → p ∣ N → z < p) :
    (z + 1) ^ (Ω N) ≤ N := by
  rw [ArithmeticFunction.cardFactors_apply]
  calc (z + 1) ^ N.primeFactorsList.length ≤ N.primeFactorsList.prod := by
        apply List.pow_card_le_prod
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactorsList hp
        have := h p hpp (Nat.dvd_of_mem_primeFactorsList hp)
        omega
    _ = N := Nat.prod_primeFactorsList hN

/-- Sifted `n` with `√x ≤ n ≤ x` have `Ω(n) + Ω(n+2) ≤ 6000 log log n`.-/
theorem cardFactors_le_of_coprime_primorial {x n : ℕ} (hx : 16 ≤ x) (hℓ : 3 ≤ Real.log (Real.log x))
    (hu : uB x ≤ Real.log ((zB x : ℝ) + 1)) (hn1 : Nat.sqrt x ≤ n) (hnx : n ≤ x)
    (hcop : Nat.Coprime (primorial (zB x)) (n * (n + 2))) :
    ((Ω n : ℕ) : ℝ) + (Ω (n + 2) : ℕ) ≤ 6000 * Real.log (Real.log n) := by
  have hx1r : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hxpos : (0 : ℝ) < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos hx1r
  have hℓpos : 0 < Real.log (Real.log x) := by linarith
  have hn0 : n ≠ 0 := by
    intro h0
    subst h0
    have : Nat.sqrt x = 0 := by omega
    rw [Nat.sqrt_eq_zero] at this
    omega
  have hN0 : n * (n + 2) ≠ 0 := by positivity
  have hrough : ∀ p, p.Prime → p ∣ n * (n + 2) → zB x < p := by
    intro p hp hpn
    by_contra h
    exact (coprime_primorial_iff.mp hcop) p hp (by omega) hpn
  have hpow := pow_cardFactors_le hN0 hrough
  have hpow' : ((zB x : ℝ) + 1) ^ (Ω (n * (n + 2))) ≤ ((x : ℝ) + 2) ^ 2 := by
    calc ((zB x : ℝ) + 1) ^ (Ω (n * (n + 2))) = (((zB x + 1) ^ (Ω (n * (n + 2))) : ℕ) : ℝ) := by
          push_cast; ring
      _ ≤ ((n * (n + 2) : ℕ) : ℝ) := by exact_mod_cast hpow
      _ ≤ ((x : ℝ) + 2) ^ 2 := by
          push_cast
          have : (n : ℝ) ≤ x := by exact_mod_cast hnx
          nlinarith
  -- take logs
  have hL := Real.log_le_log (by positivity) hpow'
  rw [Real.log_pow, Real.log_pow] at hL
  push_cast at hL
  -- `Ω ≤ 2 log(x+2) / log(z+1) ≤ 2 log(x+2) / u`
  have hupos : 0 < uB x := by
    unfold uB
    positivity
  have hΩ : ((Ω (n * (n + 2)) : ℕ) : ℝ) ≤ 2 * Real.log ((x : ℝ) + 2) / uB x := by
    rw [le_div_iff₀ hupos]
    calc ((Ω (n * (n + 2)) : ℕ) : ℝ) * uB x ≤
          ((Ω (n * (n + 2)) : ℕ) : ℝ) * Real.log ((zB x : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hu (by positivity)
      _ ≤ 2 * Real.log ((x : ℝ) + 2) := hL
  -- `log (x+2) ≤ 3/2 log x` for `x ≥ 16`
  have hlogx2 : Real.log ((x : ℝ) + 2) ≤ 3 / 2 * Real.log x := by
    have hxr : (16 : ℝ) ≤ x := by exact_mod_cast hx
    have : (x : ℝ) + 2 ≤ (x : ℝ) ^ (3 / 2 : ℝ) := by
      have h1 : (x : ℝ) ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hxpos, Real.rpow_one,
          Real.sqrt_eq_rpow]
      rw [h1]
      have hs : (4 : ℝ) ≤ Real.sqrt x := by
        rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
      nlinarith
    calc Real.log ((x : ℝ) + 2) ≤ Real.log ((x : ℝ) ^ (3 / 2 : ℝ)) :=
          Real.log_le_log (by positivity) this
      _ = 3 / 2 * Real.log x := by rw [Real.log_rpow hxpos]
  -- hence `Ω ≤ 3000 log log x`
  have hΩ' : ((Ω (n * (n + 2)) : ℕ) : ℝ) ≤ 3000 * Real.log (Real.log x) := by
    have : 2 * Real.log ((x : ℝ) + 2) / uB x ≤ 3000 * Real.log (Real.log x) := by
      unfold uB
      rw [div_div_eq_mul_div, div_le_iff₀ hLpos]
      nlinarith
    linarith
  -- `log log n ≥ ½ log log x` for `n ≥ √x` (using `√x ≤ 2n`)
  have hlln : Real.log (Real.log x) ≤ 2 * Real.log (Real.log n) := by
    have hsx : Real.sqrt x ≤ 2 * n := by
      calc Real.sqrt x ≤ (Nat.sqrt x : ℝ) + 1 := by
            have := Nat.lt_succ_sqrt' x
            rw [Real.sqrt_le_left (by positivity)]
            exact_mod_cast this.le
        _ ≤ 2 * n := by
            have h4 : 4 ≤ Nat.sqrt x := by rw [Nat.le_sqrt]; omega
            have h4' : (4 : ℝ) ≤ Nat.sqrt x := by exact_mod_cast h4
            have : (Nat.sqrt x : ℝ) ≤ n := by exact_mod_cast hn1
            linarith
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have h1 : Real.log (Real.sqrt x) ≤ Real.log (2 * n) :=
      Real.log_le_log (by positivity) hsx
    rw [Real.log_sqrt hxpos.le, Real.log_mul (by norm_num) hnpos.ne'] at h1
    have hlog2 : Real.log 2 < 0.7 := by
      have := Real.log_two_lt_d9; linarith
    have hL16 : 4 * Real.log 2 ≤ Real.log x := by
      have h16 : Real.log ((2 : ℝ) ^ 4) ≤ Real.log x :=
        Real.log_le_log (by norm_num) (by norm_num; exact_mod_cast hx)
      rw [Real.log_pow] at h16
      push_cast at h16
      linarith
    have hlogn : Real.log x / 4 ≤ Real.log n := by linarith
    have h2 : Real.log (Real.log x / 4) ≤ Real.log (Real.log n) :=
      Real.log_le_log (by positivity) hlogn
    rw [Real.log_div hLpos.ne' (by norm_num)] at h2
    have hlog4 : Real.log 4 < 1.4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    linarith
  rw [← Nat.cast_add, ← ArithmeticFunction.cardFactors_mul hn0 (by omega)]
  linarith

end TwinPrime
