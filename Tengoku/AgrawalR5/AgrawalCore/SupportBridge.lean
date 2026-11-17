/-
Nucleo Lean della campagna Agrawal (S45) — lotto 6: il teorema di
supporto, caso canonico, in forma di divisibilità:
  `p ≡ 2 (mod 5)`, p ≠ 2  ⟹  p ∣ H_(n₀) con n₀ = (p+1)/2 ≡ 4 (mod 5),
dove la divisibilità è testimoniata dalla coppia (A_(n₀), 5^(n₀−1)+1)
con A = Lucas per n₀ pari, Fibonacci per n₀ dispari. I lemmi inversi
(da ε^(2n) = −1 alla divisibilità) cancellano unità esplicite: niente
inverse, niente dominio. Campagna UNICO, 24 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.FibBridge
import Tengoku.AgrawalR5.AgrawalCore.Reciprocity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

/--
@isnad1 id=isunit.0h1v.s4.fefebb271e3e from=translated src=- shape=7e6de1f7 vocab=c483e632
-/
lemma eps_isUnit : IsUnit (eps : GoldenRing p) :=
  IsUnit.of_mul_eq_one (eps - 1) (by
    have h := eps_sq (p := p)
    linear_combination h)

/--
@isnad1 id=ne.1h1v.s6.3aac72732369 from=translated src=- shape=0da77854 vocab=dac35cc4
-/
lemma five_ne_zero (hp5 : p ≠ 5) : (5 : ZMod p) ≠ 0 := by
  have h : ((5 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
    intro hdvd
    exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out fact_prime_five.out).mp hdvd)
  exact_mod_cast h

/--
@isnad1 id=isunit.1h1v.s5.da496c7cb6fc from=translated src=- shape=4e7691ea vocab=2bf21137
-/
lemma sqrt5_isUnit (hp5 : p ≠ 5) : IsUnit (sqrt5 : GoldenRing p) := by
  refine IsUnit.of_mul_eq_one
    (sqrt5 * AdjoinRoot.of (goldenPoly p) (5 : ZMod p)⁻¹) ?_
  have h1 : (sqrt5 : GoldenRing p) * (sqrt5 * AdjoinRoot.of (goldenPoly p)
      (5 : ZMod p)⁻¹) = (5 : GoldenRing p) * AdjoinRoot.of (goldenPoly p)
      (5 : ZMod p)⁻¹ := by
    have h := sqrt5_sq (p := p)
    linear_combination (AdjoinRoot.of (goldenPoly p) (5 : ZMod p)⁻¹) * h
  rw [h1, show (5 : GoldenRing p) = AdjoinRoot.of (goldenPoly p) (5 : ZMod p)
      from (map_ofNat _ 5).symm, ← map_mul,
      mul_inv_cancel₀ (five_ne_zero hp5), map_one]

/-- Cast a zero verso il basso: da `(a : GoldenRing p) = 0` a `p ∣ a`.
@isnad1 id=dvd.1h2v.s6.2a4096bc3ce8 from=translated src=- shape=78acb0bb vocab=2bffb0cc
-/
lemma dvd_of_natCast_eq_zero {a : ℕ} (h : ((a : ℕ) : GoldenRing p) = 0) :
    p ∣ a := by
  have h1 : AdjoinRoot.of (goldenPoly p) ((a : ℕ) : ZMod p)
      = AdjoinRoot.of (goldenPoly p) 0 := by
    rw [map_natCast, map_zero]; exact h
  exact (CharP.cast_eq_zero_iff (ZMod p) p _).mp (of_injective h1)

/-- Da `ε^(2n) = −1` con `n` pari: `p ∣ L_n`.
@isnad1 id=dvd.3h2v.s7.44b4a45cd994 from=translated src=- shape=5b312510 vocab=b1651c5a
-/
lemma dvd_lucas_of_pow_eq_neg_one {n : ℕ} (hn : 1 ≤ n) (hev : Even n)
    (h : (eps : GoldenRing p) ^ (2 * n) = -1) : p ∣ lucas n := by
  have hm : ((eps * eps' : GoldenRing p)) ^ n = 1 := by
    rw [eps_mul_eps']
    exact hev.neg_one_pow
  have hsum := eps_pow_add_eps'_pow (p := p) hn
  have key : ((lucas n : ℕ) : GoldenRing p) * eps ^ n = 0 := by
    calc ((lucas n : ℕ) : GoldenRing p) * eps ^ n
        = (eps ^ n + eps' ^ n) * eps ^ n := by rw [hsum]
      _ = eps ^ (2 * n) + (eps * eps') ^ n := by
          rw [two_mul, pow_add, mul_pow]; ring
      _ = -1 + 1 := by rw [h, hm]
      _ = 0 := by ring
  exact dvd_of_natCast_eq_zero
    (((eps_isUnit.pow n).mul_left_eq_zero).mp key)

/-- Da `ε^(2n) = −1` con `n` dispari: `p ∣ F_n`.
@isnad1 id=dvd.4h2v.s7.e69cc127f3ad from=translated src=- shape=1df1d76d vocab=a3605bff
-/
lemma dvd_fib_of_pow_eq_neg_one {n : ℕ} (hn : 1 ≤ n) (hodd : Odd n)
    (hp5 : p ≠ 5) (h : (eps : GoldenRing p) ^ (2 * n) = -1) :
    p ∣ Nat.fib n := by
  have hm : ((eps * eps' : GoldenRing p)) ^ n = -1 := by
    rw [eps_mul_eps']
    exact hodd.neg_one_pow
  have hf : (eps ^ n - eps' ^ n : GoldenRing p)
      = (Nat.fib n : GoldenRing p) * sqrt5 := by
    rw [golden_pow_pred (eps_sq (p := p)) hn,
        golden_pow_pred (eps'_sq (p := p)) hn]
    unfold eps' sqrt5
    ring
  have key : ((Nat.fib n : ℕ) : GoldenRing p) * (sqrt5 * eps ^ n) = 0 := by
    calc ((Nat.fib n : ℕ) : GoldenRing p) * (sqrt5 * eps ^ n)
        = ((Nat.fib n : GoldenRing p) * sqrt5) * eps ^ n := by ring
      _ = (eps ^ n - eps' ^ n) * eps ^ n := by rw [hf]
      _ = eps ^ (2 * n) - (eps * eps') ^ n := by
          rw [two_mul, pow_add, mul_pow]; ring
      _ = -1 - -1 := by rw [h, hm]
      _ = 0 := by ring
  exact dvd_of_natCast_eq_zero
    ((((sqrt5_isUnit hp5).mul (eps_isUnit.pow n)).mul_left_eq_zero).mp key)

end AgrawalCore
