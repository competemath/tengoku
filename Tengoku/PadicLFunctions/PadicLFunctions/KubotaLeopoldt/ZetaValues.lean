import Tengoku.Seed.NumberTheory.Bernoulli

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rational zeta values at non-positive integers

RJW (arXiv:2309.15692) §4 interpolates the values `ζ(−k)`. As rational numbers these
are `ζ(−k) = (−1)^k B_{k+1}/(k+1)` (RJW TeX line 1455, with mathlib's `bernoulli`
convention `B₁ = −1/2`); the whole p-adic chain of §4 only ever uses this rational
value, cast into `ℚ_p`. The identification with the complex `riemannZeta (−k)` is the
bridge `zetaNeg_eq_riemannZeta` in `ZetaValuesComplex.lean` (kept separate so the main
chain does not import complex analysis).
-/

/-- The rational number `ζ(−k) = (−1)^k B_{k+1}/(k+1)` (RJW TeX line 1455; mathlib's
`bernoulli` convention). For the identification with the complex zeta function see
`zetaNeg_eq_riemannZeta`.-/
namespace Tengoku.PadicLFunctions end Tengoku.PadicLFunctions open Tengoku.PadicLFunctions def Tengoku.PadicLFunctions.zetaNeg (k : ℕ) : ℚ :=
  (-1) ^ k * bernoulli (k + 1) / (k + 1)

/--
@isnad1 id=eq.0h0v.s4.a29e8a813f94 from=translated src=- shape=38de1a77 vocab=ba2228a3
-/
@[simp]
lemma Tengoku.PadicLFunctions.zetaNeg_zero : zetaNeg 0 = -(1 / 2) := by
  norm_num [zetaNeg, bernoulli_one]

/-- The trivial zeros: `ζ(−k) = 0` for even `k ≥ 2` (odd Bernoulli numbers vanish).
@isnad1 id=eq.2h1v.s4.0cfb03397233 from=translated src=- shape=8474a955 vocab=f08693ba
-/
lemma Tengoku.PadicLFunctions.zetaNeg_eq_zero_of_even {k : ℕ} (hk : k ≠ 0) (h : Even k) : zetaNeg k = 0 := by
  rw [zetaNeg, bernoulli_eq_zero_of_odd h.add_one (by omega), mul_zero, zero_div]

/-- Sign removal in the Kubota–Leopoldt interpolation (RJW TeX line 1596: "we may
remove the `(−1)^k` as `ζ(1−k) ≠ 0` if and only if `k` is even"): for `k > 0`,
`(−1)^k (1−q^{k−1}) ζ(1−k) = (1−q^{k−1}) ζ(1−k)` — at `k = 1` the factor
`1−q⁰` vanishes, at even `k` the sign is `+1`, and at odd `k ≥ 3` the zeta value vanishes.
@isnad1 id=eq.1h2v.s7.aa56c0575fad from=translated src=- shape=17a5bc8d vocab=b9570523
-/
lemma Tengoku.PadicLFunctions.neg_one_pow_mul_one_sub_pow_mul_zetaNeg (q : ℚ) {k : ℕ} (hk : 0 < k) :
    (-1) ^ k * ((1 - q ^ (k - 1)) * zetaNeg (k - 1))
      = (1 - q ^ (k - 1)) * zetaNeg (k - 1) := by
  obtain rfl | hk1 := eq_or_ne k 1
  · simp
  · rcases Nat.even_or_odd k with he | ho
    · rw [he.neg_one_pow, one_mul]
    · rw [zetaNeg_eq_zero_of_even (by omega) (Nat.Odd.sub_odd ho odd_one)]
      ring
-- Tengoku: root names of this library moved to Tengoku.PadicLFunctions so they do not collide with other libraries (generated)
