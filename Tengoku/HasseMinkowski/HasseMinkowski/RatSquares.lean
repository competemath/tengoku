/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic
import Tengoku.Seed.Data.Rat.Lemmas
import Tengoku.Seed.Data.Nat.Factorization.Basic
import Tengoku.Seed.Data.Nat.Squarefree
import Tengoku.Seed.Algebra.Ring.Int.Parity
import Tengoku.Seed.Algebra.Ring.Parity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rational square classes via `p`-adic valuations

Layer 1 of the Hasse–Minkowski development. A rational number `q` is a square in `ℚ`
if and only if `q` is nonnegative and every one of its `p`-adic valuations is even.

The proof reduces `q = q.num / q.den` to the corresponding statement for naturals: an
integer (resp. natural) is a square exactly when all exponents in its prime
factorization are even. Since `q.num` and `q.den` are coprime, at most one of them is
divisible by any given prime, so the evenness of the difference
`padicValRat p q = (q.num).factorization p - (q.den).factorization p`
forces the two exponents to be even individually.
-/

namespace HasseMinkowski

/-! ### Squares in `ℕ` -/

-- Theorem: a natural number is a square exactly when all the exponents in its prime
-- factorization are even. (Not available in Mathlib in this toolchain, so proved here.)
/--
@isnad1 id=iff.0h1v.s5.5390c1a78f0d from=translated src=- shape=baec31d3 vocab=6a2a8782
-/
lemma isSquare_nat_iff_even_factorization {n : ℕ} :
    IsSquare n ↔ ∀ p : ℕ, p.Prime → Even (n.factorization p) := by
  constructor
  · rintro ⟨m, rfl⟩ p hp
    by_cases hm : m = 0
    · simp [hm]
    · rw [Nat.factorization_mul hm hm]
      exact ⟨m.factorization p, rfl⟩
  · intro h
    by_cases hn : n = 0
    · exact ⟨0, by simp [hn]⟩
    obtain ⟨b, a, hab, ha⟩ := exists_sq_mul_squarefree n
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hn (by simpa using hab.symm)
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hn (by simpa using hab.symm)
    have ha1 : a = 1 := by
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have hfac1 : a.factorization p = 1 :=
        Nat.factorization_eq_one_of_squarefree ha hp hpd
      have hfac : n.factorization p = 2 * b.factorization p + 1 := by
        rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb0) ha0, Nat.factorization_pow]
        simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
        rw [hfac1]
      obtain ⟨c, hc⟩ := h p hp
      rw [hfac] at hc
      omega
    exact ⟨b, by rw [← hab, ha1, mul_one, pow_two]⟩

-- Theorem: if `a` and `b` are coprime naturals, then for any prime `p` at most one of
-- `a.factorization p`, `b.factorization p` is nonzero.
/--
@isnad1 id=or.2h3v.s6.b893377c5bf6 from=translated src=- shape=da12d7a4 vocab=0cbe4ff8
-/
lemma factorization_eq_zero_or_eq_zero_of_coprime {a b p : ℕ} (hp : p.Prime)
    (hab : Nat.Coprime a b) : a.factorization p = 0 ∨ b.factorization p = 0 := by
  rcases eq_or_ne (a.factorization p) 0 with h | h
  · exact Or.inl h
  rcases eq_or_ne (b.factorization p) 0 with h' | h'
  · exact Or.inr h'
  exfalso
  have ha : a ≠ 0 := by rintro rfl; simp at h
  have hb : b ≠ 0 := by rintro rfl; simp at h'
  have hpa : p ∣ a :=
    (hp.dvd_iff_one_le_factorization ha).mpr (Nat.one_le_iff_ne_zero.mpr h)
  have hpb : p ∣ b :=
    (hp.dvd_iff_one_le_factorization hb).mpr (Nat.one_le_iff_ne_zero.mpr h')
  have hpg : p ∣ 1 := by
    have := Nat.dvd_gcd hpa hpb
    rwa [hab] at this
  exact hp.ne_one (Nat.dvd_one.mp hpg)

/-! ### Rational squares via `p`-adic valuations

Since `q.num` and `q.den` are coprime, at most one of them is divisible by a given
prime `p`, so only one of the two exponents in `padicValRat p q` is nonzero. Evenness
of the difference therefore forces evenness of each exponent separately, which by
`isSquare_nat_iff_even_factorization` makes both `q.num` and `q.den` squares. -/

-- Theorem: the `p`-adic valuation of a nonzero rational is the difference of the
-- `p`-adic valuations (prime factorizations) of its numerator and denominator.
/--
@isnad1 id=even.2h2v.s4.718ae0725456 from=translated src=- shape=1272420c vocab=31dc29b5
-/
theorem even_padicValRat_of_isSquare {q : ℚ} (hq : IsSquare q) (p : ℕ) (hp : p.Prime) :
    Even (padicValRat p q) := by
  obtain ⟨r, rfl⟩ := hq
  by_cases hr : r = 0
  · simp [hr]
  · rw [padicValRat.mul (p := p) (hp := Fact.mk hp) hr hr]
    exact ⟨padicValRat p r, rfl⟩

-- Theorem: a square rational is nonnegative.
/--
@isnad1 id=le.1h1v.s4.b6cfb44560a9 from=translated src=- shape=979a7069 vocab=49019991
-/
theorem nonneg_of_isSquare {q : ℚ} (hq : IsSquare q) : 0 ≤ q :=
  hq.nonneg

-- Theorem: for `q : ℚ`, `q` is a square iff `q ≥ 0` and every `p`-adic valuation
-- of `q` is even.

end HasseMinkowski
