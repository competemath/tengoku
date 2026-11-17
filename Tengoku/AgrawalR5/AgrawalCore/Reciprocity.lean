/-
Nucleo Lean della campagna Agrawal (S45) — lotto 5: la reciprocità.
`p ≡ ±2 (mod 5)` (cioè p inerte in Q(√5)) implica che 5 non è un
quadrato mod p: le ipotesi dei teoremi diventano quelle aritmetiche
vere del paper. Campagna UNICO, 24 luglio 2026.
-/
import Tengoku.Seed.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Tengoku.Seed.Tactic.NormNum.Prime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/--
@isnad1 id=fact.0h0v.s2.4bcaaa0995da from=translated src=- shape=8d7dbbf6 vocab=c1c9ca6d
-/
instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

variable {p : ℕ} [Fact p.Prime]

/-- Per `p ≠ 2` primo con `p ≡ 2` o `3 (mod 5)`, il `5` non è un
quadrato mod `p` (reciprocità quadratica, ramo `5 ≡ 1 (mod 4)`).
@isnad1 id=not.2h1v.s6.c2ba5756a72c from=translated src=- shape=ff3a6ed7 vocab=2926f0b2
-/
theorem not_isSquare_five (hp2 : p ≠ 2) (hp : p % 5 = 2 ∨ p % 5 = 3) :
    ¬ IsSquare (5 : ZMod p) := by
  have hp5 : p ≠ 5 := by rcases hp with h | h <;> omega
  have h50 : ((5 : ℤ) : ZMod p) ≠ 0 := by
    have h : ((5 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
      intro hdvd
      exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out fact_prime_five.out).mp hdvd)
    exact_mod_cast h
  intro hsq
  have h1 : legendreSym p 5 = 1 :=
    (legendreSym.eq_one_iff p h50).mpr (by exact_mod_cast hsq)
  have hrec : legendreSym p 5 = legendreSym 5 p :=
    legendreSym.quadratic_reciprocity_one_mod_four (by norm_num) hp2
  have hmod : legendreSym 5 (p : ℤ) = legendreSym 5 ((p % 5 : ℕ) : ℤ) := by
    rw [legendreSym.mod]
    norm_cast
  rcases hp with h | h
  · rw [h] at hmod
    have hval : legendreSym 5 ((2 : ℕ) : ℤ) = -1 := by decide
    rw [hrec, hmod, hval] at h1
    exact absurd h1 (by norm_num)
  · rw [h] at hmod
    have hval : legendreSym 5 ((3 : ℕ) : ℤ) = -1 := by decide
    rw [hrec, hmod, hval] at h1
    exact absurd h1 (by norm_num)

/-- Per `p ≠ 2,5` primo con `p ≡ 1` o `4 (mod 5)`, il `5` è un
quadrato modulo `p`. È la direzione split, complementare a
`not_isSquare_five`.
@isnad1 id=issquare.2h1v.s6.7d3617590dd9 from=translated src=- shape=30f42ee2 vocab=2926f0b2
-/
theorem isSquare_five_of_split (hp2 : p ≠ 2)
    (hp : p % 5 = 1 ∨ p % 5 = 4) :
    IsSquare (5 : ZMod p) := by
  have hp5 : p ≠ 5 := by rcases hp with h | h <;> omega
  have h50 : ((5 : ℤ) : ZMod p) ≠ 0 := by
    have h : ((5 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
      intro hdvd
      exact hp5
        ((Nat.prime_dvd_prime_iff_eq Fact.out fact_prime_five.out).mp hdvd)
    exact_mod_cast h
  have hrec : legendreSym p 5 = legendreSym 5 p :=
    legendreSym.quadratic_reciprocity_one_mod_four (by norm_num) hp2
  have hmod : legendreSym 5 (p : ℤ) = legendreSym 5 ((p % 5 : ℕ) : ℤ) := by
    rw [legendreSym.mod]
    norm_cast
  have h1 : legendreSym p 5 = 1 := by
    rw [hrec, hmod]
    rcases hp with h | h
    · rw [h]
      decide
    · rw [h]
      decide
  have hs : IsSquare ((5 : ℤ) : ZMod p) :=
    (legendreSym.eq_one_iff p h50).mp h1
  exact_mod_cast hs

end AgrawalCore
