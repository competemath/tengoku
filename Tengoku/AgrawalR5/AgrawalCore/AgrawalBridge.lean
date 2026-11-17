/-
Nucleo Lean della campagna Agrawal (S45) — lotto 9: IL PONTE.
Dalla congruenza di Agrawal a r = 5 alla pseudoprimalità base 5,
SENZA ipotesi intermedie: se n è squarefree, 5 ∤ n, e
(X−1)^n ≡ X^n − 1 (mod n, X^5−1), allora n ∣ 5^(n−1) − 1.
Via diretta: la congruenza è un'identità polinomiale, quindi si
valuta nei quattro punti x^j dell'anello (Z/p)[X]/Φ₅ (dove x^5 = 1);
il prodotto delle quattro dà 5^n = 5 grazie all'identità a cofattore
(x−1)(x²−1)(x³−1)(x⁴−1) = 5 + Φ₅·(x⁶−2x⁵+x³+3x−4). Niente Frobenius,
niente norme. Campagna UNICO, 24 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.Entanglement
import Tengoku.AgrawalR5.AgrawalCore.FermatShadow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

/-- L'identità del prodotto: dalle radici di `Φ₅`,
`(ζ−1)(ζ²−1)(ζ³−1)(ζ⁴−1) = 5`. Cofattore esplicito PARI-verificato.
@isnad1 id=eq.1h2v.s8.16bb6119cffb from=translated src=- shape=b9197467 vocab=9c1cdc1d
-/
theorem prod_pow_sub_one {R : Type*} [CommRing R] {ζ : R}
    (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) :
    (ζ - 1) * (ζ ^ 2 - 1) * (ζ ^ 3 - 1) * (ζ ^ 4 - 1) = 5 := by
  linear_combination (ζ ^ 6 - 2 * ζ ^ 5 + ζ ^ 3 + 3 * ζ - 4) * hζ

/-- Potenze modulo 5 dell'esponente, quando `x^5 = 1`.
@isnad1 id=eq.1h3v.s6.ff0eac1be5df from=translated src=- shape=422c7d31 vocab=87c448d2
-/
lemma pow_mod_five {R : Type*} [Monoid R] {x : R} (hx : x ^ 5 = 1)
    (m : ℕ) : x ^ m = x ^ (m % 5) := by
  conv_lhs => rw [← Nat.div_add_mod m 5]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

/-- Il quinto polinomio ciclotomico su `ZMod p`.-/
noncomputable def phi5 (p : ℕ) : Polynomial (ZMod p) :=
  X ^ 4 + X ^ 3 + X ^ 2 + X + 1

/-- L'anello ciclotomico `T = (Z/p)[X]/Φ₅`.-/
abbrev Phi5Ring (p : ℕ) := AdjoinRoot (phi5 p)

variable {p : ℕ} [Fact p.Prime]

noncomputable def zeta5 : Phi5Ring p := AdjoinRoot.root (phi5 p)

/--
@isnad1 id=eq.0h1v.s5.66556675e461 from=translated src=- shape=ce52dc10 vocab=2ed01fa2
-/
lemma phi5_degree : (phi5 p).degree = 4 := by
  unfold phi5; compute_degree!

instance : Nontrivial (Phi5Ring p) :=
  AdjoinRoot.nontrivial _ (by rw [phi5_degree]; norm_num)

/--
@isnad1 id=eq.0h1v.s8.f13c98651e46 from=translated src=- shape=fc80f675 vocab=5b0520c1
-/
lemma zeta5_rel :
    (zeta5 : Phi5Ring p) ^ 4 + zeta5 ^ 3 + zeta5 ^ 2 + zeta5 + 1 = 0 := by
  have h : (Polynomial.aeval (zeta5 : Phi5Ring p)) (phi5 p) = 0 := by
    unfold zeta5
    rw [AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_self
  simpa [phi5, map_add, map_pow, map_one, Polynomial.aeval_X] using h

/--
@isnad1 id=eq.0h1v.s6.30d5b8fc512b from=translated src=- shape=3101749e vocab=a44e590f
-/
lemma zeta5_pow_five : (zeta5 : Phi5Ring p) ^ 5 = 1 :=
  zeta_pow_five zeta5_rel

/--
@isnad1 id=injectiv.0h1v.s7.7ef023e51c64 from=translated src=- shape=bd91a0e8 vocab=cf8fc126
-/
lemma phi5_of_injective :
    Function.Injective (AdjoinRoot.of (phi5 p)) :=
  (AdjoinRoot.of (phi5 p)).injective

/-- **Il passo locale del ponte.** Se la congruenza di Agrawal vale in
`(Z/p)[X]` modulo `X^5 − 1`, `p ≠ 5`, `5 ∤ n`, `n ≥ 1`, allora
`5^(n−1) = 1` in `Z/p`.
@isnad1 id=eq.4h2v.s10.57284e09206d from=translated src=- shape=295bb30a vocab=f496f101
-/
theorem agrawal_local (hp5 : p ≠ 5) {n : ℕ} (hn : 1 ≤ n)
    (h5n : n % 5 ≠ 0)
    (h : ∃ g : Polynomial (ZMod p),
      (X - 1) ^ n = X ^ n - 1 + (X ^ 5 - 1) * g) :
    (5 : ZMod p) ^ (n - 1) = 1 := by
  obtain ⟨g, hg⟩ := h
  set z : Phi5Ring p := zeta5 with hz_def
  have hz : z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0 := zeta5_rel
  have hz5 : z ^ 5 = 1 := zeta5_pow_five
  -- le quattro valutazioni della stessa identità polinomiale
  have eval_at : ∀ j : ℕ, (z ^ j - 1) ^ n = z ^ (j * n) - 1 := by
    intro j
    have hcong := congrArg (Polynomial.aeval (z ^ j)) hg
    simp only [map_add, map_sub, map_mul, map_pow, map_one,
      Polynomial.aeval_X] at hcong
    have hj5 : ((z ^ j) ^ 5 : Phi5Ring p) = 1 := by
      rw [← pow_mul, mul_comm j 5, pow_mul, hz5, one_pow]
    rw [hj5, sub_self, zero_mul, add_zero, ← pow_mul, mul_comm j n,
      mul_comm] at hcong
    exact hcong
  have c1 := eval_at 1
  have c2 := eval_at 2
  have c3 := eval_at 3
  have c4 := eval_at 4
  -- il prodotto delle quattro: 5^n = 5 in T
  have big : (5 : Phi5Ring p) ^ n = 5 := by
    have lhs : (5 : Phi5Ring p) ^ n
        = (z ^ 1 - 1) ^ n * (z ^ 2 - 1) ^ n * (z ^ 3 - 1) ^ n
          * (z ^ 4 - 1) ^ n := by
      rw [← mul_pow, ← mul_pow, ← mul_pow]
      congr 1
      rw [pow_one]
      exact (prod_pow_sub_one hz).symm
    rw [lhs, c1, c2, c3, c4,
      pow_mod_five hz5 (1 * n), pow_mod_five hz5 (2 * n),
      pow_mod_five hz5 (3 * n), pow_mod_five hz5 (4 * n)]
    have hk : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
    rcases hk with hk | hk | hk | hk
    · have e1 : 1 * n % 5 = 1 := by omega
      have e2 : 2 * n % 5 = 2 := by omega
      have e3 : 3 * n % 5 = 3 := by omega
      have e4 : 4 * n % 5 = 4 := by omega
      rw [e1, e2, e3, e4]
      linear_combination (z ^ 6 - 2 * z ^ 5 + z ^ 3 + 3 * z - 4) * hz
    · have e1 : 1 * n % 5 = 2 := by omega
      have e2 : 2 * n % 5 = 4 := by omega
      have e3 : 3 * n % 5 = 1 := by omega
      have e4 : 4 * n % 5 = 3 := by omega
      rw [e1, e2, e3, e4]
      linear_combination (z ^ 6 - 2 * z ^ 5 + z ^ 3 + 3 * z - 4) * hz
    · have e1 : 1 * n % 5 = 3 := by omega
      have e2 : 2 * n % 5 = 1 := by omega
      have e3 : 3 * n % 5 = 4 := by omega
      have e4 : 4 * n % 5 = 2 := by omega
      rw [e1, e2, e3, e4]
      linear_combination (z ^ 6 - 2 * z ^ 5 + z ^ 3 + 3 * z - 4) * hz
    · have e1 : 1 * n % 5 = 4 := by omega
      have e2 : 2 * n % 5 = 3 := by omega
      have e3 : 3 * n % 5 = 2 := by omega
      have e4 : 4 * n % 5 = 1 := by omega
      rw [e1, e2, e3, e4]
      linear_combination (z ^ 6 - 2 * z ^ 5 + z ^ 3 + 3 * z - 4) * hz
  -- discesa a ZMod p
  have hdown : (5 : ZMod p) ^ n = 5 := by
    apply phi5_of_injective
    rw [map_pow, map_ofNat]
    calc (5 : Phi5Ring p) ^ n = 5 := big
      _ = AdjoinRoot.of (phi5 p) 5 := (map_ofNat _ 5).symm
  have h50 : (5 : ZMod p) ≠ 0 := by
    have hh : ((5 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
      intro hd
      exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hd)
    exact_mod_cast hh
  have hstep : (5 : ZMod p) ^ (n - 1) * 5 = 1 * 5 := by
    rw [one_mul, ← pow_succ]
    have e : n - 1 + 1 = n := by omega
    rw [e]
    exact hdown
  exact mul_right_cancel₀ h50 hstep

/-- **IL PONTE, senza ipotesi intermedie.** Se `n` è squarefree,
`5 ∤ n`, e vale la congruenza di Agrawal a `r = 5`
(`(X−1)^n ≡ X^n − 1` modulo `(n, X^5−1)`), allora `n` è uno
pseudoprimo di Fermat in base `5`: `n ∣ 5^(n−1) − 1`. I controesempi
squarefree alla congettura possono nascondersi solo lì.
@isnad1 id=dvd.3h1v.s9.1c96fce48ead from=translated src=- shape=e0c37648 vocab=fc2d30d4
-/
theorem agrawal_fermat_shadow {n : ℕ} (hsq : Squarefree n)
    (h5 : ¬ (5 ∣ n))
    (h : ∃ g : Polynomial (ZMod n),
      (X - 1) ^ n = X ^ n - 1 + (X ^ 5 - 1) * g) :
    n ∣ 5 ^ (n - 1) - 1 := by
  have key : ∀ q ∈ n.primeFactors, q ∣ 5 ^ (n - 1) - 1 := by
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqd : q ∣ n := Nat.dvd_of_mem_primeFactors hq
    haveI : Fact q.Prime := ⟨hqp⟩
    have hq5 : q ≠ 5 := fun hcon => h5 (hcon ▸ hqd)
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h0 => by
      subst h0; simp at hq)
    have h5n : n % 5 ≠ 0 := fun hcon =>
      h5 (Nat.dvd_of_mod_eq_zero hcon)
    -- riduzione della congruenza da ZMod n a ZMod q
    obtain ⟨g, hg⟩ := h
    have hmap := congrArg (Polynomial.map (ZMod.castHom hqd (ZMod q))) hg
    simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_one, Polynomial.map_X] at hmap
    have hloc := agrawal_local hq5 hn1 h5n
      ⟨g.map (ZMod.castHom hqd (ZMod q)), hmap⟩
    -- discesa alla divisibilità
    have hge : 1 ≤ 5 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
    have h1 : ((5 ^ (n - 1) - 1 : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_sub hge]
      push_cast
      rw [hloc]
      ring
    exact (CharP.cast_eq_zero_iff (ZMod q) q _).mp h1
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  nth_rewrite 1 [← hprod]
  exact Finset.prod_primes_dvd (5 ^ (n - 1) - 1)
    (fun q hq => (Nat.prime_of_mem_primeFactors hq).prime) key

end AgrawalCore
