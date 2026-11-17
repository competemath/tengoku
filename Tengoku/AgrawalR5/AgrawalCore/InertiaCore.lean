/-
Nucleo Lean della campagna Agrawal (S45) — lotto 2: il cuore aureo.
`R = (ZMod p)[X]/(X² − X − 1)`, ε la radice aurea. Sotto l'ipotesi che
5 non sia un quadrato mod p (p inerte in Q(√5)):
  · `golden_frobenius`   : ε^p = 1 − ε
  · `golden_pow_p_succ`  : ε^(p+1) = −1
  · `inertia_J`          : mai ε^(2n) = 1 e 5^(n−1) = 1 insieme
                           (teorema d'inerzia di J_n, forma aurea)
  · `support_canonical`  : ε^(p+1) = −1 e 5^((p−1)/2) = −1
                           (caso canonico del teorema di supporto)
  · `golden_pow_fib`     : ε^(n+1) = F_(n+1)·ε + F_n  (ponte Fibonacci)
La catena è più elementare della prova dei fascicoli: s = 2ε−1 ha
s² = 5, Eulero dà s^p = −s, quindi ε^p = 1−ε senza dicotomie di
Frobenius né conteggi di radici. Campagna UNICO, 24 luglio 2026.
-/
import Tengoku.Seed.RingTheory.AdjoinRoot
import Tengoku.Seed.FieldTheory.Finite.Basic
import Tengoku.Seed.NumberTheory.LegendreSymbol.Basic
import Tengoku.Seed.Data.Nat.Fib.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

/-- Il polinomio aureo `X² − X − 1` su `ZMod p`.-/
noncomputable def goldenPoly (p : ℕ) : Polynomial (ZMod p) := X ^ 2 - X - 1

/-- L'anello aureo `R = (ZMod p)[X]/(X² − X − 1)`.-/
abbrev GoldenRing (p : ℕ) := AdjoinRoot (goldenPoly p)

/-- La radice aurea `ε`.-/
noncomputable def eps : GoldenRing p := AdjoinRoot.root (goldenPoly p)

/--
@isnad1 id=eq.0h1v.s5.79d974ea84a1 from=translated src=- shape=ce52dc10 vocab=08ac4031
-/
lemma goldenPoly_degree : (goldenPoly p).degree = 2 := by
  unfold goldenPoly; compute_degree!

instance : Nontrivial (GoldenRing p) :=
  AdjoinRoot.nontrivial _ (by rw [goldenPoly_degree]; norm_num)

/-- L'equazione aurea: `ε² = ε + 1`.
@isnad1 id=eq.0h1v.s6.c7384416b024 from=translated src=- shape=e9ab50b8 vocab=b5177e10
-/
lemma eps_sq : (eps : GoldenRing p) ^ 2 = eps + 1 := by
  have h : (Polynomial.aeval (eps : GoldenRing p)) (goldenPoly p) = 0 := by
    unfold eps
    rw [AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_self
  simp only [goldenPoly, map_sub, map_pow, map_one, Polynomial.aeval_X] at h
  linear_combination h

/-- L'inclusione di `ZMod p` nell'anello aureo è iniettiva.
@isnad1 id=injectiv.0h1v.s7.f122f290475e from=translated src=- shape=bd91a0e8 vocab=bfebb5b0
-/
lemma of_injective : Function.Injective (AdjoinRoot.of (goldenPoly p)) :=
  (AdjoinRoot.of (goldenPoly p)).injective

instance : CharP (GoldenRing p) p :=
  charP_of_injective_ringHom (of_injective (p := p)) p

/--
@isnad1 id=ne.1h1v.s6.9ef57fbfb6e9 from=translated src=- shape=0da77854 vocab=dac35cc4
-/
lemma two_ne_zero' (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  have h : ((2 : ℕ) : ZMod p) = 0 ↔ p ∣ 2 := CharP.cast_eq_zero_iff _ p 2
  intro h0
  have : p ∣ 2 := h.mp (by exact_mod_cast h0)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)

/-- `√5 := 2ε − 1`.-/
noncomputable def sqrt5 : GoldenRing p := 2 * eps - 1

/--
@isnad1 id=eq.0h1v.s6.d78c1e83bb91 from=translated src=- shape=3101749e vocab=7918929b
-/
lemma sqrt5_sq : (sqrt5 : GoldenRing p) ^ 2 = 5 := by
  have h := eps_sq (p := p)
  unfold sqrt5
  linear_combination 4 * h

/-- Criterio di Eulero, lato non-quadrato: `5^((p−1)/2) = −1`.
@isnad1 id=eq.2h1v.s7.1bbb5cd43299 from=translated src=- shape=b0b7ea95 vocab=bbc3a86a
-/
lemma euler_nonsquare (h5 : ¬ IsSquare (5 : ZMod p)) (hp2 : p ≠ 2) :
    (5 : ZMod p) ^ ((p - 1) / 2) = -1 := by
  have h50 : (5 : ZMod p) ≠ 0 := fun h => h5 ⟨0, by rw [h]; ring⟩
  have hcrit : (5 : ZMod p) ^ (p / 2) ≠ 1 :=
    fun h => h5 ((ZMod.euler_criterion p h50).mpr h)
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have e1 : p / 2 = (p - 1) / 2 := by omega
  rw [e1] at hcrit
  have hsq : (5 : ZMod p) ^ ((p - 1) / 2) * (5 : ZMod p) ^ ((p - 1) / 2) = 1 := by
    rw [← pow_add]
    have e2 : (p - 1) / 2 + (p - 1) / 2 = p - 1 := by omega
    rw [e2]
    exact ZMod.pow_card_sub_one_eq_one h50
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact absurd h hcrit
  · exact h

/-- Il Frobenius manda `√5` in `−√5` (caso inerte).
@isnad1 id=eq.2h1v.s7.74f08b86f873 from=translated src=- shape=8624f1ad vocab=87a43d81
-/
lemma sqrt5_pow_p (h5 : ¬ IsSquare (5 : ZMod p)) (hp2 : p ≠ 2) :
    (sqrt5 : GoldenRing p) ^ p = - sqrt5 := by
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h5k : (5 : ZMod p) ^ k = -1 := by
    have h := euler_nonsquare h5 hp2
    have e : (p - 1) / 2 = k := by omega
    rwa [e] at h
  have hsplit : (sqrt5 : GoldenRing p) ^ p = (sqrt5 ^ 2) ^ k * sqrt5 := by
    rw [← pow_mul, ← pow_succ, ← hk]
  rw [hsplit, sqrt5_sq]
  have hcast : (5 : GoldenRing p) ^ k
      = AdjoinRoot.of (goldenPoly p) ((5 : ZMod p) ^ k) := by
    rw [map_pow, map_ofNat]
  rw [hcast, h5k, map_neg, map_one]
  ring

/-- **Il Frobenius aureo**: nel caso inerte `ε^p = 1 − ε`.
@isnad1 id=eq.2h1v.s7.e6d000d12246 from=translated src=- shape=07bd4db7 vocab=7098744e
-/
theorem golden_frobenius (h5 : ¬ IsSquare (5 : ZMod p)) (hp2 : p ≠ 2) :
    (eps : GoldenRing p) ^ p = 1 - eps := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hs := sqrt5_pow_p h5 hp2
  have h2p : (2 : GoldenRing p) ^ p = 2 := by
    rw [show (2 : GoldenRing p) = AdjoinRoot.of (goldenPoly p) (2 : ZMod p) from
          (map_ofNat _ 2).symm, ← map_pow, ZMod.pow_card]
  have hexp : (sqrt5 : GoldenRing p) ^ p = 2 * eps ^ p - 1 := by
    unfold sqrt5
    rw [show (2 * eps - 1 : GoldenRing p) = 2 * eps + (-1) by ring,
        add_pow_char, mul_pow, h2p, hodd.neg_one_pow]
    ring
  have key : (2 : GoldenRing p) * (eps ^ p - (1 - eps)) = 0 := by
    rw [hexp] at hs
    unfold sqrt5 at hs
    linear_combination hs
  have hu : IsUnit (2 : GoldenRing p) := by
    have h2z : IsUnit (2 : ZMod p) := isUnit_iff_ne_zero.mpr (two_ne_zero' hp2)
    have h := h2z.map (AdjoinRoot.of (goldenPoly p))
    rwa [map_ofNat] at h
  have h0 := (hu.mul_right_eq_zero).mp key
  linear_combination h0

/-- **Il semiperiodo aureo**: nel caso inerte `ε^(p+1) = −1`.
@isnad1 id=eq.2h1v.s7.b9e655736b36 from=translated src=- shape=efd4c773 vocab=501a61c6
-/
theorem golden_pow_p_succ (h5 : ¬ IsSquare (5 : ZMod p)) (hp2 : p ≠ 2) :
    (eps : GoldenRing p) ^ (p + 1) = -1 := by
  have h := golden_frobenius h5 hp2
  have he := eps_sq (p := p)
  rw [pow_succ, h]
  linear_combination -he

/-- **Teorema d'inerzia di `J_n` (forma aurea).** Se `5` non è un quadrato
mod `p` (cioè `p` è inerte in `Q(√5)`), nessun `n ≥ 1` soddisfa
contemporaneamente `ε^(2n) = 1` e `5^(n−1) = 1`: nessun primo inerte
divide `J_n = gcd(B_n, 5^(n−1) − 1)`.
@isnad1 id=false.5h2v.s7.42ded2ed8d7d from=translated src=- shape=2d26fedd vocab=34188385
-/
theorem inertia_J (h5 : ¬ IsSquare (5 : ZMod p)) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 1 ≤ n) (hB : (eps : GoldenRing p) ^ (2 * n) = 1)
    (h1 : (5 : ZMod p) ^ (n - 1) = 1) : False := by
  rcases Nat.even_or_odd n with he | ho
  · -- n pari: allora 5 = (5^(n/2))² sarebbe un quadrato
    obtain ⟨m, hm⟩ := he
    apply h5
    refine ⟨(5 : ZMod p) ^ m, ?_⟩
    have h5n : (5 : ZMod p) ^ n = 5 := by
      have e : n = (n - 1) + 1 := by omega
      rw [e, pow_succ, h1, one_mul]
    calc (5 : ZMod p) = 5 ^ n := h5n.symm
      _ = 5 ^ m * 5 ^ m := by rw [← pow_add, ← hm]
  · -- n dispari: 1 = ε^((p+1)n) = −1, assurdo per p ≠ 2
    obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
    have h1' : (eps : GoldenRing p) ^ ((p + 1) * n) = 1 := by
      have e : (p + 1) * n = 2 * n * (k + 1) := by rw [hk]; ring
      rw [e, pow_mul, hB, one_pow]
    have h2' : (eps : GoldenRing p) ^ ((p + 1) * n) = -1 := by
      rw [pow_mul, golden_pow_p_succ h5 hp2]
      exact ho.neg_one_pow
    have h12 : (1 : GoldenRing p) = -1 := h1'.symm.trans h2'
    have h20 : (AdjoinRoot.of (goldenPoly p)) (2 : ZMod p)
        = (AdjoinRoot.of (goldenPoly p)) 0 := by
      rw [map_ofNat, map_zero]
      linear_combination h12
    exact two_ne_zero' hp2 (of_injective h20)

/-- **Caso canonico del teorema di supporto** (forma aurea): per `p`
inerte valgono `ε^(p+1) = −1` e `5^((p−1)/2) = −1`, cioè le due
congruenze che testimoniano `p ∣ H_((p+1)/2)`.
@isnad1 id=and.2h1v.s8.44ad15ceca88 from=translated src=- shape=c5f215fc vocab=57464035
-/
theorem support_canonical (h5 : ¬ IsSquare (5 : ZMod p)) (hp2 : p ≠ 2) :
    (eps : GoldenRing p) ^ (p + 1) = -1 ∧ (5 : ZMod p) ^ ((p - 1) / 2) = -1 :=
  ⟨golden_pow_p_succ h5 hp2, euler_nonsquare h5 hp2⟩

/-- **Ponte Fibonacci**: `ε^(n+1) = F_(n+1)·ε + F_n` nell'anello aureo.
@isnad1 id=eq.0h2v.s7.a81c6fa1397d from=translated src=- shape=d491c141 vocab=288efca0
-/
theorem golden_pow_fib : ∀ n : ℕ, (eps : GoldenRing p) ^ (n + 1)
    = (Nat.fib (n + 1) : GoldenRing p) * eps + (Nat.fib n : GoldenRing p)
  | 0 => by simp
  | n + 1 => by
    have ih := golden_pow_fib n
    have he := eps_sq (p := p)
    rw [pow_succ, ih, Nat.fib_add_two]
    push_cast
    linear_combination (Nat.fib (n + 1) : GoldenRing p) * he

end AgrawalCore
