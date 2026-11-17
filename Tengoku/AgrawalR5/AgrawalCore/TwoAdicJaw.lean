/-
Nucleo Lean della campagna Agrawal — lotto 10: LA SECONDA GANASCIA.

Il ponte (lotto 9) porta ogni controesempio squarefree dentro gli
pseudoprimi di Fermat base 5. Qui si mostra che quella conclusione, sui
soli fattori INERTI in Q(√5), ha una conseguenza 2-adica rigida:

  p ≡ ±2 (mod 5), p ∣ n, n controesempio  ⟹  v₂(p−1) ≤ v₂(n−1).

Il meccanismo: per p inerte il criterio di Eulero dà 5^((p−1)/2) = −1,
quindi l'ordine di 5 mod p è 2-adicamente SATURO (v₂(ord) = v₂(p−1)),
mentre il ponte forza ord ∣ n−1. Per p split accade l'opposto
(5^((p−1)/2) = 1 ⟹ ord ∣ (p−1)/2) e nessun vincolo si trasmette: le due
classi di Artin si comportano in modo opposto.

Corollario leggibile: un controesempio n ≡ 3 (mod 4) può avere fattori
inerti soltanto ≡ 3 (mod 4).

Campagna UNICO, 25 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.AgrawalBridge
import Tengoku.AgrawalR5.AgrawalCore.InertiaCore
import Tengoku.AgrawalR5.AgrawalCore.Reciprocity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

open Polynomial

/-- Un divisore di `2^(k+1) * v` che non divide `2^k * v` è
2-adicamente saturo: `2^(k+1)` lo divide.
@isnad1 id=dvd.3h3v.s6.4ca69bcf7933 from=translated src=- shape=06bebf9a vocab=0eadfadb
-/
lemma pow_two_dvd_of_not_dvd_half {d k v : ℕ} (hd0 : d ≠ 0)
    (hdvd : d ∣ 2 ^ (k + 1) * v) (hnot : ¬ d ∣ 2 ^ k * v) :
    2 ^ (k + 1) ∣ d := by
  have hsplit : 2 ^ (d.factorization 2) * (d / 2 ^ (d.factorization 2)) = d :=
    Nat.ordProj_mul_ordCompl_eq_self d 2
  have hodd : ¬ (2 : ℕ) ∣ (d / 2 ^ (d.factorization 2)) :=
    Nat.not_dvd_ordCompl Nat.prime_two hd0
  have hcop : Nat.Coprime (d / 2 ^ (d.factorization 2)) (2 ^ (k + 1)) :=
    Nat.Coprime.pow_right _
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
  have hdvdv : d / 2 ^ (d.factorization 2) ∣ v :=
    hcop.dvd_of_dvd_mul_left (dvd_trans (Nat.ordCompl_dvd d 2) hdvd)
  by_contra hcon
  have hbk : d.factorization 2 ≤ k := by
    by_contra hle
    push Not at hle
    exact hcon (dvd_trans (pow_dvd_pow 2 hle) (Nat.ordProj_dvd d 2))
  exact hnot (hsplit ▸ Nat.mul_dvd_mul (pow_dvd_pow 2 hbk) hdvdv)

/-- **La ganascia locale.** Se `5` non è un quadrato mod `p` e
`5 ^ (n−1) = 1` in `ZMod p`, allora ogni potenza di due che divide
`p − 1` divide anche `n − 1`, cioè `v₂(p−1) ≤ v₂(n−1)`.
@isnad1 id=dvd.4h3v.s7.99197f17d966 from=translated src=- shape=67fa81d6 vocab=374ff0a0
-/
theorem two_adic_jaw_local {p n k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h5 : ¬ IsSquare (5 : ZMod p)) (hn : (5 : ZMod p) ^ (n - 1) = 1)
    (hk : 2 ^ k ∣ p - 1) : 2 ^ k ∣ n - 1 := by
  have hpp : p.Prime := Fact.out
  have hp1 : 2 ≤ p := hpp.two_le
  have hodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left hp2
  have hp10 : p - 1 ≠ 0 := by omega
  have h50 : (5 : ZMod p) ≠ 0 := fun h => h5 ⟨0, by rw [h]; ring⟩
  have hdn : orderOf (5 : ZMod p) ∣ n - 1 := orderOf_dvd_of_pow_eq_one hn
  have hdp : orderOf (5 : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one h50
  have hd0 : orderOf (5 : ZMod p) ≠ 0 := by
    intro h0
    rw [h0] at hdp
    exact hp10 (Nat.eq_zero_of_zero_dvd hdp)
  -- decomposizione 2-adica di p − 1
  set a := (p - 1).factorization 2 with ha
  set u := (p - 1) / 2 ^ a with hu
  have hsplit : 2 ^ a * u = p - 1 := Nat.ordProj_mul_ordCompl_eq_self (p - 1) 2
  have ha1 : 1 ≤ a := by
    have h2 : (2 : ℕ) ∣ p - 1 := by omega
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hp10
      (p := 2) (n := p - 1) (k := 1)).mp (by simpa using h2)
    omega
  -- (p − 1)/2 = 2 ^ (a − 1) * u
  have hhalf : 2 ^ (a - 1) * u = (p - 1) / 2 := by
    have hpow : (2 : ℕ) ^ a = 2 * 2 ^ (a - 1) := by
      conv_lhs => rw [show a = 1 + (a - 1) by omega]
      rw [pow_add, pow_one]
    rw [← hsplit, hpow, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  -- il criterio di Eulero vieta la discesa a metà
  have hnot : ¬ orderOf (5 : ZMod p) ∣ 2 ^ (a - 1) * u := by
    rw [hhalf]
    intro hcon
    have h1 : (5 : ZMod p) ^ ((p - 1) / 2) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp hcon
    have h2 : (5 : ZMod p) ^ ((p - 1) / 2) = -1 := euler_nonsquare h5 hp2
    rw [h1] at h2
    exact two_ne_zero' hp2 (by linear_combination h2)
  have hdvd' : orderOf (5 : ZMod p) ∣ 2 ^ ((a - 1) + 1) * u := by
    rw [show (a - 1) + 1 = a by omega, hsplit]
    exact hdp
  have hsat : 2 ^ a ∣ orderOf (5 : ZMod p) := by
    have := pow_two_dvd_of_not_dvd_half hd0 hdvd' hnot
    rwa [show (a - 1) + 1 = a by omega] at this
  have hka : k ≤ a :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hp10).mp hk
  exact dvd_trans (dvd_trans (pow_dvd_pow 2 hka) hsat) hdn

/-- **La seconda ganascia, forma globale.** Sia `n` squarefree con
`5 ∤ n` che soddisfa la congruenza di Agrawal a `r = 5`, e sia `p` un
suo fattore primo dispari INERTE in `Q(√5)` (`p ≡ ±2 mod 5`). Allora
`v₂(p−1) ≤ v₂(n−1)`: la profondità 2-adica di ogni fattore inerte è
limitata da quella di `n − 1`.
@isnad1 id=dvd.8h3v.s9.52ba74226a2b from=translated src=- shape=a0b14d33 vocab=353830b2
-/
theorem agrawal_two_adic_jaw {n : ℕ} (hsq : Squarefree n) (h5 : ¬ (5 ∣ n))
    (h : ∃ g : Polynomial (ZMod n),
      (X - 1) ^ n = X ^ n - 1 + (X ^ 5 - 1) * g)
    {p k : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hp2 : p ≠ 2)
    (hinert : p % 5 = 2 ∨ p % 5 = 3) (hk : 2 ^ k ∣ p - 1) :
    2 ^ k ∣ n - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hbridge : n ∣ 5 ^ (n - 1) - 1 := agrawal_fermat_shadow hsq h5 h
  have hpd : p ∣ 5 ^ (n - 1) - 1 := dvd_trans hpn hbridge
  have hge : 1 ≤ 5 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
  have hloc : (5 : ZMod p) ^ (n - 1) = 1 := by
    have h0 : ((5 ^ (n - 1) - 1 : ℕ) : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hpd
    rw [Nat.cast_sub hge] at h0
    push_cast at h0
    linear_combination h0
  exact two_adic_jaw_local hp2 (not_isSquare_five hp2 hinert) hloc hk

/-- **Corollario mod 4.** Un controesempio squarefree `n ≡ 3 (mod 4)`
può avere fattori primi inerti soltanto `≡ 3 (mod 4)`.
@isnad1 id=eq.8h2v.s9.4c53cb4b7903 from=translated src=- shape=2d2978cb vocab=353830b2
-/
theorem agrawal_inert_mod_four {n : ℕ} (hsq : Squarefree n) (h5 : ¬ (5 ∣ n))
    (h : ∃ g : Polynomial (ZMod n),
      (X - 1) ^ n = X ^ n - 1 + (X ^ 5 - 1) * g)
    (hn4 : n % 4 = 3) {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hp2 : p ≠ 2)
    (hinert : p % 5 = 2 ∨ p % 5 = 3) :
    p % 4 = 3 := by
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  by_contra hcon
  have hdvd : 2 ^ 2 ∣ p - 1 := by
    have h1 : 1 ≤ p := hp.one_lt.le
    have : p % 4 = 1 := by omega
    omega
  have hkey : 2 ^ 2 ∣ n - 1 :=
    agrawal_two_adic_jaw hsq h5 h hp hpn hp2 hinert hdvd
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; omega)
  omega

end AgrawalCore
