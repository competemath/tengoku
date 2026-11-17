/-
Nucleo Lean della campagna Agrawal — lotto 19: IL PROFILO H4.

Questo modulo definisce finalmente la successione aritmetica

  Aₙ = Lₙ  se n è pari,  Fₙ se n è dispari,
  Hₙ = gcd(Aₙ, 5^(n-1) + 1),

e dimostra il ponte end-to-end, nel nucleo aureo:

  p ∣ Hₙ  ↔  ε^(2n) = -1  ∧  5^(n-1) = -1  (mod p).

La direzione Fibonacci/Lucas mancante viene provata in entrambi i casi
di parità. Il modulo non afferma H4: l'esclusione universale dei primi
split resta precisamente la congettura aperta.

Campagna UNICO, 26 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.SupportBridge
import Tengoku.AgrawalR5.AgrawalCore.TwoAdicJaw

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

/-- Il termine misto Fibonacci--Lucas usato nella congettura H4.-/
def goldenA (n : ℕ) : ℕ := if Even n then lucas n else Nat.fib n

/-- La successione gcd che codifica il profilo scalare H4.-/
def goldenH (n : ℕ) : ℕ := Nat.gcd (goldenA n) (5 ^ (n - 1) + 1)

lemma goldenA_of_even {n : ℕ} (hn : Even n) : goldenA n = lucas n := by
  simp [goldenA, hn]

lemma goldenA_of_odd {n : ℕ} (hn : Odd n) : goldenA n = Nat.fib n := by
  have hne : ¬ Even n := by
    rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := hn
    omega
  simp [goldenA, hne]

omit [Fact p.Prime] in
/-- Dividere `Hₙ` equivale a dividere entrambi i suoi argomenti.-/
lemma dvd_goldenH_iff {n : ℕ} :
    p ∣ goldenH n ↔ p ∣ goldenA n ∧ p ∣ 5 ^ (n - 1) + 1 := by
  exact Nat.dvd_gcd_iff

/-- La congruenza scalare negativa di `5` è esattamente la divisibilità
del secondo argomento di `Hₙ`.-/
lemma five_pow_eq_neg_one_iff_dvd {n : ℕ} :
    (5 : ZMod p) ^ (n - 1) = -1 ↔ p ∣ 5 ^ (n - 1) + 1 := by
  constructor
  · intro h
    rw [← CharP.cast_eq_zero_iff (ZMod p) p]
    push_cast
    rw [h]
    ring
  · intro h
    have h0 : ((5 ^ (n - 1) + 1 : ℕ) : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p _).mpr h
    push_cast at h0
    linear_combination h0

/-- Se `n` è pari e `p ∣ Lₙ`, allora `ε^(2n) = -1`.-/
lemma pow_eq_neg_one_of_dvd_lucas_even {n : ℕ} (hn : 1 ≤ n)
    (hev : Even n) (hdvd : p ∣ lucas n) :
    (eps : GoldenRing p) ^ (2 * n) = -1 := by
  have hL : ((lucas n : ℕ) : GoldenRing p) = 0 :=
    natCast_eq_zero_of_dvd hdvd
  have hsum := eps_pow_add_eps'_pow (p := p) hn
  rw [hL] at hsum
  have hneg : (eps : GoldenRing p) ^ n = -eps' ^ n := by
    linear_combination hsum
  have hprod : (eps : GoldenRing p) ^ n * eps' ^ n = 1 := by
    rw [← mul_pow, eps_mul_eps']
    exact hev.neg_one_pow
  calc
    (eps : GoldenRing p) ^ (2 * n) = eps ^ n * eps ^ n := by
      rw [two_mul, pow_add]
    _ = eps' ^ n * eps' ^ n := by rw [hneg]; ring
    _ = -1 := by
      rw [hneg] at hprod
      linear_combination -hprod

/-- Se `n` è dispari e `p ∣ Fₙ`, allora `ε^(2n) = -1`.-/
lemma pow_eq_neg_one_of_dvd_fib_odd {n : ℕ} (hn : 1 ≤ n)
    (hodd : Odd n) (hdvd : p ∣ Nat.fib n) :
    (eps : GoldenRing p) ^ (2 * n) = -1 := by
  have hF : ((Nat.fib n : ℕ) : GoldenRing p) = 0 :=
    natCast_eq_zero_of_dvd hdvd
  have hdiff : (eps ^ n - eps' ^ n : GoldenRing p)
      = (Nat.fib n : GoldenRing p) * sqrt5 := by
    rw [golden_pow_pred (eps_sq (p := p)) hn,
        golden_pow_pred (eps'_sq (p := p)) hn]
    unfold eps' sqrt5
    ring
  rw [hF, zero_mul] at hdiff
  have heq : (eps : GoldenRing p) ^ n = eps' ^ n := by
    linear_combination hdiff
  calc
    (eps : GoldenRing p) ^ (2 * n) = eps ^ n * eps ^ n := by
      rw [two_mul, pow_add]
    _ = eps ^ n * eps' ^ n := by rw [heq]
    _ = (eps * eps') ^ n := (mul_pow _ _ _).symm
    _ = (-1 : GoldenRing p) ^ n := by rw [eps_mul_eps']
    _ = -1 := hodd.neg_one_pow

/-- La prima coordinata del profilo H è equivalente al semiperiodo aureo
negativo.-/
theorem golden_pow_eq_neg_one_iff_dvd_A {n : ℕ} (hn : 1 ≤ n)
    (hp5 : p ≠ 5) :
    (eps : GoldenRing p) ^ (2 * n) = -1 ↔ p ∣ goldenA n := by
  constructor
  · intro h
    rcases Nat.even_or_odd n with hev | hodd
    · rw [goldenA_of_even hev]
      exact dvd_lucas_of_pow_eq_neg_one hn hev h
    · rw [goldenA_of_odd hodd]
      exact dvd_fib_of_pow_eq_neg_one hn hodd hp5 h
  · intro h
    rcases Nat.even_or_odd n with hev | hodd
    · rw [goldenA_of_even hev] at h
      exact pow_eq_neg_one_of_dvd_lucas_even hn hev h
    · rw [goldenA_of_odd hodd] at h
      exact pow_eq_neg_one_of_dvd_fib_odd hn hodd h

/-- **Ponte aritmetico completo per H4.** Per `n ≥ 1` e `p ≠ 5`,
`p ∣ Hₙ` se e solo se valgono simultaneamente le due congruenze scalari
negative nel nucleo aureo.-/
theorem dvd_goldenH_iff_scalar_profile {n : ℕ} (hn : 1 ≤ n)
    (hp5 : p ≠ 5) :
    p ∣ goldenH n ↔
      (eps : GoldenRing p) ^ (2 * n) = -1
        ∧ (5 : ZMod p) ^ (n - 1) = -1 := by
  rw [dvd_goldenH_iff, golden_pow_eq_neg_one_iff_dvd_A hn hp5,
      five_pow_eq_neg_one_iff_dvd]

/-- Se una potenza di `5` è `-1`, l'ordine di `5` contiene esattamente
un livello 2-adico in più dell'esponente. Questa è la metà elementare
del bersaglio di saturazione H4.-/
theorem orderOf_five_two_adic_lower_bound_of_neg_one {n : ℕ}
    (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hneg : (5 : ZMod p) ^ (n - 1) = -1) :
    2 ^ ((n - 1).factorization 2 + 1) ∣ orderOf (5 : ZMod p) := by
  have h50 : (5 : ZMod p) ≠ 0 := five_ne_zero hp5
  have hp1 : p - 1 ≠ 0 := by
    have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hdp : orderOf (5 : ZMod p) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one h50
  have hd0 : orderOf (5 : ZMod p) ≠ 0 := by
    intro h0
    rw [h0] at hdp
    exact hp1 (Nat.eq_zero_of_zero_dvd hdp)
  have hpow : (5 : ZMod p) ^ (2 * (n - 1)) = 1 := by
    rw [two_mul, pow_add, hneg]
    ring
  have hdvd : orderOf (5 : ZMod p) ∣ 2 * (n - 1) :=
    orderOf_dvd_of_pow_eq_one hpow
  have hnot : ¬ orderOf (5 : ZMod p) ∣ n - 1 := by
    intro h
    have hone : (5 : ZMod p) ^ (n - 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp h
    rw [hone] at hneg
    exact two_ne_zero' hp2 (by linear_combination hneg)
  set a := (n - 1).factorization 2 with ha
  set u := (n - 1) / 2 ^ a with hu
  have hsplit : 2 ^ a * u = n - 1 :=
    Nat.ordProj_mul_ordCompl_eq_self (n - 1) 2
  have hdvd' : orderOf (5 : ZMod p) ∣ 2 ^ (a + 1) * u := by
    have heq : 2 ^ (a + 1) * u = 2 * (n - 1) := by
      calc
        2 ^ (a + 1) * u = 2 * (2 ^ a * u) := by rw [pow_succ]; ring
        _ = 2 * (n - 1) := by rw [hsplit]
    rw [heq]
    exact hdvd
  have hnot' : ¬ orderOf (5 : ZMod p) ∣ 2 ^ a * u := by
    rwa [hsplit]
  exact pow_two_dvd_of_not_dvd_half hd0 hdvd' hnot'

/-- Forma esatta del lemma precedente: la valutazione 2-adica
dell'ordine di `5` è precisamente una unità più profonda di quella
dell'esponente che porta `5` a `-1`.-/
theorem orderOf_five_factorization_two_of_neg_one {n : ℕ}
    (hn : 2 ≤ n) (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hneg : (5 : ZMod p) ^ (n - 1) = -1) :
    (orderOf (5 : ZMod p)).factorization 2
      = (n - 1).factorization 2 + 1 := by
  have h50 : (5 : ZMod p) ≠ 0 := five_ne_zero hp5
  have hp1 : p - 1 ≠ 0 := by
    have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hdp : orderOf (5 : ZMod p) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one h50
  have hd0 : orderOf (5 : ZMod p) ≠ 0 := by
    intro h0
    rw [h0] at hdp
    exact hp1 (Nat.eq_zero_of_zero_dvd hdp)
  have hlower : (n - 1).factorization 2 + 1
      ≤ (orderOf (5 : ZMod p)).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hd0).mp
      (orderOf_five_two_adic_lower_bound_of_neg_one hp2 hp5 hneg)
  have hpow : (5 : ZMod p) ^ (2 * (n - 1)) = 1 := by
    rw [two_mul, pow_add, hneg]
    ring
  have hdvd : orderOf (5 : ZMod p) ∣ 2 * (n - 1) :=
    orderOf_dvd_of_pow_eq_one hpow
  have he0 : n - 1 ≠ 0 := by omega
  have htwoe0 : 2 * (n - 1) ≠ 0 := Nat.mul_ne_zero (by norm_num) he0
  have hfac : (orderOf (5 : ZMod p)).factorization
      ≤ (2 * (n - 1)).factorization :=
    (Nat.factorization_le_iff_dvd hd0 htwoe0).mpr hdvd
  have hupper := hfac 2
  rw [Nat.factorization_mul (by norm_num) he0] at hupper
  norm_num at hupper
  omega

/-- Per un primo inerte, l'ordine di `5` satura l'intera componente
2-primaria di `p-1`.-/
theorem orderOf_five_factorization_two_eq_card_of_nonsquare
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) (h5 : ¬ IsSquare (5 : ZMod p)) :
    (orderOf (5 : ZMod p)).factorization 2
      = (p - 1).factorization 2 := by
  have h50 : (5 : ZMod p) ≠ 0 := five_ne_zero hp5
  have hp1 : p - 1 ≠ 0 := by
    have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hdp : orderOf (5 : ZMod p) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one h50
  have hd0 : orderOf (5 : ZMod p) ≠ 0 := by
    intro h0
    rw [h0] at hdp
    exact hp1 (Nat.eq_zero_of_zero_dvd hdp)
  set a := (p - 1).factorization 2 with ha
  set u := (p - 1) / 2 ^ a with hu
  have hsplit : 2 ^ a * u = p - 1 :=
    Nat.ordProj_mul_ordCompl_eq_self (p - 1) 2
  have ha1 : 1 ≤ a := by
    have hodd : p % 2 = 1 :=
      (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp2
    have h2 : (2 : ℕ) ∣ p - 1 := by omega
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hp1).mp
      (by simpa using h2)
  have hhalf : 2 ^ (a - 1) * u = (p - 1) / 2 := by
    have hpow : (2 : ℕ) ^ a = 2 * 2 ^ (a - 1) := by
      conv_lhs => rw [show a = 1 + (a - 1) by omega]
      rw [pow_add, pow_one]
    rw [← hsplit, hpow, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  have hnot : ¬ orderOf (5 : ZMod p) ∣ 2 ^ (a - 1) * u := by
    rw [hhalf]
    intro h
    have hone : (5 : ZMod p) ^ ((p - 1) / 2) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp h
    have hneg := euler_nonsquare h5 hp2
    rw [hone] at hneg
    exact two_ne_zero' hp2 (by linear_combination hneg)
  have hdvd' : orderOf (5 : ZMod p) ∣ 2 ^ ((a - 1) + 1) * u := by
    rw [show (a - 1) + 1 = a by omega, hsplit]
    exact hdp
  have hpowdvd : 2 ^ a ∣ orderOf (5 : ZMod p) := by
    have h := pow_two_dvd_of_not_dvd_half hd0 hdvd' hnot
    rwa [show (a - 1) + 1 = a by omega] at h
  have hlower : a ≤ (orderOf (5 : ZMod p)).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hd0).mp hpowdvd
  have hfac : (orderOf (5 : ZMod p)).factorization
      ≤ (p - 1).factorization :=
    (Nat.factorization_le_iff_dvd hd0 hp1).mpr hdp
  have hupper := hfac 2
  omega

/-- Ogni divisore primo di `Hₙ` soddisfa il lower bound 2-adico che
precede la congettura di saturazione.-/
theorem dvd_goldenH_two_adic_lower_bound {n : ℕ} (hn : 2 ≤ n)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) (hdvd : p ∣ goldenH n) :
    2 ^ ((n - 1).factorization 2 + 1) ∣ orderOf (5 : ZMod p) := by
  have hscalar :=
    (dvd_goldenH_iff_scalar_profile (p := p) (by omega) hp5).mp hdvd
  exact orderOf_five_two_adic_lower_bound_of_neg_one hp2 hp5 hscalar.2

/-- La valutazione 2-adica dell'ordine di `5` è determinata esattamente
da ogni divisore primo di `Hₙ`.-/
theorem dvd_goldenH_order_factorization_two {n : ℕ} (hn : 2 ≤ n)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) (hdvd : p ∣ goldenH n) :
    (orderOf (5 : ZMod p)).factorization 2
      = (n - 1).factorization 2 + 1 := by
  have hscalar :=
    (dvd_goldenH_iff_scalar_profile (p := p) (by omega) hp5).mp hdvd
  exact orderOf_five_factorization_two_of_neg_one hn hp2 hp5 hscalar.2

/-- **Forma kernel-pura del muro H4.** Per ogni divisore primo di `Hₙ`,
l'inerzia di `5` è equivalente all'uguaglianza fra la profondità 2-adica
di `p-1` e quella, già determinata, dell'ordine di `5`. Il teorema non
afferma che tale uguaglianza valga sempre.-/
theorem dvd_goldenH_nonsquare_iff_two_adic_saturation {n : ℕ}
    (hn : 2 ≤ n) (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hdvd : p ∣ goldenH n) :
    ¬ IsSquare (5 : ZMod p) ↔
      (p - 1).factorization 2 = (n - 1).factorization 2 + 1 := by
  have horder :=
    dvd_goldenH_order_factorization_two hn hp2 hp5 hdvd
  constructor
  · intro h5
    have hinert :=
      orderOf_five_factorization_two_eq_card_of_nonsquare hp2 hp5 h5
    omega
  · intro hsat hsq
    have h50 : (5 : ZMod p) ≠ 0 := five_ne_zero hp5
    have hp1 : p - 1 ≠ 0 := by
      have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
      omega
    have hd0 : orderOf (5 : ZMod p) ≠ 0 := by
      have hdp : orderOf (5 : ZMod p) ∣ p - 1 :=
        ZMod.orderOf_dvd_card_sub_one h50
      intro h0
      rw [h0] at hdp
      exact hp1 (Nat.eq_zero_of_zero_dvd hdp)
    have hodd : p % 2 = 1 :=
      (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp2
    have hhalfexp : p / 2 = (p - 1) / 2 := by omega
    have heuler : (5 : ZMod p) ^ ((p - 1) / 2) = 1 := by
      rw [← hhalfexp]
      exact (ZMod.euler_criterion p h50).mp hsq
    have hordhalf : orderOf (5 : ZMod p) ∣ (p - 1) / 2 :=
      orderOf_dvd_of_pow_eq_one heuler
    have hhalf0 : (p - 1) / 2 ≠ 0 := by
      have hpge3 : 3 ≤ p := by omega
      omega
    have hfac : (orderOf (5 : ZMod p)).factorization
        ≤ ((p - 1) / 2).factorization :=
      (Nat.factorization_le_iff_dvd hd0 hhalf0).mpr hordhalf
    have hle := hfac 2
    have h2 : (2 : ℕ) ∣ p - 1 := by omega
    rw [Nat.factorization_div h2] at hle
    have htwo : (2 : ℕ).factorization 2 = 1 := by
      rw [Nat.Prime.factorization Nat.prime_two]
      simp
    simp [htwo] at hle
    have hb1 : 1 ≤ (p - 1).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hp1).mp
        (by simpa using h2)
    omega

end AgrawalCore
