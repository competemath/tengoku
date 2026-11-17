/-
Nucleo Lean della campagna Agrawal — lotto 18: LA PARTIZIONE FORZATA.

Nel programma costruttivo del 25 luglio avevamo scoperto per via sperimentale
che i primi piccoli vanno divisi in due famiglie disgiunte — una ammessa a
dividere i `p−1`, l'altra i `p+1` — altrimenti `gcd(L,M) > 2` e il sistema
cinese muore. La trattavamo come un accorgimento tecnico di costruzione.

**Non è un accorgimento: è una necessità**, e vale per ogni numero che sia
simultaneamente di Carmichael e di Lucas–Carmichael.

La catena. Da `p−1 ∣ n−1` e `p+1 ∣ n+1` con `n = p·m` segue che entrambe le
condizioni si leggono su `m−1`, cioè `(p²−1)/2 ∣ n/p − 1`: è la forma
unificata già usata in tutta la campagna. Se un primo dispari `q` divide
`p²−1`, allora `q ∣ m−1`, cioè `n ≡ p (mod q)`. Se un secondo fattore `p'`
vede lo stesso `q`, allora `p ≡ n ≡ p' (mod q)`; ma se `q ∣ p−1` e
`q ∣ p'+1`, sottraendo si ottiene `q ∣ 2`, assurdo per `q` dispari.

  · `dvd_sub_of_korselt_pair` : entrambe le condizioni si leggono su `m−1`
  · `dvd_of_dvd_sq_sub_one`   : `q ∣ p²−1` ⟹ `q ∣ m−1`
  · `common_divisor_forced`   : la forma esatta — ogni divisore comune
                                trasversale divide `2`
  · `partition_forced`        : il corollario per un primo `q`
  · `three_dvd_sq_sub_one`    : 3 divide sempre `p²−1`, quindi il vincolo per
                                `q = 3` è universale: tutti i fattori sono
                                congrui fra loro modulo 3

Prior art: la compatibilità `gcd(pᵢ - 1, pⱼ + 1) = 2` per insiemi di
Williams compare esplicitamente in McIntosh (2014). Il contributo di questo
modulo è la sua verifica kernel-pura e la scomposizione in lemmi riusabili,
non una rivendicazione di priorità matematica.

Campagna UNICO, 26 luglio 2026.
-/
import Tengoku.Seed.RingTheory.Int.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/-- **La forma unificata di Korselt.** Se `n = p·m` soddisfa
`p−1 ∣ n−1` (Carmichael) e `p+1 ∣ n+1` (Lucas–Carmichael), allora entrambe le
condizioni si leggono su `m−1`.
@isnad1 id=and.2h2v.s7.b2d30903062b from=translated src=- shape=4c4857b5 vocab=ec041f02
-/
theorem dvd_sub_of_korselt_pair {p m : ℤ}
    (hcar : (p - 1) ∣ (p * m - 1)) (hluc : (p + 1) ∣ (p * m + 1)) :
    (p - 1) ∣ (m - 1) ∧ (p + 1) ∣ (m - 1) := by
  obtain ⟨c, hc⟩ := hcar
  obtain ⟨d, hd⟩ := hluc
  refine ⟨⟨c - m, by linarith [hc]⟩, ⟨m - d, by linarith [hd]⟩⟩

/-- Se un primo `q` divide `p²−1` e valgono le due condizioni di Korselt per
`p`, allora `q ∣ m−1`, cioè `n ≡ p (mod q)`.
@isnad1 id=dvd.4h3v.s7.e1de45107f12 from=translated src=- shape=f8e713da vocab=d1076782
-/
theorem dvd_of_dvd_sq_sub_one {p m q : ℤ} (hq : Prime q)
    (hcar : (p - 1) ∣ (p * m - 1)) (hluc : (p + 1) ∣ (p * m + 1))
    (hdvd : q ∣ (p - 1) * (p + 1)) :
    q ∣ (m - 1) := by
  obtain ⟨h1, h2⟩ := dvd_sub_of_korselt_pair hcar hluc
  rcases hq.dvd_mul.mp hdvd with h | h
  · exact h.trans h1
  · exact h.trans h2

/-- **La forma esatta della partizione forzata.** Se `d` divide `p−1` per un
fattore e `p'+1` per un altro, e se entrambi soddisfano le condizioni di
Korselt rispetto allo stesso `n`, allora `d ∣ 2`. Non servono né primalità
né disparità di `d`.
@isnad1 id=dvd.7h5v.s7.5e14c5769f8f from=translated src=- shape=a491aae2 vocab=ec041f02
-/
theorem common_divisor_forced {p p' m m' d : ℤ}
    (hcar : (p - 1) ∣ (p * m - 1)) (hluc : (p + 1) ∣ (p * m + 1))
    (hcar' : (p' - 1) ∣ (p' * m' - 1)) (hluc' : (p' + 1) ∣ (p' * m' + 1))
    (hsame : p * m = p' * m')
    (hleft : d ∣ (p - 1)) (hright : d ∣ (p' + 1)) :
    d ∣ 2 := by
  obtain ⟨hp, _⟩ := dvd_sub_of_korselt_pair hcar hluc
  obtain ⟨_, hp'⟩ := dvd_sub_of_korselt_pair hcar' hluc'
  -- n ≡ p (mod q) da sinistra, n ≡ p' (mod q) da destra
  have hm : d ∣ (m - 1) := hleft.trans hp
  have hm' : d ∣ (m' - 1) := hright.trans hp'
  -- n − p = p·m − p = p(m−1), quindi q ∣ n − p; analogamente q ∣ n − p'
  have h1 : d ∣ (p * m - p) := by
    have : p * m - p = p * (m - 1) := by ring
    exact this ▸ hm.mul_left p
  have h2 : d ∣ (p' * m' - p') := by
    have : p' * m' - p' = p' * (m' - 1) := by ring
    exact this ▸ hm'.mul_left p'
  -- da q ∣ n−p e q ∣ n−p' segue q ∣ p' − p
  have h3 : d ∣ (p' - p) := by
    have : p' - p = (p * m - p) - (p' * m' - p') := by rw [hsame]; ring
    exact this ▸ dvd_sub h1 h2
  -- e da q ∣ p−1, q ∣ p'+1 segue q ∣ (p'+1) − (p−1) = (p'−p) + 2
  have h4 : d ∣ ((p' + 1) - (p - 1)) := dvd_sub hright hleft
  have : (2 : ℤ) = ((p' + 1) - (p - 1)) - (p' - p) := by ring
  exact this ▸ dvd_sub h4 h3

/-- **La partizione forzata, forma prima.** Un primo `q` che divide
trasversalmente `p−1` e `p'+1` deve dividere `2`; per `q` dispari le due
famiglie non possono coesistere.
@isnad1 id=dvd.8h5v.s7.eef70d3744f0 from=translated src=- shape=e0c5f1d1 vocab=d1076782
-/
theorem partition_forced {p p' m m' q : ℤ} (_hq : Prime q)
    (hcar : (p - 1) ∣ (p * m - 1)) (hluc : (p + 1) ∣ (p * m + 1))
    (hcar' : (p' - 1) ∣ (p' * m' - 1)) (hluc' : (p' + 1) ∣ (p' * m' + 1))
    (hsame : p * m = p' * m')
    (hleft : q ∣ (p - 1)) (hright : q ∣ (p' + 1)) :
    q ∣ 2 :=
  common_divisor_forced hcar hluc hcar' hluc' hsame hleft hright

/-- Tre divide sempre `p²−1` per `p` non multiplo di 3: il vincolo della
partizione per `q = 3` è dunque universale, e in un Carmichael ∩
Lucas–Carmichael tutti i fattori primi sono congrui fra loro modulo 3.
@isnad1 id=dvd.1h1v.s5.e2f9539cd444 from=translated src=- shape=3e31d414 vocab=ec041f02
-/
theorem three_dvd_sq_sub_one {p : ℤ} (hp : ¬ ((3 : ℤ) ∣ p)) :
    (3 : ℤ) ∣ (p - 1) * (p + 1) := by
  have h : p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases h with h | h
  · exact Dvd.dvd.mul_right (by omega) _
  · exact Dvd.dvd.mul_left (by omega) _

/-- **Corollario universale modulo 3.** Due fattori non divisibili per `3`
che soddisfano entrambe le condizioni di Korselt rispetto allo stesso `n`
sono congrui modulo `3`.
@isnad1 id=dvd.7h4v.s7.67b120a8d1cb from=translated src=- shape=02a173ca vocab=ec041f02
-/
theorem three_congruence_forced {p p' m m' : ℤ}
    (hp3 : ¬ ((3 : ℤ) ∣ p)) (hp3' : ¬ ((3 : ℤ) ∣ p'))
    (hcar : (p - 1) ∣ (p * m - 1)) (hluc : (p + 1) ∣ (p * m + 1))
    (hcar' : (p' - 1) ∣ (p' * m' - 1)) (hluc' : (p' + 1) ∣ (p' * m' + 1))
    (hsame : p * m = p' * m') :
    (3 : ℤ) ∣ (p' - p) := by
  have hprime : Prime (3 : ℤ) := by norm_num
  have hm : (3 : ℤ) ∣ (m - 1) :=
    dvd_of_dvd_sq_sub_one hprime hcar hluc (three_dvd_sq_sub_one hp3)
  have hm' : (3 : ℤ) ∣ (m' - 1) :=
    dvd_of_dvd_sq_sub_one hprime hcar' hluc' (three_dvd_sq_sub_one hp3')
  have h1 : (3 : ℤ) ∣ (p * m - p) := by
    have : p * m - p = p * (m - 1) := by ring
    exact this ▸ hm.mul_left p
  have h2 : (3 : ℤ) ∣ (p' * m' - p') := by
    have : p' * m' - p' = p' * (m' - 1) := by ring
    exact this ▸ hm'.mul_left p'
  have : p' - p = (p * m - p) - (p' * m' - p') := by
    rw [hsame]
    ring
  exact this ▸ dvd_sub h1 h2

/-- **Dalla riga forte alla firma cubica.** La divisibilità sul complemento
`10(p²−1) ∣ m−1` è esattamente la parametrizzazione
`p*m = p + 10*u*(p³−p)` usata nel ramo Lenstra a cinque fattori.
@isnad1 id=ex.1h2v.s6.54a99be2ca0f from=translated src=- shape=abe2fda9 vocab=ec041f02
-/
theorem cubic_signature_of_strong_row {p m : ℤ}
    (hrow : 10 * (p * p - 1) ∣ (m - 1)) :
    ∃ u : ℤ, p * m = p + 10 * u * (p * p * p - p) := by
  obtain ⟨u, hu⟩ := hrow
  refine ⟨u, ?_⟩
  have hm : m = 1 + 10 * (p * p - 1) * u := by linarith
  rw [hm]
  ring

/-- **La firma cubica restituisce la riga forte.** Per `p ≠ 0`, la
parametrizzazione cubica non contiene informazione ulteriore rispetto alla
divisibilità sul complemento.
@isnad1 id=dvd.2h3v.s7.e15b5f95df98 from=translated src=- shape=0e0bb828 vocab=ec041f02
-/
theorem strong_row_of_cubic_signature {p m u : ℤ} (hp : p ≠ 0)
    (hsig : p * m = p + 10 * u * (p * p * p - p)) :
    10 * (p * p - 1) ∣ (m - 1) := by
  refine ⟨u, ?_⟩
  apply mul_left_cancel₀ hp
  calc
    p * (m - 1) = p * m - p := by ring
    _ = 10 * u * (p * p * p - p) := by linarith
    _ = p * (10 * (p * p - 1) * u) := by ring

end AgrawalCore
