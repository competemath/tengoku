/-
Nucleo Lean della campagna Agrawal — RAMO BIFATTORIALE INCONDIZIONATO.

Questo modulo isola ciò che segue senza assumere H4 quando `n = p*q`.
Se `n² ≠ 1 (mod 5)`, esattamente uno dei due primi è split in
`Q(√5)` e l'altro è inerte. Il lemma squarefree d'ingresso fornisce
poi, sul fattore split, la riga locale effettiva con esponente uguale
all'altro primo.

Non si afferma che questa riga sia impossibile: quella è precisamente
la parte locale ancora aperta. Il risultato riduce però il caso a due
fattori a un solo sistema misto split–inerte, senza usare H4.
-/
import Tengoku.AgrawalR5.AgrawalCore.SquarefreeIngress
import Tengoku.AgrawalR5.AgrawalCore.Reciprocity
import Tengoku.AgrawalR5.AgrawalCore.H4Witness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

/-- Classe split in `Q(√5)`, scritta soltanto in termini di residui.-/
def SplitModFive (a : ℕ) : Prop :=
  a % 5 = 1 ∨ a % 5 = 4

/-- Classe inerte in `Q(√5)`, scritta soltanto in termini di residui.-/
def InertModFive (a : ℕ) : Prop :=
  a % 5 = 2 ∨ a % 5 = 3

/-- Ogni potenza `ζ^a` con `a` invertibile modulo `5` è ancora una radice
di `Φ₅`.-/
lemma phi5_aeval_zeta_pow_of_unit {p a : ℕ} [Fact p.Prime]
    (ha : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4) :
    Polynomial.aeval ((zeta5 : Phi5Ring p) ^ a) (phi5 p) = 0 := by
  rcases ha with ha | ha | ha | ha
  · simpa [zeta5_pow_mod, ha] using phi5_aeval_zeta (p := p)
  · simpa [zeta5_pow_mod, ha] using phi5_aeval_zeta_pow_two (p := p)
  · simpa [zeta5_pow_mod, ha] using phi5_aeval_zeta_pow_three (p := p)
  · simpa [zeta5_pow_mod, ha] using phi5_aeval_zeta_pow_four (p := p)

/-- Le righe locali si moltiplicano quando il primo esponente è invertibile
modulo `5`: se `a,b ∈ S(p,5)`, allora `ab ∈ S(p,5)`.-/
theorem localS5_mul {p a b : ℕ} [Fact p.Prime]
    (ha5 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4)
    (ha : LocalS5 p a) (hb : LocalS5 p b) :
    LocalS5 p (a * b) := by
  calc
    ((zeta5 : Phi5Ring p) - 1) ^ (a * b)
        = (((zeta5 : Phi5Ring p) - 1) ^ a) ^ b := pow_mul _ _ _
    _ = (zeta5 ^ a - 1) ^ b := by rw [ha]
    _ = zeta5 ^ (a * b) - 1 :=
      localS5_row hb (phi5_aeval_zeta_pow_of_unit ha5)

/-- La riga con esponente `2` è impossibile in caratteristica diversa da
`2` e `5`.-/
theorem not_localS5_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ¬ LocalS5 p 2 := by
  intro h
  have hzero : (2 : Phi5Ring p) * (zeta5 - 1) = 0 := by
    unfold LocalS5 at h
    linear_combination -h
  have h2z : IsUnit (2 : ZMod p) :=
    isUnit_iff_ne_zero.mpr (two_ne_zero' hp2)
  have h2u : IsUnit (2 : Phi5Ring p) := by
    have hm := h2z.map (AdjoinRoot.of (phi5 p))
    rwa [map_ofNat] at hm
  have hz0 : (zeta5 : Phi5Ring p) - 1 = 0 :=
    (h2u.mul_right_eq_zero).mp hzero
  exact (zeta_sub_one_isUnit (p := p) hp5).ne_zero hz0

/-- **Parity of an order-four local row.**

In characteristic different from `2` and `5`, a literal local row whose
residue modulo `5` is `2` or `3` is automatically odd.  Indeed, compare
the row at `ζ` with the conjugate row at `ζ⁻¹ = ζ⁴`.  If the exponent
were even, conjugation would force `ζ³ - 1 = -(ζ³ - 1)` in the residue-2
case, or `ζ² - 1 = -(ζ² - 1)` in the residue-3 case.  Both elements are
units away from `5`, while `2` is a unit away from characteristic `2`.-/
theorem localS5_orderFour_odd {p m : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hrow : LocalS5 p m) (hm : m % 5 = 2 ∨ m % 5 = 3) :
    Odd m := by
  rcases Nat.even_or_odd m with heven | hodd
  · exfalso
    have h4raw := localS5_row (p := p) hrow
      (phi5_aeval_zeta_pow_four (p := p))
    have h2z : IsUnit (2 : ZMod p) :=
      isUnit_iff_ne_zero.mpr (two_ne_zero' hp2)
    have h2u : IsUnit (2 : Phi5Ring p) := by
      have hmap := h2z.map (AdjoinRoot.of (phi5 p))
      rwa [map_ofNat] at hmap
    rcases hm with hm2 | hm3
    · have h1 :
          ((zeta5 : Phi5Ring p) - 1) ^ m = zeta5 ^ 2 - 1 := by
        unfold LocalS5 at hrow
        calc
          ((zeta5 : Phi5Ring p) - 1) ^ m = zeta5 ^ m - 1 := hrow
          _ = zeta5 ^ 2 - 1 := by rw [zeta5_pow_mod, hm2]
      have h4 :
          ((zeta5 : Phi5Ring p) ^ 4 - 1) ^ m = zeta5 ^ 3 - 1 := by
        calc
          ((zeta5 : Phi5Ring p) ^ 4 - 1) ^ m =
              zeta5 ^ (4 * m) - 1 := h4raw
          _ = zeta5 ^ 3 - 1 := by
            rw [zeta5_pow_mod]
            congr 2
            omega
      have h4neg :
          ((zeta5 : Phi5Ring p) ^ 4 - 1) ^ m =
              -(zeta5 ^ 3 - 1) := by
        calc
          ((zeta5 : Phi5Ring p) ^ 4 - 1) ^ m =
              (-(zeta5 ^ 4) * (zeta5 - 1)) ^ m := by
                rw [u4_eq_cyclo_factor]
          _ = (-(zeta5 ^ 4)) ^ m * (zeta5 - 1) ^ m := by
                rw [mul_pow]
          _ = (zeta5 ^ 4) ^ m * (zeta5 - 1) ^ m := by
                rw [heven.neg_pow]
          _ = zeta5 ^ (4 * m) * (zeta5 ^ 2 - 1) := by
                rw [← pow_mul, h1]
          _ = zeta5 ^ 3 * (zeta5 ^ 2 - 1) := by
                rw [zeta5_pow_mod]
                congr 2
                omega
          _ = -(zeta5 ^ 3 - 1) := by
                have hz5 := zeta5_pow_five (p := p)
                linear_combination hz5
      have hzero :
          (2 : Phi5Ring p) * (zeta5 ^ 3 - 1) = 0 := by
        linear_combination h4neg - h4
      exact (h2u.mul (u3_isUnit (p := p) hp5)).ne_zero hzero
    · have h1 :
          ((zeta5 : Phi5Ring p) - 1) ^ m = zeta5 ^ 3 - 1 := by
        unfold LocalS5 at hrow
        calc
          ((zeta5 : Phi5Ring p) - 1) ^ m = zeta5 ^ m - 1 := hrow
          _ = zeta5 ^ 3 - 1 := by rw [zeta5_pow_mod, hm3]
      have h4 :
          ((zeta5 : Phi5Ring p) ^ 4 - 1) ^ m = zeta5 ^ 2 - 1 := by
        calc
          ((zeta5 : Phi5Ring p) ^ 4 - 1) ^ m =
              zeta5 ^ (4 * m) - 1 := h4raw
          _ = zeta5 ^ 2 - 1 := by
            rw [zeta5_pow_mod]
            congr 2
            omega
      have h4neg :
          ((zeta5 : Phi5Ring p) ^ 4 - 1) ^ m =
              -(zeta5 ^ 2 - 1) := by
        calc
          ((zeta5 : Phi5Ring p) ^ 4 - 1) ^ m =
              (-(zeta5 ^ 4) * (zeta5 - 1)) ^ m := by
                rw [u4_eq_cyclo_factor]
          _ = (-(zeta5 ^ 4)) ^ m * (zeta5 - 1) ^ m := by
                rw [mul_pow]
          _ = (zeta5 ^ 4) ^ m * (zeta5 - 1) ^ m := by
                rw [heven.neg_pow]
          _ = zeta5 ^ (4 * m) * (zeta5 ^ 3 - 1) := by
                rw [← pow_mul, h1]
          _ = zeta5 ^ 2 * (zeta5 ^ 3 - 1) := by
                rw [zeta5_pow_mod]
                congr 2
                omega
          _ = -(zeta5 ^ 2 - 1) := by
                have hz5 := zeta5_pow_five (p := p)
                linear_combination hz5
      have hzero :
          (2 : Phi5Ring p) * (zeta5 ^ 2 - 1) = 0 := by
        linear_combination h4neg - h4
      exact (h2u.mul (u2_isUnit (p := p) hp5)).ne_zero hzero
  · exact hodd

/-- Un esponente locale dispari di ordine `4` modulo `5` produce sempre
un testimone nella normalizzazione `2*n-1`, `n ≡ 4 (mod 5)`.

Nel ramo `3 mod 5` si usa il cubo dell'esponente: `3³ ≡ 2 (mod 5)`;
`localS5_mul` garantisce che il cubo resta una riga locale.-/
theorem hasOrderFourTransport_of_odd_local {p m : ℕ} [Fact p.Prime]
    (hodd : Odd m) (hrow : LocalS5 p m)
    (hm : m % 5 = 2 ∨ m % 5 = 3) :
    HasOrderFourTransport p := by
  have witness_of_odd {t : ℕ} (htodd : Odd t) (ht5 : t % 5 = 2)
      (htrow : LocalS5 p t) : HasOrderFourTransport p := by
    rcases htodd with ⟨d, hd⟩
    refine ⟨d + 1, ?_⟩
    constructor
    · omega
    constructor
    · omega
    · have he : 2 * (d + 1) - 1 = 2 * d + 1 := by omega
      rw [he, ← hd]
      exact htrow
  rcases hm with hm2 | hm3
  · exact witness_of_odd hodd hm2 hrow
  · have hm_unit :
        m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 :=
      Or.inr (Or.inr (Or.inl hm3))
    have hsq : LocalS5 p (m * m) :=
      localS5_mul hm_unit hrow hrow
    have hm_sq : (m * m) % 5 = 4 := by
      rw [Nat.mul_mod, hm3]
    have hm_sq_unit :
        (m * m) % 5 = 1 ∨ (m * m) % 5 = 2 ∨
          (m * m) % 5 = 3 ∨ (m * m) % 5 = 4 :=
      Or.inr (Or.inr (Or.inr hm_sq))
    have hcube0 : LocalS5 p ((m * m) * m) :=
      localS5_mul hm_sq_unit hsq hrow
    have hcube : LocalS5 p (m ^ 3) := by
      simpa [pow_succ] using hcube0
    have hcube5 : m ^ 3 % 5 = 2 := by
      rw [Nat.pow_mod, hm3]
    exact witness_of_odd hodd.pow hcube5 hcube

/-- Any good local row of order four modulo `5` produces the normalized
`HasOrderFourTransport` witness.  The parity input is no longer external:
it follows from `localS5_orderFour_odd`.-/
theorem hasOrderFourTransport_of_local {p m : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hrow : LocalS5 p m) (hm : m % 5 = 2 ∨ m % 5 = 3) :
    HasOrderFourTransport p :=
  hasOrderFourTransport_of_odd_local
    (localS5_orderFour_odd hp2 hp5 hrow hm) hrow hm

/-- Se il prodotto di due primi buoni non ha quadrato `1 mod 5`, allora
uno e uno solo dei due fattori è split e l'altro è inerte.-/
theorem two_prime_residue_partition {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp5 : p ≠ 5) (hq5 : q ≠ 5)
    (hbad : (p * q) ^ 2 % 5 ≠ 1) :
    (SplitModFive p ∧ InertModFive q) ∨
      (InertModFive p ∧ SplitModFive q) := by
  have hp0 : p % 5 ≠ 0 := by
    intro h0
    have hdiv : 5 ∣ p := Nat.dvd_of_mod_eq_zero h0
    exact hp5
      ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hdiv).symm
  have hq0 : q % 5 ≠ 0 := by
    intro h0
    have hdiv : 5 ∣ q := Nat.dvd_of_mod_eq_zero h0
    exact hq5
      ((Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp hdiv).symm
  have hpLt : p % 5 < 5 := Nat.mod_lt p (by norm_num)
  have hqLt : q % 5 < 5 := Nat.mod_lt q (by norm_num)
  interval_cases hpv : p % 5 <;>
    interval_cases hqv : q % 5 <;>
    simp [SplitModFive, InertModFive, hpv, hqv, Nat.mul_mod,
      Nat.pow_mod] at hp0 hq0 hbad ⊢

/-- **TRAPPOLA BIFATTORIALE, forma kernel-pura.**

Se `p*q` soddisfa la congruenza globale e viola la conclusione quadratica
modulo `5`, il fattore split porta la riga locale effettiva con esponente
pari all'altro primo, che è inerte.-/
theorem two_prime_candidate_split_local_row {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : p ≠ 5) (hq5 : q ≠ 5)
    (hbad : (p * q) ^ 2 % 5 ≠ 1)
    (hglobal : AgrawalCongruenceFive (p * q)) :
    (SplitModFive p ∧ InertModFive q ∧
      IsSquare (5 : ZMod p) ∧ @LocalS5 p q ⟨hp⟩) ∨
    (InertModFive p ∧ SplitModFive q ∧
      IsSquare (5 : ZMod q) ∧ @LocalS5 q p ⟨hq⟩) := by
  rcases two_prime_residue_partition hp hq hp5 hq5 hbad with
    ⟨hps, hqi⟩ | ⟨hpi, hqs⟩
  · left
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      intro h
      subst p
      simp [SplitModFive] at hps
    have hrow0 := localS5_of_global_factor (p := p) hp5
      (dvd_mul_right p q) hglobal
    have hpdiv : (p * q) / p = q := Nat.mul_div_cancel_left q hp.pos
    exact ⟨hps, hqi, isSquare_five_of_split hp2 hps, by
      simpa [hpdiv] using hrow0⟩
  · right
    haveI : Fact q.Prime := ⟨hq⟩
    have hq2 : q ≠ 2 := by
      intro h
      subst q
      simp [SplitModFive] at hqs
    have hrow0 := localS5_of_global_factor (p := q) hq5
      (dvd_mul_left q p) hglobal
    have hqdiv : (p * q) / q = p := by
      rw [Nat.mul_comm]
      exact Nat.mul_div_cancel_left p hq.pos
    exact ⟨hpi, hqs, isSquare_five_of_split hq2 hqs, by
      simpa [hqdiv] using hrow0⟩

/-- **CORONA BIFATTORIALE, senza H4.**

Ogni candidato globale della forma `p*q` che viola `n² ≡ 1 (mod 5)`
esibisce necessariamente un testimone split d'ordine quattro. Pertanto H4,
se assunta soltanto sui due fattori del candidato, esclude già tutto il
ramo bifattoriale.-/
theorem two_prime_candidate_has_splitOrderFourWitness {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : p ≠ 5) (hq5 : q ≠ 5)
    (hbad : (p * q) ^ 2 % 5 ≠ 1)
    (hglobal : AgrawalCongruenceFive (p * q)) :
    SplitOrderFourWitness (p * q) := by
  rcases two_prime_candidate_split_local_row hp hq hp5 hq5 hbad hglobal with
    ⟨hps, hqi, hsquare, hrow⟩ | ⟨hpi, hqs, hsquare, hrow⟩
  · have hq2 : q ≠ 2 := by
      intro h
      subst q
      haveI : Fact p.Prime := ⟨hp⟩
      exact not_localS5_two
        (p := p)
        (by
          intro hp_eq
          subst p
          simp [SplitModFive] at hps)
        hp5 hrow
    haveI : Fact p.Prime := ⟨hp⟩
    have htransport : HasOrderFourTransport p :=
      hasOrderFourTransport_of_odd_local
        (hq.odd_of_ne_two hq2) hrow hqi
    exact ⟨p, hp, dvd_mul_right p q, hsquare, htransport⟩
  · have hp2 : p ≠ 2 := by
      intro h
      subst p
      haveI : Fact q.Prime := ⟨hq⟩
      exact not_localS5_two
        (p := q)
        (by
          intro hq_eq
          subst q
          simp [SplitModFive] at hqs)
        hq5 hrow
    haveI : Fact q.Prime := ⟨hq⟩
    have htransport : HasOrderFourTransport q :=
      hasOrderFourTransport_of_odd_local
        (hp.odd_of_ne_two hp2) hrow hpi
    exact ⟨q, hq, dvd_mul_left q p, hsquare, htransport⟩

/-- **CASO BIFATTORIALE SOTTO H4 LOCALE.**

Se H4 vale soltanto sui fattori di `p*q`, allora la congruenza globale e
la violazione di `n² ≡ 1 (mod 5)` non possono coesistere. Nessuna forma
universale di H4 è nascosta nell'enunciato.-/
theorem no_two_prime_candidate_of_localH4 {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : p ≠ 5) (hq5 : q ≠ 5)
    (hlocal : LocalH4For (p * q)) :
    ¬ (AgrawalCongruenceFive (p * q) ∧ (p * q) ^ 2 % 5 ≠ 1) := by
  rintro ⟨hglobal, hbad⟩
  have hwitness :=
    two_prime_candidate_has_splitOrderFourWitness
      hp hq hp5 hq5 hbad hglobal
  exact ((not_localH4For_iff_splitOrderFourWitness (p * q)).mpr hwitness)
    hlocal

end AgrawalCore
