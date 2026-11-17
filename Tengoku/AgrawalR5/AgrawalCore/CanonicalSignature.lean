/-
Firma dell'involuzione canonica dei livelli H4.

Questo modulo formalizza le conseguenze universali delle due uguaglianze
di gcd. L'esistenza costruttiva della classe viene tenuta separata: nessuna
scelta computazionale entra nei teoremi di supporto.
-/
import Tengoku.Seed.Data.Nat.GCD.Basic
import Tengoku.Seed.Data.Nat.ModEq
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

def CanonicalSignature (m r s k : ℕ) : Prop :=
  Nat.gcd m (k - 1) = 2 * r ∧ Nat.gcd m (k + 1) = 2 * s

theorem canonicalSignature_dvd_sub_add {m r s k : ℕ}
    (h : CanonicalSignature m r s k) :
    2 * r ∣ k - 1 ∧ 2 * s ∣ k + 1 := by
  constructor
  · rw [← h.1]
    exact Nat.gcd_dvd_right m (k - 1)
  · rw [← h.2]
    exact Nat.gcd_dvd_right m (k + 1)

/-- La firma forza `k² ≡ 1` modulo `4rs`.-/
theorem canonicalSignature_involution {r s k : ℕ} (hk : 1 ≤ k)
    (h : CanonicalSignature (4 * r * s) r s k) :
    k ^ 2 ≡ 1 [MOD 4 * r * s] := by
  obtain ⟨hr, hs⟩ := canonicalSignature_dvd_sub_add h
  have hprod : (2 * r) * (2 * s) ∣ (k - 1) * (k + 1) :=
    Nat.mul_dvd_mul hr hs
  have hm : 4 * r * s ∣ (k - 1) * (k + 1) := by
    simpa only [mul_assoc, show 2 * r * (2 * s) = 4 * r * s by ring] using hprod
  have hid : (k - 1) * (k + 1) = k ^ 2 - 1 := by
    apply Nat.eq_sub_of_add_eq
    nlinarith [Nat.sub_add_cancel hk]
  have hd : 4 * r * s ∣ k ^ 2 - 1 := by rwa [hid] at hm
  exact ((Nat.modEq_iff_dvd' (by nlinarith : 1 ≤ k ^ 2)).mpr hd).symm

/-- Un rappresentante con la firma canonica è automaticamente invertibile
modulo `4rs`.-/
theorem canonicalSignature_coprime {r s k : ℕ} (hk : 1 ≤ k)
    (h : CanonicalSignature (4 * r * s) r s k) :
    Nat.Coprime k (4 * r * s) := by
  have hinv := canonicalSignature_involution hk h
  have hd : 4 * r * s ∣ k ^ 2 - 1 :=
    (Nat.modEq_iff_dvd' (by nlinarith : 1 ≤ k ^ 2)).mp hinv.symm
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.dvd_one.mp
  have hgk : Nat.gcd k (4 * r * s) ∣ k ^ 2 :=
    dvd_trans (Nat.gcd_dvd_left k (4 * r * s)) (dvd_pow_self k (by norm_num))
  have hgm : Nat.gcd k (4 * r * s) ∣ k ^ 2 - 1 :=
    dvd_trans (Nat.gcd_dvd_right k (4 * r * s)) hd
  have hone : Nat.gcd k (4 * r * s) ∣ k ^ 2 - (k ^ 2 - 1) :=
    Nat.dvd_sub hgk hgm
  simpa [Nat.sub_sub_self (by nlinarith : 1 ≤ k ^ 2)] using hone

/-- Due rappresentanti con la stessa firma sono congruenti almeno modulo
`2rs`; è la parte CRT della unicità canonica.-/
theorem canonicalSignature_modEq_two_mul {r s k j : ℕ}
    (_hr : 0 < r) (hs : 0 < s) (hrs : Nat.Coprime r s)
    (hk : CanonicalSignature (4 * r * s) r s k)
    (hj : CanonicalSignature (4 * r * s) r s j) :
    k ≡ j [MOD 2 * r * s] := by
  obtain ⟨hkr, hks⟩ := canonicalSignature_dvd_sub_add hk
  obtain ⟨hjr, hjs⟩ := canonicalSignature_dvd_sub_add hj
  have hkpos : 1 ≤ k := by
    have hle : 2 * s ≤ k + 1 := Nat.le_of_dvd (by positivity) hks
    omega
  have hjpos : 1 ≤ j := by
    have hle : 2 * s ≤ j + 1 := Nat.le_of_dvd (by positivity) hjs
    omega
  have hrmod : k ≡ j [MOD 2 * r] := by
    have h1k : 1 ≡ k [MOD 2 * r] :=
      (Nat.modEq_iff_dvd' hkpos).mpr hkr
    have h1j : 1 ≡ j [MOD 2 * r] :=
      (Nat.modEq_iff_dvd' hjpos).mpr hjr
    exact h1k.symm.trans h1j
  have hsmod : k ≡ j [MOD 2 * s] := by
    have hk0 : k + 1 ≡ 0 [MOD 2 * s] :=
      Nat.modEq_zero_iff_dvd.mpr hks
    have hj0 : j + 1 ≡ 0 [MOD 2 * s] :=
      Nat.modEq_zero_iff_dvd.mpr hjs
    exact Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) (hk0.trans hj0.symm)
  have hg : Nat.gcd (2 * r) (2 * s) = 2 := by
    rw [show 2 * r = r * 2 by ring, show 2 * s = s * 2 by ring,
      Nat.gcd_mul_right, hrs.gcd_eq_one]
  have hlcmEq : Nat.lcm (2 * r) (2 * s) = 2 * r * s := by
    rw [Nat.lcm_eq_mul_div, hg]
    rw [show 2 * r * (2 * s) = (2 * r * s) * 2 by ring,
      Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
  rcases le_total k j with hkj | hjk
  · have hdr : 2 * r ∣ j - k := (Nat.modEq_iff_dvd' hkj).mp hrmod
    have hds : 2 * s ∣ j - k := (Nat.modEq_iff_dvd' hkj).mp hsmod
    have hdl : Nat.lcm (2 * r) (2 * s) ∣ j - k := Nat.lcm_dvd hdr hds
    exact (Nat.modEq_iff_dvd' hkj).mpr (by rwa [hlcmEq] at hdl)
  · have hdr : 2 * r ∣ k - j :=
      (Nat.modEq_iff_dvd' hjk).mp hrmod.symm
    have hds : 2 * s ∣ k - j :=
      (Nat.modEq_iff_dvd' hjk).mp hsmod.symm
    have hdl : Nat.lcm (2 * r) (2 * s) ∣ k - j := Nat.lcm_dvd hdr hds
    exact ((Nat.modEq_iff_dvd' hjk).mpr (by rwa [hlcmEq] at hdl)).symm

private theorem canonicalSignature_plus_quotient_coprime {r s k : ℕ}
    (_hr : 0 < r) (hs : 0 < s)
    (h : CanonicalSignature (4 * r * s) r s k) :
    Nat.Coprime ((k + 1) / (2 * s)) (2 * r) := by
  have hgpos : 0 < Nat.gcd (4 * r * s) (k + 1) := by
    rw [h.2]
    positivity
  have hc := Nat.coprime_div_gcd_div_gcd hgpos
  have hdiv : (4 * r * s) / (2 * s) = 2 * r := by
    rw [show 4 * r * s = (2 * r) * (2 * s) by ring,
      Nat.mul_div_cancel _ (by positivity : 0 < 2 * s)]
  simpa [h.2, hdiv] using hc.symm

private theorem canonicalSignature_minus_quotient_coprime {r s k : ℕ}
    (hr : 0 < r) (_hs : 0 < s)
    (h : CanonicalSignature (4 * r * s) r s k) :
    Nat.Coprime ((k - 1) / (2 * r)) (2 * s) := by
  have hgpos : 0 < Nat.gcd (4 * r * s) (k - 1) := by
    rw [h.1]
    positivity
  have hc := Nat.coprime_div_gcd_div_gcd hgpos
  have hdiv : (4 * r * s) / (2 * r) = 2 * s := by
    rw [show 4 * r * s = (2 * s) * (2 * r) by ring,
      Nat.mul_div_cancel _ (by positivity : 0 < 2 * r)]
  simpa [h.1, hdiv] using hc.symm

/-- **Unicità canonica nel range fondamentale.** L'opposizione di parità
seleziona uno solo dei due lift CRT modulo `4rs`.-/
theorem canonicalSignature_unique {r s k j : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hrs : Nat.Coprime r s)
    (hpar : Odd (r + s))
    (hklt : k < 4 * r * s) (hjlt : j < 4 * r * s)
    (hk : CanonicalSignature (4 * r * s) r s k)
    (hj : CanonicalSignature (4 * r * s) r s j) :
    k = j := by
  wlog hkj : k ≤ j generalizing k j
  · exact (this hjlt hklt hj hk (le_of_not_ge hkj)).symm
  have hmod := canonicalSignature_modEq_two_mul hr hs hrs hk hj
  let L := 2 * r * s
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hmEq : 4 * r * s = 2 * L := by dsimp [L]; ring
  have lift_difference :
      ∀ {a b : ℕ}, a < 4 * r * s → b < 4 * r * s →
        a ≡ b [MOD L] → a ≤ b → a = b ∨ b = a + L := by
    intro a b halt hblt hab habLe
    have hdvd : L ∣ b - a := (Nat.modEq_iff_dvd' habLe).mp hab
    obtain ⟨t, ht⟩ := hdvd
    have hdiff : b - a < 2 * L := by
      rw [← hmEq]
      omega
    have htlt : t < 2 := by
      nlinarith
    interval_cases t
    · left; omega
    · right; omega
  rcases lift_difference hklt hjlt hmod hkj with hEq | hLift
  · exact hEq
  · have hplusK :=
      canonicalSignature_plus_quotient_coprime hr hs hk
    have hplusJ :=
      canonicalSignature_plus_quotient_coprime hr hs hj
    have hminusK :=
      canonicalSignature_minus_quotient_coprime hr hs hk
    have hminusJ :=
      canonicalSignature_minus_quotient_coprime hr hs hj
    rcases Nat.even_or_odd r with hrEven | hrOdd
    · have hsOdd : Odd s := by
        rcases hrEven with ⟨u, hu⟩
        rcases hpar with ⟨v, hv⟩
        exact ⟨v - u, by omega⟩
      have hkdiv : 2 * r ∣ k - 1 := (canonicalSignature_dvd_sub_add hk).1
      have hquot :
          (j - 1) / (2 * r) = (k - 1) / (2 * r) + s := by
        rw [hLift]
        have hkpos : 1 ≤ k := by
          have hks : 2 * s ∣ k + 1 := (canonicalSignature_dvd_sub_add hk).2
          have hle : 2 * s ≤ k + 1 := Nat.le_of_dvd (by positivity) hks
          omega
        rw [show k + L - 1 = (k - 1) + (2 * r) * s by
          dsimp [L]; omega]
        exact Nat.add_mul_div_left (k - 1) s (by positivity)
      have hoK : Odd ((k - 1) / (2 * r)) :=
        Nat.coprime_two_right.mp
          (hminusK.coprime_dvd_right (by exact dvd_mul_right 2 s))
      have hoJ : Odd ((j - 1) / (2 * r)) :=
        Nat.coprime_two_right.mp
          (hminusJ.coprime_dvd_right (by exact dvd_mul_right 2 s))
      obtain ⟨a, ha⟩ := hoK
      obtain ⟨b, hb⟩ := hoJ
      obtain ⟨c, hc⟩ := hsOdd
      omega
    · have hquot :
          (j + 1) / (2 * s) = (k + 1) / (2 * s) + r := by
        rw [hLift]
        rw [show k + L + 1 = (k + 1) + (2 * s) * r by
          dsimp [L]; ring]
        exact Nat.add_mul_div_left (k + 1) r (by positivity)
      have hoK : Odd ((k + 1) / (2 * s)) :=
        Nat.coprime_two_right.mp
          (hplusK.coprime_dvd_right (by exact dvd_mul_right 2 r))
      have hoJ : Odd ((j + 1) / (2 * s)) :=
        Nat.coprime_two_right.mp
          (hplusJ.coprime_dvd_right (by exact dvd_mul_right 2 r))
      obtain ⟨a, ha⟩ := hoK
      obtain ⟨b, hb⟩ := hoJ
      obtain ⟨c, hc⟩ := hrOdd
      omega

end AgrawalCore
