/-
Estrazione dei coefficienti nel ramo split della riduzione H4.

La norma di `c+dγ` può annullarsi modulo un primo split in una sola
componente. Per questo il ponte corretto deve controllare entrambe le
immersioni `γ` e `5-γ`. Questo modulo formalizza esattamente tale passaggio.
-/
import Tengoku.AgrawalR5.AgrawalCore.PrimitiveSupport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

/-- Fuori dal primo ramificato `5`, una radice di `X²-5X+5` è distinta
dalla sua coniugata.
@isnad1 id=ne.2h2v.s8.bd49644cdf9c from=translated src=- shape=5981b958 vocab=77397734
-/
theorem gamma_split_difference_ne_zero (hp5 : p ≠ 5) (x : ZMod p)
    (hx : x ^ 2 = 5 * x - 5) :
    2 * x - 5 ≠ 0 := by
  intro hd
  have h5zero : (5 : ZMod p) = 0 := by
    linear_combination (2 * x - 5) * hd - 4 * hx
  have hpdiv : p ∣ 5 :=
    (CharP.cast_eq_zero_iff (ZMod p) p 5).mp h5zero
  exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hpdiv)

/-- Se una forma lineare si annulla in entrambe le componenti split,
entrambi i coefficienti sono nulli.
@isnad1 id=and.3h4v.s8.66e7b94fd2aa from=translated src=- shape=ad160e77 vocab=068a6270
-/
theorem coeffs_zero_of_both_gamma_evals {K : Type*} [Field K]
    (x c d : K) (hsep : 2 * x - 5 ≠ 0)
    (hx : c + d * x = 0) (hxc : c + d * (5 - x) = 0) :
    c = 0 ∧ d = 0 := by
  have hdprod : d * (2 * x - 5) = 0 := by
    linear_combination hx - hxc
  have hd : d = 0 := (mul_eq_zero.mp hdprod).resolve_right hsep
  constructor
  · simpa [hd] using hx
  · exact hd

/-- Versione aritmetica: l'annullamento nelle due componenti equivale
alla divisibilità dei valori assoluti dei coefficienti per `p`.
@isnad1 id=iff.2h4v.s8.8e2b19cf5e2c from=translated src=- shape=f0ff908d vocab=bbc3c232
-/
theorem both_gamma_evals_zero_iff_dvd_coeffs (hp5 : p ≠ 5)
    (x : ZMod p) (hxpoly : x ^ 2 = 5 * x - 5) (c d : ℤ) :
    (((c : ZMod p) + (d : ZMod p) * x = 0) ∧
        ((c : ZMod p) + (d : ZMod p) * (5 - x) = 0)) ↔
      p ∣ c.natAbs ∧ p ∣ d.natAbs := by
  constructor
  · rintro ⟨hx, hxc⟩
    obtain ⟨hc0, hd0⟩ :=
      coeffs_zero_of_both_gamma_evals x (c : ZMod p) (d : ZMod p)
        (gamma_split_difference_ne_zero hp5 x hxpoly) hx hxc
    constructor
    · have hci : (p : ℤ) ∣ c :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp hc0
      simpa using (Int.natAbs_dvd_natAbs.mpr hci)
    · have hdi : (p : ℤ) ∣ d :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hd0
      simpa using (Int.natAbs_dvd_natAbs.mpr hdi)
  · rintro ⟨hpc, hpd⟩
    have hci : (p : ℤ) ∣ c := by
      apply Int.natAbs_dvd_natAbs.mp
      simpa using hpc
    have hdi : (p : ℤ) ∣ d := by
      apply Int.natAbs_dvd_natAbs.mp
      simpa using hpd
    have hc0 : (c : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mpr hci
    have hd0 : (d : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mpr hdi
    simp [hc0, hd0]

/-- Ponte split completo per le due forme lineari che producono i quattro
coefficienti della riduzione primitiva.
@isnad1 id=iff.2h6v.s9.e7628fea688b from=translated src=- shape=824b8f47 vocab=601d2ce6
-/
theorem split_pair_zero_iff_four_coefficient_gcd (hp5 : p ≠ 5)
    (x : ZMod p) (hxpoly : x ^ 2 = 5 * x - 5)
    (c d a w : ℤ) :
    ((((c : ZMod p) + (d : ZMod p) * x = 0) ∧
        ((c : ZMod p) + (d : ZMod p) * (5 - x) = 0)) ∧
      (((a : ZMod p) + (w : ZMod p) * x = 0) ∧
        ((a : ZMod p) + (w : ZMod p) * (5 - x) = 0))) ↔
      p ∣ fourCoefficientGcd c.natAbs d.natAbs a.natAbs w.natAbs := by
  rw [dvd_fourCoefficientGcd_iff]
  constructor
  · rintro ⟨hcd, haw⟩
    obtain ⟨hc, hd⟩ :=
      (both_gamma_evals_zero_iff_dvd_coeffs hp5 x hxpoly c d).mp hcd
    obtain ⟨ha, hw⟩ :=
      (both_gamma_evals_zero_iff_dvd_coeffs hp5 x hxpoly a w).mp haw
    exact ⟨hc, hd, ha, hw⟩
  · rintro ⟨hc, hd, ha, hw⟩
    exact ⟨(both_gamma_evals_zero_iff_dvd_coeffs hp5 x hxpoly c d).mpr ⟨hc, hd⟩,
      (both_gamma_evals_zero_iff_dvd_coeffs hp5 x hxpoly a w).mpr ⟨ha, hw⟩⟩

end AgrawalCore
