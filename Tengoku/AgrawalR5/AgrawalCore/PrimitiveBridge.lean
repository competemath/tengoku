/-
Ponte kernel-puro fra l'ideale primitivo e il gcd a quattro coefficienti.

Il teorema non afferma che tutti i divisori siano inerti. Formalizza invece
esattamente la riduzione:

* `Φₘ(γ)` si annulla nelle due componenti split;
* `γᵏ` scambia le due radici;
* se e solo se il primo divide i quattro coefficienti canonici.

Questo elimina sia l'ambiguità della sola norma sia l'ipotesi opaca
`hcoeff` per l'oggetto primitivo definito qui.
-/
import Tengoku.AgrawalR5.AgrawalCore.PrimitiveCoefficients
import Tengoku.AgrawalR5.AgrawalCore.PrimitiveEvaluation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

/-- L'intero canonico a quattro coefficienti associato a `(m,k)`.-/
noncomputable def primitiveFourCoefficientD (m k : ℕ) : ℕ :=
  let cd := cyclotomicGammaCoeffs m
  fourCoefficientGcd cd.1.natAbs cd.2.natAbs
    (gammaU k + 1).natAbs (gammaU (k - 1) + 1).natAbs

/-- Formulazione intrinseca dell'annullamento dell'ideale primitivo nelle
due componenti split.-/
def PrimitiveFourVanish (p m k : ℕ) [Fact p.Prime] (x : ZMod p) : Prop :=
  Polynomial.eval₂ (Int.castRingHom (ZMod p)) x
      (Polynomial.cyclotomic m ℤ) = 0 ∧
    Polynomial.eval₂ (Int.castRingHom (ZMod p)) (5 - x)
      (Polynomial.cyclotomic m ℤ) = 0 ∧
    x ^ k = 5 - x ∧
    (5 - x) ^ k = x

variable {p : ℕ} [Fact p.Prime]

private theorem prime_not_dvd_five (hp5 : p ≠ 5) : ¬ p ∣ 5 := by
  intro h
  exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp h)

private theorem dvd_five_mul_iff (hp5 : p ≠ 5) (n : ℕ) :
    p ∣ 5 * n ↔ p ∣ n := by
  constructor
  · intro h
    rcases (Fact.out : p.Prime).dvd_mul.mp h with h5 | hn
    · exact absurd h5 (prime_not_dvd_five hp5)
    · exact hn
  · exact fun h => dvd_mul_of_dvd_right h 5

/-- **Ponte dei quattro coefficienti, senza ipotesi esterna.**-/
theorem primitiveFourVanish_iff_dvd_D (hp5 : p ≠ 5)
    (m k : ℕ) (hk : 1 ≤ k) (x : ZMod p)
    (hxpoly : x ^ 2 = 5 * x - 5) :
    PrimitiveFourVanish p m k x ↔ p ∣ primitiveFourCoefficientD m k := by
  let c : ℤ := (cyclotomicGammaCoeffs m).1
  let d : ℤ := (cyclotomicGammaCoeffs m).2
  let A : ℤ := gammaU k + 1
  let W : ℤ := gammaU (k - 1) + 1
  have hconjpoly : (5 - x) ^ 2 = 5 * (5 - x) - 5 := by
    rw [show (5 - x) ^ 2 = x ^ 2 - 10 * x + 25 by ring, hxpoly]
    ring
  have hcycX :
      Polynomial.eval₂ (Int.castRingHom (ZMod p)) x
          (Polynomial.cyclotomic m ℤ) =
        (c : ZMod p) + (d : ZMod p) * x := by
    simpa [c, d] using
      eval₂_cyclotomic_gamma_coeffs (Int.castRingHom (ZMod p)) x hxpoly m
  have hcycConj :
      Polynomial.eval₂ (Int.castRingHom (ZMod p)) (5 - x)
          (Polynomial.cyclotomic m ℤ) =
        (c : ZMod p) + (d : ZMod p) * (5 - x) := by
    simpa [c, d] using
      eval₂_cyclotomic_gamma_coeffs (Int.castRingHom (ZMod p))
        (5 - x) hconjpoly m
  have hpowX :
      x ^ k - (5 - x) = ((-5 * W : ℤ) : ZMod p) + (A : ZMod p) * x := by
    simpa [A, W] using gamma_pow_sub_conj x hxpoly hk
  have hpowConj :
      (5 - x) ^ k - x =
        ((-5 * W : ℤ) : ZMod p) + (A : ZMod p) * (5 - x) := by
    simpa [A, W] using gamma_pow_sub_conj (5 - x) hconjpoly hk
  have hcyclo :
      (Polynomial.eval₂ (Int.castRingHom (ZMod p)) x
          (Polynomial.cyclotomic m ℤ) = 0 ∧
        Polynomial.eval₂ (Int.castRingHom (ZMod p)) (5 - x)
          (Polynomial.cyclotomic m ℤ) = 0) ↔
        p ∣ c.natAbs ∧ p ∣ d.natAbs := by
    rw [hcycX, hcycConj]
    exact both_gamma_evals_zero_iff_dvd_coeffs hp5 x hxpoly c d
  have htransport :
      (x ^ k = 5 - x ∧ (5 - x) ^ k = x) ↔
        p ∣ (-5 * W).natAbs ∧ p ∣ A.natAbs := by
    have hpair :=
      both_gamma_evals_zero_iff_dvd_coeffs hp5 x hxpoly (-5 * W) A
    constructor
    · rintro ⟨hx, hxc⟩
      apply hpair.mp
      constructor
      · rw [← hpowX]
        exact sub_eq_zero.mpr hx
      · rw [← hpowConj]
        exact sub_eq_zero.mpr hxc
    · intro h
      obtain ⟨hx, hxc⟩ := hpair.mpr h
      constructor
      · apply sub_eq_zero.mp
        rw [hpowX]
        exact hx
      · apply sub_eq_zero.mp
        rw [hpowConj]
        exact hxc
  have hW : p ∣ (-5 * W).natAbs ↔ p ∣ W.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_neg]
    norm_num
    exact dvd_five_mul_iff hp5 W.natAbs
  constructor
  · rintro ⟨hcx, hcc, htx, htc⟩
    obtain ⟨hc, hd⟩ := hcyclo.mp ⟨hcx, hcc⟩
    obtain ⟨h5W, hA⟩ := htransport.mp ⟨htx, htc⟩
    have hW' := hW.mp h5W
    rw [primitiveFourCoefficientD, dvd_fourCoefficientGcd_iff]
    simpa [c, d, A, W] using And.intro hc (And.intro hd (And.intro hA hW'))
  · intro hD
    rw [primitiveFourCoefficientD, dvd_fourCoefficientGcd_iff] at hD
    have hD' :
        p ∣ c.natAbs ∧ p ∣ d.natAbs ∧ p ∣ A.natAbs ∧ p ∣ W.natAbs := by
      simpa [c, d, A, W] using hD
    obtain ⟨hc, hd, hA, hW'⟩ := hD'
    obtain ⟨hcx, hcc⟩ := hcyclo.mpr ⟨hc, hd⟩
    obtain ⟨htx, htc⟩ := htransport.mpr ⟨hW.mpr hW', hA⟩
    exact ⟨hcx, hcc, htx, htc⟩

end AgrawalCore
