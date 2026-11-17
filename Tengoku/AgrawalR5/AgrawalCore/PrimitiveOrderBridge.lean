/-
Dal supporto primitivo al profilo esatto degli ordini.

Questo modulo chiude il ponte tra l'annullamento a quattro coefficienti
e la firma `(2r,2s)`: la radice di `Φ_(4rs)` ha ordine esattamente
`4rs`, mentre i due esponenti `k+1` e `k-1` hanno gli ordini prescritti
dalle due uguaglianze di gcd.
-/
import Tengoku.AgrawalR5.AgrawalCore.CanonicalSignature
import Tengoku.AgrawalR5.AgrawalCore.PrimitiveBridge
import Tengoku.Seed.RingTheory.Polynomial.Cyclotomic.Roots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

variable {p m k r s : ℕ} [Fact p.Prime]

/-- La prima componente di `PrimitiveFourVanish` è precisamente
l'affermazione che `x` è una radice di `Φₘ` sul campo residuo.
@isnad1 id=isroot.1h4v.s5.766f293f4e6e from=translated src=- shape=9a8fd7a4 vocab=7638ce69
-/
theorem primitiveFourVanish_isRoot (x : ZMod p)
    (h : PrimitiveFourVanish p m k x) :
    IsRoot (cyclotomic m (ZMod p)) x := by
  rw [IsRoot.def, ← map_cyclotomic_int m (ZMod p), eval_map]
  exact h.1

/-- Fuori dalla caratteristica che divide il livello, l'annullamento
ciclotomico forza ordine esattamente `m`.
@isnad1 id=eq.2h4v.s5.08d202e9f41f from=translated src=- shape=2a8d9dc0 vocab=c563b27e
-/
theorem primitiveFourVanish_order_eq (hpm : ¬p ∣ m) (x : ZMod p)
    (h : PrimitiveFourVanish p m k x) :
    orderOf x = m := by
  letI : NeZero (m : ZMod p) := NeZero.of_not_dvd (ZMod p) hpm
  have hroot := primitiveFourVanish_isRoot x h
  exact (isRoot_cyclotomic_iff.mp hroot).eq_orderOf.symm

private theorem canonicalSignature_one_impossible
    (hr : 0 < r) (hs : 0 < s)
    (h : CanonicalSignature (4 * r * s) r s 1) : False := by
  have hfirst : 4 * r * s = 2 * r := by simpa [CanonicalSignature] using h.1
  have hrspos : 0 < r * s := Nat.mul_pos hr hs
  nlinarith

/-- **Profilo d'ordine esatto del risultante primitivo.**
Se il livello è buono, la firma canonica converte i due trasporti nelle
due componenti di ordine `2r` e `2s`.
@isnad1 id=and.6h5v.s8.96b144b9b627 from=translated src=- shape=391332fa vocab=43e27cb8
-/
theorem primitiveFourVanish_exact_order_profile
    (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (x : ZMod p) (h : PrimitiveFourVanish p (4 * r * s) k x) :
    orderOf x = 4 * r * s ∧
      orderOf (x ^ (k + 1)) = 2 * r ∧
      orderOf (x ^ (k - 1)) = 2 * s := by
  have hxord :
      orderOf x = 4 * r * s :=
    primitiveFourVanish_order_eq hpm x h
  have hk1 : k - 1 ≠ 0 := by
    intro hk0
    have hkEq : k = 1 := by omega
    subst k
    exact canonicalSignature_one_impossible hr hs hsig
  constructor
  · exact hxord
  constructor
  · rw [orderOf_pow' x (by omega : k + 1 ≠ 0), hxord, hsig.2]
    have hdiv : 4 * r * s / (2 * s) = 2 * r := by
      rw [show 4 * r * s = (2 * r) * (2 * s) by ring,
        Nat.mul_div_cancel _ (by positivity : 0 < 2 * s)]
    exact hdiv
  · rw [orderOf_pow' x hk1, hxord, hsig.1]
    have hdiv : 4 * r * s / (2 * r) = 2 * s := by
      rw [show 4 * r * s = (2 * s) * (2 * r) by ring,
        Nat.mul_div_cancel _ (by positivity : 0 < 2 * r)]
    exact hdiv

/-- Forma aritmetica: la divisibilità del gcd canonico produce il
profilo esatto, senza una norma o un certificato esterno.
@isnad1 id=and.8h5v.s8.e422ff893ee5 from=translated src=- shape=0adcbbee vocab=5d0544b1
-/
theorem dvd_primitiveFourCoefficientD_exact_order_profile
    (hp5 : p ≠ 5) (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (x : ZMod p) (hxpoly : x ^ 2 = 5 * x - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k) :
    orderOf x = 4 * r * s ∧
      orderOf (x ^ (k + 1)) = 2 * r ∧
      orderOf (x ^ (k - 1)) = 2 * s := by
  have hv :
      PrimitiveFourVanish p (4 * r * s) k x :=
    (primitiveFourVanish_iff_dvd_D hp5 (4 * r * s) k hkpos x hxpoly).mpr hD
  exact primitiveFourVanish_exact_order_profile hr hs hkpos hpm hsig x hv

end AgrawalCore
