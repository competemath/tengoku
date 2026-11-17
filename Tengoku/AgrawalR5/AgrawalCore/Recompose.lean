/-
Nucleo Lean della campagna Agrawal (S45) — lotto 10: RICOMPOSIZIONE.
Il percorso INVERSO rispetto a `AgrawalBridge.lean`: lì si parte dalla
congruenza globale e se ne deducono conseguenze; qui la congruenza
globale si COSTRUISCE a partire dalle sue due componenti locali. Serve
alla formalizzazione della proposizione di Lenstra: la congruenza di
Agrawal `(X−1)^n ≡ X^n − 1` modulo il fattore lineare `X − 1` è
automatica (banale, componente A); tutto il contenuto sta nel
dimostrarla modulo `Φ₅`. Il lemma di ricomposizione (componente B)
incolla le due congruenze locali in un'unica congruenza modulo
`X^5 − 1 = (X−1)·Φ₅`, perché i due fattori sono coprimi quando `p ≠ 5`
(`Φ₅(1) = 5 ≠ 0`). Campagna UNICO, 26 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.AgrawalBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

/-- **(A) Componente banale.** La valutazione in `X = 1` manda
`(X−1)^n` in `0`, per ogni `n ≥ 1`: la congruenza di Agrawal è
automatica sul fattore lineare `X − 1`, qualunque sia l'anello.-/
lemma eval_one_sub_pow {R : Type*} [CommRing R] {n : ℕ} (hn : 0 < n) :
    Polynomial.eval 1 ((Polynomial.X - 1) ^ n : Polynomial R) = 0 := by
  rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, sub_self,
    zero_pow hn.ne']

/-- **(A) Componente banale, bis.** La valutazione in `X = 1` manda
`X^n − 1` in `0`, per ogni `n` (anche `n = 0`).-/
lemma eval_one_pow_sub {R : Type*} [CommRing R] (n : ℕ) :
    Polynomial.eval 1 ((Polynomial.X ^ n - 1) : Polynomial R) = 0 := by
  simp

/-- **(C) La fattorizzazione ciclotomica esplicita.** `X^5 − 1 =
(X − 1) · Φ₅` in `(Z/p)[X]`: srotolando la definizione di `phi5`
è un'identità polinomiale, chiusa da `ring`.-/
lemma X_pow_five_sub_one_eq (p : ℕ) :
    (Polynomial.X - 1) * phi5 p = Polynomial.X ^ 5 - 1 := by
  unfold phi5
  ring

/-- **(B) Il ricomponimento — il pezzo che conta.** Sia `p` primo,
`p ≠ 5`. Se un polinomio `f` è divisibile sia dal fattore lineare
`X − 1` sia dal quinto ciclotomico `Φ₅`, allora è divisibile dal loro
prodotto `X^5 − 1`. La chiave è la coprimalità dei due fattori:
`X − 1` è irriducibile (grado 1) e non divide `Φ₅`, perché
`Φ₅(1) = 5 ≠ 0` quando `p ≠ 5`; da qui `IsCoprime.mul_dvd` dà la tesi.-/
theorem dvd_of_dvd_both {p : ℕ} [Fact p.Prime] (hp5 : p ≠ 5)
    (f : Polynomial (ZMod p))
    (h1 : (Polynomial.X - 1) ∣ f) (h2 : phi5 p ∣ f) :
    (Polynomial.X ^ 5 - 1) ∣ f := by
  -- `5 ≠ 0` in `Z/p`, perché `p` primo e `p ≠ 5`.
  have h50 : (5 : ZMod p) ≠ 0 := by
    have hh : ((5 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
      intro hd
      exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hd)
    exact_mod_cast hh
  -- `Φ₅(1) = 5`.
  have heval5 : Polynomial.eval 1 (phi5 p) = 5 := by
    unfold phi5
    simp
    ring
  -- `X − 1` è irriducibile: ha grado `1` su un corpo.
  have hdeg : (Polynomial.X - 1 : Polynomial (ZMod p)).degree = 1 := by
    rw [← Polynomial.C_1]
    exact Polynomial.degree_X_sub_C 1
  have hirr : Irreducible (Polynomial.X - 1 : Polynomial (ZMod p)) :=
    Polynomial.irreducible_of_degree_eq_one hdeg
  -- coprimalità: `X − 1` irriducibile divide `Φ₅` oppure è coprimo con
  -- `Φ₅`; la prima alternativa è esclusa perché `Φ₅(1) ≠ 0`.
  have hcop : IsCoprime (Polynomial.X - 1 : Polynomial (ZMod p)) (phi5 p) := by
    rcases EuclideanDomain.dvd_or_coprime (Polynomial.X - 1) (phi5 p) hirr with hdvd | hcop
    · exfalso
      obtain ⟨c, hc⟩ := hdvd
      apply h50
      rw [← heval5, hc]
      simp
    · exact hcop
  have hdvd_prod := hcop.mul_dvd h1 h2
  rwa [X_pow_five_sub_one_eq p] at hdvd_prod

end AgrawalCore
