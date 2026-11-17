/-
Nucleo Lean della campagna Agrawal — lotto 14: L'INCOLLAGGIO LOCALE.

Il cuore (`lenstra_local`) dà la congruenza nella componente ciclotomica
`F_p[X]/Φ₅`. La componente banale `X ↦ 1` è gratuita: lì entrambi i membri si
annullano. Poiché `X^5-1 = (X-1)·Φ₅` e i due fattori sono coprimi per `p ≠ 5`
(`dvd_of_dvd_both` del lotto Recompose), le due informazioni si incollano e
danno la congruenza di Agrawal modulo `p`:
    (X-1)^n = X^n - 1 + (X^5-1)·g   in  (Z/p)[X] .

È il passaggio che il ponte `agrawal_fermat_shadow` percorre in discesa; qui si
percorre in salita, ed è ciò che serve per COSTRUIRE un controesempio invece
che per dedurne proprietà.

  · `sub_dvd_of_eval_one` : `X-1` divide `(X-1)^n - (X^n-1)`
  · `phi5_dvd_of_local`   : `Φ₅` divide lo stesso, se vale la congruenza in
                            `Phi5Ring p`
  · `agrawal_mod_p`       : la congruenza modulo `p`
Campagna UNICO, 26 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.LenstraLocal
import Tengoku.AgrawalR5.AgrawalCore.Recompose

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

/-- Lo scarto `(X-1)^n - (X^n-1)` si annulla in `X = 1`, dunque è divisibile
per `X - 1`.
@isnad1 id=dvd.1h2v.s9.e9253c6e06aa from=translated src=- shape=d4cfad94 vocab=af86596d
-/
lemma sub_dvd_of_eval_one {n : ℕ} (hn : 0 < n) :
    (X - 1 : Polynomial (ZMod p)) ∣ ((X - 1) ^ n - (X ^ n - 1)) := by
  have h : Polynomial.eval 1 (((X - 1) ^ n - (X ^ n - 1)) : Polynomial (ZMod p)) = 0 := by
    rw [Polynomial.eval_sub, eval_one_sub_pow hn, eval_one_pow_sub, sub_zero]
  have := (Polynomial.dvd_iff_isRoot (p := ((X - 1) ^ n - (X ^ n - 1) : Polynomial (ZMod p)))
    (a := (1 : ZMod p))).2 h
  simpa using this

/-- Se la congruenza vale nella componente ciclotomica, allora `Φ₅` divide lo
scarto: è la definizione stessa del quoziente `AdjoinRoot`.
@isnad1 id=dvd.1h2v.s9.dc36aead7cd0 from=translated src=- shape=da1e7826 vocab=196a1c9d
-/
lemma phi5_dvd_of_local {n : ℕ}
    (h : ((zeta5 : Phi5Ring p) - 1) ^ n = zeta5 ^ n - 1) :
    (phi5 p) ∣ ((X - 1) ^ n - (X ^ n - 1)) := by
  rw [← AdjoinRoot.mk_eq_zero]
  have hz : (AdjoinRoot.mk (phi5 p)) X = zeta5 := rfl
  simp only [map_sub, map_pow, map_one, hz]
  rw [h, sub_self]

/-- **La congruenza modulo `p`.** Incollando la componente ciclotomica (dal
cuore) con quella banale si ottiene la congruenza di Agrawal in `(Z/p)[X]`.
@isnad1 id=ex.3h2v.s10.85bdd2a92c61 from=translated src=- shape=e39ef432 vocab=2ac8010e
-/
theorem agrawal_mod_p {n : ℕ} (hn : 0 < n) (hp5 : p ≠ 5)
    (h : ((zeta5 : Phi5Ring p) - 1) ^ n = zeta5 ^ n - 1) :
    ∃ g : Polynomial (ZMod p),
      (X - 1) ^ n = X ^ n - 1 + (X ^ 5 - 1) * g := by
  obtain ⟨g, hg⟩ := dvd_of_dvd_both hp5 _ (sub_dvd_of_eval_one hn) (phi5_dvd_of_local h)
  exact ⟨g, by linear_combination hg⟩

end AgrawalCore
