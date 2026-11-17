/-
La ricorrenza quadratica usata nella riduzione primitiva di H4.

Questo modulo formalizza la parte che prima viveva soltanto negli script:
se `γ² = 5γ - 5` e

  U₀ = 0, U₁ = 1, Uₙ₊₂ = 5Uₙ₊₁ - 5Uₙ,

allora `γⁿ⁺¹ = Uₙ₊₁ γ - 5Uₙ`.

Non contiene alcuna affermazione sull'inerzia dei divisori: H4 resta aperta.
-/
import Tengoku.Seed.Algebra.Ring.Defs
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/-- La successione intera associata a `X² - 5X + 5`.-/
def gammaU : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * gammaU (n + 1) - 5 * gammaU n

/--
@isnad1 id=eq.0h0v.s3.a33994104879 from=translated src=- shape=1ac31801 vocab=9c297e57
-/
@[simp] theorem gammaU_zero : gammaU 0 = 0 := rfl

/--
@isnad1 id=eq.0h0v.s3.c0c21e8e8e25 from=translated src=- shape=1ac31801 vocab=9c297e57
-/
@[simp] theorem gammaU_one : gammaU 1 = 1 := rfl

/--
@isnad1 id=eq.0h1v.s6.83360fc78107 from=translated src=- shape=73d0e5d2 vocab=dccb6510
-/
@[simp] theorem gammaU_add_two (n : ℕ) :
    gammaU (n + 2) = 5 * gammaU (n + 1) - 5 * gammaU n := by
  rw [gammaU]

/-- Formula di potenza universale per una radice di `X² - 5X + 5`.
@isnad1 id=eq.1h3v.s7.277193404eb7 from=translated src=- shape=8b6431c8 vocab=adcf3193
-/
theorem gamma_pow_succ {R : Type*} [CommRing R] (γ : R)
    (hγ : γ ^ 2 = 5 * γ - 5) :
    ∀ n : ℕ, γ ^ (n + 1) =
      (gammaU (n + 1) : R) * γ - 5 * (gammaU n : R)
  | 0 => by simp
  | n + 1 => by
      rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ,
        gamma_pow_succ γ hγ n, gammaU_add_two]
      push_cast
      linear_combination (gammaU (n + 1) : R) * hγ

/-- La stessa formula all'indice `n≥1`, nella notazione del paper.
@isnad1 id=eq.2h3v.s7.ceac5d3528de from=translated src=- shape=f21d9607 vocab=7c8c3eb0
-/
theorem gamma_pow_formula {R : Type*} [CommRing R] (γ : R)
    (hγ : γ ^ 2 = 5 * γ - 5) {n : ℕ} (hn : 1 ≤ n) :
    γ ^ n = (gammaU n : R) * γ - 5 * (gammaU (n - 1) : R) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm] using gamma_pow_succ γ hγ j

/-- Coefficienti della coniugazione quadratica `γ ↦ 5-γ`.-/
def gammaConjCoeffs (c d : ℤ) : ℤ × ℤ :=
  (c + 5 * d, -d)

/-- Valutare i coefficienti coniugati in `γ` equivale a valutare gli
stessi coefficienti in `5-γ`.
@isnad1 id=eq.0h4v.s7.46c342d0a882 from=translated src=- shape=1500cfee vocab=fbe95f85
-/
theorem gamma_conj_eval {R : Type*} [CommRing R] (γ : R) (c d : ℤ) :
    ((gammaConjCoeffs c d).1 : R) + ((gammaConjCoeffs c d).2 : R) * γ
      = (c : R) + (d : R) * (5 - γ) := by
  simp [gammaConjCoeffs]
  ring

end AgrawalCore
