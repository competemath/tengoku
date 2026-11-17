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

@[simp] theorem gammaU_zero : gammaU 0 = 0 := rfl

@[simp] theorem gammaU_one : gammaU 1 = 1 := rfl

@[simp] theorem gammaU_add_two (n : ℕ) :
    gammaU (n + 2) = 5 * gammaU (n + 1) - 5 * gammaU n := by
  rw [gammaU]

/-- Formula di potenza universale per una radice di `X² - 5X + 5`.-/
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

/-- La stessa formula all'indice `n≥1`, nella notazione del paper.-/
theorem gamma_pow_formula {R : Type*} [CommRing R] (γ : R)
    (hγ : γ ^ 2 = 5 * γ - 5) {n : ℕ} (hn : 1 ≤ n) :
    γ ^ n = (gammaU n : R) * γ - 5 * (gammaU (n - 1) : R) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm] using gamma_pow_succ γ hγ j

/-- Coefficienti della coniugazione quadratica `γ ↦ 5-γ`.-/
def gammaConjCoeffs (c d : ℤ) : ℤ × ℤ :=
  (c + 5 * d, -d)

/-- Valutare i coefficienti coniugati in `γ` equivale a valutare gli
stessi coefficienti in `5-γ`.-/
theorem gamma_conj_eval {R : Type*} [CommRing R] (γ : R) (c d : ℤ) :
    ((gammaConjCoeffs c d).1 : R) + ((gammaConjCoeffs c d).2 : R) * γ
      = (c : R) + (d : R) * (5 - γ) := by
  simp [gammaConjCoeffs]
  ring

end AgrawalCore
