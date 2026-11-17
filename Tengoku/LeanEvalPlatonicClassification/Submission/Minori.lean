import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 27 — I MINORI DELLA MATRICE TRIDIAGONALE
(19 lug 2026).

Il blocco algebrico della classificazione. Per una matrice di Coxeter a
STRINGA, con diagonale 1 e sottodiagonale `−cᵢ`, i minori principali
soddisfano la ricorrenza a tre termini

    D₀ = 1,  D₁ = 1,  D_{k+2} = D_{k+1} − c_k² · D_k

e la matrice è definita positiva esattamente quando tutti i minori sono
positivi (criterio di Sylvester).

Qui: la ricorrenza, i valori di `cos²(π/m)` per i casi che servono, e
i conti che eliminano le stringhe non ammesse. È algebra pura, senza
politopi: il ponte con la geometria vive altrove.
-/

open Real

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

/-- I minori principali della matrice tridiagonale con diagonale 1 e
sottodiagonale `−c k`.-/
noncomputable def minoreGram (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (k + 2) => minoreGram c (k + 1) - (c k) ^ 2 * minoreGram c k

@[simp] theorem minoreGram_zero (c : ℕ → ℝ) : minoreGram c 0 = 1 := rfl

@[simp] theorem minoreGram_one (c : ℕ → ℝ) : minoreGram c 1 = 1 := rfl

theorem minoreGram_succ_succ (c : ℕ → ℝ) (k : ℕ) :
    minoreGram c (k + 2) =
      minoreGram c (k + 1) - (c k) ^ 2 * minoreGram c k := rfl

end LeanEval.Geometry.PlatonicClassification
