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

/--
@isnad1 id=eq.0h1v.s4.c77e6d94f1ec from=translated src=- shape=777ad2f6 vocab=54f22e9e
-/
@[simp] theorem minoreGram_zero (c : ℕ → ℝ) : minoreGram c 0 = 1 := rfl

/--
@isnad1 id=eq.0h1v.s4.4a2d0e5c1eb3 from=translated src=- shape=777ad2f6 vocab=54f22e9e
-/
@[simp] theorem minoreGram_one (c : ℕ → ℝ) : minoreGram c 1 = 1 := rfl

/--
@isnad1 id=eq.0h2v.s6.a27dd42d61c8 from=translated src=- shape=65cea163 vocab=e196675a
-/
theorem minoreGram_succ_succ (c : ℕ → ℝ) (k : ℕ) :
    minoreGram c (k + 2) =
      minoreGram c (k + 1) - (c k) ^ 2 * minoreGram c k := rfl

end LeanEval.Geometry.PlatonicClassification
