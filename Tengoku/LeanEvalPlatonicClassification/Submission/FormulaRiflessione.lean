import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.AdiacenzaUnica
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasportatore
import Tengoku.LeanEvalPlatonicClassification.Submission.RelazioniCoxeter
import Tengoku.LeanEvalPlatonicClassification.Submission.Iperpiano
import Tengoku.LeanEvalPlatonicClassification.Submission.Normali

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 19 — LA FORMULA DELLA RIFLESSIONE (19 lug 2026).

Sapere che i punti fissi sono un iperpiano non basta: serve la FORMULA,

    rᵢ x = x − 2⟪αᵢ, x − pᵢ⟫ • αᵢ,

perché è da lì che si leggono gli angoli fra i normali, e quindi la
matrice di Gram.

Dimostrazione, algebra lineare pura sulla parte lineare `L` di `rᵢ`:
`L` fissa la giacitura dell'iperpiano; manda dunque `α` in `c • α`
(un'isometria preserva l'ortogonale della giacitura, che è la retta di
`α`); `c = ±1` per la norma; e `c = +1` costringerebbe `rᵢ` all'identità,
esclusa da `simpleReflection_ne_id`.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- La componente di un vettore ortogonale a un unitario.
@isnad1 id=eq.1h3v.s8.a44482145184 from=translated src=- shape=82854a19 vocab=871ca769
-/
theorem inner_comp_ortogonale {α v : E n} (hα : ‖α‖ = 1) :
    ⟪α, v - (⟪α, v⟫ : ℝ) • α⟫ = 0 := by
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hα]
  ring

/-- Un vettore ortogonale a tutta la giacitura è multiplo del normale.
@isnad1 id=eq.2h3v.s8.dbaa2d3a7525 from=translated src=- shape=4f61a761 vocab=642f2024
-/
theorem multiplo_del_normale {α w : E n} (hα : ‖α‖ = 1)
    (hw : ∀ v : E n, ⟪α, v⟫ = 0 → ⟪w, v⟫ = 0) :
    w = (⟪α, w⟫ : ℝ) • α := by
  have hdec : ⟪α, w - (⟪α, w⟫ : ℝ) • α⟫ = 0 :=
    inner_comp_ortogonale (α := α) (v := w) hα
  have h0 : ⟪w, w - (⟪α, w⟫ : ℝ) • α⟫ = 0 := hw _ hdec
  have h1 : ⟪(⟪α, w⟫ : ℝ) • α, w - (⟪α, w⟫ : ℝ) • α⟫ = 0 := by
    rw [real_inner_smul_left, hdec, mul_zero]
  have h2 : ⟪w - (⟪α, w⟫ : ℝ) • α, w - (⟪α, w⟫ : ℝ) • α⟫ = 0 := by
    rw [inner_sub_left, h0, h1, sub_zero]
  have hz := inner_self_eq_zero.mp h2
  exact sub_eq_zero.mp hz

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
