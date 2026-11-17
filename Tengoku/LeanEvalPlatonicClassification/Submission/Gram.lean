import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.AdiacenzaUnica
import Tengoku.LeanEvalPlatonicClassification.Submission.MossaInvolutiva
import Tengoku.LeanEvalPlatonicClassification.Submission.Trasportatore
import Tengoku.LeanEvalPlatonicClassification.Submission.RelazioniCoxeter
import Tengoku.LeanEvalPlatonicClassification.Submission.GruppoFinito
import Tengoku.LeanEvalPlatonicClassification.Submission.Ordini
import Tengoku.LeanEvalPlatonicClassification.Submission.Iperpiano
import Tengoku.LeanEvalPlatonicClassification.Submission.Normali
import Tengoku.LeanEvalPlatonicClassification.Submission.FormulaRiflessione
import Tengoku.LeanEvalPlatonicClassification.Submission.Ortogonalita

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 20 — LA MATRICE DI GRAM, PARTE FONDATA
(19 lug 2026).

Si raccolgono le voci della matrice di Gram dei normali che sono già
dimostrate:

  ⟪αᵢ, αᵢ⟫ = 1              (normalizzazione)
  ⟪αᵢ, αⱼ⟫ = 0  se |i−j| ≥ 2  (dalla commutazione: `Ortogonalita`)

e, sul versante combinatorio, il valore ESATTO della matrice di Coxeter
fuori dalla tridiagonale:

  mᵢⱼ = 2       se |i−j| ≥ 2

Le due cose combaciano come devono: −cos(π/mᵢⱼ) = −cos(π/2) = 0.

La voce che manca è la sottodiagonale `⟪αᵢ, αᵢ₊₁⟫ = −cos(π/mᵢ)`, che
dipende da `mᵢ ≥ 3`, che dipende dal muro (connettività dei residui).
Qui NON la si assume di nascosto: è semplicemente assente.

La famiglia dei normali è esposta come DATO (skolemizzazione esplicita),
non nascosta dentro un esistenziale: è la lezione dei fascicoli persi
nella notte della rigidità.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- La diagonale della Gram.
@isnad1 id=eq.1h2v.s6.572d404a9233 from=translated src=- shape=adf6615d vocab=68be66f6
-/
theorem gram_diagonale {α : E n} (hα : ‖α‖ = 1) : ⟪α, α⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, hα]
  norm_num

end LeanEval.Geometry.PlatonicClassification
