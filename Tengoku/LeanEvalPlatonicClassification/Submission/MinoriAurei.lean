import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.Minori

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
MOTORE COXETER, PASSO 28 — LE STRINGHE AUREE E IL CONFINE
(19 lug 2026).

Le stringhe che contengono un 5 escono dai razionali: `cos(π/5)` è
`(1 + √5)/4` e il suo quadrato porta la sezione aurea. Qui i valori
esatti e le verifiche di positività per i due politopi quadridimensionali
aurei (600-celle e 120-celle), più i confini che devono cadere.

Poi il fatto che chiude la dimensione ≥ 5: la stringa `(3,3,5)` è
positiva in rango 4 ma NON in rango 5, ed è per questo che i solidi
aurei non hanno analoghi oltre la quarta dimensione.
-/

open Real

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

/-- Stime numeriche su `√5`, per i conti di positività.-/
theorem sqrt_five_bounds : 2.23 < Real.sqrt 5 ∧ Real.sqrt 5 < 2.24 := by
  constructor
  · have : (2.23 : ℝ) ^ 2 < 5 := by norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5),
      Real.sqrt_nonneg 5]
  · have : (5 : ℝ) < 2.24 ^ 2 := by norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5),
      Real.sqrt_nonneg 5]

end LeanEval.Geometry.PlatonicClassification
