import Tengoku.Seed.Tactic
import Tengoku.LeanTheoremsAroundMillenniumProblems.PanopticDuplicados

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quitar una predicción sube el PQ exactamente cuando su aportación es menor que PQ/2

Espejo de `PanopticCandidato.pq_candidato_iff`. Una predicción ya en la lista aporta al
numerador su IoU esperado `p · j` (probabilidad `p` de estar emparejada, IoU `j` cuando
lo está) y al denominador exactamente `½` en las dos ramas: si era acierto, al quitarla
un verdadero positivo pasa a falso negativo (`n − 1`, `fn + 1`, neto `−½`); si era fallo,
desaparece un falso positivo (`fp − 1`, neto `−½`). Por eso el PQ tras quitarla es
`(s − p·j) / (den − ½)`, y es **mayor** que el de partida si y solo si `p · j < PQ / 2`.

Es la regla con la que la campaña decide qué bandas de predicciones (por tamaño, por
agrupación, por confianza) se conservan: en validación ninguna banda del campeón queda
por debajo de `PQ/2 ≈ 0.216`, así que no hay nada que quitar (informe §93).
-/

namespace Panoptic

/-- El PQ tras quitar una predicción que aportaba `p · j` al numerador. El denominador
baja exactamente `½` tanto si era acierto como si era fallo.-/
noncomputable def pqQuitar (s p j : ℝ) (n fp fn : ℕ) : ℝ :=
  (s - p * j) / (den n fp fn - 1 / 2)

/-- Si la predicción era **acierto**: `n − 1` y `fn + 1`, el denominador baja `½`.
@isnad1 id=eq.0h3v.s6.28d5d88d7cc1 from=translated src=- shape=42d129e0 vocab=9566eac9
-/
lemma den_quitar_acierto (n fp m : ℕ) :
    den n fp (m + 1) = den (n + 1) fp m - 1 / 2 := by
  unfold den; push_cast; ring

/-- Si la predicción era **fallo**: `fp − 1`, el denominador baja `½`.
@isnad1 id=eq.0h3v.s5.3f69e3f5ea2f from=translated src=- shape=e8ebb864 vocab=9566eac9
-/
lemma den_quitar_fallo (n fp m : ℕ) :
    den n fp m = den n (fp + 1) m - 1 / 2 := by
  unfold den; push_cast; ring

/-- **Quitar sube el PQ si y solo si la aportación es menor que PQ/2.** Se pide que el
denominador restante sea positivo (queda al menos otra predicción o anotación).
@isnad1 id=iff.1h6v.s6.93e171ab7dd2 from=translated src=- shape=5ea75260 vocab=7e5002f5
-/
theorem pq_quitar_iff (s p j : ℝ) (n fp fn : ℕ) (hd : 1 / 2 < den n fp fn) :
    pq s n fp fn < pqQuitar s p j n fp fn ↔ p * j < pq s n fp fn / 2 := by
  have hd0 : (0 : ℝ) < den n fp fn := by linarith
  have hd2 : (0 : ℝ) < den n fp fn - 1 / 2 := by linarith
  unfold pqQuitar
  rw [pq_def, div_lt_div_iff₀ hd0 hd2, div_div,
      lt_div_iff₀ (by positivity : (0:ℝ) < den n fp fn * 2)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- La forma en que se usa: por debajo del umbral, quitar **sube** la nota.
@isnad1 id=lt.2h6v.s6.3f8aaa64dc7b from=translated src=- shape=03f21422 vocab=7e5002f5
-/
theorem pq_lt_quitar (s p j : ℝ) (n fp fn : ℕ) (hd : 1 / 2 < den n fp fn)
    (h : p * j < pq s n fp fn / 2) : pq s n fp fn < pqQuitar s p j n fp fn :=
  (pq_quitar_iff s p j n fp fn hd).mpr h

/-- Y el recíproco, que es el que decide en §93: si la aportación llega a `PQ/2`,
quitar la predicción **no** sube la nota.
@isnad1 id=le.2h6v.s6.ef27314bffe3 from=translated src=- shape=fc43a460 vocab=89340a79
-/
theorem quitar_le_pq (s p j : ℝ) (n fp fn : ℕ) (hd : 1 / 2 < den n fp fn)
    (h : pq s n fp fn / 2 ≤ p * j) : pqQuitar s p j n fp fn ≤ pq s n fp fn := by
  rw [← not_lt]
  intro hc
  exact absurd ((pq_quitar_iff s p j n fp fn hd).mp hc) (not_lt.mpr h)

/-- Añadir y quitar son inversos: quitar de la lista con el candidato añadido devuelve
el PQ de partida. Cierra el circuito `pq_candidato_iff` ↔ `pq_quitar_iff`.
@isnad1 id=eq.0h6v.s6.67c359c7128b from=translated src=- shape=7c9b31cf vocab=f7ce63e3
-/
theorem quitar_candidato (s p j : ℝ) (n fp fn : ℕ) :
    (s + p * j - p * j) / (den n fp fn + 1 / 2 - 1 / 2) = pq s n fp fn := by
  rw [pq_def]; ring_nf

end Panoptic
