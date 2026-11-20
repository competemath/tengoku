import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Por qué una métrica que cuenta todos los pares se puede inflar duplicando

La Panoptic Quality del reto de filamentos solares (IEEE BigData Cup 2026) es

    PQ = (Σ_{pares emparejados} IoU) / (|TP| + ½|FP| + ½|FN|),

y el evaluador oficial acumula **todos** los pares `(predicción, verdad)` con
IoU > ½, no un emparejamiento uno a uno. Al fundir dos tuberías nuestras con un
filtro laxo de duplicados medimos `PQ = 0.4852` con **458 aciertos sobre 456
instancias reales**: imposible, y la señal de que algo estaba mal en la métrica y
no en el modelo.

Este fichero demuestra que esa aritmética no era un accidente:

* `pq_dup_iff` — con acumulación de todos los pares, añadir un duplicado de una
  predicción ya emparejada, con IoU `v`, sube el PQ **exactamente cuando
  `v > PQ`**. No hace falta que el duplicado aporte información: basta con que
  sea mejor que la media ponderada que ya llevas.
* `pq_fp_lt` — con emparejamiento uno a uno el mismo duplicado no puede
  emparejar (su verdad ya está tomada), cuenta como falso positivo, y el PQ
  **baja siempre**.

Juntos dicen lo que el informe afirma con números: la métrica tal y como está
especificada es explotable, y exigir emparejamiento uno a uno la arregla.

La medida que motivó esto: en AFINA el campeón tiene PQ 0.4326 y sus aciertos
promedian IoU 0.687. Como `0.687 > 0.4326`, `pq_dup_iff` dice que **cada
duplicado subía la nota**, que es justo lo que observamos.
-/

namespace Panoptic

/-- Panoptic Quality: `s` es la suma de los IoU de los pares emparejados y `n`
cuántos son; `fp` y `fn` cuentan predicciones sin verdad y verdades sin
predicción, y pesan ½ cada una.-/
noncomputable def pq (s : ℝ) (n fp fn : ℕ) : ℝ :=
  s / (n + (fp + fn) / 2)

/-- El denominador de PQ.-/
noncomputable def den (n fp fn : ℕ) : ℝ := (n : ℝ) + (fp + fn) / 2

/--
@isnad1 id=eq.0h4v.s4.b5d9afbf2e88 from=translated src=- shape=14531ed5 vocab=daa9aabf
-/
lemma pq_def (s : ℝ) (n fp fn : ℕ) : pq s n fp fn = s / den n fp fn := rfl

/--
@isnad1 id=le.0h3v.s4.c5748ff6e545 from=translated src=- shape=1995cd38 vocab=02a2f54d
-/
lemma den_nonneg (n fp fn : ℕ) : 0 ≤ den n fp fn := by
  unfold den
  positivity

/-- **Duplicar sube la nota exactamente cuando el duplicado supera al PQ.**

Añadir una predicción que empareja con una verdad ya emparejada, con IoU `v`,
suma `v` al numerador y `1` al denominador (un TP más), y no crea ningún falso
positivo, porque el evaluador acumula todos los pares por encima del umbral.
El PQ resultante es mayor si y solo si `v` es mayor que el PQ de partida.
@isnad1 id=iff.1h5v.s6.52224f4e34ad from=translated src=- shape=e45153ff vocab=db2aa954
-/
theorem pq_dup_iff (s v : ℝ) (n fp fn : ℕ) (hd : 0 < den n fp fn) :
    pq s n fp fn < pq (s + v) (n + 1) fp fn ↔ pq s n fp fn < v := by
  have hd1 : (0 : ℝ) < den n fp fn + 1 := by linarith
  have hden : den (n + 1) fp fn = den n fp fn + 1 := by
    unfold den; push_cast; ring
  rw [pq_def, pq_def, hden]
  rw [div_lt_div_iff₀ hd hd1, div_lt_iff₀ hd]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- La misma cuenta, en la forma en que se usa: si el duplicado es mejor que el
PQ actual, la nota sube **estrictamente**.
@isnad1 id=lt.2h5v.s6.c143ab91405f from=translated src=- shape=be8fc95e vocab=db2aa954
-/
theorem pq_lt_pq_dup (s v : ℝ) (n fp fn : ℕ) (hd : 0 < den n fp fn)
    (hv : pq s n fp fn < v) : pq s n fp fn < pq (s + v) (n + 1) fp fn :=
  (pq_dup_iff s v n fp fn hd).mpr hv

/-- **Con emparejamiento uno a uno, el duplicado baja la nota.**

Si cada verdad sólo puede emparejarse una vez, el duplicado no empareja: cuenta
como falso positivo. El numerador no cambia y el denominador crece en ½, así que
el PQ baja estrictamente siempre que hubiera algo que perder (`0 < s`).
@isnad1 id=lt.2h4v.s5.3b0329c38374 from=translated src=- shape=98921a4a vocab=db2aa954
-/
theorem pq_fp_lt (s : ℝ) (n fp fn : ℕ) (hs : 0 < s) (hd : 0 < den n fp fn) :
    pq s n (fp + 1) fn < pq s n fp fn := by
  have hden : den n (fp + 1) fn = den n fp fn + 1 / 2 := by
    unfold den; push_cast; ring
  have hd2 : (0 : ℝ) < den n fp fn + 1 / 2 := by linarith
  rw [pq_def, pq_def, hden, div_lt_div_iff₀ hd2 hd]
  nlinarith

/-- La brecha entre las dos reglas, dicha de una vez: bajo acumulación de todos
los pares un duplicado suficientemente bueno sube la nota, mientras que bajo
emparejamiento uno a uno el mismo duplicado la baja. Una métrica que se puede
mover en direcciones opuestas según cómo se cuente no está midiendo calidad.
@isnad1 id=and.3h5v.s6.0d8ae7a26c43 from=translated src=- shape=2acd068f vocab=db2aa954
-/
theorem duplicado_sube_pero_uno_a_uno_baja
    (s v : ℝ) (n fp fn : ℕ) (hs : 0 < s) (hd : 0 < den n fp fn)
    (hv : pq s n fp fn < v) :
    pq s n fp fn < pq (s + v) (n + 1) fp fn ∧ pq s n (fp + 1) fn < pq s n fp fn :=
  ⟨pq_lt_pq_dup s v n fp fn hd hv, pq_fp_lt s n fp fn hs hd⟩

end Panoptic
