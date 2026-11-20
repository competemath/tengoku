import Tengoku.LeanTheoremsAroundMillenniumProblems.PanopticTecho

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# El umbral 1/2 es exacto, no un convenio

`PanopticTecho.empareja_a_lo_sumo_una` demuestra que con anotaciones disjuntas y
umbral **IoU > 1/2** una predicción empareja con como mucho una anotación: por
eso el evaluador puede acumular pares sin resolver un problema de asignación.

Queda la pregunta natural: ¿es el `1/2` el valor justo, o valdría cualquier
umbral? Aquí se cierra por el otro lado.

* `empata_con_dos_en_un_medio` — con `≥ 1/2` el enunciado es **falso**: hay una
  predicción que empata el umbral con dos anotaciones disjuntas a la vez. El
  testigo es mínimo: `A = {1,2}`, `B = {3,4}`, `P = {1,2,3,4}`, con
  `iou P A = iou P B = 1/2`.
* `umbral_exacto` — las dos mitades juntas: por encima de 1/2 el emparejamiento
  es único; en 1/2 exacto deja de serlo.

Consecuencia para la métrica: el `0.5` de Panoptic Quality (Kirillov et al.,
CVPR 2019) no es una constante elegida por conveniencia entre varias posibles.
Es el **ínfimo** de los umbrales que hacen que "la predicción `P` empareja con la
anotación `A`" sea una función parcial bien definida. Por debajo —y en el propio
1/2— el emparejamiento uno a uno deja de venir dado y hay que *elegirlo*
resolviendo una asignación (húngaro), que es justo lo que la fórmula publicada
no hace.

Y por eso el defecto que documenta `PanopticDuplicados` está donde está: la
unicidad la garantiza la hipótesis de que **las anotaciones** son disjuntas, que
nadie exige de **las predicciones**. La asimetría no se arregla moviendo el
umbral.
-/

namespace Panoptic

open Finset

/-- El testigo: dos anotaciones disjuntas y una predicción que empata el umbral
con las dos.
@isnad1 id=eq.0h0v.s6.8a7c7646e433 from=translated src=- shape=1ce750fd vocab=7f6bcf3e
-/
lemma iou_testigo : iou ({1, 2} : Finset ℕ) ({1, 2, 3, 4} : Finset ℕ) = 1 / 2 := by
  unfold iou
  norm_num [Finset.inter_comm]

/-- **Con `≥ 1/2` la unicidad se rompe.**

`P = {1,2,3,4}` alcanza exactamente el umbral con `A = {1,2}` y con `B = {3,4}`,
que son disjuntas. Luego la desigualdad **estricta** de `empareja_a_lo_sumo_una`
no es una comodidad de la demostración: es necesaria.
@isnad1 id=ex.0h0v.s6.98cf8d3d3e1c from=translated src=- shape=282d6f5d vocab=e0d9adf8
-/
theorem empata_con_dos_en_un_medio :
    ∃ (P A B : Finset ℕ), Disjoint A B ∧ (1 : ℝ) / 2 ≤ iou P A ∧ (1 : ℝ) / 2 ≤ iou P B := by
  refine ⟨{1, 2, 3, 4}, {1, 2}, {3, 4}, by decide, ?_, ?_⟩
  · rw [show iou ({1,2,3,4} : Finset ℕ) {1,2} = iou ({1,2} : Finset ℕ) {1,2,3,4} by
      unfold iou; rw [Finset.inter_comm, Finset.union_comm]]
    rw [iou_testigo]
  · rw [show iou ({1,2,3,4} : Finset ℕ) {3,4} = 1 / 2 by
      unfold iou; norm_num]

/-- **El umbral 1/2 es exacto.**

Por encima, el emparejamiento contra anotaciones disjuntas es único; en 1/2 hay
contraejemplo. Dicho de una vez: `1/2` es el ínfimo de los umbrales que hacen
del emparejamiento una función parcial, y la métrica publicada depende de ello
sin decirlo.
@isnad1 id=and.0h0v.s7.9bcb52778a42 from=translated src=- shape=6474e208 vocab=30ae33e8
-/
theorem umbral_exacto :
    (∀ (P A B : Finset ℕ), Disjoint A B → (1 : ℝ) / 2 < iou P A → (1 : ℝ) / 2 < iou P B → False)
    ∧ ¬ (∀ (P A B : Finset ℕ), Disjoint A B → (1 : ℝ) / 2 ≤ iou P A → (1 : ℝ) / 2 ≤ iou P B → False) := by
  refine ⟨fun P A B hAB hA hB => empareja_a_lo_sumo_una P A B hAB hA hB, ?_⟩
  intro h
  obtain ⟨P, A, B, hAB, hA, hB⟩ := empata_con_dos_en_un_medio
  exact h P A B hAB hA hB

end Panoptic
