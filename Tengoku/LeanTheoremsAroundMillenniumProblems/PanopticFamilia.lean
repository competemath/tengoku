import Tengoku.Seed.Tactic
import Tengoku.LeanTheoremsAroundMillenniumProblems.PanopticDuplicados

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# El agujero no está en los pesos: está en cómo se cuenta

`PanopticDuplicados` demuestra que la Panoptic Quality del reto de filamentos,

    PQ = (Σ IoU de los pares) / (|TP| + ½|FP| + ½|FN|),

sube al añadir un duplicado con IoU `v` exactamente cuando `v > PQ`, porque el
evaluador oficial acumula **todos** los pares por encima del umbral en vez de
emparejar uno a uno.

Queda una pregunta natural que aquel fichero no contesta: ¿es culpa del ½? Si
los falsos positivos pesaran más, ¿desaparecería el incentivo a duplicar?

La respuesta es que no, y es general. Este fichero trabaja con toda la familia

    M = s / (n + a·fp + b·fn),      a, b ≥ 0

que contiene a PQ (`a = b = ½`) y a los agregados de tipo F₁/Dice, y demuestra:

* `dup_iff` — duplicar sube la nota **exactamente cuando `v > M`**, para
  cualesquiera pesos `a` y `b`. Los pesos **no aparecen en la condición**.
* `ningun_peso_lo_arregla` — dicho como corolario: no existe elección de `a` y
  `b` que quite el incentivo. El defecto es de la regla de conteo, no de la
  ponderación, así que la única cura es estructural (emparejamiento uno a uno,
  o exigir partición).
* `fp_baja` / `fp_no_baja` — el otro lado, y su frontera exacta: bajo
  emparejamiento uno a uno el duplicado cuenta como falso positivo y la nota
  baja **si y sólo si `a > 0`**.

Por qué importa fuera del papel: el 9-sep-2026 nuestro propio juez de la tubería
de instancias admitía solapes, es decir contaba como este `M` con acumulación de
todos los pares. Inflaba **+0.0111** en el punto de operación, casi tanto como
nuestra barra de promoción (+0.015), y además **desplazaba el óptimo** (corte de
confianza 0.70 → 0.85): con duplicados gratis compensaba bajar el corte. El
teorema no describía sólo al evaluador del reto; describía el sesgo de nuestro
propio instrumento.
-/

namespace PanopticFamilia

/-- Denominador de la familia: aciertos, más los falsos positivos y negativos
con sus pesos. PQ es el caso `a = b = ½`.-/
noncomputable def den (a b : ℝ) (n fp fn : ℕ) : ℝ := (n : ℝ) + a * fp + b * fn

/-- La métrica: suma de valores de los pares emparejados sobre el denominador.-/
noncomputable def m (a b s : ℝ) (n fp fn : ℕ) : ℝ := s / den a b n fp fn

/--
@isnad1 id=eq.0h6v.s5.e7e2009fab3e from=translated src=- shape=92f5542d vocab=f0c6cf85
-/
lemma m_def (a b s : ℝ) (n fp fn : ℕ) : m a b s n fp fn = s / den a b n fp fn := rfl

/--
@isnad1 id=le.2h5v.s5.dcffd8e1d41a from=translated src=- shape=5fced1ec vocab=219c0a1a
-/
lemma den_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n fp fn : ℕ) :
    0 ≤ den a b n fp fn := by
  unfold den; positivity

/-- **La pieza clave, y es puramente estructural.** Un acierto más sube el
denominador en exactamente `1`, pase lo que pase con `a` y `b`: los pesos sólo
tocan a `fp` y a `fn`, y un duplicado no crea ninguno de los dos. De aquí sale
todo lo demás.
@isnad1 id=eq.0h5v.s5.605f559c07d1 from=translated src=- shape=4d45e637 vocab=f6cb4edb
-/
lemma den_succ (a b : ℝ) (n fp fn : ℕ) :
    den a b (n + 1) fp fn = den a b n fp fn + 1 := by
  unfold den; push_cast; ring

/-- **Duplicar sube la nota exactamente cuando el duplicado supera a la nota,
sean cuales sean los pesos.**

Añadir una predicción que empareja con una verdad ya emparejada suma `v` al
numerador y `1` al denominador, y no crea falsos positivos porque el evaluador
acumula todos los pares. Nótese que `a` y `b` no aparecen en la condición.
@isnad1 id=iff.1h7v.s6.712d1ae0e00b from=translated src=- shape=6689a16f vocab=048a4a84
-/
theorem dup_iff (a b s v : ℝ) (n fp fn : ℕ) (hd : 0 < den a b n fp fn) :
    m a b s n fp fn < m a b (s + v) (n + 1) fp fn ↔ m a b s n fp fn < v := by
  have hd1 : (0 : ℝ) < den a b n fp fn + 1 := by linarith
  rw [m_def, m_def, den_succ, div_lt_div_iff₀ hd hd1, div_lt_iff₀ hd]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Ninguna elección de pesos quita el incentivo a duplicar.**

Cuantificado sobre `a` y `b`: para todo par de pesos, cualquier duplicado mejor
que la nota actual la sube. No hay ponderación que arregle esto, porque el
problema no está en cuánto castigas los errores sino en que un duplicado no
cuenta como error. La cura tiene que cambiar la regla de conteo.
@isnad1 id=lt.2h7v.s6.8dfb6ac3a752 from=translated src=- shape=2b190214 vocab=048a4a84
-/
theorem ningun_peso_lo_arregla (s v : ℝ) (n fp fn : ℕ) :
    ∀ a b : ℝ, 0 < den a b n fp fn → m a b s n fp fn < v →
      m a b s n fp fn < m a b (s + v) (n + 1) fp fn := by
  intro a b hd hv
  exact (dup_iff a b s v n fp fn hd).mpr hv

/-- Un falso positivo sube el denominador en `a`.
@isnad1 id=eq.0h5v.s5.853fc4fecdca from=translated src=- shape=ca088ea3 vocab=f6cb4edb
-/
lemma den_fp (a b : ℝ) (n fp fn : ℕ) :
    den a b n (fp + 1) fn = den a b n fp fn + a := by
  unfold den; push_cast; ring

/-- **Con emparejamiento uno a uno el duplicado baja la nota, si `a > 0`.**

Al no poder emparejar (su verdad ya está tomada) cuenta como falso positivo: el
numerador no cambia y el denominador crece en `a`.
@isnad1 id=lt.3h6v.s6.ae67ae22f03d from=translated src=- shape=6ece808e vocab=048a4a84
-/
theorem fp_baja (a b s : ℝ) (n fp fn : ℕ) (ha : 0 < a) (hs : 0 < s)
    (hd : 0 < den a b n fp fn) :
    m a b s n (fp + 1) fn < m a b s n fp fn := by
  have hd2 : (0 : ℝ) < den a b n fp fn + a := by linarith
  rw [m_def, m_def, den_fp, div_lt_div_iff₀ hd2 hd]
  nlinarith

/-- **La frontera exacta.** Si los falsos positivos no pesan (`a = 0`), ni
siquiera el emparejamiento uno a uno castiga al duplicado: la nota se queda
igual. Es decir, `a > 0` en el teorema anterior no es una comodidad técnica,
es la hipótesis justa.
@isnad1 id=eq.0h5v.s5.d5c553f9b482 from=translated src=- shape=6cd5757e vocab=6404b56e
-/
theorem fp_no_baja (b s : ℝ) (n fp fn : ℕ) :
    m 0 b s n (fp + 1) fn = m 0 b s n fp fn := by
  rw [m_def, m_def, den_fp, add_zero]

/-- Las dos direcciones de una vez, para toda la familia: contando todos los
pares un duplicado bueno **sube** la nota, y emparejando uno a uno el mismo
duplicado la **baja**. Una métrica que se mueve en direcciones opuestas según
cómo se cuente no está midiendo calidad.
@isnad1 id=and.4h7v.s7.2345322b1635 from=translated src=- shape=b96c59c6 vocab=048a4a84
-/
theorem sube_o_baja_segun_se_cuente (a b s v : ℝ) (n fp fn : ℕ)
    (ha : 0 < a) (hs : 0 < s) (hd : 0 < den a b n fp fn)
    (hv : m a b s n fp fn < v) :
    m a b s n fp fn < m a b (s + v) (n + 1) fp fn ∧
      m a b s n (fp + 1) fn < m a b s n fp fn :=
  ⟨(dup_iff a b s v n fp fn hd).mpr hv, fp_baja a b s n fp fn ha hs hd⟩

/-- La Panoptic Quality del reto es el miembro `a = b = ½` de esta familia, así
que todo lo anterior se le aplica y `PanopticDuplicados.pq_dup_iff` es su
instancia.
@isnad1 id=eq.0h4v.s6.f907b8657cdf from=translated src=- shape=76b68bee vocab=7795fc3b
-/
theorem pq_es_instancia (s : ℝ) (n fp fn : ℕ) :
    Panoptic.pq s n fp fn = m (1/2) (1/2) s n fp fn := by
  rw [Panoptic.pq, m_def]
  unfold den
  congr 1
  ring

end PanopticFamilia
