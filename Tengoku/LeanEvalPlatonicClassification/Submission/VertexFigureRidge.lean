import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.ConnettivitaRidgeRiduzione

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
FIGURA AL VERTICE: INTERFACCIA ESATTA DEL SOTTO-KILL-GATE (21 lug 2026).

Questo file non postula assiomi e non costruisce surrettiziamente una
proiezione del residuo.  Isola i dati combinatori esatti di una vera figura
al vertice: le facce non puntuali di `B` che contengono `v` sono equivalenti,
conservando l'ordine, alle facce di un politopo di dimensione inferiore; la
dimensione scende esattamente di uno.

Da questi dati si dimostra:

* il trasporto di un cammino di ridge della figura in un cammino nello star;
* per induzione forte sulla dimensione intrinseca, `RidgeConnectedAboveOne`
  per ogni politopo;
* quindi il target `VertexStarRidgeConnectedAboveThree`.

L'unico enunciato geometrico ancora richiesto è
`VertexFigureGaloisExists`: l'esistenza di questi dati per ogni faccia e
vertice.  Lasciarlo come ipotesi esplicita rende il confine del lavoro
kernel-certificato controllabile con `#print axioms`.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Una faccia di dimensione positiva di `P`, contenuta in `B` e incidente
al vertice marcato `v`.  Sono precisamente le facce che devono sopravvivere
nella figura al vertice; la faccia puntuale `{v}` corrisponderebbe alla
faccia vuota, esclusa dalla nozione `IsFace` del benchmark.-/
structure PositiveVertexStarFace (P : ConvexPolytope n)
    (B : Set (E n)) (v : E n) where
  carrier : Set (E n)
  isFace : P.IsFace carrier
  subset_base : carrier ⊆ B
  mem_vertex : v ∈ carrier
  dim_pos : 1 ≤ faceDim carrier

/-- Una faccia non vuota ordinaria di un politopo.-/
structure PolytopeFace (P : ConvexPolytope n) where
  carrier : Set (E n)
  isFace : P.IsFace carrier

/--
@isnad1 id=eq.1h6v.s5.01e5ea885578 from=translated src=- shape=bd9a41e6 vocab=f3eca42c
-/
@[ext]
theorem PositiveVertexStarFace.ext
    {P : ConvexPolytope n} {B : Set (E n)} {v : E n}
    {F G : PositiveVertexStarFace P B v} (h : F.carrier = G.carrier) :
    F = G := by
  cases F
  cases G
  cases h
  rfl

/--
@isnad1 id=eq.1h4v.s5.b2e7c8a6b0ec from=translated src=- shape=0f6ad357 vocab=9b156b2f
-/
@[ext]
theorem PolytopeFace.ext {P : ConvexPolytope n}
    {F G : PolytopeFace P} (h : F.carrier = G.carrier) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- I dati di Galois necessari e sufficienti della figura al vertice.

`faceEquiv` identifica le facce positive dello star con tutte le facce della
figura. `map_subset_iff` dice che è una equivalenza d'ordine, mentre
`map_dim` registra lo shift di dimensione.-/
structure VertexFigureGaloisData (P : ConvexPolytope n)
    (B : Set (E n)) (v : E n) where
  figure : ConvexPolytope n
  faceEquiv : PositiveVertexStarFace P B v ≃ PolytopeFace figure
  map_subset_iff : ∀ F G,
    F.carrier ⊆ G.carrier ↔
      (faceEquiv F).carrier ⊆ (faceEquiv G).carrier
  map_dim : ∀ F,
    faceDim (faceEquiv F).carrier + 1 = faceDim F.carrier

/-- Il solo gate geometrico rimasto: ogni intervallo di facce sopra un
vertice ammette una vera figura al vertice con la corrispondenza di Galois e
lo shift dimensionale.-/
def VertexFigureGaloisExists : Prop :=
  ∀ {n : ℕ} (P : ConvexPolytope n) (B : Set (E n))
    (hB : P.IsFace B) (v : E n),
    v ∈ (facePolytope P hB).vertices →
    1 ≤ faceDim B →
    Nonempty (VertexFigureGaloisData P B v)

namespace VertexFigureGaloisData

variable {P : ConvexPolytope n} {B : Set (E n)} {v : E n}

/-- La faccia superiore dello star corrisponde al corpo intero della figura.
@isnad1 id=eq.3h5v.s7.c289ff5c8548 from=translated src=- shape=c3ead782 vocab=e4019739
-/
theorem map_top_eq_toSet (D : VertexFigureGaloisData P B v)
    (hB : P.IsFace B) (hvB : v ∈ B) (hdB : 1 ≤ faceDim B) :
    (D.faceEquiv
      { carrier := B
        isFace := hB
        subset_base := Subset.rfl
        mem_vertex := hvB
        dim_pos := hdB }).carrier = D.figure.toSet := by
  let T : PositiveVertexStarFace P B v :=
    { carrier := B
      isFace := hB
      subset_base := Subset.rfl
      mem_vertex := hvB
      dim_pos := hdB }
  let U : PolytopeFace D.figure :=
    { carrier := D.figure.toSet
      isFace := toSet_isFace D.figure }
  have hUT : (D.faceEquiv.symm U).carrier ⊆ T.carrier :=
    (D.faceEquiv.symm U).subset_base
  have himage : U.carrier ⊆ (D.faceEquiv T).carrier := by
    have h := (D.map_subset_iff (D.faceEquiv.symm U) T).mp hUT
    simpa only [D.faceEquiv.apply_symm_apply] using h
  apply Set.Subset.antisymm
  · exact face_subset_toSet D.figure (D.faceEquiv T).isFace
  · exact himage

/-- La dimensione intrinseca della figura è esattamente una in meno della
dimensione della faccia di base.
@isnad1 id=eq.3h5v.s6.c8d569948d75 from=translated src=- shape=42be884a vocab=bac1a219
-/
theorem figure_dim_add_one (D : VertexFigureGaloisData P B v)
    (hB : P.IsFace B) (hvB : v ∈ B) (hdB : 1 ≤ faceDim B) :
    faceDim D.figure.toSet + 1 = faceDim B := by
  let T : PositiveVertexStarFace P B v :=
    { carrier := B
      isFace := hB
      subset_base := Subset.rfl
      mem_vertex := hvB
      dim_pos := hdB }
  have hdim := D.map_dim T
  have htop := D.map_top_eq_toSet hB hvB hdB
  simpa only [T, htop] using hdim

end VertexFigureGaloisData

end LeanEval.Geometry.PlatonicClassification
