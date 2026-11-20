import Tengoku.TuzaLean.Tuza.Basic.Graph
import Tengoku.TuzaLean.Tuza.Basic.Coloring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The complete family of triangles with one red edge. -/

namespace Tuza

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complete family of triangles with exactly one red edge.
The ambient graph has edge set A; membership in R means red.-/
noncomputable def oneRedTriangles (A R : Finset (Sym2 V)) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (trianglesOn A).filter (fun T => (T ∩ R).card = 1)

/--
@isnad1 id=iff.0h4v.s6.cc282cc8bef3 from=translated src=- shape=d1064727 vocab=30138ea9
-/
@[simp] theorem mem_oneRedTriangles {A R T : Finset (Sym2 V)} :
    T ∈ oneRedTriangles A R ↔ IsTriangle T ∧ T ⊆ A ∧ (T ∩ R).card = 1 := by
  classical
  simp [oneRedTriangles, and_assoc]

/--
@isnad1 id=coloredf.0h3v.s5.473e23fe2575 from=translated src=- shape=a7d39096 vocab=c12038a5
-/
theorem oneRedTriangles_colored (A R : Finset (Sym2 V)) :
    ColoredFamily (oneRedTriangles A R) R := by
  intro T hT
  obtain ⟨ht, _, hr⟩ := mem_oneRedTriangles.mp hT
  exact ⟨ht.card_eq_three, hr⟩

/-- Deleting any edge set preserves completeness of the colored family.
@isnad1 id=eq.0h4v.s6.6cd39d2cf187 from=translated src=- shape=e3cfa6a1 vocab=e03a0796
-/
theorem oneRedTriangles_sdiff (A R C : Finset (Sym2 V)) :
    oneRedTriangles (A \ C) R = residual (oneRedTriangles A R) C := by
  classical
  ext T
  simp only [oneRedTriangles, mem_filter, trianglesOn_sdiff, mem_residual]
  tauto

/--
@isnad1 id=le.0h3v.s5.a8bf103ec7bb from=translated src=- shape=15ba393d vocab=a49ba368
-/
theorem oneRedTriangles_subset {A R : Finset (Sym2 V)} :
    oneRedTriangles A R ⊆ trianglesOn A := by
  classical
  exact filter_subset _ _

end Tuza
