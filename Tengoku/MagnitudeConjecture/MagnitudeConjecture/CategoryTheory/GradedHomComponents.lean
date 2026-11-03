import Tengoku.MagnitudeConjecture.MagnitudeConjecture.CategoryTheory.GradedDegreeCategory

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Homogeneous components of maps

An internal Hom grading gives finite homogeneous decompositions of every map.
Taking degree zero of a composite pairs opposite degrees. This is the
identity decomposition used to classify graded indecomposables as shifts.
-/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

open CategoryTheory
open scoped BigOperators

namespace MagnitudeConjecture.GradedCategory.HomGrading

universe u v w

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable (G : HomGrading k C)

/-- The finite homogeneous decomposition of a map.-/
def decomposeHom (X Y : C) :
    (X ⟶ Y) ≃ₗ[k] DirectSum ℤ (fun d ↦ G.component X Y d) := by
  letI := (G.internal X Y).chooseDecomposition
  exact DirectSum.decomposeLinearEquiv (G.component X Y)

/-- Projection onto degree `d`, viewed as an ambient map.-/
def part (X Y : C) (d : ℤ) : (X ⟶ Y) →ₗ[k] (X ⟶ Y) :=
  (G.component X Y d).subtype.comp
    ((DirectSum.component k ℤ (fun i ↦ G.component X Y i) d).comp
      (G.decomposeHom X Y).toLinearMap)

/--
@isnad1 id=mem.0h7v.s8.50667c72e3ef from=translated src=- shape=de929c53 vocab=a5403df3
-/
theorem part_mem {X Y : C} (d : ℤ) (f : X ⟶ Y) :
    G.part X Y d f ∈ G.component X Y d :=
  ((G.decomposeHom X Y f) d).property

/--
@isnad1 id=eq.1h7v.s8.4a4aa061daa4 from=translated src=- shape=54d6c831 vocab=a5403df3
-/
theorem part_of_mem {X Y : C} {d : ℤ} {f : X ⟶ Y}
    (hf : f ∈ G.component X Y d) : G.part X Y d f = f := by
  letI := (G.internal X Y).chooseDecomposition
  exact DirectSum.decompose_of_mem_same (G.component X Y) hf

/--
@isnad1 id=eq.2h8v.s9.99955ee19dbb from=translated src=- shape=29a30fd9 vocab=a5403df3
-/
theorem part_of_mem_ne {X Y : C} {d e : ℤ} {f : X ⟶ Y}
    (hf : f ∈ G.component X Y d) (hde : d ≠ e) : G.part X Y e f = 0 := by
  letI := (G.internal X Y).chooseDecomposition
  exact DirectSum.decompose_of_mem_ne (G.component X Y) hf hde

/--
@isnad1 id=eq.0h6v.s12.56109847f047 from=translated src=- shape=a98e4582 vocab=f2e837e5
-/
theorem sum_parts {X Y : C} (f : X ⟶ Y) :
    ∑ d ∈ (G.decomposeHom X Y f).support, G.part X Y d f = f := by
  classical
  letI := (G.internal X Y).chooseDecomposition
  exact DirectSum.sum_support_decompose (G.component X Y) f

/-- With the first factor homogeneous of degree `d`, only degree `-d` of
the second factor contributes to degree zero of their composite.
@isnad1 id=eq.1h9v.s9.5ff5fdac6b27 from=translated src=- shape=83fdb956 vocab=12af440e
-/
theorem part_zero_comp_homogeneous {X Y Z : C} {d : ℤ} (f : X ⟶ Y)
    (hf : f ∈ G.component X Y d) (g : Y ⟶ Z) :
    G.part X Z 0 (f ≫ g) = f ≫ G.part Y Z (-d) g := by
  letI := (G.internal Y Z).chooseDecomposition
  apply DirectSum.Decomposition.inductionOn (ℳ := G.component Y Z)
    (motive := fun g ↦ G.part X Z 0 (f ≫ g) = f ≫ G.part Y Z (-d) g)
  · simp
  · intro e g
    by_cases he : e = -d
    · subst e
      rw [G.part_of_mem g.property]
      apply G.part_of_mem
      simpa using G.comp_mem hf g.property
    · rw [G.part_of_mem_ne g.property he, Limits.comp_zero]
      exact G.part_of_mem_ne (G.comp_mem hf g.property) (by omega)
  · intro g g' hg hg'
    simp only [Preadditive.comp_add, map_add, hg, hg']

/-- Degree-zero convolution has a finite sum indexed only by the support of
the first factor.
@isnad1 id=eq.0h8v.s13.eefc8e230684 from=translated src=- shape=4375d454 vocab=fd06e794
-/
theorem part_zero_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    G.part X Z 0 (f ≫ g) =
      ∑ d ∈ (G.decomposeHom X Y f).support,
        G.part X Y d f ≫ G.part Y Z (-d) g := by
  classical
  calc
    _ = G.part X Z 0 ((∑ d ∈ (G.decomposeHom X Y f).support,
        G.part X Y d f) ≫ g) := by rw [G.sum_parts f]
    _ = _ := by
      rw [Preadditive.sum_comp, map_sum]
      apply Finset.sum_congr rfl
      intro d hd
      exact G.part_zero_comp_homogeneous _ (G.part_mem d f) g

/-- Taking degree zero preserves the identity map.
@isnad1 id=eq.0h4v.s8.78852f627ad6 from=translated src=- shape=c6af447d vocab=5394d2f7
-/
theorem part_zero_id (X : C) : G.part X X 0 (𝟙 X) = 𝟙 X :=
  G.part_of_mem (G.id_mem X)

end MagnitudeConjecture.GradedCategory.HomGrading
