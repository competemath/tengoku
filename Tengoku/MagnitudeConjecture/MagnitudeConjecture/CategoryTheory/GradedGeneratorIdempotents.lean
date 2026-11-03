import Tengoku.MagnitudeConjecture.MagnitudeConjecture.CategoryTheory.GradedGeneratorModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Complete homogeneous idempotents of the graded projective generator -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.GradedCategory.HomGrading
universe u v w
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C] [HasFiniteBiproducts C]
variable {ι : Type} [Fintype ι] (P : ι → C)

/-- The opposite endomorphism projecting onto one summand of the generator.-/
def generatorIdempotent (p : ι) : (End (⨁ P))ᵐᵒᵖ :=
  MulOpposite.op (End.of (biproduct.π P p ≫ biproduct.ι P p))

/--
@isnad1 id=eq.0h4v.s7.09c259b704f5 from=translated src=- shape=f51e28ea vocab=a9c00789
-/
theorem generatorIdempotent_idempotent (p : ι) :
    generatorIdempotent P p * generatorIdempotent P p = generatorIdempotent P p := by
  apply MulOpposite.unop_injective
  change End.of ((biproduct.π P p ≫ biproduct.ι P p) ≫
    (biproduct.π P p ≫ biproduct.ι P p)) = End.of (biproduct.π P p ≫ biproduct.ι P p)
  simp [Category.assoc]

/--
@isnad1 id=pairwise.0h3v.s8.16fc655e4803 from=translated src=- shape=8ae26762 vocab=789af2c2
-/
theorem generatorIdempotent_orthogonal : Pairwise fun p q ↦
    generatorIdempotent P p * generatorIdempotent P q = 0 := by
  intro p q hpq
  apply MulOpposite.unop_injective
  change End.of ((biproduct.π P p ≫ biproduct.ι P p) ≫
    (biproduct.π P q ≫ biproduct.ι P q)) = End.of 0
  simp [Category.assoc, biproduct.ι_π, hpq]

include k in
/--
@isnad1 id=eq.0h4v.s7.44c2e770e148 from=translated src=- shape=5383cc40 vocab=8344ac16
-/
theorem sum_generatorIdempotent : ∑ p, generatorIdempotent P p = 1 := by
  apply (generatorOppositeEquiv (k := k) P).injective
  rw [map_sum]
  change ∑ p, biproduct.π P p ≫ biproduct.ι P p = 𝟙 (⨁ P)
  exact biproduct.total

variable (G : HomGrading k C) [∀ i X, FiniteDimensional k (P i ⟶ X)]

/-- Each summand projection is homogeneous of degree zero.
@isnad1 id=mem.0h6v.s9.316334564281 from=translated src=- shape=51f4bac7 vocab=ee53b7b3
-/
theorem generatorIdempotent_mem_zero (p : ι) :
    generatorIdempotent P p ∈ (G.generatorAlgebraGrading P).component 0 := by
  classical
  intro i hi j hj
  change biproduct.ι P i ≫ (biproduct.π P p ≫ biproduct.ι P p) ≫ biproduct.π P j ∈
    G.component (P i) (P j) 0
  by_cases hip : i = p
  · subst i
    by_cases hpj : p = j
    · subst j
      simpa using G.id_mem (P p)
    · simp [Category.assoc, hpj]
  · simp [← Category.assoc, hip]

/-- A degree absent in every projective Hom space is absent in the generator algebra.
@isnad1 id=eq.1h6v.s9.5905de0cab12 from=translated src=- shape=2465f14d vocab=6e18bb63
-/
theorem generatorAlgebra_component_eq_bot (d : ℤ)
    (hd : ∀ i j, G.component (P i) (P j) d = ⊥) :
    (G.generatorAlgebraGrading P).component d = ⊥ := by
  apply bot_unique
  intro a ha
  change a = 0
  apply (generatorOppositeEquiv (k := k) P).injective
  apply (generatorMatrixEquiv (k := k) P).injective
  funext i j
  have h := ha i (Set.mem_univ i) j (Set.mem_univ j)
  change _ ∈ G.component (P i) (P j) d at h
  rw [hd, Submodule.mem_bot] at h
  change biproduct.ι P i ≫ a.unop.asHom ≫ biproduct.π P j = 0 at h
  change biproduct.ι P i ≫ a.unop.asHom ≫ biproduct.π P j =
    biproduct.ι P i ≫ (0 : ⨁ P ⟶ ⨁ P) ≫ biproduct.π P j
  simpa only [zero_comp, comp_zero] using h

end MagnitudeConjecture.GradedCategory.HomGrading
