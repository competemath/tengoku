import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.Linear
import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dimension shifting across a projective middle term

A short exact sequence `0 ⟶ K ⟶ P ⟶ X ⟶ 0` with projective middle term
induces the natural linear equivalence

`Extⁿ⁺¹(K,Y) ≃ Extⁿ⁺²(X,Y)`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace MagnitudeConjecture.ProjectiveMiddleDimensionShift

universe uk w v u

variable {k : Type uk} [CommRing k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]
  [HasExt.{w} C]

/-- The connecting map in positive degree is bijective when the middle term
of the short exact sequence is projective.
@isnad1 id=bijectiv.1h5v.s9.2b9f98db629d from=translated src=- shape=49a4a07d vocab=12657eb2
-/
theorem connecting_bijective
    {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
    (Y : C) (n : ℕ) :
    Function.Bijective
      (Ext.precompOfLinear hS.extClass k Y
        (show 1 + (n + 1) = n + 2 by omega)) := by
  constructor
  · intro x y hxy
    have hzero :
        Ext.precompOfLinear hS.extClass k Y
            (show 1 + (n + 1) = n + 2 by omega) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁
      hS Y (x - y) (show 1 + (n + 1) = n + 2 by omega) hzero
    have hx₂zero : x₂ = 0 := Ext.eq_zero_of_projective x₂
    rw [hx₂zero, Ext.comp_zero] at hx₂
    exact sub_eq_zero.mp hx₂.symm
  · intro z
    have hz :
        (Ext.mk₀ S.g).comp z (zero_add (n + 2)) = 0 :=
      Ext.eq_zero_of_projective _
    obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₃
      hS Y z hz (show 1 + (n + 1) = n + 2 by omega)
    exact ⟨x, hx⟩

/-- Dimension shifting, in the variance and normalization used by
Auslander's coherent duality.-/
def linearEquiv
    {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
    (Y : C) (n : ℕ) :
    Ext.{w} S.X₁ Y (n + 1) ≃ₗ[k] Ext.{w} S.X₃ Y (n + 2) :=
  LinearEquiv.ofBijective
    (Ext.precompOfLinear hS.extClass k Y
      (show 1 + (n + 1) = n + 2 by omega))
    (connecting_bijective (k := k) hS Y n)

/--
@isnad1 id=eq.1h6v.s10.41183557bc24 from=translated src=- shape=e4206912 vocab=fb6b30fa
-/
@[simp]
theorem linearEquiv_apply
    {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
    (Y : C) (n : ℕ) (x : Ext.{w} S.X₁ Y (n + 1)) :
    linearEquiv (k := k) hS Y n x =
      hS.extClass.comp x (show 1 + (n + 1) = n + 2 by omega) :=
  rfl

/-- Dimension shifting is natural under postcomposition in the second Ext
variable.
@isnad1 id=eq.1h8v.s11.a9192bcf2f28 from=translated src=- shape=fd85f33a vocab=ba7487d8
-/
theorem linearEquiv_postcomp
    {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
    {Y Z : C} (a : Y ⟶ Z) (n : ℕ)
    (x : Ext.{w} S.X₁ Y (n + 1)) :
    linearEquiv (k := k) hS Z n
        (x.comp (Ext.mk₀ a) (add_zero (n + 1))) =
      (linearEquiv (k := k) hS Y n x).comp
      (Ext.mk₀ a) (add_zero (n + 2)) := by
  rw [linearEquiv_apply, linearEquiv_apply]
  exact (Ext.comp_assoc_of_third_deg_zero hS.extClass x
    (Ext.mk₀ a) (show 1 + (n + 1) = n + 2 by omega)).symm

end MagnitudeConjecture.ProjectiveMiddleDimensionShift
