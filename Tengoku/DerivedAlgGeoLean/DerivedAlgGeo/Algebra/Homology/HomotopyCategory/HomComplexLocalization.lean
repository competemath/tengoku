/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Algebra.Module.FinitePresentation
import Tengoku.Seed.RingTheory.TensorProduct.IsBaseChangePi
import Tengoku.Seed.Algebra.Category.ModuleCat.Localization
import Tengoku.Seed.Algebra.Homology.HomotopyCategory.HomComplex
import Tengoku.Seed.Algebra.Homology.Embedding.CochainComplex
import Tengoku.Seed.Data.Int.Interval

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Localization of Hom-complex cochains under finite effective support

When the source complex is supported in a finite interval and its terms are
finitely presented, localization of modules commutes with each degree of its
Hom complex. The comparison also commutes with the Hom-complex differential.
Finite projective terms provide a useful specialization.

In each fixed degree, a termwise strictly bounded-above source and a termwise
strictly bounded-below target also have finite effective support. Finite
presentation of the source terms on that degree-dependent interval gives the
same localization comparison.

This is a cochain-level statement. It does not yet identify cohomology of Hom
complexes, derived-category Homs, or bounded-coherent geometric base change.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open scoped ModuleCat.Algebra

namespace CochainComplex.HomComplex

universe u v w

noncomputable section

section FiniteCochains

variable {R : Type u} [CommRing R]
  {C : Type w} [Category.{v} C] [Preadditive C] [Linear R C]
  (P Q : CochainComplex C ℤ)
  (a b n : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]

private abbrev finiteCochain :=
  (i : {p : ℤ // p ∈ Finset.Icc a b}) → (P.X i.1 ⟶ Q.X (i.1 + n))

private def cochainRestrict :
    Cochain P Q n →ₗ[R] finiteCochain P Q a b n where
  toFun γ i := γ.v i.1 (i.1 + n) rfl
  map_add' x y := by
    funext i
    rfl
  map_smul' r x := by
    funext i
    rfl

private lemma cochain_eq_zero_outside (γ : Cochain P Q n) (p : ℤ)
    (hp : p ∉ Finset.Icc a b) : γ.v p (p + n) rfl = 0 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hp
  rcases hp with h | h
  · exact (P.isZero_of_isStrictlyGE a p h).eq_zero_of_src _
  · exact (P.isZero_of_isStrictlyLE b p h).eq_zero_of_src _

private def cochainExtend :
    finiteCochain P Q a b n →ₗ[R] Cochain P Q n where
  toFun v := Cochain.mk fun p q hpq => by
    subst q
    exact if hp : p ∈ Finset.Icc a b then v ⟨p, hp⟩ else 0
  map_add' x y := by
    apply Cochain.ext
    intro p q hpq
    subst q
    by_cases hp : a ≤ p ∧ p ≤ b
    · simp [Cochain.mk_v, Finset.mem_Icc, hp, Cochain.add_v]
    · simp [Cochain.mk_v, Finset.mem_Icc, hp, Cochain.add_v]
  map_smul' r x := by
    apply Cochain.ext
    intro p q hpq
    subst q
    by_cases hp : a ≤ p ∧ p ≤ b
    · simp [Cochain.mk_v, Finset.mem_Icc, hp, Cochain.smul_v]
    · simp [Cochain.mk_v, Finset.mem_Icc, hp, Cochain.smul_v]

private def cochainFiniteEquiv :
    Cochain P Q n ≃ₗ[R] finiteCochain P Q a b n where
  toLinearMap := cochainRestrict (R := R) P Q a b n
  invFun := cochainExtend (R := R) P Q a b n
  left_inv γ := by
    apply Cochain.ext
    intro p q hpq
    subst q
    by_cases hp : a ≤ p ∧ p ≤ b
    · simp [cochainExtend, cochainRestrict, Cochain.mk_v, Finset.mem_Icc, hp]
    · have hfin : p ∉ Finset.Icc a b := by simpa only [Finset.mem_Icc] using hp
      simp [cochainExtend, Cochain.mk_v, Finset.mem_Icc, hp,
        cochain_eq_zero_outside P Q a b n γ p hfin]
  right_inv v := by
    funext i
    have hi : a ≤ (i : ℤ) ∧ (i : ℤ) ≤ b := Finset.mem_Icc.mp i.2
    simp [cochainExtend, cochainRestrict, Cochain.mk_v, Finset.mem_Icc, hi]

end FiniteCochains

variable {R : Type u} [CommRing R]
  (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
  (a b n : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]

variable (S : Submonoid R)

private abbrev localizedP :=
  ((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj P

private abbrev localizedQ :=
  ((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj Q

/-- The cochain map induced by localizing both complexes degreewise.-/
def cochainLocalizedMap :
    Cochain P Q n →ₗ[R]
      Cochain
        (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj P)
        (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj Q)
        n where
  toFun γ := γ.map (ModuleCat.localizedModuleFunctor.{u} S)
  map_add' x y := by
    exact Cochain.map_add x y (ModuleCat.localizedModuleFunctor.{u} S)
  map_smul' r x := by
    apply Cochain.ext
    intro p q hpq
    simp only [Cochain.map_v, Cochain.smul_v]
    apply ModuleCat.hom_ext
    dsimp [ModuleCat.localizedModuleFunctor, ModuleCat.localizedModuleMap]
    simp only [map_smul]
    ext y
    change r •
      ((IsLocalizedModule.mapExtendScalars S
        ((P.X p).localizedModuleMkLinearMap S)
        ((Q.X q).localizedModuleMkLinearMap S) (Localization S))
        (x.v p q hpq).hom) y =
      (algebraMap R (Localization S) r) •
        ((IsLocalizedModule.mapExtendScalars S
          ((P.X p).localizedModuleMkLinearMap S)
          ((Q.X q).localizedModuleMkLinearMap S) (Localization S))
          (x.v p q hpq).hom) y
    exact (IsScalarTower.algebraMap_smul (Localization S) r _).symm

private def homLocalizedMap (M N : ModuleCat.{u} R) :
    (M ⟶ N) →ₗ[R] (M.localizedModule S ⟶ N.localizedModule S) := by
  let eR : (M ⟶ N) ≃ₗ[R] (M →ₗ[R] N) := ModuleCat.homLinearEquiv
  let eA : (M.localizedModule S ⟶ N.localizedModule S) ≃ₗ[R]
      (M.localizedModule S →ₗ[Localization S] N.localizedModule S) :=
    ModuleCat.homLinearEquiv
  exact eA.symm.toLinearMap ∘ₗ
    (IsLocalizedModule.mapExtendScalars S
      (M.localizedModuleMkLinearMap S) (N.localizedModuleMkLinearMap S)
      (Localization S)) ∘ₗ eR.toLinearMap

/-- Degreewise localization respects the Hom-complex differential.-/
theorem cochainLocalizedMap_delta (m : ℤ) (γ : Cochain P Q n) :
    cochainLocalizedMap P Q m S (δ n m γ) =
      δ n m (cochainLocalizedMap P Q n S γ) := by
  exact (δ_map n m γ (ModuleCat.localizedModuleFunctor.{u} S)).symm

end

end CochainComplex.HomComplex

namespace CochainComplex.HomComplex

universe u v w

noncomputable section

section HalfBoundedCochains

variable {R : Type u} [CommRing R]
  {C : Type w} [Category.{v} C] [Preadditive C] [Linear R C]
  (P Q : CochainComplex C ℤ) (c b n : ℤ)
  [P.IsStrictlyLE b] [Q.IsStrictlyGE c]

private lemma halfBounded_eq_zero_outside (γ : Cochain P Q n) (p : ℤ)
    (hp : p ∉ Finset.Icc (c - n) b) : γ.v p (p + n) rfl = 0 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hp
  rcases hp with h | h
  · exact (Q.isZero_of_isStrictlyGE c (p + n) (by omega)).eq_zero_of_tgt _
  · exact (P.isZero_of_isStrictlyLE b p h).eq_zero_of_src _

private def halfBoundedFiniteEquiv :
    Cochain P Q n ≃ₗ[R] finiteCochain P Q (c - n) b n where
  toLinearMap := cochainRestrict (R := R) P Q (c - n) b n
  invFun := cochainExtend (R := R) P Q (c - n) b n
  left_inv γ := by
    apply Cochain.ext
    intro p q hpq
    subst q
    by_cases hp : p ∈ Finset.Icc (c - n) b
    · change (if h : p ∈ Finset.Icc (c - n) b then
          γ.v p (p + n) rfl else 0) = γ.v p (p + n) rfl
      simp only [dite_eq_left hp]
    · rw [halfBounded_eq_zero_outside P Q c b n γ p hp]
      change (if h : p ∈ Finset.Icc (c - n) b then
          γ.v p (p + n) rfl else 0) = 0
      simp only [dite_eq_right hp]
  right_inv v := by
    funext i
    change (if h : (i : ℤ) ∈ Finset.Icc (c - n) b then
        v ⟨i.1, h⟩ else 0) = v i
    simp only [dite_eq_left i.2]

end HalfBoundedCochains

variable {R : Type u} [CommRing R]
  (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (S : Submonoid R)

end

end CochainComplex.HomComplex
