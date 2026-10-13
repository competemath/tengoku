/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Algebra.Homology.Ext.DualNumbers
public import Tengoku.Tauceti.TauCeti.RepresentationTheory.GrothendieckGroup.CartanMatrix

/-!
# The Cartan matrix of the dual numbers

Let `k` be a field, let `A = k[ε]` be the dual numbers `k[ε]/(ε²)`, and let `S = A/(ε)` be its
residue field, viewed as an `A`-module. The ring `A` is local and Artinian, its only
indecomposable finitely generated projective module is `A` itself, and its only simple module is
`S`. The short exact sequence

```text
0 ⟶ S --ε--> A ⟶ S ⟶ 0
```

shows that `A` has two composition factors, both isomorphic to `S`. Hence the Cartan map
`K₀(proj A) ⟶ G₀(mod A)` sends `[A]` to `2 • [S]`, and the Cartan matrix of `A` is the
one-by-one matrix `2`. Its determinant is `2`, so it is not invertible over `ℤ`.

This is the example showing that unimodularity of the Cartan matrix needs finite projective
resolutions: every class in the image of the Cartan map has even `S`-coordinate, while `[S]` has
coordinate one. Since the Cartan map sends the alternating class of a finite projective resolution
of a module to the class of that module, `S` admits no finite resolution by finitely generated
projective modules.

## Main results

* `TauCeti.jordanHolderMultiplicity_dualNumber_dualNumberResidue`: `[A : S] = 2`.
* `TauCeti.cartanMap_dualNumberFreeProj`: the Cartan map sends `[A]` to `2 • [S]`.
* `TauCeti.cartanMatrix_dualNumber`: the Cartan matrix of `A` is `2`, with
  `TauCeti.det_cartanMatrix_dualNumber` and `TauCeti.not_isUnit_cartanMatrix_dualNumber`.
* `TauCeti.cartanMap_dualNumber_ne_dualNumberResidueFG`: `[S]` is not in the image of the
  Cartan map, so `TauCeti.not_surjective_cartanMap_dualNumber`: the Cartan map is not surjective.
* `TauCeti.not_admitsFiniteResolution_dualNumberResidue`: `S` has no finite resolution by finitely
  generated projective modules.

## References

* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3.
-/

open CategoryTheory TrivSqZeroExt

public section

namespace TauCeti

universe u

variable (k : Type u) [Field k]

/-! ### The composition factors of `k[ε]` -/

/-- The inclusion `k[ε]/(ε) ⟶ k[ε]`, `x ↦ x ε`, onto the maximal ideal. -/
private noncomputable def dualNumberResidueToFree :
    dualNumberResidue k →ₗ[DualNumber k] DualNumber k where
  toFun x := inr (dualNumberResidueEquiv k x)
  map_add' _ _ := by rw [map_add, inr_add]
  map_smul' a x := by
    rw [dualNumberResidueEquiv_smul]
    ext <;> simp [-dualNumberResidueEquiv_apply]
    first
      | (all_goals grind; done)
      | (all_goals simp_all; done)
      | (all_goals aesop; done)
      | (all_goals omega; done)
      | (all_goals norm_num; done)
      | (all_goals positivity; done)
      | (all_goals linarith; done)
      | (all_goals decide; done)
      | (all_goals tauto; done)

private theorem dualNumberResidueToFree_apply (x : dualNumberResidue k) :
    dualNumberResidueToFree k x = inr (dualNumberResidueEquiv k x) :=
  (rfl)

private theorem dualNumberResidueToFree_injective :
    Function.Injective (dualNumberResidueToFree k) :=
  fun x y h ↦ (dualNumberResidueEquiv k).injective <| inr_injective <| by
    rwa [dualNumberResidueToFree_apply, dualNumberResidueToFree_apply] at h

private theorem exact_dualNumberResidueToFree_dualNumberProj :
    Function.Exact (dualNumberResidueToFree k) (dualNumberProj k).hom := by
  intro y
  rw [dualNumberProj_apply]
  refine ⟨fun hy ↦ ⟨(dualNumberResidueEquiv k).symm (snd y), ?_⟩, ?_⟩
  · rw [dualNumberResidueToFree_apply, LinearEquiv.apply_symm_apply]
    ext
    · rw [fst_inr, hy]
      -- as in `ker_dualNumberProj`, the two zeros agree after unfolding restriction of scalars
      rfl
    · rw [snd_inr]
  · rintro ⟨x, rfl⟩
    rw [dualNumberResidueToFree_apply, fst_inr]
    -- as in `ker_dualNumberProj`, the two zeros agree after unfolding restriction of scalars
    rfl

/-- **`k[ε]` has two composition factors isomorphic to its residue field**:
`[k[ε] : k[ε]/(ε)] = 2`, read off the short exact sequence `0 ⟶ S --ε--> A ⟶ S ⟶ 0`. -/
@[simp]
theorem jordanHolderMultiplicity_dualNumber_dualNumberResidue :
    jordanHolderMultiplicity (DualNumber k) (DualNumber k) (dualNumberResidue k) = 2 := by
  rw [jordanHolderMultiplicity_eq_add_of_exact _ _ (dualNumberResidueToFree_injective k)
    (dualNumberProj_surjective k) (exact_dualNumberResidueToFree_dualNumberProj k),
    jordanHolderMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv _ (LinearEquiv.refl _ _)]

/-! ### The Cartan map and matrix -/

/-- The rank-one free module over `k[ε]`, as an object of the category of finitely generated
projective modules. -/
noncomputable abbrev dualNumberFreeProj :
    (finiteProjectiveModules (DualNumber k)).FullSubcategory :=
  ⟨dualNumberFree k, finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩

/-- The residue module `k[ε]/(ε)`, as an object of the category of finitely generated modules. -/
noncomputable abbrev dualNumberResidueFG : FGModuleCat.{u} (DualNumber k) :=
  FGModuleCat.of (DualNumber k) (dualNumberResidue k)

/-- `k[ε]` is, up to isomorphism, the only indecomposable finitely generated projective
`k[ε]`-module. -/
theorem isExhaustiveIndecomposableProjectiveFamily_dualNumberFreeProj :
    IsExhaustiveIndecomposableProjectiveFamily fun _ : Unit ↦ dualNumberFreeProj k :=
  isExhaustiveIndecomposableProjectiveFamily_of_isLocalRing _ (LinearEquiv.refl _ _)

/-- `k[ε]/(ε)` is, up to isomorphism, the only simple finitely generated `k[ε]`-module. -/
theorem isExhaustiveSimpleFamily_dualNumberResidueFG :
    IsExhaustiveSimpleFamily fun _ : Unit ↦ dualNumberResidueFG k :=
  isExhaustiveSimpleFamily_of_isLocalRing _

/-! ### The residue field has no finite projective resolution -/

end TauCeti
