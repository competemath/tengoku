/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Tengoku.Seed.Algebra.Category.Grp.Zero
public import Tengoku.ZanelloLc.FormalDeps.Port.Mathlib.Algebra.Category.ModuleCat.Baer
public import Tengoku.Seed.Algebra.Homology.ShortComplex.ModuleCat
public import Tengoku.Seed.CategoryTheory.Abelian.Injective.Dimension
public import Tengoku.Seed.CategoryTheory.Abelian.Projective.Dimension
public import Tengoku.Seed.LinearAlgebra.Dimension.Finite
public import Tengoku.Seed.RingTheory.LocalProperties.ProjectiveDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Global Dimension of a Ring

In this file, we define the global dimension of ring and proved some of its basic properties.

# Main definition and results

* `globalDimension` : The global (homological) dimension of a (commutative) ring defined as
  the supremum of projective dimension over all modules.

* `globalDimension_le_tfae` : For natrual number `n`, `globalDimension R ≤ n` iff all
  finitely generated modules over `R` has projective dimension not exceeding `n` iff for all
  `i ≥ n + 1`, `Ext N M i` vanish.

* `globalDimension_eq_sup_projectiveDimension_finite` : Global dimension is equal to the supremum of
  projective dimension over finitely generated modules.

# TODO

1. Take injective dimension into consideration in `globalDimension_le_tfae`.
2. Reduce vanishing of all `Ext N M i`, `i ≥ n + 1` to vanishing of `Ext N M (n + 1)`.
3. Prove that global dimension is invariant of universe if assuming `Small.{v} R`.

-/

@[expose] public section
namespace Tengoku.ZanelloLc end Tengoku.ZanelloLc open Tengoku.ZanelloLc 
universe v u

open CategoryTheory

section GlobalDimension

variable (R : Type u) [CommRing R]

open Abelian

/-- The global (homological) dimension of a (commutative) ring defined as
the supremum of projective dimension over all modules.-/
noncomputable def _root_.Tengoku.ZanelloLc.globalDimension : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{v} R), projectiveDimension.{v} M

lemma _root_.Tengoku.ZanelloLc.globalDimension_eq_bot_iff [Small.{v} R] : globalDimension.{v} R = ⊥ ↔ Subsingleton R := by
  simp only [globalDimension, iSup_eq_bot, projectiveDimension_eq_bot_iff,
    ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun h ↦ ?_, fun h M ↦ Module.subsingleton R M⟩
  let _ := h (ModuleCat.of R (Shrink.{v} R))
  exact (equivShrink.{v} R).subsingleton

lemma _root_.Tengoku.ZanelloLc.globalDimension_le_iff (n : ℕ) : globalDimension.{v} R ≤ n ↔
    ∀ M : ModuleCat.{v} R, HasProjectiveDimensionLE M n := by
  simp [globalDimension, projectiveDimension_le_iff]

lemma _root_.Tengoku.ZanelloLc.globalDimension_le_tfae [Small.{v} R] (n : ℕ) :
    [globalDimension.{v} R ≤ n,
    ∀ M : ModuleCat.{v} R, [Module.Finite R M] → HasProjectiveDimensionLE M n,
    ∀ m ≥ n + 1, ∀ (N M : ModuleCat.{v} R), Subsingleton (Ext N M m),
    ∀ M : ModuleCat.{v} R, HasInjectiveDimensionLE M n].TFAE := by
  tfae_have 1 → 2 := by
    simpa only [globalDimension, iSup_le_iff, projectiveDimension_le_iff]
      using fun h M _ ↦ h M
  tfae_have 2 → 3 := by
    exact fun h m ge N M ↦ ext_subsingleton_of_quotients M m
      (fun I ↦ ((h (ModuleCat.of R (Shrink.{v} (R ⧸ I)))).subsingleton _ _ _ ge M)) N
  tfae_have 3 → 1 := by
    intro h
    simp only [globalDimension, iSup_le_iff, projectiveDimension_le_iff]
    intro M
    exact HasProjectiveDimensionLT.mk (fun i hi {N} e ↦ @Subsingleton.eq_zero _ _ (h i hi M N) e)
  tfae_have 3 → 4 := by
    intro h M
    exact HasInjectiveDimensionLT.mk (fun i hi {N} e ↦ @Subsingleton.eq_zero _ _ (h i hi N M) e)
  tfae_have 4 → 3 := by
    intro h i hi N M
    exact (h M).subsingleton _ _ i hi N
  tfae_finish

end GlobalDimension

end
-- Tengoku: root names of this library moved to Tengoku.ZanelloLc so they do not collide with other libraries (generated)
