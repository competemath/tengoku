/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.NumberTheory.NumberField.AdeleRing
import Tengoku.Seed.NumberTheory.NumberField.Completion.FinitePlace
import Tengoku.Seed.Topology.Algebra.Group.Units

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.ClassfieldtheoryYamaguchi end Tengoku.ClassfieldtheoryYamaguchi open Tengoku.ClassfieldtheoryYamaguchi
set_option autoImplicit false

/-!
# Ideles of a number field

This file defines the ideles of a number field.

The finite ideles are defined as the restricted product of the multiplicative
groups of the finite completions with respect to the unit groups of their
valuation rings.  This is deliberately not the topology induced from the
finite adele ring: the latter is not the idele topology.  The infinite factor
is the unit group of the finite product of the archimedean completions.
-/

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The finite idele group attached to a Dedekind domain and its fraction
field.  The number-field definition below specializes this to the ring of
integers.-/
abbrev _root_.Tengoku.ClassfieldtheoryYamaguchi.FiniteIdeleGroupOf
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F] :=
  Πʳ v : HeightOneSpectrum R,
    [(v.adicCompletion F)ˣ, (v.adicCompletionIntegers F).units]

/-- The group of finite ideles of a number field.-/
abbrev _root_.Tengoku.ClassfieldtheoryYamaguchi.FiniteIdeleGroup :=
  FiniteIdeleGroupOf (𝓞 K) K

/-- The product of the multiplicative groups of the archimedean completions.-/
abbrev _root_.Tengoku.ClassfieldtheoryYamaguchi.InfiniteIdeleGroup :=
  (NumberField.InfiniteAdeleRing K)ˣ

/-- The idele group `I_K`.-/
abbrev _root_.Tengoku.ClassfieldtheoryYamaguchi.IdeleGroup :=
  InfiniteIdeleGroup K × FiniteIdeleGroup K

namespace Tengoku.ClassfieldtheoryYamaguchi.FiniteIdeleGroup

variable {K}

/-- Evaluation of a finite idele at a finite place.-/
def component (v : HeightOneSpectrum (𝓞 K)) :
    FiniteIdeleGroup K →* (v.adicCompletion K)ˣ where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl

/--
@isnad1 id=eq.0h3v.s11.300a67d07dfc from=translated src=- shape=5fabff8a vocab=b4a19dbe
-/
@[simp]
theorem component_apply (a : FiniteIdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    component v a = a v :=
  rfl

/-- A finite idele is a local integral unit at all but finitely many finite
places.
@isnad1 id=eventual.0h2v.s11.14224136d681 from=translated src=- shape=bc2c9a2b vocab=f683633b
-/
theorem eventually_mem_localUnits (a : FiniteIdeleGroup K) :
    ∀ᶠ v in Filter.cofinite,
      a v ∈ (v.adicCompletionIntegers K).units :=
  a.2

end Tengoku.ClassfieldtheoryYamaguchi.FiniteIdeleGroup

namespace Tengoku.ClassfieldtheoryYamaguchi.InfiniteIdeleGroup

variable {K}

/-- The component of an infinite idele at an archimedean place.-/
def component (v : InfinitePlace K) :
    InfiniteIdeleGroup K →* v.Completionˣ :=
  (Pi.evalMonoidHom (fun w : InfinitePlace K ↦ w.Completionˣ) v).comp
    ContinuousMulEquiv.piUnits.toMonoidHom

omit [NumberField K] in
/--
@isnad1 id=eq.0h3v.s10.c6e790e17c6c from=translated src=- shape=7760bc9d vocab=5ac0a822
-/
@[simp]
theorem component_apply (a : InfiniteIdeleGroup K) (v : InfinitePlace K) :
    component v a = ContinuousMulEquiv.piUnits a v :=
  rfl

end Tengoku.ClassfieldtheoryYamaguchi.InfiniteIdeleGroup

namespace Tengoku.ClassfieldtheoryYamaguchi.IdeleGroup

variable {K}

/-- Algebraically, the finite ideles over a Dedekind domain are the units of
its finite adele ring.-/
def finiteEquivFiniteAdeleUnitsOf
  (R : Type*) [CommRing R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F] :
    FiniteIdeleGroupOf R F ≃*
    (IsDedekindDomain.FiniteAdeleRing R F)ˣ :=
  (RestrictedProduct.unitsEquiv
    (ι := HeightOneSpectrum R)
    (S := fun v : HeightOneSpectrum R ↦ ValuationSubring (v.adicCompletion F))
    (B := fun v : HeightOneSpectrum R ↦ v.adicCompletionIntegers F)
    (𝓕 := Filter.cofinite)
    (fun v : HeightOneSpectrum R ↦ v.adicCompletion F)).symm

/-- The component of an idele at an archimedean place.-/
def infiniteComponent (v : InfinitePlace K) :
    IdeleGroup K →* v.Completionˣ :=
  (InfiniteIdeleGroup.component v).comp (MonoidHom.fst _ _)

/-- The component of an idele at a finite place.-/
def finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup K →* (v.adicCompletion K)ˣ :=
  (FiniteIdeleGroup.component v).comp (MonoidHom.snd _ _)

/--
@isnad1 id=eq.0h3v.s11.b8e3ad2c9f7b from=translated src=- shape=b1a4d47a vocab=67cd5553
-/
@[simp]
theorem infiniteComponent_apply (a : IdeleGroup K) (v : InfinitePlace K) :
    infiniteComponent v a = ContinuousMulEquiv.piUnits a.1 v :=
  rfl

/--
@isnad1 id=eq.0h3v.s11.830c64bb1751 from=translated src=- shape=3516b842 vocab=133674f6
-/
@[simp]
theorem finiteComponent_apply (a : IdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    finiteComponent v a = a.2 v :=
  rfl

/-- Algebraically, the finite ideles are the units of the finite adele ring.
The topology on the left is the restricted-product topology and is not
transported through this equivalence.-/
def finiteEquivFiniteAdeleUnits :
    FiniteIdeleGroup K ≃*
      (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ :=
  finiteEquivFiniteAdeleUnitsOf (𝓞 K) K

/-- Algebraically, the idele group is the unit group of the adele ring.

This is only a multiplicative equivalence.  It is intentionally not stated as
a homeomorphism because the idele topology is finer than the topology induced
from the adele ring.-/
def equivAdeleRingUnits :
    IdeleGroup K ≃* (NumberField.AdeleRing (𝓞 K) K)ˣ :=
  ((MulEquiv.refl (InfiniteIdeleGroup K)).prodCongr
      (finiteEquivFiniteAdeleUnits (K := K))).trans
    MulEquiv.prodUnits.symm

/--
@isnad1 id=eq.0h2v.s12.f9e4217a599d from=translated src=- shape=5bc05344 vocab=322ac22f
-/
@[simp]
theorem equivAdeleRingUnits_fst (a : IdeleGroup K) :
    (MulEquiv.prodUnits (equivAdeleRingUnits a)).1 = a.1 := by
  rfl

/--
@isnad1 id=eq.0h2v.s13.cf5c1e7110c2 from=translated src=- shape=c3c8b6e1 vocab=e05b4c40
-/
@[simp]
theorem equivAdeleRingUnits_snd (a : IdeleGroup K) :
    (MulEquiv.prodUnits (equivAdeleRingUnits a)).2 =
      finiteEquivFiniteAdeleUnits (K := K) a.2 := by
  rfl

end Tengoku.ClassfieldtheoryYamaguchi.IdeleGroup
-- Tengoku: root names of this library moved to Tengoku.ClassfieldtheoryYamaguchi so they do not collide with other libraries (generated)
