/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Curves.Derivations
import Tengoku.Seed.Algebra.DualNumber

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Infinitesimal automorphisms and derivations

An automorphism over the dual numbers which reduces to the identity has
the form `f ↦ f + ε D(f)`.  Multiplicativity is exactly the Leibniz
rule, and changing `D` to `-D` gives the inverse.  This module packages
that elementary correspondence without invoking schemes or algebraic
groups, then applies the regular-derivation theorems to the resulting
infinitesimal automorphisms.

This is the infinitesimal-automorphism bridge in blueprint Lemma 8.4.

**Status:** in progress (M4b, issue #13, P7).
-/

namespace AclGeom

noncomputable section

open scoped DualNumber
open TrivSqZeroExt

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- A `k`-algebra automorphism of `F[ε]` which fixes `ε` and reduces to
the identity on `F` modulo `ε`.-/
structure InfinitesimalAutomorphism (k F : Type*) [Field k] [Field F]
    [Algebra k F] where
  /-- The underlying automorphism of the dual-number algebra.-/
  toAlgEquiv : DualNumber F ≃ₐ[k] DualNumber F
  /-- Reduction modulo `ε` is the identity on constant dual numbers.-/
  fst_map_inl' : ∀ x : F, (toAlgEquiv (inl x)).fst = x
  /-- The infinitesimal parameter is fixed.-/
  map_eps' : toAlgEquiv (DualNumber.eps : DualNumber F) = DualNumber.eps

namespace InfinitesimalAutomorphism

instance : CoeFun (InfinitesimalAutomorphism k F)
    (fun _ ↦ DualNumber F → DualNumber F) :=
  ⟨fun σ ↦ σ.toAlgEquiv⟩

/--
@isnad1 id=eq.1h4v.s8.a00d3e448819 from=translated src=- shape=ac13fb15 vocab=acde8063
-/
@[ext]
theorem ext {σ τ : InfinitesimalAutomorphism k F}
    (h : σ.toAlgEquiv = τ.toAlgEquiv) : σ = τ := by
  cases σ
  cases τ
  cases h
  rfl

/--
@isnad1 id=eq.0h4v.s8.ed7007cdd51c from=translated src=- shape=3dce1bba vocab=ef3a6d72
-/
@[simp]
theorem fst_map_inl (σ : InfinitesimalAutomorphism k F) (x : F) :
    (σ (inl x)).fst = x := σ.fst_map_inl' x

/--
@isnad1 id=eq.0h3v.s9.3b3b854ffc77 from=translated src=- shape=d4f2e5e6 vocab=44dce374
-/
@[simp]
theorem map_eps (σ : InfinitesimalAutomorphism k F) :
    σ (DualNumber.eps : DualNumber F) = DualNumber.eps := σ.map_eps'

/-- A derivation acts on dual numbers by
`(x + yε) ↦ x + (y + D x)ε`.-/
def ofDerivationAlgEquiv (D : Derivation k F F) :
    DualNumber F ≃ₐ[k] DualNumber F where
  toFun z := (z.fst, z.snd + D z.fst)
  invFun z := (z.fst, z.snd - D z.fst)
  left_inv z := by
    apply TrivSqZeroExt.ext <;> simp
  right_inv z := by
    apply TrivSqZeroExt.ext <;> simp
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · rfl
    · change x.fst * y.snd + x.snd * y.fst +
          D (x.fst * y.fst) =
        x.fst * (y.snd + D y.fst) +
          (x.snd + D x.fst) * y.fst
      rw [D.leibniz]
      simp only [smul_eq_mul]
      ring
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · rfl
    · change x.snd + y.snd + D (x.fst + y.fst) =
        x.snd + D x.fst + (y.snd + D y.fst)
      rw [D.map_add]
      abel
  commutes' c := by
    apply TrivSqZeroExt.ext
    · rfl
    · simp only [TrivSqZeroExt.algebraMap_eq_inl', fst_inl, snd_inl,
        snd_mk, D.map_algebraMap, add_zero]

/-- The infinitesimal automorphism `1 + εD` attached to a derivation
`D`.-/
def ofDerivation (D : Derivation k F F) :
    InfinitesimalAutomorphism k F where
  toAlgEquiv := ofDerivationAlgEquiv D
  fst_map_inl' := by
    intro x
    rfl
  map_eps' := by
    apply TrivSqZeroExt.ext
    · rfl
    · change 1 + D 0 = 1
      rw [map_zero, add_zero]

/--
@isnad1 id=eq.0h4v.s9.29df3f1ad603 from=translated src=- shape=0efb85ea vocab=e3d6b8dd
-/
@[simp]
theorem ofDerivation_apply (D : Derivation k F F) (z : DualNumber F) :
    ofDerivation D z = (z.fst, z.snd + D z.fst) := rfl

/--
@isnad1 id=eq.0h4v.s9.5e2c4655a4c8 from=translated src=- shape=f4f26e1b vocab=f478beaf
-/
@[simp]
theorem ofDerivation_apply_inl (D : Derivation k F F) (x : F) :
    ofDerivation D (inl x) = (x, D x) := by
  apply TrivSqZeroExt.ext
  · rfl
  · change 0 + D x = D x
    rw [zero_add]

/--
@isnad1 id=eq.0h3v.s9.b2070cec513b from=translated src=- shape=e417f14e vocab=78e6b92c
-/
@[simp]
theorem ofDerivation_apply_eps (D : Derivation k F F) :
    ofDerivation D (DualNumber.eps : DualNumber F) = DualNumber.eps := by
  exact (ofDerivation D).map_eps

/-- Extract the coefficient of `ε` in the image of each constant
dual number.-/
def toDerivation (σ : InfinitesimalAutomorphism k F) :
    Derivation k F F where
  toLinearMap :=
    { toFun := fun x ↦ (σ (inl x)).snd
      map_add' := by
        intro x y
        change (σ (inl (x + y))).snd =
          (σ (inl x)).snd + (σ (inl y)).snd
        rw [inl_add, map_add, snd_add]
      map_smul' := by
        intro c x
        change (σ (inl (c • x))).snd = c • (σ (inl x)).snd
        rw [inl_smul, map_smul, snd_smul] }
  map_one_eq_zero' := by
    change (σ (inl (1 : F))).snd = 0
    rw [inl_one, map_one]
    exact snd_one
  leibniz' := by
    intro x y
    change (σ (inl (x * y))).snd =
      x • (σ (inl y)).snd + y • (σ (inl x)).snd
    rw [inl_mul, map_mul, DualNumber.snd_mul,
      σ.fst_map_inl, σ.fst_map_inl]
    simp only [smul_eq_mul]
    ring

/--
@isnad1 id=eq.0h4v.s9.b435a4f93dfe from=translated src=- shape=3e3daa85 vocab=ee8f0142
-/
@[simp]
theorem toDerivation_apply (σ : InfinitesimalAutomorphism k F)
    (x : F) : σ.toDerivation x = (σ (inl x)).snd := rfl

/-- Every infinitesimal automorphism fixes the pure `ε`-part.
@isnad1 id=eq.0h4v.s8.e63d56d2d6e0 from=translated src=- shape=37f3b447 vocab=459424ff
-/
@[simp]
theorem map_inr (σ : InfinitesimalAutomorphism k F) (x : F) :
    σ (inr x) = inr x := by
  have hinr : (inl x : DualNumber F) * DualNumber.eps = inr x := by
    apply TrivSqZeroExt.ext
    · simp only [fst_mul, fst_inl, DualNumber.fst_eps, fst_inr,
        mul_zero]
    · simp only [DualNumber.snd_mul, fst_inl, DualNumber.snd_eps,
        snd_inl, DualNumber.fst_eps, snd_inr, mul_one, mul_zero,
        add_zero]
  calc
    σ (inr x) = σ ((inl x : DualNumber F) * DualNumber.eps) := by
      rw [hinr]
    _ = σ (inl x) * σ DualNumber.eps := map_mul _ _ _
    _ = inr x := by
      rw [σ.map_eps]
      apply TrivSqZeroExt.ext
      · simp only [fst_mul, σ.fst_map_inl, DualNumber.fst_eps,
          fst_inr, mul_zero]
      · simp only [DualNumber.snd_mul, σ.fst_map_inl,
          DualNumber.snd_eps, DualNumber.fst_eps, snd_inr, mul_one,
          mul_zero, add_zero]

/--
@isnad1 id=eq.0h3v.s7.5fa755f5aa43 from=translated src=- shape=998d9fc6 vocab=74043831
-/
@[simp]
theorem toDerivation_ofDerivation (D : Derivation k F F) :
    (ofDerivation D).toDerivation = D := by
  ext x
  change 0 + D x = D x
  rw [zero_add]

/--
@isnad1 id=eq.0h3v.s5.7f3c0880aa02 from=translated src=- shape=19868076 vocab=f13a30e2
-/
@[simp]
theorem ofDerivation_toDerivation
    (σ : InfinitesimalAutomorphism k F) :
    ofDerivation σ.toDerivation = σ := by
  apply InfinitesimalAutomorphism.ext
  apply AlgEquiv.ext
  intro z
  rw [← z.inl_fst_add_inr_snd_eq, map_add, map_add, σ.map_inr]
  apply TrivSqZeroExt.ext
  · simp
    exact add_zero z.fst
  · simp
    rfl

/-- `k`-derivations of `F` are equivalent to infinitesimal
automorphisms of `F[ε]` reducing to the identity.-/
def derivationEquiv :
    Derivation k F F ≃ InfinitesimalAutomorphism k F where
  toFun := ofDerivation
  invFun := toDerivation
  left_inv := toDerivation_ofDerivation
  right_inv := ofDerivation_toDerivation

/-- Regularity of an infinitesimal automorphism means regularity of
its associated vector field at every place.-/
def IsRegular [IsAlgClosed k] [IsFunctionFieldOneVar k F]
    (σ : InfinitesimalAutomorphism k F) : Prop :=
  DerivationIsRegular σ.toDerivation

/-- An infinitesimal automorphism fixes a place to first order when
its associated vector field vanishes there.-/
def VanishesAt [IsAlgClosed k] [IsFunctionFieldOneVar k F]
    (σ : InfinitesimalAutomorphism k F) (P : Place k F) : Prop :=
  DerivationVanishesAt σ.toDerivation P

/-- The identity infinitesimal automorphism.-/
def refl : InfinitesimalAutomorphism k F :=
  ofDerivation 0

/--
@isnad1 id=eq.0h3v.s8.884e88e0c382 from=translated src=- shape=eee87abb vocab=08eb4214
-/
@[simp]
theorem refl_apply (z : DualNumber F) :
    refl (k := k) (F := F) z = z := by
  apply TrivSqZeroExt.ext <;> simp [refl]

end InfinitesimalAutomorphism

end

end AclGeom
