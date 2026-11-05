/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Tengoku.AclGeom.AclGeom.Correspondence.Composition
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.FieldTheory.Normal.Closure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite covers carried by selected correspondence branches

A selected finite-correspondence pair `(x,y)` determines three concrete
subfields of the ambient algebraically closed field: `k(x)`, `k(y)`, and
`k(x,y)`.  Interalgebraicity says exactly that the joint branch field is a
finite extension of either endpoint field.  This is the field-theoretic
finite cover needed before passing to normal closures and gluing the
selected correspondence groupoid.

This module is part of the finite-cover integration in blueprint §8.1.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

namespace FiniteCover

variable {E L : IntermediateField k Ω}

/-- An equivalence between two nested intermediate-field extensions.

Both the base and total fields are transported as `k`-algebras, and the
displayed square with the two inclusions commutes.  This is the appropriate
notion of equivalence when the coefficient field varies: an equivalence of
the total fields alone does not remember which finite extension is being
normalized.-/
structure ExtensionEquiv {E L E' L' : IntermediateField k Ω}
    (h : E ≤ L) (h' : E' ≤ L') where
  /-- Equivalence of the base fields.-/
  baseEquiv : (↥E) ≃ₐ[k] (↥E')
  /-- Equivalence of the total fields.-/
  totalEquiv : (↥L) ≃ₐ[k] (↥L')
  /-- The total-field equivalence restricts to the base-field equivalence.-/
  commutes :
    totalEquiv.toAlgHom.comp (IntermediateField.inclusion h) =
      (IntermediateField.inclusion h').comp baseEquiv.toAlgHom

namespace ExtensionEquiv

variable {E L E' L' E'' L'' : IntermediateField k Ω}
  {h : E ≤ L} {h' : E' ≤ L'} {h'' : E'' ≤ L''}

/-- Two extension equivalences are equal when their base and total
equivalences are equal.-/
@[ext] theorem ext {e e' : ExtensionEquiv h h'}
    (hbase : e.baseEquiv = e'.baseEquiv)
    (htotal : e.totalEquiv = e'.totalEquiv) : e = e' := by
  cases e
  cases e'
  cases hbase
  cases htotal
  rfl

/-- Pointwise form of the commutative-square condition.-/
@[simp] theorem commutes_apply (e : ExtensionEquiv h h') (x : E) :
    e.totalEquiv (IntermediateField.inclusion h x) =
      IntermediateField.inclusion h' (e.baseEquiv x) :=
  DFunLike.congr_fun e.commutes x

/-- The identity equivalence of a nested extension.-/
def refl (h : E ≤ L) : ExtensionEquiv h h where
  baseEquiv := AlgEquiv.refl
  totalEquiv := AlgEquiv.refl
  commutes := rfl

/-- Equal nested intermediate fields determine an extension equivalence.
The inclusion proofs themselves are immaterial.-/
def ofEq (hE : E = E') (hL : L = L') : ExtensionEquiv h h' := by
  subst E'
  subst L'
  exact refl h

/-- The base equivalence of an equality-induced extension equivalence is
the canonical equality-induced equivalence.-/
@[simp] theorem ofEq_baseEquiv (hE : E = E') (hL : L = L') :
    (ofEq (h := h) (h' := h') hE hL).baseEquiv =
      IntermediateField.equivOfEq hE := by
  subst E'
  subst L'
  have hh : h' = h := Subsingleton.elim _ _
  subst h'
  rfl

/-- Reverse an equivalence of nested extensions.-/
def symm (e : ExtensionEquiv h h') : ExtensionEquiv h' h where
  baseEquiv := e.baseEquiv.symm
  totalEquiv := e.totalEquiv.symm
  commutes := by
    apply AlgHom.ext
    intro x
    apply e.totalEquiv.injective
    simp

/-- Compose equivalences of nested extensions.-/
def trans (e : ExtensionEquiv h h') (e' : ExtensionEquiv h' h'') :
    ExtensionEquiv h h'' where
  baseEquiv := e.baseEquiv.trans e'.baseEquiv
  totalEquiv := e.totalEquiv.trans e'.totalEquiv
  commutes := by
    apply AlgHom.ext
    intro x
    simp

@[simp] theorem refl_baseEquiv (h : E ≤ L) :
    (refl h).baseEquiv = AlgEquiv.refl := rfl

@[simp] theorem refl_totalEquiv (h : E ≤ L) :
    (refl h).totalEquiv = AlgEquiv.refl := rfl

@[simp] theorem symm_baseEquiv (e : ExtensionEquiv h h') :
    e.symm.baseEquiv = e.baseEquiv.symm := rfl

@[simp] theorem symm_totalEquiv (e : ExtensionEquiv h h') :
    e.symm.totalEquiv = e.totalEquiv.symm := rfl

@[simp] theorem trans_baseEquiv (e : ExtensionEquiv h h')
    (e' : ExtensionEquiv h' h'') :
    (e.trans e').baseEquiv = e.baseEquiv.trans e'.baseEquiv := rfl

@[simp] theorem trans_totalEquiv (e : ExtensionEquiv h h')
    (e' : ExtensionEquiv h' h'') :
    (e.trans e').totalEquiv = e.totalEquiv.trans e'.totalEquiv := rfl

end ExtensionEquiv

/-- Finite-dimensionality is insensitive to equality-based changes of the
displayed base and total intermediate fields.  Packaging the dependent
transport here avoids rewriting through the inclusion proof in
`extendScalars`.-/
theorem finiteDimensional_of_eq
    {E L E' L' : IntermediateField k Ω}
    (h : E ≤ L) (h' : E' ≤ L') (hE : E = E') (hL : L = L')
    (hfin : FiniteDimensional (↥E') (↥(extendScalars h'))) :
    FiniteDimensional (↥E) (↥(extendScalars h)) := by
  subst E'
  subst L'
  exact hfin

/-- Normal closure is invariant under equivalences of both the original
extension and the ambient algebraically closed field, when the base is
fixed.  This is the functorial form of the `iSup`-of-field-ranges
definition.-/
theorem map_normalClosure_eq_of_equiv
    {F K K' A A' : Type*}
    [Field F] [Field K] [Field K'] [Field A] [Field A']
    [Algebra F K] [Algebra F K'] [Algebra F A] [Algebra F A']
    (eK : K ≃ₐ[F] K') (eA : A ≃ₐ[F] A') :
    (normalClosure F K A).map eA.toAlgHom =
      normalClosure F K' A' := by
  simp only [normalClosure_def]
  rw [IntermediateField.map_iSup]
  simp_rw [AlgHom.map_fieldRange]
  rw [← (AlgEquiv.arrowCongr eK eA).iSup_comp]
  apply iSup_congr
  intro f
  ext x
  change (∃ y, eA (f y) = x) ↔
    ∃ y, eA (f (eK.symm y)) = x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨eK y, by simp⟩
  · rintro ⟨y, rfl⟩
    exact ⟨eK.symm y, rfl⟩

/-- If the lower scalar map is surjective, taking a normal closure is
unchanged by restricting scalars along that map.  In particular this
applies when the two base fields are equivalent.-/
theorem normalClosure_restrictScalars_of_surjective
    {F F' K A : Type*}
    [Field F] [Field F'] [Field K] [Field A]
    [Algebra F F'] [Algebra F K] [Algebra F A]
    [Algebra F' K] [Algebra F' A]
    [IsScalarTower F F' K] [IsScalarTower F F' A]
    (hsurj : Function.Surjective (algebraMap F F')) :
    normalClosure F K A =
      (normalClosure F' K A).restrictScalars F := by
  let upgrade (g : K →ₐ[F] A) : K →ₐ[F'] A :=
    { g.toRingHom with
      commutes' := fun x ↦ by
        obtain ⟨y, rfl⟩ := hsurj x
        simp only [← IsScalarTower.algebraMap_apply]
        exact g.commutes y }
  apply le_antisymm
  · rw [normalClosure_le_iff]
    intro g
    rintro _ ⟨x, rfl⟩
    exact (AlgHom.fieldRange_le_normalClosure (upgrade g)) ⟨x, rfl⟩
  · let N : IntermediateField F A := normalClosure F K A
    let N' : IntermediateField F' A :=
      { N.toSubfield with
        algebraMap_mem' := fun x ↦ by
          obtain ⟨y, rfl⟩ := hsurj x
          rw [← IsScalarTower.algebraMap_apply F F' A]
          exact N.algebraMap_mem y }
    change normalClosure F' K A ≤ N'
    rw [normalClosure_le_iff]
    intro g
    rintro _ ⟨x, rfl⟩
    exact (AlgHom.fieldRange_le_normalClosure
      (g.restrictScalars F)) ⟨x, rfl⟩

/-- The normal closure in the ambient field of a nested intermediate-field
extension.-/
def normalClosureOver (h : E ≤ L) : IntermediateField (↥E) Ω :=
  normalClosure (↥E) (extendScalars h) Ω

/-- The original finite extension embeds literally in its ambient normal
closure.-/
theorem extendScalars_le_normalClosureOver (h : E ≤ L) :
    extendScalars h ≤ normalClosureOver h :=
  le_normalClosure _

/-- A canonical model of the normal closure inside the algebraic closure
of the base field.  Unlike `normalClosureOver`, this model does not depend
on the original ambient algebraically closed field.-/
def canonicalNormalClosure (h : E ≤ L) :
    IntermediateField (↥E) (AlgebraicClosure (↥E)) :=
  normalClosure (↥E) (extendScalars h) (AlgebraicClosure (↥E))

/-- The canonical normal closure of a finite extension is finite.-/
theorem canonicalNormalClosure_finiteDimensional (h : E ≤ L)
    (hfin : FiniteDimensional (↥E) (↥(extendScalars h))) :
    FiniteDimensional (↥E) (↥(canonicalNormalClosure h)) := by
  letI := hfin
  exact normalClosure.is_finiteDimensional
    (↥E) (↥(extendScalars h)) (AlgebraicClosure (↥E))

/-- The canonical normal closure is normal over its base.-/
theorem canonicalNormalClosure_normal (h : E ≤ L)
    (halg : Algebra.IsAlgebraic (↥E) (↥(extendScalars h))) :
    Normal (↥E) (↥(canonicalNormalClosure h)) := by
  letI := halg
  exact
    (Algebra.IsAlgebraic.isNormalClosure_normalClosure
      (F := ↥E) (K := ↥(extendScalars h))
      (L := AlgebraicClosure (↥E))
      (fun _ ↦ IsAlgClosed.splits _)).normal

/-- The ambient and canonical constructions are equivalent normal closures
of the same algebraic extension.-/
def normalClosureOverEquivCanonical [IsAlgClosed Ω] (h : E ≤ L)
    (halg : Algebra.IsAlgebraic (↥E) (↥(extendScalars h))) :
    (↥(normalClosureOver h)) ≃ₐ[↥E] (↥(canonicalNormalClosure h)) := by
  letI := halg
  letI : IsNormalClosure (↥E) (↥(extendScalars h))
      (↥(normalClosureOver h)) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure
      (F := ↥E) (K := ↥(extendScalars h)) (L := Ω)
      (fun _ ↦ IsAlgClosed.splits _)
  letI : IsNormalClosure (↥E) (↥(extendScalars h))
      (↥(canonicalNormalClosure h)) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure
      (F := ↥E) (K := ↥(extendScalars h))
      (L := AlgebraicClosure (↥E))
      (fun _ ↦ IsAlgClosed.splits _)
  exact IsNormalClosure.equiv
    (F := ↥E) (K := ↥(extendScalars h))
    (L := ↥(normalClosureOver h))
    (L' := ↥(canonicalNormalClosure h))

/-- The literal ambient branch, transported into the canonical normal
closure.  This records a distinguished branch in the canonical model;
using only uniqueness of normal closures would otherwise forget which
conjugate was selected in the original ambient field.-/
noncomputable def canonicalSelectedEmbedding [IsAlgClosed Ω] (h : E ≤ L)
    (halg : Algebra.IsAlgebraic (↥E) (↥(extendScalars h))) :
    (↥(extendScalars h)) →ₐ[↥E] (↥(canonicalNormalClosure h)) :=
  (normalClosureOverEquivCanonical h halg).toAlgHom.comp
    (IntermediateField.inclusion (extendScalars_le_normalClosureOver h))

/-- A compatible equivalence of finite extensions together with an
equivalence of their canonical normal closures.  The normal-cover map is
semilinear over the displayed base equivalence.  Keeping this as explicit
data records the unavoidable choice in uniqueness of normal closures while
still supporting coherent identity, inverse, and composition operations.-/
structure NormalExtensionEquiv
    {E L E' L' : IntermediateField k Ω}
    (h : E ≤ L) (h' : E' ≤ L') extends ExtensionEquiv h h' where
  /-- Equivalence of the canonical normal-cover fields.-/
  normalEquiv :
    (↥(canonicalNormalClosure h)) ≃+*
      (↥(canonicalNormalClosure h'))
  /-- The normal-cover equivalence extends the base-field equivalence.-/
  normal_commutes :
    normalEquiv.toRingHom.comp
        (algebraMap (↥E) (↥(canonicalNormalClosure h))) =
      (algebraMap (↥E') (↥(canonicalNormalClosure h'))).comp
        baseEquiv.toRingEquiv.toRingHom

namespace NormalExtensionEquiv

variable {E L E' L' E'' L'' : IntermediateField k Ω}
  {h : E ≤ L} {h' : E' ≤ L'} {h'' : E'' ≤ L''}

/-- Pointwise form of compatibility on the normal covers.-/
@[simp] theorem normal_commutes_apply (e : NormalExtensionEquiv h h')
    (x : E) :
    e.normalEquiv
        (algebraMap (↥E) (↥(canonicalNormalClosure h)) x) =
      algebraMap (↥E') (↥(canonicalNormalClosure h'))
        (e.baseEquiv x) :=
  DFunLike.congr_fun e.normal_commutes x

/-- Normal-extension equivalences are determined by their extension square
and their normal-cover equivalence.-/
@[ext] theorem ext {e e' : NormalExtensionEquiv h h'}
    (hext : e.toExtensionEquiv = e'.toExtensionEquiv)
    (hnormal : e.normalEquiv = e'.normalEquiv) : e = e' := by
  cases e
  cases e'
  cases hext
  cases hnormal
  rfl

/-- Identity equivalence of an extension and its canonical normal cover.-/
def refl (h : E ≤ L) : NormalExtensionEquiv h h where
  toExtensionEquiv := ExtensionEquiv.refl h
  normalEquiv := RingEquiv.refl _
  normal_commutes := rfl

/-- Reverse a compatible normal-extension equivalence.-/
def symm (e : NormalExtensionEquiv h h') :
    NormalExtensionEquiv h' h where
  toExtensionEquiv := e.toExtensionEquiv.symm
  normalEquiv := e.normalEquiv.symm
  normal_commutes := by
    apply RingHom.ext
    intro x
    apply e.normalEquiv.injective
    simp

/-- Compose compatible normal-extension equivalences.-/
def trans (e : NormalExtensionEquiv h h')
    (e' : NormalExtensionEquiv h' h'') :
    NormalExtensionEquiv h h'' where
  toExtensionEquiv := e.toExtensionEquiv.trans e'.toExtensionEquiv
  normalEquiv := e.normalEquiv.trans e'.normalEquiv
  normal_commutes := by
    apply RingHom.ext
    intro x
    simp

end NormalExtensionEquiv

namespace ExtensionEquiv

variable {E L E' L' : IntermediateField k Ω}
  {h : E ≤ L} {h' : E' ≤ L'}

/-- Lift an equivalence of finite extensions to a compatible equivalence
of canonical normal closures.  The construction uses uniqueness of
algebraic closures, so the returned lift is chosen rather than strictly
functorial; `NormalExtensionEquiv.refl`, `.symm`, and `.trans` provide the
coherent operations on chosen lifts.-/
noncomputable def normalLift (e : ExtensionEquiv h h') :
    NormalExtensionEquiv h h' := by
  letI algEL : Algebra (↥E) (↥L) :=
    (IntermediateField.inclusion h).toRingHom.toAlgebra
  letI algE'L' : Algebra (↥E') (↥L') :=
    (IntermediateField.inclusion h').toRingHom.toAlgebra
  letI algEE' : Algebra (↥E) (↥E') :=
    e.baseEquiv.toRingEquiv.toRingHom.toAlgebra
  letI algEL' : Algebra (↥E) (↥L') :=
    ((IntermediateField.inclusion h').toRingHom.comp
      e.baseEquiv.toRingEquiv.toRingHom).toAlgebra
  letI towerEL' : IsScalarTower (↥E) (↥E') (↥L') :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let φr : AlgebraicClosure (↥E) ≃+* AlgebraicClosure (↥E') :=
    IsAlgClosure.equivOfEquiv
      (AlgebraicClosure (↥E)) (AlgebraicClosure (↥E'))
      e.baseEquiv.toRingEquiv
  let φ : AlgebraicClosure (↥E) ≃ₐ[↥E]
      AlgebraicClosure (↥E') :=
    { φr with
      commutes' := fun x ↦ by
        exact IsAlgClosure.equivOfEquiv_algebraMap
          (AlgebraicClosure (↥E)) (AlgebraicClosure (↥E'))
          e.baseEquiv.toRingEquiv x }
  let ψ : (↥L) ≃ₐ[↥E] (↥L') :=
    { e.totalEquiv.toRingEquiv with
      commutes' := fun x ↦ e.commutes_apply x }
  have hmap :
      (canonicalNormalClosure h).map φ.toAlgHom =
        (canonicalNormalClosure h').restrictScalars (↥E) := by
    calc
      (canonicalNormalClosure h).map φ.toAlgHom =
          normalClosure (↥E) (↥L') (AlgebraicClosure (↥E')) := by
        exact map_normalClosure_eq_of_equiv ψ φ
      _ = (canonicalNormalClosure h').restrictScalars (↥E) := by
        exact @normalClosure_restrictScalars_of_surjective
          (↥E) (↥E') (↥L') (AlgebraicClosure (↥E'))
          inferInstance inferInstance inferInstance inferInstance
          algEE' algEL' inferInstance algE'L' inferInstance
          towerEL' inferInstance e.baseEquiv.surjective
  let n : (↥(canonicalNormalClosure h)) ≃ₐ[↥E]
      (↥((canonicalNormalClosure h').restrictScalars (↥E))) :=
    (IntermediateField.equivMap (canonicalNormalClosure h) φ.toAlgHom).trans
      (IntermediateField.equivOfEq hmap)
  refine
    { toExtensionEquiv := e
      normalEquiv := n.toRingEquiv
      normal_commutes := ?_ }
  apply RingHom.ext
  intro x
  exact n.commutes x

@[simp] theorem normalLift_toExtensionEquiv (e : ExtensionEquiv h h') :
    e.normalLift.toExtensionEquiv = e := by
  simp [normalLift]

end ExtensionEquiv

/-- A normal closure of a finite extension remains finite.-/
theorem normalClosureOver_finiteDimensional (h : E ≤ L)
    (hfin : FiniteDimensional (↥E) (↥(extendScalars h))) :
    FiniteDimensional (↥E) (↥(normalClosureOver h)) := by
  letI := hfin
  exact normalClosure.is_finiteDimensional (↥E) (↥(extendScalars h)) Ω

/-- Inside an algebraically closed ambient field, the normal closure of an
algebraic extension is normal over its base.-/
theorem normalClosureOver_normal [IsAlgClosed Ω] (h : E ≤ L)
    (halg : Algebra.IsAlgebraic (↥E) (↥(extendScalars h))) :
    Normal (↥E) (↥(normalClosureOver h)) := by
  letI := halg
  exact
    (Algebra.IsAlgebraic.isNormalClosure_normalClosure
      (F := ↥E) (K := ↥(extendScalars h)) (L := Ω)
      (fun _ ↦ IsAlgClosed.splits _)).normal

/-- Embeddings of the original extension into the ambient field are
equivalent to embeddings into its normal closure.  Thus every conjugate
branch already lives on the normal cover.-/
def embeddingEquivNormal (h : E ≤ L) :
    ((↥(extendScalars h)) →ₐ[↥E] (↥(normalClosureOver h))) ≃
      ((↥(extendScalars h)) →ₐ[↥E] Ω) :=
  normalClosure.algHomEquiv (↥E) (↥(extendScalars h)) Ω

/-- The unique lift of an ambient embedding of the finite extension to
the normal cover.-/
def liftEmbedding (h : E ≤ L)
    (f : (↥(extendScalars h)) →ₐ[↥E] Ω) :
    (↥(extendScalars h)) →ₐ[↥E] (↥(normalClosureOver h)) :=
  (embeddingEquivNormal h).symm f

/-- Composing a lifted branch with the normal-cover inclusion recovers
the original ambient embedding.-/
@[simp] theorem normalClosure_val_comp_liftEmbedding (h : E ≤ L)
    (f : (↥(extendScalars h)) →ₐ[↥E] Ω) :
    (normalClosureOver h).val.comp (liftEmbedding h f) = f :=
  (embeddingEquivNormal h).apply_symm_apply f

/-- The literal selected component is the lift of the inclusion of the
original extension into the ambient field.-/
def selectedEmbedding (h : E ≤ L) :
    (↥(extendScalars h)) →ₐ[↥E] (↥(normalClosureOver h)) :=
  liftEmbedding h (extendScalars h).val

/-- The selected embedding evaluates to the original literal branch in
the ambient field.-/
@[simp] theorem normalClosure_val_comp_selectedEmbedding (h : E ≤ L) :
    (normalClosureOver h).val.comp (selectedEmbedding h) =
      (extendScalars h).val :=
  normalClosure_val_comp_liftEmbedding h _

/-- Embeddings of a finite normal cover into the ambient field are exactly
its automorphisms.-/
def normalEmbeddingEquivAut (h : E ≤ L)
    [Normal (↥E) (↥(normalClosureOver h))] :
    ((↥(normalClosureOver h)) →ₐ[↥E] Ω) ≃
      ((↥(normalClosureOver h)) ≃ₐ[↥E] (↥(normalClosureOver h))) :=
  Normal.algHomEquivAut (↥E) Ω (↥(normalClosureOver h))

end FiniteCover

namespace FiniteCorrespondencePair

variable (P : FiniteCorrespondencePair k Ω)

/-- The one-variable function field generated by the source coordinate.-/
def sourceField : IntermediateField k Ω :=
  adjoin k {P.source}

/-- The one-variable function field generated by the target coordinate.-/
def targetField : IntermediateField k Ω :=
  adjoin k {P.target}

/-- The joint function field of the selected correspondence branch.-/
def branchField : IntermediateField k Ω :=
  adjoin k {P.source, P.target}

/-- The source function field embeds in the selected branch field.-/
theorem sourceField_le_branchField : P.sourceField ≤ P.branchField :=
  adjoin.mono k _ _ (by simp)

/-- The target function field embeds in the selected branch field.-/
theorem targetField_le_branchField : P.targetField ≤ P.branchField :=
  adjoin.mono k _ _ (by simp)

/-- The selected branch field regarded as a cover of its source field.-/
def branchOverSource : IntermediateField (↥P.sourceField) Ω :=
  extendScalars P.sourceField_le_branchField

/-- The selected branch field regarded as a cover of its target field.-/
def branchOverTarget : IntermediateField (↥P.targetField) Ω :=
  extendScalars P.targetField_le_branchField

/-- Over the source field, the branch field is generated by the target.-/
theorem branchOverSource_eq_adjoin_target :
    P.branchOverSource = adjoin (↥P.sourceField) {P.target} := by
  refine restrictScalars_injective k ?_
  unfold branchOverSource
  rw [extendScalars_restrictScalars]
  unfold sourceField branchField
  rw [adjoin_adjoin_left]
  simp only [Set.union_singleton, Set.pair_comm]

/-- The selected branch is a finite cover of its source function field.-/
theorem branchOverSource_finiteDimensional :
    FiniteDimensional (↥P.sourceField) (↥P.branchOverSource) := by
  rw [P.branchOverSource_eq_adjoin_target]
  exact finiteDimensional_adjoin fun x hx ↦ by
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ((mem_racl_iff k).1 P.target_mem_source).isIntegral

/-- The normal closure of the selected branch over its source function
field, taken inside the ambient algebraically closed field.-/
def sourceNormalField : IntermediateField (↥P.sourceField) Ω :=
  FiniteCover.normalClosureOver P.sourceField_le_branchField

/-- The normal closure of the selected branch over its target function
field.-/
def targetNormalField : IntermediateField (↥P.targetField) Ω :=
  FiniteCover.normalClosureOver P.targetField_le_branchField

/-- The joint field of two consecutive selected branches.-/
def chainField (Q : FiniteCorrespondencePair k Ω) :
    IntermediateField k Ω :=
  adjoin k {P.source, P.target, Q.target}

/-- The left branch field embeds in the joint chain field.-/
theorem branchField_le_chainField (Q : FiniteCorrespondencePair k Ω) :
    P.branchField ≤ P.chainField Q := by
  unfold branchField chainField
  apply adjoin.mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

/-- When the middle coordinates agree, the right branch field embeds in
the joint chain field.-/
theorem rightBranchField_le_chainField
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    Q.branchField ≤ P.chainField Q :=
  adjoin.mono k _ _ (by simp [← h])

/-- The endpoint branch selected by composition embeds in the joint chain
field.-/
theorem compositeBranchField_le_chainField
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    (P.comp Q h).branchField ≤ P.chainField Q := by
  unfold branchField chainField
  apply adjoin.mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)

/-- The chain field as an extension of the left branch field.-/
def chainOverLeft (Q : FiniteCorrespondencePair k Ω) :
    IntermediateField (↥P.branchField) Ω :=
  extendScalars (P.branchField_le_chainField Q)

/-- The chain field as an extension of the right branch field.-/
def chainOverRight (Q : FiniteCorrespondencePair k Ω)
    (h : P.target = Q.source) : IntermediateField (↥Q.branchField) Ω :=
  extendScalars (P.rightBranchField_le_chainField Q h)

/-- The chain field as an extension of the composite endpoint branch.-/
def chainOverComposite (Q : FiniteCorrespondencePair k Ω)
    (h : P.target = Q.source) :
    IntermediateField (↥(P.comp Q h).branchField) Ω :=
  extendScalars (P.compositeBranchField_le_chainField Q h)

/-- Over the composite endpoint branch, the chain field is generated by
the shared middle coordinate.-/
theorem chainOverComposite_eq_adjoin_middle
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    P.chainOverComposite Q h =
      adjoin (↥(P.comp Q h).branchField) {P.target} := by
  refine restrictScalars_injective k ?_
  unfold chainOverComposite
  rw [extendScalars_restrictScalars]
  unfold branchField chainField
  rw [adjoin_adjoin_left]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  tauto

/-- The joint chain field is finite over the selected composite endpoint
branch.-/
theorem chainOverComposite_finiteDimensional
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    FiniteDimensional (↥(P.comp Q h).branchField)
      (↥(P.chainOverComposite Q h)) := by
  rw [P.chainOverComposite_eq_adjoin_middle Q h]
  exact finiteDimensional_adjoin fun x hx ↦ by
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact (isAlgebraic_of_le
      (P.comp Q h).sourceField_le_branchField
      ((mem_racl_iff k).1 P.target_mem_source)).isIntegral

/-- The normal closure of a chain field over its selected composite
endpoint branch.  It adjoins all ambient conjugates of the shared middle
coordinate.-/
def chainNormalOverComposite
    (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    IntermediateField (↥(P.comp Q h).branchField) Ω :=
  FiniteCover.normalClosureOver
    (P.compositeBranchField_le_chainField Q h)

end FiniteCorrespondencePair

end

end AclGeom
