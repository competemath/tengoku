/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Random Set Theory - Foundations

## Overview

This file defines the fundamental objects of random set theory:

1. **RandomSet** : a measurable set-valued map from a probability space
2. **RandomSet.support** : the union of all realizations
3. **RandomSet.range** : the set of all possible values
4. **RandomSet.map** : image of a random set by a measurable function
5. **RandomSet.measurableSet** : measurability of the graph

We also define **RandomSetFamily** for families of random sets and
**RandomSetProcess** for stochastic processes of random sets.

## References

- Molchanov, I. (2005). *Theory of Random Sets*. Springer.
- Aumann, R. J. (1965). Integrals of set-valued functions.
- Castaing, C., & Valadier, M. (1979). *Convex analysis and measurable multifunctions*.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set
open MeasureTheory
open scoped Pointwise

noncomputable section

/-!
## 1. Random Sets - Definition
-/

/-- A membership-measurable set-valued map: for each `x`, the event
`{ω | x ∈ S ω}` is measurable.  This is the measurable-space structure on
`Set X` currently supplied by mathlib.  Classical random closed sets use
Effros measurability, defined separately below.-/
structure _root_.Tengoku.Randomsettheory.RandomSet (Ω X : Type*) [MeasurableSpace Ω] [TopologicalSpace X] where
  toFun : Ω → Set X
  measurable' : Measurable toFun

variable {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]

namespace Tengoku.Randomsettheory.RandomSet

instance : CoeFun (RandomSet Ω X) (fun _ => Ω → Set X) where
  coe S := S.toFun

/-- Build a random set from an explicitly measurable set-valued map.-/
def ofMeasurable (S : Ω → Set X) (hS : Measurable S) : RandomSet Ω X :=
  ⟨S, hS⟩

/--
@isnad1 id=eq.1h4v.s5.69cbfd2cf4f6 from=translated src=- shape=3ba1b22c vocab=f5632397
-/
@[simp] theorem ofMeasurable_apply (S : Ω → Set X) (hS : Measurable S) (ω : Ω) :
    ofMeasurable S hS ω = S ω :=
  rfl

/-!
## 2. Basic Operations
-/

/-- The random set that is constantly a single set `K`.-/
noncomputable def const (K : Set X) : RandomSet Ω X where
  toFun := fun _ => K
  measurable' := measurable_const

/-- The empty random set.-/
noncomputable def empty : RandomSet Ω X where
  toFun := fun _ => ∅
  measurable' := measurable_const (a := (∅ : Set X))

/-- Union of two random sets.-/
noncomputable def union (S T : RandomSet Ω X) : RandomSet Ω X where
  toFun := fun ω => S ω ∪ T ω
  measurable' := by
    rw [measurable_set_iff]
    intro a
    have hS : Measurable (fun ω => a ∈ S ω) := by
      have hS_measSet : MeasurableSet {ω | a ∈ S ω} := S.measurable' (measurableSet_mem a)
      simpa using measurableSet_setOfPred.mp hS_measSet
    have hT : Measurable (fun ω => a ∈ T ω) := by
      have hT_measSet : MeasurableSet {ω | a ∈ T ω} := T.measurable' (measurableSet_mem a)
      simpa using measurableSet_setOfPred.mp hT_measSet
    simpa using hS.or hT

/-- Intersection of two random sets.-/
noncomputable def inter (S T : RandomSet Ω X) : RandomSet Ω X where
  toFun := fun ω => S ω ∩ T ω
  measurable' := by
    rw [measurable_set_iff]
    intro a
    have hS : Measurable (fun ω => a ∈ S ω) := by
      have hS_measSet : MeasurableSet {ω | a ∈ S ω} := S.measurable' (measurableSet_mem a)
      simpa using measurableSet_setOfPred.mp hS_measSet
    have hT : Measurable (fun ω => a ∈ T ω) := by
      have hT_measSet : MeasurableSet {ω | a ∈ T ω} := T.measurable' (measurableSet_mem a)
      simpa using measurableSet_setOfPred.mp hT_measSet
    simpa using hS.and hT

/-- Complement of a random set.-/
noncomputable def compl (S : RandomSet Ω X) : RandomSet Ω X where
  toFun := fun ω => (S ω)ᶜ
  measurable' := by
    rw [measurable_set_iff]
    intro a
    have hS : Measurable (fun ω => a ∈ S ω) := by
      have hS_measSet : MeasurableSet {ω | a ∈ S ω} := S.measurable' (measurableSet_mem a)
      simpa using measurableSet_setOfPred.mp hS_measSet
    simpa using hS.not

/-- Pointwise addition of two random sets (Minkowski sum).
Requires `X` to be an additive commutative monoid.-/
noncomputable def add [AddCommMonoid X] (S T : RandomSet Ω X)
    (hmeas : Measurable fun ω => S ω + T ω) : RandomSet Ω X where
  toFun := fun ω => S ω + T ω
  measurable' := hmeas

/--
@isnad1 id=eq.1h5v.s6.38b0c7a9c742 from=translated src=- shape=87a00a0f vocab=88aa59d1
-/
@[simp] theorem add_apply [AddCommMonoid X] (S T : RandomSet Ω X)
    (hmeas : Measurable fun ω => S ω + T ω) (ω : Ω) :
    add S T hmeas ω = S ω + T ω :=
  rfl

/-- Pointwise scalar multiplication of a random set.
Requires `X` to be a vector space over `ℝ`.-/
noncomputable def smul [AddCommGroup X] [Module ℝ X] (r : ℝ) (S : RandomSet Ω X)
    (hmeas : Measurable fun ω => r • S ω) : RandomSet Ω X where
  toFun := fun ω => r • S ω
  measurable' := hmeas

/--
@isnad1 id=eq.1h5v.s7.ecd5e97ff46f from=translated src=- shape=44fb45cc vocab=9274de6c
-/
@[simp] theorem smul_apply [AddCommGroup X] [Module ℝ X]
    (r : ℝ) (S : RandomSet Ω X) (hmeas : Measurable fun ω => r • S ω) (ω : Ω) :
    smul r S hmeas ω = r • S ω :=
  rfl

/-- Nonzero scalar multiplication preserves membership measurability.  The
zero case depends on measurability of the nonemptiness event and is therefore
not valid for an arbitrary membership-measurable correspondence.-/
noncomputable def smulOfNe [AddCommGroup X] [Module ℝ X]
    (r : ℝ) (hr : r ≠ 0) (S : RandomSet Ω X) : RandomSet Ω X where
  toFun := fun ω => r • S ω
  measurable' := by
    rw [measurable_set_iff]
    intro a
    have hmem : Measurable (fun ω => r⁻¹ • a ∈ S ω) := by
      have hmeasSet : MeasurableSet {ω | r⁻¹ • a ∈ S ω} :=
        S.measurable' (measurableSet_mem (r⁻¹ • a))
      simpa [measurableSet_setOfPred] using hmeasSet
    have hequiv : (fun ω => a ∈ r • S ω) = (fun ω => r⁻¹ • a ∈ S ω) := by
      ext ω
      rw [mem_smul_set_iff_inv_smul_mem₀ hr]
    simpa [hequiv] using hmem

/--
@isnad1 id=eq.1h5v.s7.9218d981f906 from=translated src=- shape=de0ec842 vocab=1c467045
-/
@[simp] theorem smulOfNe_apply [AddCommGroup X] [Module ℝ X]
    (r : ℝ) (hr : r ≠ 0) (S : RandomSet Ω X) (ω : Ω) :
    smulOfNe r hr S ω = r • S ω :=
  rfl

/-!
## 3. Support of a Random Set
-/

/-- The support of a random set: the union of all realizations.-/
def support (S : RandomSet Ω X) : Set X := ⋃ ω, S ω

/-- The range of a random set: the set of all values it takes.-/
def range (S : RandomSet Ω X) : Set X := S.support

/--
@isnad1 id=iff.0h4v.s5.7d23ad616e2f from=translated src=- shape=dc464512 vocab=9e3ddecb
-/
lemma mem_support {S : RandomSet Ω X} {x : X} : x ∈ S.support ↔ ∃ ω, x ∈ S ω := by
  simp [support]

/--
@isnad1 id=iff.0h4v.s5.1d9f2aa8eba1 from=translated src=- shape=dc464512 vocab=766b978b
-/
lemma mem_range_iff {S : RandomSet Ω X} {x : X} : x ∈ S.range ↔ ∃ ω, x ∈ S ω := by
  simp [range, support]

/-!
## 4. Almost Sure Properties
-/

/-- Two random sets `S` and `T` are almost surely equal if they differ only on a null set.-/
def aEq (S T : RandomSet Ω X) (μ : Measure Ω) : Prop :=
  S.toFun =ᵐ[μ] T.toFun

/--
@isnad1 id=iff.0h5v.s6.c84a2acaa775 from=translated src=- shape=7f2a61d7 vocab=2dc6a067
-/
lemma aEq_iff (S T : RandomSet Ω X) (μ : Measure Ω) : S.aEq T μ ↔ ∀ᵐ ω ∂μ, S ω = T ω := by
  rfl

/-!
## 5. Effros-measurable random closed sets

For a topological state space, the classical random-set notion asks that the
event that `S` hits an open set be measurable.  It is deliberately kept
separate from membership measurability: neither notion implies the other in
full generality without separability or closed-valued hypotheses.
-/

/-- A correspondence is Effros measurable when all open hitting events are
measurable.-/
def IsEffrosMeasurable (S : Ω → Set X) : Prop :=
  ∀ U : Set X, IsOpen U → MeasurableSet {ω | (S ω ∩ U).Nonempty}

/--
@isnad1 id=iseffros.0h3v.s4.8637b2dfd5e0 from=translated src=- shape=ce587ab1 vocab=88ea0549
-/
theorem isEffrosMeasurable_const (K : Set X) :
    IsEffrosMeasurable (fun _ : Ω => K) := by
  intro U _
  by_cases h : (K ∩ U).Nonempty
  · simp [h]
  · simp [h]

/--
@isnad1 id=iseffros.0h2v.s4.627c687e3f6d from=translated src=- shape=9ec1bce7 vocab=524124a7
-/
theorem isEffrosMeasurable_empty :
    IsEffrosMeasurable (fun _ : Ω => (∅ : Set X)) :=
  isEffrosMeasurable_const ∅

/--
@isnad1 id=iseffros.2h4v.s5.4e5e4be8f1ab from=translated src=- shape=beecaef8 vocab=07699ea9
-/
theorem IsEffrosMeasurable.union {S T : Ω → Set X}
    (hS : IsEffrosMeasurable S) (hT : IsEffrosMeasurable T) :
    IsEffrosMeasurable (fun ω => S ω ∪ T ω) := by
  intro U hU
  have hEq : {ω | ((S ω ∪ T ω) ∩ U).Nonempty} =
      {ω | (S ω ∩ U).Nonempty} ∪ {ω | (T ω ∩ U).Nonempty} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨x, hx, hxU⟩
      rcases hx with hxS | hxT
      · exact Or.inl ⟨x, hxS, hxU⟩
      · exact Or.inr ⟨x, hxT, hxU⟩
    · rintro (⟨x, hxS, hxU⟩ | ⟨x, hxT, hxU⟩)
      · exact ⟨x, Or.inl hxS, hxU⟩
      · exact ⟨x, Or.inr hxT, hxU⟩
  rw [hEq]
  exact (hS U hU).union (hT U hU)

/--
@isnad1 id=iseffros.2h4v.s5.8d143c77e099 from=translated src=- shape=91bc882d vocab=88ea0549
-/
theorem IsEffrosMeasurable.congr {S T : Ω → Set X}
    (hS : IsEffrosMeasurable S) (hST : ∀ ω, S ω = T ω) :
    IsEffrosMeasurable T := by
  intro U hU
  convert hS U hU using 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  rw [← hST ω]

/--
@isnad1 id=iseffros.2h5v.s5.dc4a38a00b4f from=translated src=- shape=db316675 vocab=8d30e61d
-/
theorem IsEffrosMeasurable.image {Y : Type*} [TopologicalSpace Y]
    {S : Ω → Set X} (hS : IsEffrosMeasurable S) {f : X → Y}
    (hf : Continuous f) :
    IsEffrosMeasurable (fun ω => f '' S ω) := by
  intro U hU
  have hEq : {ω | ((f '' S ω) ∩ U).Nonempty} =
      {ω | (S ω ∩ f ⁻¹' U).Nonempty} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, ⟨x, hxS, rfl⟩, hfxU⟩
      exact ⟨x, hxS, hfxU⟩
    · rintro ⟨x, hxS, hfxU⟩
      exact ⟨f x, ⟨x, hxS, rfl⟩, hfxU⟩
  rw [hEq]
  exact hS (f ⁻¹' U) (hf.isOpen_preimage U hU)

/-- A classical Effros-measurable random closed set.-/
structure EffrosRandomClosedSet (Ω X : Type*)
    [MeasurableSpace Ω] [TopologicalSpace X] where
  toFun : Ω → Set X
  isClosed' : ∀ ω, IsClosed (toFun ω)
  measurable' : IsEffrosMeasurable toFun

instance : CoeFun (EffrosRandomClosedSet Ω X) (fun _ => Ω → Set X) where
  coe S := S.toFun

namespace EffrosRandomClosedSet

def const (K : Set X) (hK : IsClosed K) : EffrosRandomClosedSet Ω X where
  toFun := fun _ => K
  isClosed' := fun _ => hK
  measurable' := isEffrosMeasurable_const K

def empty : EffrosRandomClosedSet Ω X :=
  const ∅ isClosed_empty

def union (S T : EffrosRandomClosedSet Ω X) : EffrosRandomClosedSet Ω X where
  toFun := fun ω => S ω ∪ T ω
  isClosed' := fun ω => (S.isClosed' ω).union (T.isClosed' ω)
  measurable' := S.measurable'.union T.measurable'

/--
@isnad1 id=eq.1h4v.s5.595656654df6 from=translated src=- shape=46fa02b0 vocab=15a3a0d2
-/
@[simp] theorem const_apply (K : Set X) (hK : IsClosed K) (ω : Ω) :
    const K hK ω = K :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.a3d11a3ef6a4 from=translated src=- shape=df084ab0 vocab=dd5d4365
-/
@[simp] theorem empty_apply (ω : Ω) : (empty : EffrosRandomClosedSet Ω X) ω = ∅ :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.d45b45b151a4 from=translated src=- shape=679ab429 vocab=4cbf6132
-/
@[simp] theorem union_apply (S T : EffrosRandomClosedSet Ω X) (ω : Ω) :
    union S T ω = S ω ∪ T ω :=
  rfl

end EffrosRandomClosedSet

/-!
## 6. Random Set Families
-/

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι]

/-- A finite family of random sets indexed by `ι`.-/
structure RandomSetFamily (Ω X : Type*) [MeasurableSpace Ω] [TopologicalSpace X] where
  sets : ι → RandomSet Ω X
  measurable_family : Measurable (fun (p : ι × Ω) => (sets p.1) p.2)

/-!
## 7. Valued Properties

When `X` is a metric space, we can restrict to closed-valued random sets.
-/

section ValuedProperties

variable [MetricSpace X] [AddCommGroup X] [Module ℝ X]

/-- A random set whose values are almost surely closed.-/
def IsClosedValued (S : RandomSet Ω X) : Prop := ∀ ω, IsClosed (S ω)

/-- A random set whose values are almost surely compact.-/
def IsCompactValued (S : RandomSet Ω X) : Prop := ∀ ω, IsCompact (S ω)

/-- A random set whose values are almost surely convex.-/
def IsConvexValued (S : RandomSet Ω X) : Prop := ∀ ω, Convex ℝ (S ω)

/-- A random closed set.-/
structure RandomClosedSet (Ω X : Type*) [MeasurableSpace Ω] [MetricSpace X] where
  toRandomSet : RandomSet Ω X
  isClosed' : IsClosedValued toRandomSet

end ValuedProperties

end Tengoku.Randomsettheory.RandomSet
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
