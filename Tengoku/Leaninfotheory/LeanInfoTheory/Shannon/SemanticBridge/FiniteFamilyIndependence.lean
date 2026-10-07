/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.FiniteFamily
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.Independence

/-!
# Mutual independence for finite dependent families

The public law-facing predicate defines mutual independence of a finite atom
by pointwise factorization of its PMF marginal into one-coordinate marginals.
The source-facing predicate is definitionally the same statement applied to
`familyLawOf`.

Both predicates are type-generic: forming them requires neither a finite
ambient variable type nor finite component alphabets. Finiteness assumptions
enter only in later entropy theorems and finite-sum proofs. The selected atom
is a `Finset`, so its dependent coordinate product has no chosen ordering; for
the empty atom, the product of coordinate masses is one.

The private infrastructure below proves the intended dependent-family entropy
characterization. It keeps the normalized finite product PMF, dependent
coordinate equivalences, block laws, and induction machinery out of the
public representation.
-/

open scoped BigOperators ENNReal

namespace LeanInfoTheory.Shannon

universe u v w

noncomputable section

/-! ## Public predicates -/

/--
A finite atom of a dependent PMF family is mutually independent when its joint
marginal factors pointwise into its one-coordinate marginals.

The product is indexed by the subtype of variables selected by `s`. This
statement therefore supports dependent component alphabets, arbitrary ambient
variable types, empty and singleton atoms, and zero coordinate masses without
additional typeclass assumptions.
-/
def IsMutuallyIndependentFamily
    {Var : Type u} {alpha : Var -> Type v}
    (q : PMF ((i : Var) -> alpha i)) (s : Finset Var) : Prop :=
  ∀ x : FamilyOutcome alpha s,
    familyMarginal q s x =
      ∏ i : s, (q.map fun y => y i) (x i)

/--
Mutual independence of a finite source-indexed family.

This is a thin specialization of `IsMutuallyIndependentFamily` to the joint
pushforward law `familyLawOf p X`; it introduces no separate source semantics.
-/
def IsMutuallyIndependentFamilyOf
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (s : Finset Var) : Prop :=
  IsMutuallyIndependentFamily (familyLawOf p X) s

/-! ## Normalized product law -/

private def familyProduct
    {Var : Type u} {alpha : Var -> Type v}
    [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (s : Finset Var) :
    PMF (FamilyOutcome alpha s) := by
  classical
  exact
    PMF.ofFintype
      (fun x => ∏ i : s, (q.map fun y => y i) (x i))
      (by
        rw [← Fintype.prod_sum]
        apply Finset.prod_eq_one
        intro i _
        exact
          (tsum_fintype
            (fun j : alpha i => (q.map fun y => y i) j)).symm.trans
            (q.map fun y => y i).tsum_coe)

private theorem familyProduct_apply
    {Var : Type u} {alpha : Var -> Type v}
    [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (s : Finset Var)
    (x : FamilyOutcome alpha s) :
    familyProduct q s x =
      ∏ i : s, (q.map fun y => y i) (x i) :=
  by
    classical
    rfl

private theorem isMutuallyIndependentFamily_iff_eq_familyProduct
    {Var : Type u} {alpha : Var -> Type v}
    [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (s : Finset Var) :
    IsMutuallyIndependentFamily q s ↔
      familyMarginal q s = familyProduct q s := by
  classical
  constructor
  · intro h
    apply PMF.ext
    intro x
    rw [familyProduct_apply]
    exact h x
  · intro h x
    rw [h, familyProduct_apply]

/-! ## Disjoint-block transport -/

private theorem familyProduct_map_piFinsetUnion_symm
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) {a b : Finset Var}
    (hab : Disjoint a b) :
    (familyProduct q (a ∪ b)).map (Equiv.piFinsetUnion alpha hab).symm =
      indepProd (familyProduct q a) (familyProduct q b) := by
  classical
  apply PMF.ext
  rintro ⟨xa, xb⟩
  have hmap :
      ((familyProduct q (a ∪ b)).map
          (Equiv.piFinsetUnion alpha hab).symm) (xa, xb) =
        familyProduct q (a ∪ b)
          (Equiv.piFinsetUnion alpha hab (xa, xb)) := by
    simpa using
      PMF.map_apply_equiv (familyProduct q (a ∪ b))
        (Equiv.piFinsetUnion alpha hab).symm
        (Equiv.piFinsetUnion alpha hab (xa, xb))
  rw [hmap, familyProduct_apply, indepProd_apply,
    familyProduct_apply, familyProduct_apply]
  let e : a ⊕ b ≃ (a ∪ b : Finset Var) :=
    Equiv.Finset.union a b hab
  calc
    (∏ i : (a ∪ b : Finset Var),
        (q.map fun y => y i)
          (Equiv.piFinsetUnion alpha hab (xa, xb) i)) =
        ∏ j : a ⊕ b,
          (q.map fun y => y (e j))
            (Equiv.piFinsetUnion alpha hab (xa, xb) (e j)) := by
      exact
        (e.prod_comp fun i =>
          (q.map fun y => y i)
            (Equiv.piFinsetUnion alpha hab (xa, xb) i)).symm
    _ =
        (∏ i : a, (q.map fun y => y i) (xa i)) *
          ∏ i : b, (q.map fun y => y i) (xb i) := by
      rw [Fintype.prod_sum_type]
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        simp only [e, Equiv.Finset.union_inl]
        rw [Equiv.piFinsetUnion_left alpha hab i.property
          (Finset.mem_union_left b i.property)]
        rcases i with ⟨i, hi⟩
        rfl
      · apply Finset.prod_congr rfl
        intro i _
        simp only [e, Equiv.Finset.union_inr]
        rw [Equiv.piFinsetUnion_right alpha hab i.property
          (Finset.mem_union_right a i.property)]
        rcases i with ⟨i, hi⟩
        rfl

private def familyPairLaw
    {Var : Type u} {alpha : Var -> Type v}
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    PMF (FamilyOutcome alpha a × FamilyOutcome alpha b) :=
  q.map fun y => (a.restrict y, b.restrict y)

private theorem familyMarginal_map_piFinsetUnion_symm
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var]
    (q : PMF ((i : Var) -> alpha i)) {a b : Finset Var}
    (hab : Disjoint a b) :
    (familyMarginal q (a ∪ b)).map
        (Equiv.piFinsetUnion alpha hab).symm =
      familyPairLaw q a b := by
  rw [familyMarginal, familyPairLaw, PMF.map_comp]
  apply congrArg (fun f => q.map f)
  funext y
  apply (Equiv.piFinsetUnion alpha hab).injective
  change
    (Equiv.piFinsetUnion alpha hab)
        ((Equiv.piFinsetUnion alpha hab).symm ((a ∪ b).restrict y)) =
      (Equiv.piFinsetUnion alpha hab) (a.restrict y, b.restrict y)
  rw [Equiv.apply_symm_apply]
  funext i
  rcases Finset.mem_union.mp i.property with hi | hi
  · rw [Equiv.piFinsetUnion_left alpha hab hi i.property]
    rfl
  · rw [Equiv.piFinsetUnion_right alpha hab hi i.property]
    rfl

private theorem fstMarginal_familyPairLaw
    {Var : Type u} {alpha : Var -> Type v}
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    fstMarginal (familyPairLaw q a b) = familyMarginal q a := by
  rw [fstMarginal, familyPairLaw, familyMarginal, PMF.map_comp]
  rfl

private theorem sndMarginal_familyPairLaw
    {Var : Type u} {alpha : Var -> Type v}
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    sndMarginal (familyPairLaw q a b) = familyMarginal q b := by
  rw [sndMarginal, familyPairLaw, familyMarginal, PMF.map_comp]
  rfl

private theorem familyProduct_restrict_left
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) {a b : Finset Var}
    (hab : Disjoint a b) :
    (familyProduct q (a ∪ b)).map
        (Finset.restrict₂ (Finset.subset_union_left (s₁ := a) (s₂ := b))) =
      familyProduct q a := by
  classical
  let e := Equiv.piFinsetUnion alpha hab
  have hfun :
      Prod.fst ∘ e.symm =
        Finset.restrict₂
          (Finset.subset_union_left (s₁ := a) (s₂ := b)) := by
    funext x
    funext i
    have hcoord :=
      congrFun (e.apply_symm_apply x)
        (⟨i, Finset.mem_union_left b i.property⟩ :
          (a ∪ b : Finset Var))
    rw [Equiv.piFinsetUnion_left alpha hab i.property
      (Finset.mem_union_left b i.property)] at hcoord
    exact hcoord
  have hsplit := congrArg (fun p => p.map Prod.fst)
    (familyProduct_map_piFinsetUnion_symm q hab)
  change
    ((familyProduct q (a ∪ b)).map e.symm).map Prod.fst =
      (indepProd (familyProduct q a) (familyProduct q b)).map Prod.fst
    at hsplit
  rw [PMF.map_comp, hfun] at hsplit
  change
    (familyProduct q (a ∪ b)).map
        (Finset.restrict₂
          (Finset.subset_union_left (s₁ := a) (s₂ := b))) =
      fstMarginal (indepProd (familyProduct q a) (familyProduct q b))
    at hsplit
  rw [fstMarginal_indepProd] at hsplit
  exact hsplit

private theorem familyProduct_restrict_right
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) {a b : Finset Var}
    (hab : Disjoint a b) :
    (familyProduct q (a ∪ b)).map
        (Finset.restrict₂ (Finset.subset_union_right (s₁ := a) (s₂ := b))) =
      familyProduct q b := by
  classical
  let e := Equiv.piFinsetUnion alpha hab
  have hfun :
      Prod.snd ∘ e.symm =
        Finset.restrict₂
          (Finset.subset_union_right (s₁ := a) (s₂ := b)) := by
    funext x
    funext i
    have hcoord :=
      congrFun (e.apply_symm_apply x)
        (⟨i, Finset.mem_union_right a i.property⟩ :
          (a ∪ b : Finset Var))
    rw [Equiv.piFinsetUnion_right alpha hab i.property
      (Finset.mem_union_right a i.property)] at hcoord
    exact hcoord
  have hsplit := congrArg (fun p => p.map Prod.snd)
    (familyProduct_map_piFinsetUnion_symm q hab)
  change
    ((familyProduct q (a ∪ b)).map e.symm).map Prod.snd =
      (indepProd (familyProduct q a) (familyProduct q b)).map Prod.snd
    at hsplit
  rw [PMF.map_comp, hfun] at hsplit
  change
    (familyProduct q (a ∪ b)).map
        (Finset.restrict₂
          (Finset.subset_union_right (s₁ := a) (s₂ := b))) =
      sndMarginal (indepProd (familyProduct q a) (familyProduct q b))
    at hsplit
  rw [sndMarginal_indepProd] at hsplit
  exact hsplit

private theorem isMutuallyIndependentFamily_union_restrict_left
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Finite (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) {a b : Finset Var}
    (hab : Disjoint a b) (h : IsMutuallyIndependentFamily q (a ∪ b)) :
    IsMutuallyIndependentFamily q a := by
  let (i : Var) : Fintype (alpha i) := Fintype.ofFinite (alpha i)
  rw [isMutuallyIndependentFamily_iff_eq_familyProduct] at h ⊢
  calc
    familyMarginal q a =
        (familyMarginal q (a ∪ b)).map
          (Finset.restrict₂
            (Finset.subset_union_left (s₁ := a) (s₂ := b))) :=
      (familyMarginal_restrict q
        (Finset.subset_union_left (s₁ := a) (s₂ := b))).symm
    _ =
        (familyProduct q (a ∪ b)).map
          (Finset.restrict₂
            (Finset.subset_union_left (s₁ := a) (s₂ := b))) :=
      congrArg
        (fun p => p.map
          (Finset.restrict₂
            (Finset.subset_union_left (s₁ := a) (s₂ := b)))) h
    _ = familyProduct q a := familyProduct_restrict_left q hab

private theorem isMutuallyIndependentFamily_union_restrict_right
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Finite (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) {a b : Finset Var}
    (hab : Disjoint a b) (h : IsMutuallyIndependentFamily q (a ∪ b)) :
    IsMutuallyIndependentFamily q b := by
  let (i : Var) : Fintype (alpha i) := Fintype.ofFinite (alpha i)
  rw [isMutuallyIndependentFamily_iff_eq_familyProduct] at h ⊢
  calc
    familyMarginal q b =
        (familyMarginal q (a ∪ b)).map
          (Finset.restrict₂
            (Finset.subset_union_right (s₁ := a) (s₂ := b))) :=
      (familyMarginal_restrict q
        (Finset.subset_union_right (s₁ := a) (s₂ := b))).symm
    _ =
        (familyProduct q (a ∪ b)).map
          (Finset.restrict₂
            (Finset.subset_union_right (s₁ := a) (s₂ := b))) :=
      congrArg
        (fun p => p.map
          (Finset.restrict₂
            (Finset.subset_union_right (s₁ := a) (s₂ := b)))) h
    _ = familyProduct q b := familyProduct_restrict_right q hab

private theorem isIndependent_familyPairLaw_of_mutuallyIndependent_union
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Finite (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) {a b : Finset Var}
    (hab : Disjoint a b) (h : IsMutuallyIndependentFamily q (a ∪ b)) :
    IsIndependent (familyPairLaw q a b) := by
  let (i : Var) : Fintype (alpha i) := Fintype.ofFinite (alpha i)
  have ha :=
    isMutuallyIndependentFamily_union_restrict_left q hab h
  have hb :=
    isMutuallyIndependentFamily_union_restrict_right q hab h
  rw [isMutuallyIndependentFamily_iff_eq_familyProduct] at h ha hb
  rw [IsIndependent, fstMarginal_familyPairLaw,
    sndMarginal_familyPairLaw]
  calc
    familyPairLaw q a b =
        (familyMarginal q (a ∪ b)).map
          (Equiv.piFinsetUnion alpha hab).symm :=
      (familyMarginal_map_piFinsetUnion_symm q hab).symm
    _ =
        (familyProduct q (a ∪ b)).map
          (Equiv.piFinsetUnion alpha hab).symm :=
      congrArg
        (fun p => p.map (Equiv.piFinsetUnion alpha hab).symm) h
    _ = indepProd (familyProduct q a) (familyProduct q b) :=
      familyProduct_map_piFinsetUnion_symm q hab
    _ = indepProd (familyMarginal q a) (familyMarginal q b) := by
      rw [ha, hb]

private theorem mutuallyIndependent_union_of_restrict_and_pair
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Finite (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) {a b : Finset Var}
    (hab : Disjoint a b)
    (ha : IsMutuallyIndependentFamily q a)
    (hb : IsMutuallyIndependentFamily q b)
    (hp : IsIndependent (familyPairLaw q a b)) :
    IsMutuallyIndependentFamily q (a ∪ b) := by
  let (i : Var) : Fintype (alpha i) := Fintype.ofFinite (alpha i)
  rw [isMutuallyIndependentFamily_iff_eq_familyProduct] at ha hb ⊢
  rw [IsIndependent, fstMarginal_familyPairLaw,
    sndMarginal_familyPairLaw] at hp
  have hmaps :
      (familyMarginal q (a ∪ b)).map
          (Equiv.piFinsetUnion alpha hab).symm =
        (familyProduct q (a ∪ b)).map
          (Equiv.piFinsetUnion alpha hab).symm := by
    calc
      (familyMarginal q (a ∪ b)).map
          (Equiv.piFinsetUnion alpha hab).symm =
          familyPairLaw q a b :=
        familyMarginal_map_piFinsetUnion_symm q hab
      _ = indepProd (familyMarginal q a) (familyMarginal q b) := hp
      _ = indepProd (familyProduct q a) (familyProduct q b) := by
        rw [ha, hb]
      _ = (familyProduct q (a ∪ b)).map
          (Equiv.piFinsetUnion alpha hab).symm :=
        (familyProduct_map_piFinsetUnion_symm q hab).symm
  apply PMF.ext
  intro x
  have hx := congrArg
    (fun p => p ((Equiv.piFinsetUnion alpha hab).symm x)) hmaps
  change
    ((familyMarginal q (a ∪ b)).map
      (Equiv.piFinsetUnion alpha hab).symm)
        ((Equiv.piFinsetUnion alpha hab).symm x) =
      ((familyProduct q (a ∪ b)).map
        (Equiv.piFinsetUnion alpha hab).symm)
          ((Equiv.piFinsetUnion alpha hab).symm x)
    at hx
  rw [PMF.map_apply_equiv (familyMarginal q (a ∪ b))
      (Equiv.piFinsetUnion alpha hab).symm x,
    PMF.map_apply_equiv (familyProduct q (a ∪ b))
      (Equiv.piFinsetUnion alpha hab).symm x] at hx
  exact hx

/-! ## Empty and singleton atoms -/

/-- Every dependent PMF family is mutually independent on the empty atom. -/
@[simp] theorem isMutuallyIndependentFamily_empty
    {Var : Type u} {alpha : Var -> Type v}
    (q : PMF ((i : Var) -> alpha i)) :
    IsMutuallyIndependentFamily q ∅ := by
  intro x
  rw [Fintype.prod_empty]
  have hrestrict :
      (∅ : Finset Var).restrict (π := alpha) =
        Function.const ((i : Var) -> alpha i) x := by
    funext y i
    rcases i with ⟨i, hi⟩
    simp at hi
  rw [familyMarginal, hrestrict, PMF.map_const]
  simp

private def singletonFamilyEval
    {Var : Type u} {alpha : Var -> Type v} (i : Var) :
    FamilyOutcome alpha {i} -> alpha i := by
  classical
  exact fun x => x ⟨i, Finset.mem_singleton_self i⟩

private theorem singletonFamilyEval_injective
    {Var : Type u} {alpha : Var -> Type v} (i : Var) :
    Function.Injective (singletonFamilyEval (alpha := alpha) i) := by
  classical
  intro x y hxy
  funext j
  have hj : (j : Var) = i := by
    simpa only [Finset.mem_singleton] using j.property
  have hj' :
      j = (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset Var)) :=
    Subtype.ext hj
  subst j
  exact hxy

/-- Every one-coordinate marginal is mutually independent. -/
@[simp] theorem isMutuallyIndependentFamily_singleton
    {Var : Type u} {alpha : Var -> Type v}
    (q : PMF ((i : Var) -> alpha i)) (i : Var) :
    IsMutuallyIndependentFamily q {i} := by
  classical
  intro x
  have hmap :
      (familyMarginal q {i}).map
          (singletonFamilyEval (alpha := alpha) i) =
        q.map (fun y => y i) := by
    rw [familyMarginal, PMF.map_comp]
    rfl
  calc
    familyMarginal q {i} x =
        ((familyMarginal q {i}).map
          (singletonFamilyEval (alpha := alpha) i))
            (singletonFamilyEval (alpha := alpha) i x) :=
      (PMF.map_apply_of_injective (familyMarginal q {i})
        (singletonFamilyEval_injective (alpha := alpha) i) x).symm
    _ = (q.map (fun y => y i))
        (singletonFamilyEval (alpha := alpha) i x) := by rw [hmap]
    _ = ∏ j : ({i} : Finset Var),
        (q.map fun y => y j) (x j) := by
      rw [Fintype.prod_subsingleton _ ⟨i, Finset.mem_singleton_self i⟩]
      rfl

/-! ## Pair compatibility -/

private def pairFamilyEval
    {Var : Type u} {alpha : Var -> Type v} [DecidableEq Var]
    (i j : Var) :
    FamilyOutcome alpha {i, j} -> alpha i × alpha j :=
  fun x => (x ⟨i, by simp⟩, x ⟨j, by simp⟩)

private theorem pairFamilyEval_injective
    {Var : Type u} {alpha : Var -> Type v} [DecidableEq Var]
    {i j : Var} :
    Function.Injective (pairFamilyEval (alpha := alpha) i j) := by
  intro x y hxy
  funext k
  have hk : (k : Var) = i ∨ (k : Var) = j := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using k.property
  rcases hk with hki | hkj
  · have hk' :
        k = (⟨i, by simp⟩ : ({i, j} : Finset Var)) :=
      Subtype.ext hki
    subst k
    exact congrArg Prod.fst hxy
  · have hk' :
        k = (⟨j, by simp⟩ : ({i, j} : Finset Var)) :=
      Subtype.ext hkj
    subst k
    exact congrArg Prod.snd hxy

private def pairFamilyMk
    {Var : Type u} {alpha : Var -> Type v} [DecidableEq Var]
    {i j : Var} (a : alpha i) (b : alpha j) :
    FamilyOutcome alpha {i, j} :=
  fun k =>
    if hki : (k : Var) = i then
      hki.symm ▸ a
    else
      have hkj : (k : Var) = j := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, hki, false_or]
          using k.property
      hkj.symm ▸ b

private theorem pairFamilyEval_pairFamilyMk
    {Var : Type u} {alpha : Var -> Type v} [DecidableEq Var]
    {i j : Var} (hij : i ≠ j) (a : alpha i) (b : alpha j) :
    pairFamilyEval i j (pairFamilyMk a b) = (a, b) := by
  apply Prod.ext
  · simp [pairFamilyEval, pairFamilyMk]
  · simp [pairFamilyEval, pairFamilyMk, hij.symm]

private theorem pairFamily_product
    {Var : Type u} {alpha : Var -> Type v} [DecidableEq Var]
    (q : PMF ((i : Var) -> alpha i)) {i j : Var} (hij : i ≠ j)
    (x : FamilyOutcome alpha {i, j}) :
    (∏ k : ({i, j} : Finset Var),
        (q.map fun y => y k) (x k)) =
      (q.map fun y => y i) (x ⟨i, by simp⟩) *
        (q.map fun y => y j) (x ⟨j, by simp⟩) := by
  let f : Var -> ENNReal := fun k =>
    if hk : k ∈ ({i, j} : Finset Var) then
      (q.map fun y => y k) (x ⟨k, hk⟩)
    else
      1
  calc
    (∏ k : ({i, j} : Finset Var),
        (q.map fun y => y k) (x k)) =
        ∏ k : ({i, j} : Finset Var), f k := by
      apply Fintype.prod_congr
      intro k
      rw [show f k = (q.map fun y => y k) (x k) by
        simp only [f, dite_eq_left k.property]]
    _ = ∏ k ∈ ({i, j} : Finset Var), f k :=
      Finset.prod_coe_sort ({i, j} : Finset Var) f
    _ = f i * f j := Finset.prod_pair hij
    _ =
        (q.map fun y => y i) (x ⟨i, by simp⟩) *
          (q.map fun y => y j) (x ⟨j, by simp⟩) := by
      simp [f]

private theorem familyMarginal_pair_map_eval
    {Var : Type u} {alpha : Var -> Type v} [DecidableEq Var]
    (q : PMF ((i : Var) -> alpha i)) (i j : Var) :
    (familyMarginal q {i, j}).map
        (pairFamilyEval (alpha := alpha) i j) =
      q.map fun y => (y i, y j) := by
  rw [familyMarginal, PMF.map_comp]
  rfl

private theorem isMutuallyIndependentFamily_pair_iff_isIndependent
    {Var : Type u} {alpha : Var -> Type v} [DecidableEq Var]
    (q : PMF ((i : Var) -> alpha i)) {i j : Var} (hij : i ≠ j) :
    IsMutuallyIndependentFamily q {i, j} ↔
      IsIndependent (q.map fun y => (y i, y j)) := by
  rw [isIndependent_iff_apply_eq_mul_marginals]
  constructor
  · intro h a b
    let x : FamilyOutcome alpha {i, j} := pairFamilyMk a b
    have hEval :
        pairFamilyEval i j x = (a, b) :=
      pairFamilyEval_pairFamilyMk hij a b
    calc
      (q.map fun y => (y i, y j)) (a, b) =
          ((familyMarginal q {i, j}).map
            (pairFamilyEval (alpha := alpha) i j)) (a, b) := by
        rw [familyMarginal_pair_map_eval]
      _ =
          ((familyMarginal q {i, j}).map
            (pairFamilyEval (alpha := alpha) i j))
              (pairFamilyEval i j x) := by rw [hEval]
      _ = familyMarginal q {i, j} x :=
        PMF.map_apply_of_injective
          (familyMarginal q {i, j})
          pairFamilyEval_injective x
      _ =
          ∏ k : ({i, j} : Finset Var),
            (q.map fun y => y k) (x k) :=
        h x
      _ =
          (q.map fun y => y i) (x ⟨i, by simp⟩) *
            (q.map fun y => y j) (x ⟨j, by simp⟩) :=
        pairFamily_product q hij x
      _ =
          fstMarginal (q.map fun y => (y i, y j)) a *
            sndMarginal (q.map fun y => (y i, y j)) b := by
        simp [x, pairFamilyMk, hij.symm]
  · intro h x
    calc
      familyMarginal q {i, j} x =
          ((familyMarginal q {i, j}).map
            (pairFamilyEval (alpha := alpha) i j))
              (pairFamilyEval i j x) :=
        (PMF.map_apply_of_injective
          (familyMarginal q {i, j})
          pairFamilyEval_injective x).symm
      _ =
          (q.map fun y => (y i, y j))
            (pairFamilyEval i j x) := by
        rw [familyMarginal_pair_map_eval]
      _ =
          (q.map fun y => y i) (x ⟨i, by simp⟩) *
            (q.map fun y => y j) (x ⟨j, by simp⟩) := by
        simpa [pairFamilyEval] using
          h (x ⟨i, by simp⟩) (x ⟨j, by simp⟩)
      _ =
          ∏ k : ({i, j} : Finset Var),
            (q.map fun y => y k) (x k) :=
        (pairFamily_product q hij x).symm

/--
For distinct indices, mutual independence of a two-variable source family is
exactly independence of the corresponding pair of random variables.

Distinctness is essential: when the indices coincide, the selected atom
collapses to a singleton and is automatically mutually independent, whereas a
random variable need not be independent of itself.
-/
theorem isMutuallyIndependentFamilyOf_pair_iff_isIndependentOf
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    {i j : Var} (hij : i ≠ j) :
    IsMutuallyIndependentFamilyOf p X {i, j} ↔
      IsIndependentOf p (X i) (X j) := by
  change
    IsMutuallyIndependentFamily (familyLawOf p X) {i, j} ↔
      IsIndependent (p.map fun x => (X i x, X j x))
  rw [isMutuallyIndependentFamily_pair_iff_isIndependent
    (familyLawOf p X) hij]
  rw [familyLawOf, PMF.map_comp]
  rfl

/-! ## Restriction -/

/--
Mutual independence of a finite atom is inherited by each of its subatoms.
Here the atom is finite because it is a `Finset`; the additional typeclass
assumption says that the ambient family has pointwise-finite coordinate
alphabets.
-/
theorem isMutuallyIndependentFamily_mono
    {Var : Type u} {alpha : Var -> Type v}
    [forall i, Finite (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) {s t : Finset Var}
    (h : IsMutuallyIndependentFamily q t) (hst : s ⊆ t) :
    IsMutuallyIndependentFamily q s := by
  classical
  apply
    isMutuallyIndependentFamily_union_restrict_left
      q (Finset.disjoint_sdiff : Disjoint s (t \ s))
  rw [Finset.union_sdiff_of_subset hst]
  exact h

/-! ## Entropy additivity -/

private theorem familyEntropy_union_eq_add_iff_isIndependent_pairLaw
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    familyEntropy q (a ∪ b) =
        familyEntropy q a + familyEntropy q b ↔
      IsIndependent (familyPairLaw q a b) := by
  rw [familyEntropy_union]
  change
    entropy (familyPairLaw q a b) =
        entropy (familyMarginal q a) + entropy (familyMarginal q b) ↔
      IsIndependent (familyPairLaw q a b)
  rw [← fstMarginal_familyPairLaw q a b,
    ← sndMarginal_familyPairLaw q a b]
  exact
    jointEntropy_eq_add_marginalEntropy_iff_isIndependent
      (familyPairLaw q a b)

/--
The entropy of a finite dependent-family marginal is the sum of its
one-coordinate entropies exactly when the selected family is mutually
independent.
-/
theorem familyEntropy_eq_sum_singletons_iff_isMutuallyIndependentFamily
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (s : Finset Var) :
    familyEntropy q s =
        ∑ i ∈ s, familyEntropy q {i} ↔
      IsMutuallyIndependentFamily q s := by
  induction s using Finset.induction_on with
  | empty =>
      constructor
      · intro _
        exact isMutuallyIndependentFamily_empty q
      · intro _
        simp only [familyEntropy_empty, Finset.sum_empty]
  | @insert i s hi ih =>
      have hdisj : Disjoint ({i} : Finset Var) s := by
        simpa [Finset.disjoint_left] using hi
      constructor
      · intro hEntropy
        have hFull :
            familyEntropy q ({i} ∪ s) =
              familyEntropy q {i} +
                ∑ j ∈ s, familyEntropy q {j} := by
          rw [Finset.singleton_union, hEntropy, Finset.sum_insert hi]
        have hTailUpper :
            familyEntropy q s ≤
              ∑ j ∈ s, familyEntropy q {j} :=
          familyEntropy_le_sum_singletons q s
        have hUnionUpper :
            familyEntropy q ({i} ∪ s) ≤
              familyEntropy q {i} + familyEntropy q s :=
          familyEntropy_union_le_add q {i} s
        have hTailLower :
            (∑ j ∈ s, familyEntropy q {j}) ≤
              familyEntropy q s := by
          linarith
        have hTailEntropy :
            familyEntropy q s =
              ∑ j ∈ s, familyEntropy q {j} :=
          le_antisymm hTailUpper hTailLower
        have hTail :
            IsMutuallyIndependentFamily q s :=
          ih.mp hTailEntropy
        have hPairEntropy :
            familyEntropy q ({i} ∪ s) =
              familyEntropy q {i} + familyEntropy q s :=
          calc
            familyEntropy q ({i} ∪ s) =
                familyEntropy q {i} +
                  ∑ j ∈ s, familyEntropy q {j} := hFull
            _ = familyEntropy q {i} + familyEntropy q s := by
              rw [hTailEntropy]
        have hPair :
            IsIndependent (familyPairLaw q {i} s) :=
          (familyEntropy_union_eq_add_iff_isIndependent_pairLaw
            q {i} s).mp hPairEntropy
        have hIndep :
            IsMutuallyIndependentFamily q ({i} ∪ s) :=
          mutuallyIndependent_union_of_restrict_and_pair q hdisj
            (isMutuallyIndependentFamily_singleton q i) hTail hPair
        simpa [Finset.singleton_union] using hIndep
      · intro hIndepInsert
        have hIndep :
            IsMutuallyIndependentFamily q ({i} ∪ s) := by
          simpa [Finset.singleton_union] using hIndepInsert
        have hTail :
            IsMutuallyIndependentFamily q s :=
          isMutuallyIndependentFamily_union_restrict_right
            q hdisj hIndep
        have hPair :
            IsIndependent (familyPairLaw q {i} s) :=
          isIndependent_familyPairLaw_of_mutuallyIndependent_union
            q hdisj hIndep
        have hTailEntropy :
            familyEntropy q s =
              ∑ j ∈ s, familyEntropy q {j} :=
          ih.mpr hTail
        have hPairEntropy :
            familyEntropy q ({i} ∪ s) =
              familyEntropy q {i} + familyEntropy q s :=
          (familyEntropy_union_eq_add_iff_isIndependent_pairLaw
            q {i} s).mpr hPair
        calc
          familyEntropy q (insert i s) =
              familyEntropy q ({i} ∪ s) := by
            rw [Finset.singleton_union]
          _ = familyEntropy q {i} + familyEntropy q s :=
            hPairEntropy
          _ = familyEntropy q {i} +
              ∑ j ∈ s, familyEntropy q {j} := by
            rw [hTailEntropy]
          _ = ∑ j ∈ insert i s, familyEntropy q {j} := by
            rw [Finset.sum_insert hi]

/--
The source-family form of the finite entropy-additivity characterization of
mutual independence.
-/
theorem familyEntropyOf_eq_sum_singletons_iff_isMutuallyIndependentFamilyOf
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (s : Finset Var) :
    familyEntropyOf p X s =
        ∑ i ∈ s, familyEntropyOf p X {i} ↔
      IsMutuallyIndependentFamilyOf p X s := by
  simpa only [familyEntropyOf, IsMutuallyIndependentFamilyOf] using
    familyEntropy_eq_sum_singletons_iff_isMutuallyIndependentFamily
      (familyLawOf p X) s

end

end LeanInfoTheory.Shannon
