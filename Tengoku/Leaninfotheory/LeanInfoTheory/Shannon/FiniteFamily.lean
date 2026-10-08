/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.InfoMeasures
import Tengoku

/-!
# Finite families of random variables

This file introduces the lightweight representation used for entropy of finite
subfamilies of a possibly infinite family of finite-valued random variables.
Component alphabets may depend on the variable name.

A full family law lives on the dependent function type
`(i : Var) -> alpha i`. Entropy is never applied directly to that full law:
`familyEntropy q s` first restricts it to the finite atom `s : Finset Var`.
The variable-name type itself therefore need not be finite.
-/

namespace LeanInfoTheory
namespace Shannon

universe u v w

noncomputable section

/--
The outcome type of the variables selected by the finite atom `s`.

No finiteness assumption is needed to form this type. Pointwise finiteness of
the selected alphabets is required only when taking entropy.
-/
abbrev FamilyOutcome {Var : Type u} (alpha : Var -> Type v) (s : Finset Var) :=
  (i : s) -> alpha i

/--
The joint law of an indexed family of random variables under a source PMF.

The source type, variable-name type, and full dependent outcome type may all be
infinite.
-/
def familyLawOf {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i) :
    PMF ((i : Var) -> alpha i) :=
  p.map fun x i => X i x

/-- The joint marginal law of the variables selected by the finite atom `s`. -/
def familyMarginal {Var : Type u} {alpha : Var -> Type v}
    (q : PMF ((i : Var) -> alpha i)) (s : Finset Var) :
    PMF (FamilyOutcome alpha s) :=
  q.map s.restrict

/--
Shannon entropy, in nats, of the variables selected by the finite atom `s`.
-/
def familyEntropy {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (s : Finset Var) : Real :=
  entropy (familyMarginal q s)

/--
Shannon entropy, in nats, of a finite subfamily of random variables under a
source PMF.
-/
def familyEntropyOf {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (s : Finset Var) : Real :=
  familyEntropy (familyLawOf p X) s

/-! ## Algebraic family information measures -/

/--
Conditional entropy `H(A | B)` of two finite subfamilies.

The atoms may overlap.
-/
def familyCondEntropy {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) : Real :=
  familyEntropy q (a ∪ b) - familyEntropy q b

/--
Mutual information `I(A; B)` of two finite subfamilies.

The atoms may overlap.
-/
def familyMutualInfo {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) : Real :=
  familyEntropy q a + familyEntropy q b - familyEntropy q (a ∪ b)

/--
Conditional mutual information `I(A; B | C)` of three finite subfamilies.

The three-way union is normalized as `(A ∪ B) ∪ C`.
-/
def familyCondMutualInfo {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b c : Finset Var) : Real :=
  familyEntropy q (a ∪ c) + familyEntropy q (b ∪ c) -
    familyEntropy q (a ∪ b ∪ c) - familyEntropy q c

/-- Conditional entropy of two finite subfamilies under a source PMF. -/
def familyCondEntropyOf
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) : Real :=
  familyCondEntropy (familyLawOf p X) a b

/-- Mutual information of two finite subfamilies under a source PMF. -/
def familyMutualInfoOf
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) : Real :=
  familyMutualInfo (familyLawOf p X) a b

/-- Conditional mutual information of three finite subfamilies under a source PMF. -/
def familyCondMutualInfoOf
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b c : Finset Var) : Real :=
  familyCondMutualInfo (familyLawOf p X) a b c

/-! ## Marginal restriction and source-family rewrites -/

/--
Restricting a finite family marginal to a smaller atom gives the marginal on
that smaller atom.
-/
theorem familyMarginal_restrict {Var : Type u} {alpha : Var -> Type v}
    (q : PMF ((i : Var) -> alpha i)) {s t : Finset Var} (hst : s ⊆ t) :
    (familyMarginal q t).map (Finset.restrict₂ hst) =
      familyMarginal q s := by
  rw [familyMarginal, familyMarginal, PMF.map_comp,
    Finset.restrict₂_comp_restrict hst]

/--
The finite marginal of a source-indexed family is the joint law of its
selected coordinates.
-/
theorem familyMarginal_familyLawOf
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i) (s : Finset Var) :
    familyMarginal (familyLawOf p X) s =
      p.map (fun x (i : s) => X i x) := by
  rw [familyMarginal, familyLawOf, PMF.map_comp]
  have hcomp : s.restrict ∘ (fun x i => X i x) =
      (fun x (i : s) => X i x) := by
    funext x i
    rfl
  rw [hcomp]

/-- Family entropy is ordinary random-variable entropy of finite restriction. -/
theorem familyEntropy_eq_entropyOf
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (s : Finset Var) :
    familyEntropy q s = entropyOf q s.restrict :=
  rfl

/--
Source-family entropy is ordinary entropy of the selected coordinates under
the source law.
-/
theorem familyEntropyOf_eq_entropyOf
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (s : Finset Var) :
    familyEntropyOf p X s = entropyOf p (fun x (i : s) => X i x) := by
  rw [familyEntropyOf, familyEntropy, familyMarginal_familyLawOf]
  rfl

/--
Family entropy on `s` depends only on the source variables selected by `s`.
-/
theorem familyEntropyOf_congr
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X Y : (i : Var) -> omega -> alpha i)
    (s : Finset Var) (h : forall x (i : s), X i x = Y i x) :
    familyEntropyOf p X s = familyEntropyOf p Y s := by
  rw [familyEntropyOf_eq_entropyOf, familyEntropyOf_eq_entropyOf]
  congr 1
  funext x i
  exact h x i

/-! ## Base cases and nonnegativity -/

/-- The entropy of the empty family is zero. -/
@[simp]
theorem familyEntropy_empty
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) :
    familyEntropy q ∅ = 0 := by
  let z : FamilyOutcome alpha (∅ : Finset Var) := fun i => by
    rcases i with ⟨i, hi⟩
    simp at hi
  have hrestrict :
      (∅ : Finset Var).restrict (π := alpha) =
        Function.const ((i : Var) -> alpha i) z := by
    funext x i
    rcases i with ⟨i, hi⟩
    simp at hi
  rw [familyEntropy, familyMarginal, hrestrict, PMF.map_const, entropy_pure]

/-- The entropy of the empty source-indexed family is zero. -/
@[simp]
theorem familyEntropyOf_empty
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i) :
    familyEntropyOf p X ∅ = 0 := by
  simp [familyEntropyOf]

private def singletonFamilyOutcomeEval
    {Var : Type u} [DecidableEq Var] {alpha : Var -> Type v} (i : Var) :
    FamilyOutcome alpha {i} -> alpha i :=
  fun x => x ⟨i, Finset.mem_singleton_self i⟩

private theorem singletonFamilyOutcomeEval_injective
    {Var : Type u} [DecidableEq Var] {alpha : Var -> Type v} (i : Var) :
    Function.Injective (singletonFamilyOutcomeEval (alpha := alpha) i) := by
  intro x y hxy
  funext j
  have hj : (j : Var) = i := by
    simpa only [Finset.mem_singleton] using j.property
  have hj' :
      j = (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset Var)) :=
    Subtype.ext hj
  subst j
  exact hxy

/-- The entropy of a singleton family is the entropy of that coordinate. -/
theorem familyEntropy_singleton
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (i : Var) :
    familyEntropy q {i} = entropyOf q (fun x => x i) := by
  rw [familyEntropy_eq_entropyOf]
  symm
  simpa [singletonFamilyOutcomeEval] using
    (entropyOf_comp_injective q ({i} : Finset Var).restrict
      (singletonFamilyOutcomeEval_injective (alpha := alpha) i))

/--
The entropy of a singleton source-indexed family is the entropy of that source
variable.
-/
theorem familyEntropyOf_singleton
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i) (i : Var) :
    familyEntropyOf p X {i} = entropyOf p (X i) := by
  rw [familyEntropyOf, familyEntropy_singleton]
  simp [entropyOf, familyLawOf, PMF.map_comp, Function.comp_def]

/-- Entropy of every finite subfamily is nonnegative. -/
theorem familyEntropy_nonneg
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (s : Finset Var) :
    0 <= familyEntropy q s := by
  exact entropy_nonneg (familyMarginal q s)

/-- Entropy of every finite source-indexed subfamily is nonnegative. -/
theorem familyEntropyOf_nonneg
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (s : Finset Var) :
    0 <= familyEntropyOf p X s := by
  exact familyEntropy_nonneg (familyLawOf p X) s

/-! ## Union-entropy bridges -/

private def splitUnion
    {Var : Type u} [DecidableEq Var] {alpha : Var -> Type v}
    (a b : Finset Var) :
    FamilyOutcome alpha (a ∪ b) ->
      FamilyOutcome alpha a × FamilyOutcome alpha b :=
  fun x =>
    (Finset.restrict₂ Finset.subset_union_left x,
      Finset.restrict₂ Finset.subset_union_right x)

private theorem splitUnion_injective
    {Var : Type u} [DecidableEq Var] {alpha : Var -> Type v}
    (a b : Finset Var) :
    Function.Injective (splitUnion (alpha := alpha) a b) := by
  intro x y hxy
  funext i
  by_cases hi : (i : Var) ∈ a
  · exact congrFun (congrArg Prod.fst hxy) (⟨i, hi⟩ : a)
  · have hib : (i : Var) ∈ b :=
      (Finset.mem_union.mp i.property).resolve_left hi
    exact congrFun (congrArg Prod.snd hxy) (⟨i, hib⟩ : b)

private def splitTripleUnion
    {Var : Type u} [DecidableEq Var] {alpha : Var -> Type v}
    (a b c : Finset Var) :
    FamilyOutcome alpha (a ∪ b ∪ c) ->
      FamilyOutcome alpha a ×
        (FamilyOutcome alpha b × FamilyOutcome alpha c) :=
  fun x =>
    (Finset.restrict₂
        (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left) x,
      (Finset.restrict₂
          (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left) x,
        Finset.restrict₂ Finset.subset_union_right x))

private theorem splitTripleUnion_injective
    {Var : Type u} [DecidableEq Var] {alpha : Var -> Type v}
    (a b c : Finset Var) :
    Function.Injective (splitTripleUnion (alpha := alpha) a b c) := by
  intro x y hxy
  funext i
  by_cases hia : (i : Var) ∈ a
  · exact
      congrFun (congrArg Prod.fst hxy) (⟨i, hia⟩ : a)
  · by_cases hib : (i : Var) ∈ b
    · exact
        congrFun (congrArg Prod.fst (congrArg Prod.snd hxy))
          (⟨i, hib⟩ : b)
    · have hic : (i : Var) ∈ c := by
        rcases Finset.mem_union.mp i.property with hiab | hic
        · rcases Finset.mem_union.mp hiab with hia' | hib'
          · exact (hia hia').elim
          · exact (hib hib').elim
        · exact hic
      exact
        congrFun (congrArg Prod.snd (congrArg Prod.snd hxy))
          (⟨i, hic⟩ : c)

/--
Entropy on a union is the joint entropy of the two restricted subfamilies.

The atoms may overlap; no disjointness or support assumption is required.
-/
theorem familyEntropy_union
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    familyEntropy q (a ∪ b) =
      jointEntropyOf q a.restrict b.restrict := by
  rw [familyEntropy_eq_entropyOf]
  symm
  unfold jointEntropyOf
  have hsplit :
      (fun x => splitUnion (alpha := alpha) a b ((a ∪ b).restrict x)) =
        (fun x => (a.restrict x, b.restrict x)) := by
    funext x
    apply Prod.ext
    · funext i
      simp only [splitUnion, Finset.restrict, Finset.restrict₂]
    · funext i
      simp only [splitUnion, Finset.restrict, Finset.restrict₂]
  rw [← hsplit]
  exact entropyOf_comp_injective q (a ∪ b).restrict
    (splitUnion_injective (alpha := alpha) a b)

/--
Source-family entropy on a union is the joint entropy of the two selected
subfamilies.
-/
theorem familyEntropyOf_union
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) :
    familyEntropyOf p X (a ∪ b) =
      jointEntropyOf p
        (fun x (i : a) => X i x)
        (fun x (i : b) => X i x) := by
  rw [familyEntropyOf_eq_entropyOf]
  symm
  unfold jointEntropyOf
  have hsplit :
      (fun x => splitUnion (alpha := alpha) a b
          (fun i : ↥(a ∪ b) => X i x)) =
        (fun x => ((fun i : a => X i x), fun i : b => X i x)) := by
    funext x
    apply Prod.ext
    · funext i
      simp only [splitUnion, Finset.restrict₂]
    · funext i
      simp only [splitUnion, Finset.restrict₂]
  rw [← hsplit]
  exact entropyOf_comp_injective p
    (fun x (i : ↥(a ∪ b)) => X i x)
    (splitUnion_injective (alpha := alpha) a b)

/--
Entropy on a three-way union is entropy of the right-associated triple of
restricted subfamilies.

All three atoms may overlap.
-/
theorem familyEntropy_tripleUnion
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b c : Finset Var) :
    familyEntropy q (a ∪ b ∪ c) =
      entropyOf q
        (fun x => (a.restrict x, (b.restrict x, c.restrict x))) := by
  rw [familyEntropy_eq_entropyOf]
  symm
  have hsplit :
      (fun x => splitTripleUnion (alpha := alpha) a b c
          ((a ∪ b ∪ c).restrict x)) =
        (fun x => (a.restrict x, (b.restrict x, c.restrict x))) := by
    funext x
    apply Prod.ext
    · funext i
      simp only [splitTripleUnion, Finset.restrict, Finset.restrict₂]
    · apply Prod.ext
      · funext i
        simp only [splitTripleUnion, Finset.restrict, Finset.restrict₂]
      · funext i
        simp only [splitTripleUnion, Finset.restrict, Finset.restrict₂]
  rw [← hsplit]
  exact entropyOf_comp_injective q (a ∪ b ∪ c).restrict
    (splitTripleUnion_injective (alpha := alpha) a b c)

/--
Source-family entropy on a three-way union is entropy of the right-associated
triple of selected subfamilies.
-/
theorem familyEntropyOf_tripleUnion
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b c : Finset Var) :
    familyEntropyOf p X (a ∪ b ∪ c) =
      entropyOf p
        (fun x =>
          ((fun i : a => X i x),
            ((fun i : b => X i x), fun i : c => X i x))) := by
  rw [familyEntropyOf_eq_entropyOf]
  symm
  have hsplit :
      (fun x => splitTripleUnion (alpha := alpha) a b c
          (fun i : ↥(a ∪ b ∪ c) => X i x)) =
        (fun x =>
          ((fun i : a => X i x),
            ((fun i : b => X i x), fun i : c => X i x))) := by
    funext x
    apply Prod.ext
    · funext i
      simp only [splitTripleUnion, Finset.restrict₂]
    · apply Prod.ext
      · funext i
        simp only [splitTripleUnion, Finset.restrict₂]
      · funext i
        simp only [splitTripleUnion, Finset.restrict₂]
  rw [← hsplit]
  exact entropyOf_comp_injective p
    (fun x (i : ↥(a ∪ b ∪ c)) => X i x)
    (splitTripleUnion_injective (alpha := alpha) a b c)

/-! ## Compatibility with pair and triple information measures -/

/--
Family conditional entropy is ordinary conditional entropy of the two
restriction-valued random variables.
-/
theorem familyCondEntropy_eq_condEntropyOf
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    familyCondEntropy q a b =
      condEntropyOf q a.restrict b.restrict := by
  rw [familyCondEntropy, condEntropyOf_eq,
    familyEntropy_union q a b, familyEntropy_eq_entropyOf q b]

/--
Source-family conditional entropy is ordinary conditional entropy of the two
selected subfamilies.
-/
theorem familyCondEntropyOf_eq_condEntropyOf
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) :
    familyCondEntropyOf p X a b =
      condEntropyOf p
        (fun x (i : a) => X i x)
        (fun x (i : b) => X i x) := by
  unfold familyCondEntropyOf
  rw [familyCondEntropy_eq_condEntropyOf]
  unfold condEntropyOf familyLawOf
  rw [PMF.map_comp]
  have hcomp :
      (fun y : (i : Var) -> alpha i => (a.restrict y, b.restrict y)) ∘
          (fun x i => X i x) =
        (fun x => ((fun i : a => X i x), fun i : b => X i x)) := by
    funext x
    apply Prod.ext
    · funext i
      rfl
    · funext i
      rfl
  rw [hcomp]

/--
Family mutual information is ordinary mutual information of the two
restriction-valued random variables.
-/
theorem familyMutualInfo_eq_mutualInfoOf
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    familyMutualInfo q a b =
      mutualInfoOf q a.restrict b.restrict := by
  rw [familyMutualInfo, mutualInfoOf_eq,
    familyEntropy_eq_entropyOf q a, familyEntropy_eq_entropyOf q b,
    familyEntropy_union q a b]

/--
Source-family mutual information is ordinary mutual information of the two
selected subfamilies.
-/
theorem familyMutualInfoOf_eq_mutualInfoOf
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) :
    familyMutualInfoOf p X a b =
      mutualInfoOf p
        (fun x (i : a) => X i x)
        (fun x (i : b) => X i x) := by
  unfold familyMutualInfoOf
  rw [familyMutualInfo_eq_mutualInfoOf]
  unfold mutualInfoOf familyLawOf
  rw [PMF.map_comp]
  have hcomp :
      (fun y : (i : Var) -> alpha i => (a.restrict y, b.restrict y)) ∘
          (fun x i => X i x) =
        (fun x => ((fun i : a => X i x), fun i : b => X i x)) := by
    funext x
    apply Prod.ext
    · funext i
      rfl
    · funext i
      rfl
  rw [hcomp]

/--
Family conditional mutual information is ordinary conditional mutual
information of the three restriction-valued random variables.
-/
theorem familyCondMutualInfo_eq_condMutualInfoOf
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b c : Finset Var) :
    familyCondMutualInfo q a b c =
      condMutualInfoOf q a.restrict b.restrict c.restrict := by
  rw [familyCondMutualInfo, condMutualInfoOf_eq,
    familyEntropy_union q a c, familyEntropy_union q b c,
    familyEntropy_tripleUnion q a b c, familyEntropy_eq_entropyOf q c]
  ring

/--
Source-family conditional mutual information is ordinary conditional mutual
information of the three selected subfamilies.
-/
theorem familyCondMutualInfoOf_eq_condMutualInfoOf
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b c : Finset Var) :
    familyCondMutualInfoOf p X a b c =
      condMutualInfoOf p
        (fun x (i : a) => X i x)
        (fun x (i : b) => X i x)
        (fun x (i : c) => X i x) := by
  unfold familyCondMutualInfoOf
  rw [familyCondMutualInfo_eq_condMutualInfoOf]
  unfold condMutualInfoOf familyLawOf
  rw [PMF.map_comp]
  have hcomp :
      (fun y : (i : Var) -> alpha i =>
          (a.restrict y, (b.restrict y, c.restrict y))) ∘
          (fun x i => X i x) =
        (fun x =>
          ((fun i : a => X i x),
            ((fun i : b => X i x), fun i : c => X i x))) := by
    funext x
    apply Prod.ext
    · funext i
      rfl
    · apply Prod.ext
      · funext i
        rfl
      · funext i
        rfl
  rw [hcomp]

/-! ### Singleton atoms -/

private theorem jointEntropyOf_restrict_singletons
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (i j : Var) :
    jointEntropyOf q
        ({i} : Finset Var).restrict ({j} : Finset Var).restrict =
      jointEntropyOf q (fun x => x i) (fun x => x j) := by
  let f :
      FamilyOutcome alpha {i} × FamilyOutcome alpha {j} ->
        alpha i × alpha j :=
    fun x =>
      (singletonFamilyOutcomeEval (alpha := alpha) i x.1,
        singletonFamilyOutcomeEval (alpha := alpha) j x.2)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Prod.ext
    · exact singletonFamilyOutcomeEval_injective i (congrArg Prod.fst hxy)
    · exact singletonFamilyOutcomeEval_injective j (congrArg Prod.snd hxy)
  symm
  simpa [jointEntropyOf, f, singletonFamilyOutcomeEval] using
    (entropyOf_comp_injective q
      (fun x =>
        (({i} : Finset Var).restrict x,
          ({j} : Finset Var).restrict x))
      hf)

private theorem entropyOf_restrict_singleton_triple
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (i j k : Var) :
    entropyOf q
        (fun x =>
          (({i} : Finset Var).restrict x,
            (({j} : Finset Var).restrict x,
              ({k} : Finset Var).restrict x))) =
      entropyOf q (fun x => (x i, (x j, x k))) := by
  let f :
      FamilyOutcome alpha {i} ×
          (FamilyOutcome alpha {j} × FamilyOutcome alpha {k}) ->
        alpha i × (alpha j × alpha k) :=
    fun x =>
      (singletonFamilyOutcomeEval (alpha := alpha) i x.1,
        (singletonFamilyOutcomeEval (alpha := alpha) j x.2.1,
          singletonFamilyOutcomeEval (alpha := alpha) k x.2.2))
  have hf : Function.Injective f := by
    intro x y hxy
    apply Prod.ext
    · exact singletonFamilyOutcomeEval_injective i (congrArg Prod.fst hxy)
    · apply Prod.ext
      · exact singletonFamilyOutcomeEval_injective j
          (congrArg (fun z => z.2.1) hxy)
      · exact singletonFamilyOutcomeEval_injective k
          (congrArg (fun z => z.2.2) hxy)
  symm
  simpa [f, singletonFamilyOutcomeEval] using
    (entropyOf_comp_injective q
      (fun x =>
        (({i} : Finset Var).restrict x,
          (({j} : Finset Var).restrict x,
            ({k} : Finset Var).restrict x)))
      hf)

/-- Singleton atoms recover conditional entropy of ordinary coordinates. -/
theorem familyCondEntropy_singletons
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (i j : Var) :
    familyCondEntropy q {i} {j} =
      condEntropyOf q (fun x => x i) (fun x => x j) := by
  have hj :
      entropyOf q ({j} : Finset Var).restrict =
        entropyOf q (fun x => x j) := by
    rw [← familyEntropy_eq_entropyOf q {j}, familyEntropy_singleton]
  calc
    familyCondEntropy q {i} {j} =
        condEntropyOf q
          ({i} : Finset Var).restrict ({j} : Finset Var).restrict :=
      familyCondEntropy_eq_condEntropyOf q {i} {j}
    _ = jointEntropyOf q
          ({i} : Finset Var).restrict ({j} : Finset Var).restrict -
        entropyOf q ({j} : Finset Var).restrict :=
      condEntropyOf_eq q _ _
    _ = jointEntropyOf q (fun x => x i) (fun x => x j) -
        entropyOf q (fun x => x j) := by
      rw [jointEntropyOf_restrict_singletons q i j, hj]
    _ = condEntropyOf q (fun x => x i) (fun x => x j) :=
      (condEntropyOf_eq q _ _).symm

/--
Singleton source-family atoms recover conditional entropy of the corresponding
ordinary random variables.
-/
theorem familyCondEntropyOf_singletons
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i) (i j : Var) :
    familyCondEntropyOf p X {i} {j} =
      condEntropyOf p (X i) (X j) := by
  simpa [familyCondEntropyOf, condEntropyOf, familyLawOf,
    PMF.map_comp, Function.comp_def] using
    (familyCondEntropy_singletons (q := familyLawOf p X) i j)

/-- Singleton atoms recover mutual information of ordinary coordinates. -/
theorem familyMutualInfo_singletons
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (i j : Var) :
    familyMutualInfo q {i} {j} =
      mutualInfoOf q (fun x => x i) (fun x => x j) := by
  have hi :
      entropyOf q ({i} : Finset Var).restrict =
        entropyOf q (fun x => x i) := by
    rw [← familyEntropy_eq_entropyOf q {i}, familyEntropy_singleton]
  have hj :
      entropyOf q ({j} : Finset Var).restrict =
        entropyOf q (fun x => x j) := by
    rw [← familyEntropy_eq_entropyOf q {j}, familyEntropy_singleton]
  calc
    familyMutualInfo q {i} {j} =
        mutualInfoOf q
          ({i} : Finset Var).restrict ({j} : Finset Var).restrict :=
      familyMutualInfo_eq_mutualInfoOf q {i} {j}
    _ = entropyOf q ({i} : Finset Var).restrict +
          entropyOf q ({j} : Finset Var).restrict -
        jointEntropyOf q
          ({i} : Finset Var).restrict ({j} : Finset Var).restrict :=
      mutualInfoOf_eq q _ _
    _ = entropyOf q (fun x => x i) + entropyOf q (fun x => x j) -
        jointEntropyOf q (fun x => x i) (fun x => x j) := by
      rw [hi, hj, jointEntropyOf_restrict_singletons q i j]
    _ = mutualInfoOf q (fun x => x i) (fun x => x j) :=
      (mutualInfoOf_eq q _ _).symm

/--
Singleton source-family atoms recover mutual information of the corresponding
ordinary random variables.
-/
theorem familyMutualInfoOf_singletons
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i) (i j : Var) :
    familyMutualInfoOf p X {i} {j} =
      mutualInfoOf p (X i) (X j) := by
  simpa [familyMutualInfoOf, mutualInfoOf, familyLawOf,
    PMF.map_comp, Function.comp_def] using
    (familyMutualInfo_singletons (q := familyLawOf p X) i j)

/--
Singleton atoms recover conditional mutual information of ordinary
coordinates.
-/
theorem familyCondMutualInfo_singletons
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (i j k : Var) :
    familyCondMutualInfo q {i} {j} {k} =
      condMutualInfoOf q (fun x => x i) (fun x => x j) (fun x => x k) := by
  have hk :
      entropyOf q ({k} : Finset Var).restrict =
        entropyOf q (fun x => x k) := by
    rw [← familyEntropy_eq_entropyOf q {k}, familyEntropy_singleton]
  calc
    familyCondMutualInfo q {i} {j} {k} =
        condMutualInfoOf q
          ({i} : Finset Var).restrict
          ({j} : Finset Var).restrict
          ({k} : Finset Var).restrict :=
      familyCondMutualInfo_eq_condMutualInfoOf q {i} {j} {k}
    _ = jointEntropyOf q
          ({i} : Finset Var).restrict ({k} : Finset Var).restrict +
          jointEntropyOf q
            ({j} : Finset Var).restrict ({k} : Finset Var).restrict -
        entropyOf q ({k} : Finset Var).restrict -
          entropyOf q
            (fun x =>
              (({i} : Finset Var).restrict x,
                (({j} : Finset Var).restrict x,
                  ({k} : Finset Var).restrict x))) :=
      condMutualInfoOf_eq q _ _ _
    _ = jointEntropyOf q (fun x => x i) (fun x => x k) +
          jointEntropyOf q (fun x => x j) (fun x => x k) -
        entropyOf q (fun x => x k) -
          entropyOf q (fun x => (x i, (x j, x k))) := by
      rw [jointEntropyOf_restrict_singletons q i k,
        jointEntropyOf_restrict_singletons q j k, hk,
        entropyOf_restrict_singleton_triple q i j k]
    _ = condMutualInfoOf q
          (fun x => x i) (fun x => x j) (fun x => x k) :=
      (condMutualInfoOf_eq q _ _ _).symm

/--
Singleton source-family atoms recover conditional mutual information of the
corresponding ordinary random variables.
-/
theorem familyCondMutualInfoOf_singletons
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i) (i j k : Var) :
    familyCondMutualInfoOf p X {i} {j} {k} =
      condMutualInfoOf p (X i) (X j) (X k) := by
  simpa [familyCondMutualInfoOf, condMutualInfoOf, familyLawOf,
    PMF.map_comp, Function.comp_def] using
    (familyCondMutualInfo_singletons (q := familyLawOf p X) i j k)

/-! ## Elementary family information identities -/

/-- Family mutual information is symmetric: `I(B;A) = I(A;B)`. -/
theorem familyMutualInfo_swap
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    familyMutualInfo q b a = familyMutualInfo q a b := by
  unfold familyMutualInfo
  rw [Finset.union_comm b a]
  ring

/-- Source-family mutual information is symmetric. -/
theorem familyMutualInfoOf_swap
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) :
    familyMutualInfoOf p X b a = familyMutualInfoOf p X a b := by
  simpa only [familyMutualInfoOf] using
    (familyMutualInfo_swap (familyLawOf p X) a b)

/--
Family conditional mutual information is symmetric in its first two atoms:
`I(B;A|C) = I(A;B|C)`.
-/
theorem familyCondMutualInfo_swap
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b c : Finset Var) :
    familyCondMutualInfo q b a c = familyCondMutualInfo q a b c := by
  unfold familyCondMutualInfo
  rw [Finset.union_comm b a]
  ring

/-- Source-family conditional mutual information is symmetric in its first two atoms. -/
theorem familyCondMutualInfoOf_swap
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b c : Finset Var) :
    familyCondMutualInfoOf p X b a c =
      familyCondMutualInfoOf p X a b c := by
  simpa only [familyCondMutualInfoOf] using
    (familyCondMutualInfo_swap (familyLawOf p X) a b c)

/-- Conditioning on the empty atom leaves family entropy unchanged. -/
@[simp]
theorem familyCondEntropy_empty_right
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a : Finset Var) :
    familyCondEntropy q a ∅ = familyEntropy q a := by
  simp [familyCondEntropy, familyEntropy_empty]

/-- The empty atom has zero conditional entropy. -/
@[simp]
theorem familyCondEntropy_empty_left
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (b : Finset Var) :
    familyCondEntropy q ∅ b = 0 := by
  simp [familyCondEntropy]

/-- Mutual information with the empty right atom is zero. -/
@[simp]
theorem familyMutualInfo_empty_right
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a : Finset Var) :
    familyMutualInfo q a ∅ = 0 := by
  simp [familyMutualInfo, familyEntropy_empty]

/-- Conditional mutual information with the empty second atom is zero. -/
@[simp]
theorem familyCondMutualInfo_empty_right
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a c : Finset Var) :
    familyCondMutualInfo q a ∅ c = 0 := by
  unfold familyCondMutualInfo
  simp only [Finset.empty_union, Finset.union_empty]
  ring

/-- Empty conditioning reduces conditional mutual information to mutual information. -/
@[simp]
theorem familyCondMutualInfo_empty_conditioning
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    familyCondMutualInfo q a b ∅ = familyMutualInfo q a b := by
  unfold familyCondMutualInfo familyMutualInfo
  rw [familyEntropy_empty]
  simp only [Finset.union_empty]
  ring

/-- The mutual information of an atom with itself is its entropy. -/
@[simp]
theorem familyMutualInfo_self
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a : Finset Var) :
    familyMutualInfo q a a = familyEntropy q a := by
  unfold familyMutualInfo
  rw [Finset.union_self]
  ring

/-- Family mutual information as `I(A;B) = H(A) - H(A|B)`. -/
theorem familyMutualInfo_eq_entropy_sub_condEntropy
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    familyMutualInfo q a b =
      familyEntropy q a - familyCondEntropy q a b := by
  unfold familyMutualInfo familyCondEntropy
  ring

/-- Source-family mutual information as `I(A;B) = H(A) - H(A|B)`. -/
theorem familyMutualInfoOf_eq_entropyOf_sub_condEntropyOf
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) :
    familyMutualInfoOf p X a b =
      familyEntropyOf p X a - familyCondEntropyOf p X a b := by
  simpa only [familyMutualInfoOf, familyEntropyOf, familyCondEntropyOf] using
    (familyMutualInfo_eq_entropy_sub_condEntropy
      (familyLawOf p X) a b)

/--
Family conditional mutual information as
`I(A;B|C) = H(A|C) - H(A|B ∪ C)`.
-/
theorem familyCondMutualInfo_eq_condEntropy_sub_condEntropy
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b c : Finset Var) :
    familyCondMutualInfo q a b c =
      familyCondEntropy q a c - familyCondEntropy q a (b ∪ c) := by
  unfold familyCondMutualInfo familyCondEntropy
  rw [← Finset.union_assoc a b c]
  ring

/--
Source-family conditional mutual information as
`I(A;B|C) = H(A|C) - H(A|B ∪ C)`.
-/
theorem familyCondMutualInfoOf_eq_condEntropyOf_sub_condEntropyOf
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b c : Finset Var) :
    familyCondMutualInfoOf p X a b c =
      familyCondEntropyOf p X a c -
        familyCondEntropyOf p X a (b ∪ c) := by
  simpa only [familyCondMutualInfoOf, familyCondEntropyOf] using
    (familyCondMutualInfo_eq_condEntropy_sub_condEntropy
      (familyLawOf p X) a b c)

/-! ## Binary set chain rules -/

/-- Right-oriented entropy chain rule: `H(A ∪ B) = H(B) + H(A | B)`. -/
theorem familyEntropy_union_chain_rule_right
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    familyEntropy q (a ∪ b) =
      familyEntropy q b + familyCondEntropy q a b := by
  unfold familyCondEntropy
  ring

/-- Left-oriented entropy chain rule: `H(A ∪ B) = H(A) + H(B | A)`. -/
theorem familyEntropy_union_chain_rule_left
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    familyEntropy q (a ∪ b) =
      familyEntropy q a + familyCondEntropy q b a := by
  unfold familyCondEntropy
  rw [Finset.union_comm b a]
  ring

/-- Right-oriented source-family entropy chain rule. -/
theorem familyEntropyOf_union_chain_rule_right
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) :
    familyEntropyOf p X (a ∪ b) =
      familyEntropyOf p X b + familyCondEntropyOf p X a b := by
  simpa only [familyEntropyOf, familyCondEntropyOf] using
    (familyEntropy_union_chain_rule_right (familyLawOf p X) a b)

/-- Left-oriented source-family entropy chain rule. -/
theorem familyEntropyOf_union_chain_rule_left
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) :
    familyEntropyOf p X (a ∪ b) =
      familyEntropyOf p X a + familyCondEntropyOf p X b a := by
  simpa only [familyEntropyOf, familyCondEntropyOf] using
    (familyEntropy_union_chain_rule_left (familyLawOf p X) a b)

/--
Mutual-information union chain rule:
`I(A ∪ B; C) = I(A; C) + I(B; C | A)`.
-/
theorem familyMutualInfo_union_chain_rule
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b c : Finset Var) :
    familyMutualInfo q (a ∪ b) c =
      familyMutualInfo q a c + familyCondMutualInfo q b c a := by
  have htriple : b ∪ c ∪ a = a ∪ b ∪ c := by
    calc
      b ∪ c ∪ a = a ∪ (b ∪ c) := Finset.union_comm (b ∪ c) a
      _ = a ∪ b ∪ c := (Finset.union_assoc a b c).symm
  unfold familyMutualInfo familyCondMutualInfo
  rw [Finset.union_comm b a, Finset.union_comm c a, htriple]
  ring

/-- Source-family mutual-information union chain rule. -/
theorem familyMutualInfoOf_union_chain_rule
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b c : Finset Var) :
    familyMutualInfoOf p X (a ∪ b) c =
      familyMutualInfoOf p X a c +
        familyCondMutualInfoOf p X b c a := by
  simpa only [familyMutualInfoOf, familyCondMutualInfoOf] using
    (familyMutualInfo_union_chain_rule (familyLawOf p X) a b c)

/--
Conditional-mutual-information union chain rule:
`I(A ∪ B; C | D) = I(A; C | D) + I(B; C | A ∪ D)`.

The four atoms may overlap; no disjointness hypothesis is required.
-/
theorem familyCondMutualInfo_union_chain_rule
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i))
    (a b c d : Finset Var) :
    familyCondMutualInfo q (a ∪ b) c d =
      familyCondMutualInfo q a c d +
        familyCondMutualInfo q b c (a ∪ d) := by
  unfold familyCondMutualInfo
  simp only [Finset.union_left_comm, Finset.union_comm]
  ring

/-- Source-family conditional-mutual-information union chain rule. -/
theorem familyCondMutualInfoOf_union_chain_rule
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b c d : Finset Var) :
    familyCondMutualInfoOf p X (a ∪ b) c d =
      familyCondMutualInfoOf p X a c d +
        familyCondMutualInfoOf p X b c (a ∪ d) := by
  simpa only [familyCondMutualInfoOf] using
    (familyCondMutualInfo_union_chain_rule
      (familyLawOf p X) a b c d)

/-! ## Ordered prefix sums

The public chain expressions are finite sums over list positions. Lists may
contain duplicate variable names; the definitions remain total, and the chain
theorems below will show that repeated coordinates contribute the appropriate
zero terms.
-/

/--
The ordered conditional-entropy sum
`∑ k, H({l[k]} | {l[0], ..., l[k-1]})`.
-/
def familyEntropyChain
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (l : List Var) : Real :=
  ∑ k : Fin l.length,
    familyCondEntropy q {l.get k} (l.take k).toFinset

/--
The ordered conditional-mutual-information sum
`∑ k, I({l[k]}; B | {l[0], ..., l[k-1]})`.
-/
def familyMutualInfoChain
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (l : List Var)
    (b : Finset Var) : Real :=
  ∑ k : Fin l.length,
    familyCondMutualInfo q {l.get k} b (l.take k).toFinset

/-! ## Ordered entropy chain rule -/

private def familyEntropyChainAux
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (s : Finset Var) :
    List Var -> Real
  | [] => 0
  | i :: l =>
      familyCondEntropy q {i} s +
        familyEntropyChainAux q (s ∪ {i}) l

private theorem familyEntropyChain_sum_eq_aux
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (s : Finset Var) (l : List Var) :
    (∑ k : Fin l.length,
      familyCondEntropy q {l.get k}
        (s ∪ (l.take k).toFinset)) =
      familyEntropyChainAux q s l := by
  induction l generalizing s with
  | nil =>
      simp [familyEntropyChainAux]
  | cons i l ih =>
      change
        (∑ k : Fin (l.length + 1),
          familyCondEntropy q {(i :: l).get k}
            (s ∪ ((i :: l).take k).toFinset)) =
          familyEntropyChainAux q s (i :: l)
      rw [Fin.sum_univ_succ]
      simp [familyEntropyChainAux]
      simpa only [Finset.insert_union, List.get_eq_getElem] using ih (insert i s)

private theorem union_cons_toFinset
    {Var : Type u} [DecidableEq Var]
    (s : Finset Var) (i : Var) (l : List Var) :
    s ∪ (i :: l).toFinset = (s ∪ {i}) ∪ l.toFinset := by
  ext j
  simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  tauto

private theorem familyEntropy_union_eq_add_chainAux
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (s : Finset Var) (l : List Var) :
    familyEntropy q (s ∪ l.toFinset) =
      familyEntropy q s + familyEntropyChainAux q s l := by
  induction l generalizing s with
  | nil =>
      simp [familyEntropyChainAux]
  | cons i l ih =>
      rw [union_cons_toFinset, ih, familyEntropy_union_chain_rule_left]
      simp [familyEntropyChainAux, add_assoc]

private theorem familyEntropyChain_eq_aux
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (l : List Var) :
    familyEntropyChain q l = familyEntropyChainAux q ∅ l := by
  simpa [familyEntropyChain] using
    familyEntropyChain_sum_eq_aux q ∅ l

/--
Entropy chain rule for an arbitrary ordered list of variable names.

Repeated names are allowed: once a name has appeared, its later conditional
entropy contribution is zero.
-/
theorem familyEntropy_eq_entropyChain
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (l : List Var) :
    familyEntropy q l.toFinset = familyEntropyChain q l := by
  calc
    familyEntropy q l.toFinset =
        familyEntropy q ∅ + familyEntropyChainAux q ∅ l := by
      simpa using familyEntropy_union_eq_add_chainAux q ∅ l
    _ = familyEntropyChainAux q ∅ l := by
      rw [familyEntropy_empty, zero_add]
    _ = familyEntropyChain q l :=
      (familyEntropyChain_eq_aux q l).symm

/-- Source-family entropy chain rule for an arbitrary ordered list. -/
theorem familyEntropyOf_eq_entropyChain
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i) (l : List Var) :
    familyEntropyOf p X l.toFinset =
      familyEntropyChain (familyLawOf p X) l := by
  simpa only [familyEntropyOf] using
    familyEntropy_eq_entropyChain (familyLawOf p X) l

/--
Textbook entropy chain rule for a list of distinct variable names.

The `Nodup` assumption records the textbook indexing convention; the primary
chain rule above is stronger and also handles repeated names.
-/
theorem familyEntropy_chain_rule_of_nodup
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (l : List Var) (_hl : l.Nodup) :
    familyEntropy q l.toFinset =
      ∑ k : Fin l.length,
        familyCondEntropy q {l.get k} (l.take k).toFinset := by
  simpa only [familyEntropyChain] using
    familyEntropy_eq_entropyChain q l

/-- Source-family textbook entropy chain rule for distinct variable names. -/
theorem familyEntropyOf_chain_rule_of_nodup
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (l : List Var) (_hl : l.Nodup) :
    familyEntropyOf p X l.toFinset =
      ∑ k : Fin l.length,
        familyCondEntropyOf p X {l.get k} (l.take k).toFinset := by
  simpa only [familyEntropyChain, familyCondEntropyOf] using
    familyEntropyOf_eq_entropyChain p X l

/-! ## Ordered mutual-information chain rule -/

private def familyMutualInfoChainAux
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (b s : Finset Var) :
    List Var -> Real
  | [] => 0
  | i :: l =>
      familyCondMutualInfo q {i} b s +
        familyMutualInfoChainAux q b (s ∪ {i}) l

private theorem familyMutualInfoChain_sum_eq_aux
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (b s : Finset Var)
    (l : List Var) :
    (∑ k : Fin l.length,
      familyCondMutualInfo q {l.get k} b
        (s ∪ (l.take k).toFinset)) =
      familyMutualInfoChainAux q b s l := by
  induction l generalizing s with
  | nil =>
      simp [familyMutualInfoChainAux]
  | cons i l ih =>
      change
        (∑ k : Fin (l.length + 1),
          familyCondMutualInfo q {(i :: l).get k} b
            (s ∪ ((i :: l).take k).toFinset)) =
          familyMutualInfoChainAux q b s (i :: l)
      rw [Fin.sum_univ_succ]
      simp [familyMutualInfoChainAux]
      simpa only [Finset.insert_union, List.get_eq_getElem] using ih (insert i s)

private theorem familyMutualInfo_union_eq_add_chainAux
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (b s : Finset Var)
    (l : List Var) :
    familyMutualInfo q (s ∪ l.toFinset) b =
      familyMutualInfo q s b + familyMutualInfoChainAux q b s l := by
  induction l generalizing s with
  | nil =>
      simp [familyMutualInfoChainAux]
  | cons i l ih =>
      rw [union_cons_toFinset, ih, familyMutualInfo_union_chain_rule]
      simp [familyMutualInfoChainAux, add_assoc]

private theorem familyMutualInfoChain_eq_aux
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (l : List Var) (b : Finset Var) :
    familyMutualInfoChain q l b =
      familyMutualInfoChainAux q b ∅ l := by
  simpa [familyMutualInfoChain] using
    familyMutualInfoChain_sum_eq_aux q b ∅ l

/--
Mutual-information chain rule for an arbitrary ordered list of variable names.

Repeated names are allowed, and the atom `b` may overlap the list.
-/
theorem familyMutualInfo_eq_mutualInfoChain
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (l : List Var) (b : Finset Var) :
    familyMutualInfo q l.toFinset b =
      familyMutualInfoChain q l b := by
  have hempty : familyMutualInfo q ∅ b = 0 := by
    calc
      familyMutualInfo q ∅ b =
          familyMutualInfo q b ∅ :=
        familyMutualInfo_swap q b ∅
      _ = 0 := familyMutualInfo_empty_right q b
  calc
    familyMutualInfo q l.toFinset b =
        familyMutualInfo q ∅ b +
          familyMutualInfoChainAux q b ∅ l := by
      simpa using familyMutualInfo_union_eq_add_chainAux q b ∅ l
    _ = familyMutualInfoChainAux q b ∅ l := by
      rw [hempty, zero_add]
    _ = familyMutualInfoChain q l b :=
      (familyMutualInfoChain_eq_aux q l b).symm

/-- Source-family mutual-information chain rule for an arbitrary ordered list. -/
theorem familyMutualInfoOf_eq_mutualInfoChain
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (l : List Var) (b : Finset Var) :
    familyMutualInfoOf p X l.toFinset b =
      familyMutualInfoChain (familyLawOf p X) l b := by
  simpa only [familyMutualInfoOf] using
    familyMutualInfo_eq_mutualInfoChain (familyLawOf p X) l b

/--
Textbook mutual-information chain rule for distinct variable names.

The primary chain rule above is stronger and also handles repeated names.
-/
theorem familyMutualInfo_chain_rule_of_nodup
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (l : List Var)
    (b : Finset Var) (_hl : l.Nodup) :
    familyMutualInfo q l.toFinset b =
      ∑ k : Fin l.length,
        familyCondMutualInfo q {l.get k} b
          (l.take k).toFinset := by
  simpa only [familyMutualInfoChain] using
    familyMutualInfo_eq_mutualInfoChain q l b

/--
Source-family textbook mutual-information chain rule for distinct variable
names.
-/
theorem familyMutualInfoOf_chain_rule_of_nodup
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (l : List Var) (b : Finset Var) (_hl : l.Nodup) :
    familyMutualInfoOf p X l.toFinset b =
      ∑ k : Fin l.length,
        familyCondMutualInfoOf p X {l.get k} b
          (l.take k).toFinset := by
  simpa only [familyMutualInfoChain, familyCondMutualInfoOf] using
    familyMutualInfoOf_eq_mutualInfoChain p X l b

/-! ## Ordered conditional-mutual-information chain rule -/

/--
Conditional-mutual-information chain rule for an arbitrary ordered list of
variable names:
`I(l; B | C) = ∑ k, I({l[k]}; B | C ∪ {l[0], ..., l[k-1]})`.

Repeated names are allowed, including names already present in the
conditioning atom.
-/
theorem familyCondMutualInfo_chain_rule
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (l : List Var)
    (b c : Finset Var) :
    familyCondMutualInfo q l.toFinset b c =
      ∑ k : Fin l.length,
        familyCondMutualInfo q {l.get k} b
          (c ∪ (l.take k).toFinset) := by
  induction l generalizing c with
  | nil =>
      simp [familyCondMutualInfo]
  | cons i l ih =>
      rw [List.toFinset_cons, ← Finset.singleton_union]
      rw [familyCondMutualInfo_union_chain_rule]
      change
        familyCondMutualInfo q {i} b c +
            familyCondMutualInfo q l.toFinset b ({i} ∪ c) =
          ∑ k : Fin (l.length + 1),
            familyCondMutualInfo q {(i :: l).get k} b
              (c ∪ ((i :: l).take k).toFinset)
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, List.get_cons_zero, List.take_zero,
        List.toFinset_nil, Finset.union_empty]
      rw [ih]
      congr 1
      apply Fintype.sum_congr
      intro k
      simp only [Fin.val_succ, List.take_succ_cons,
        List.toFinset_cons]
      have hcond :
          {i} ∪ c ∪ (l.take k).toFinset =
            c ∪ insert i (l.take k).toFinset := by
        ext j
        simp only [Finset.mem_union, Finset.mem_singleton,
          Finset.mem_insert]
        tauto
      rw [hcond]
      have hget : (i :: l).get k.succ = l.get k := by
        exact List.get_cons_succ
      rw [hget]

/--
Source-family ordered conditional-mutual-information chain rule. As in the
law-facing theorem, repeated names and names already in the conditioning atom
are allowed.
-/
theorem familyCondMutualInfoOf_chain_rule
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (l : List Var) (b c : Finset Var) :
    familyCondMutualInfoOf p X l.toFinset b c =
      ∑ k : Fin l.length,
        familyCondMutualInfoOf p X {l.get k} b
          (c ∪ (l.take k).toFinset) := by
  simpa only [familyCondMutualInfoOf] using
    (familyCondMutualInfo_chain_rule
      (familyLawOf p X) l b c)

end

end Shannon
end LeanInfoTheory
