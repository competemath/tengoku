/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.FiniteFamily
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.Theorems

/-!
# Semantic theorems for finite subfamilies

This file begins the semantic layer for entropy of finite restrictions of a
possibly infinite family of finite-valued random variables.

The monotonicity proof compares only the finite marginal laws on two atoms.
When `s ⊆ t`, `familyMarginal_restrict` identifies the `s`-marginal as a
deterministic image of the `t`-marginal, so `entropy_map_le` applies. In
particular, the proof never forms the finite entropy of the unrestricted
full-family law.

Family mutual-information nonnegativity passes through the existing
restriction-valued random-variable bridge. Its entropy upper bounds and the
conditioning-reduces-entropy theorem are then atom-native consequences of the
family entropy-difference identities, conditional-entropy nonnegativity, and
mutual-information symmetry.

The additional-conditioning theorem formalizes the inequality
`H(A | B ∪ C) ≤ H(A | C)` from Cover--Thomas Theorem 2.6.5. Its equality
characterization is not included. Binary subadditivity then follows from the
family entropy chain rule and conditioning reduction.

N-way subadditivity bounds the entropy of a finite atom by the sum of its
singleton entropies. The corresponding equality characterization by mutual
independence is developed in the separate downstream
`LeanInfoTheory.Shannon.SemanticBridge.FiniteFamilyIndependence` module.

Submodularity is stated as nonnegativity of
`H(A) + H(B) - H(A ∪ B) - H(A ∩ B)`, directly in terms of finite-family
entropy.
-/

namespace LeanInfoTheory
namespace Shannon

open scoped BigOperators

universe u v w

noncomputable section

/-- Entropy is monotone under inclusion of finite family atoms.
@isnad1 id=le.1h5v.s5.3ede7a3461ff from=translated src=- shape=c40ebe67 vocab=f4285a97
-/
theorem familyEntropy_mono
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) {s t : Finset Var}
    (hst : s ⊆ t) :
    familyEntropy q s ≤ familyEntropy q t := by
  change entropy (familyMarginal q s) ≤ entropy (familyMarginal q t)
  rw [← familyMarginal_restrict q hst]
  exact
    entropy_map_le (familyMarginal q t) (Finset.restrict₂ hst)

/-- Source-family entropy is monotone under inclusion of finite atoms.
@isnad1 id=le.1h7v.s6.f72ec617391f from=translated src=- shape=70014649 vocab=b17a7ea9
-/
theorem familyEntropyOf_mono
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    {s t : Finset Var} (hst : s ⊆ t) :
    familyEntropyOf p X s ≤ familyEntropyOf p X t :=
  familyEntropy_mono (familyLawOf p X) hst

/-- Conditional entropy of two finite subfamilies is nonnegative.
@isnad1 id=le.0h5v.s5.29c9ff459461 from=translated src=- shape=24c832bb vocab=9bf108e2
-/
theorem familyCondEntropy_nonneg
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    0 ≤ familyCondEntropy q a b := by
  unfold familyCondEntropy
  exact sub_nonneg.mpr (familyEntropy_mono q Finset.subset_union_right)

/-- Conditional entropy of two finite source-indexed subfamilies is nonnegative.
@isnad1 id=le.0h7v.s5.7617bedd65d4 from=translated src=- shape=421ddd48 vocab=b66343f2
-/
theorem familyCondEntropyOf_nonneg
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) :
    0 ≤ familyCondEntropyOf p X a b := by
  simpa only [familyCondEntropyOf] using
    familyCondEntropy_nonneg (familyLawOf p X) a b

/-! ## Conditional mutual information and submodularity -/

/-- Conditional mutual information of finite subfamilies is nonnegative.
@isnad1 id=le.0h6v.s5.9c2b8bbc5a8b from=translated src=- shape=8240dfcc vocab=7b641470
-/
theorem familyCondMutualInfo_nonneg
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b c : Finset Var) :
    0 ≤ familyCondMutualInfo q a b c := by
  rw [familyCondMutualInfo_eq_condMutualInfoOf]
  exact condMutualInfoOf_nonneg q a.restrict b.restrict c.restrict

/--
Conditional mutual information of finite source-indexed subfamilies is
nonnegative.
@isnad1 id=le.0h8v.s5.053a36cc2d2a from=translated src=- shape=f2a658b8 vocab=ea23ef42
-/
theorem familyCondMutualInfoOf_nonneg
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b c : Finset Var) :
    0 ≤ familyCondMutualInfoOf p X a b c := by
  exact familyCondMutualInfo_nonneg (familyLawOf p X) a b c

/--
Entropy of finite family atoms is submodular:
`H(A) + H(B) - H(A ∪ B) - H(A ∩ B) ≥ 0`.
@isnad1 id=le.0h5v.s6.bcdf5a27dd7e from=translated src=- shape=ae849b43 vocab=68c60d8d
-/
theorem familyEntropy_submodular
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    0 ≤ familyEntropy q a + familyEntropy q b -
      familyEntropy q (a ∪ b) - familyEntropy q (a ∩ b) := by
  have ha : a ∪ (a ∩ b) = a := by
    ext i
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  have hb : b ∪ (a ∩ b) = b := by
    ext i
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  have hab : a ∪ b ∪ (a ∩ b) = a ∪ b := by
    ext i
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  have h := familyCondMutualInfo_nonneg q a b (a ∩ b)
  unfold familyCondMutualInfo at h
  rw [ha, hb, hab] at h
  exact h

/-- Entropy of finite source-indexed family atoms is submodular.
@isnad1 id=le.0h7v.s6.94c5e6a3607f from=translated src=- shape=4e75656f vocab=aa518529
-/
theorem familyEntropyOf_submodular
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) :
    0 ≤ familyEntropyOf p X a + familyEntropyOf p X b -
      familyEntropyOf p X (a ∪ b) - familyEntropyOf p X (a ∩ b) := by
  exact familyEntropy_submodular (familyLawOf p X) a b

/-! ## Mutual information and entropy bounds -/

/-- Mutual information of two finite subfamilies is nonnegative.
@isnad1 id=le.0h5v.s5.905bfeced83e from=translated src=- shape=24c832bb vocab=bee77025
-/
theorem familyMutualInfo_nonneg
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    0 ≤ familyMutualInfo q a b := by
  rw [familyMutualInfo_eq_mutualInfoOf]
  unfold mutualInfoOf
  exact mutualInfo_nonneg _

/-- Mutual information of two finite source-indexed subfamilies is nonnegative.
@isnad1 id=le.0h7v.s5.14b0eb5e9f2f from=translated src=- shape=421ddd48 vocab=93913897
-/
theorem familyMutualInfoOf_nonneg
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) :
    0 ≤ familyMutualInfoOf p X a b := by
  exact familyMutualInfo_nonneg (familyLawOf p X) a b

/-- Family mutual information is at most the entropy of its left atom.
@isnad1 id=le.0h5v.s5.c4f08eec79fd from=translated src=- shape=804da42f vocab=224c13d2
-/
theorem familyMutualInfo_le_entropy_left
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    familyMutualInfo q a b ≤ familyEntropy q a := by
  rw [familyMutualInfo_eq_entropy_sub_condEntropy]
  exact sub_le_self _ (familyCondEntropy_nonneg q a b)

/-- Family mutual information is at most the entropy of its right atom.
@isnad1 id=le.0h5v.s5.5c87f8c769db from=translated src=- shape=f5c3acae vocab=224c13d2
-/
theorem familyMutualInfo_le_entropy_right
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    familyMutualInfo q a b ≤ familyEntropy q b := by
  calc
    familyMutualInfo q a b = familyMutualInfo q b a :=
      familyMutualInfo_swap q b a
    _ ≤ familyEntropy q b := familyMutualInfo_le_entropy_left q b a

/-- Source-family mutual information is at most the entropy of its left atom.
@isnad1 id=le.0h7v.s5.7dfbd3e8f20c from=translated src=- shape=9efadfc2 vocab=b084ec53
-/
theorem familyMutualInfoOf_le_entropyOf_left
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) :
    familyMutualInfoOf p X a b ≤ familyEntropyOf p X a := by
  exact familyMutualInfo_le_entropy_left (familyLawOf p X) a b

/-- Source-family mutual information is at most the entropy of its right atom.
@isnad1 id=le.0h7v.s5.a875f7977fe9 from=translated src=- shape=a31ab723 vocab=b084ec53
-/
theorem familyMutualInfoOf_le_entropyOf_right
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) :
    familyMutualInfoOf p X a b ≤ familyEntropyOf p X b := by
  exact familyMutualInfo_le_entropy_right (familyLawOf p X) a b

/-- Conditioning on a finite family atom cannot increase family entropy.
@isnad1 id=le.0h5v.s5.956de496ef55 from=translated src=- shape=804da42f vocab=74215306
-/
theorem familyCondEntropy_le_entropy
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    familyCondEntropy q a b ≤ familyEntropy q a := by
  have h := familyMutualInfo_nonneg q a b
  rw [familyMutualInfo_eq_entropy_sub_condEntropy] at h
  exact sub_nonneg.mp h

/-- Conditioning cannot increase entropy for finite source-indexed subfamilies.
@isnad1 id=le.0h7v.s5.0b901be3e8fb from=translated src=- shape=9efadfc2 vocab=7f8e704a
-/
theorem familyCondEntropyOf_le_entropyOf
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) :
    familyCondEntropyOf p X a b ≤ familyEntropyOf p X a := by
  exact familyCondEntropy_le_entropy (familyLawOf p X) a b

/-! ## Additional conditioning and binary subadditivity -/

/-- Adding a finite conditioning atom cannot increase family conditional entropy.
@isnad1 id=le.0h6v.s5.d14d7579fc7e from=translated src=- shape=6788f3e3 vocab=10ec8593
-/
theorem familyCondEntropy_union_le_condEntropy
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b c : Finset Var) :
    familyCondEntropy q a (b ∪ c) ≤ familyCondEntropy q a c := by
  have h := familyCondMutualInfo_nonneg q a b c
  rw [familyCondMutualInfo_eq_condEntropy_sub_condEntropy] at h
  exact sub_nonneg.mp h

/--
Adding a finite conditioning atom cannot increase source-family conditional
entropy.
@isnad1 id=le.0h8v.s6.eb49bcbe7153 from=translated src=- shape=0af00b4c vocab=8b1398ba
-/
theorem familyCondEntropyOf_union_le_condEntropyOf
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b c : Finset Var) :
    familyCondEntropyOf p X a (b ∪ c) ≤ familyCondEntropyOf p X a c := by
  exact
    familyCondEntropy_union_le_condEntropy (familyLawOf p X) a b c

/-- Entropy of a union of two finite family atoms is subadditive.
@isnad1 id=le.0h5v.s6.ac87c2dad047 from=translated src=- shape=b88f7142 vocab=0dee9f23
-/
theorem familyEntropy_union_le_add
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (a b : Finset Var) :
    familyEntropy q (a ∪ b) ≤ familyEntropy q a + familyEntropy q b := by
  calc
    familyEntropy q (a ∪ b) =
        familyEntropy q b + familyCondEntropy q a b :=
      familyEntropy_union_chain_rule_right q a b
    _ ≤ familyEntropy q b + familyEntropy q a :=
      add_le_add_right (familyCondEntropy_le_entropy q a b) _
    _ = familyEntropy q a + familyEntropy q b := add_comm _ _

/-- Source-family entropy of a union of two finite atoms is subadditive.
@isnad1 id=le.0h7v.s6.050164da950e from=translated src=- shape=5ecd979e vocab=897b7f89
-/
theorem familyEntropyOf_union_le_add
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (a b : Finset Var) :
    familyEntropyOf p X (a ∪ b) ≤
      familyEntropyOf p X a + familyEntropyOf p X b := by
  exact familyEntropy_union_le_add (familyLawOf p X) a b

/-! ## N-way entropy subadditivity -/

/-- Family entropy is at most the sum of the selected singleton entropies.
@isnad1 id=le.0h4v.s5.28d946dc96df from=translated src=- shape=334c52bc vocab=adb496fb
-/
theorem familyEntropy_le_sum_singletons
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (s : Finset Var) :
    familyEntropy q s ≤ ∑ i ∈ s, familyEntropy q {i} := by
  induction s using Finset.induction_on with
  | empty =>
      simp [familyEntropy_empty]
  | insert i s hi ih =>
      calc
        familyEntropy q (insert i s) =
            familyEntropy q ({i} ∪ s) := by
          rw [Finset.singleton_union]
        _ ≤ familyEntropy q {i} + familyEntropy q s :=
          familyEntropy_union_le_add q {i} s
        _ ≤ familyEntropy q {i} + ∑ j ∈ s, familyEntropy q {j} :=
          add_le_add_right ih _
        _ = ∑ j ∈ insert i s, familyEntropy q {j} := by
          rw [Finset.sum_insert hi]

/--
Source-family entropy is at most the sum of the selected singleton
entropies.
@isnad1 id=le.0h6v.s6.5e8149b20157 from=translated src=- shape=7dea2d81 vocab=cf5c1747
-/
theorem familyEntropyOf_le_sum_singletons
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (s : Finset Var) :
    familyEntropyOf p X s ≤
      ∑ i ∈ s, familyEntropyOf p X {i} := by
  exact familyEntropy_le_sum_singletons (familyLawOf p X) s

/--
Textbook n-way entropy subadditivity for a list of distinct variable names.
@isnad1 id=le.1h4v.s6.9a7af741c639 from=translated src=- shape=f09d2c1b vocab=b021c6b3
-/
theorem familyEntropy_subadditivity_of_nodup
    {Var : Type u} {alpha : Var -> Type v}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (q : PMF ((i : Var) -> alpha i)) (l : List Var) (hl : l.Nodup) :
    familyEntropy q l.toFinset ≤
      ∑ k : Fin l.length, familyEntropy q {l.get k} := by
  rw [familyEntropy_chain_rule_of_nodup q l hl]
  exact Finset.sum_le_sum fun k _ =>
    familyCondEntropy_le_entropy q {l.get k} (l.take k).toFinset

/--
Source-family textbook n-way entropy subadditivity for distinct variable
names.
@isnad1 id=le.1h6v.s6.e8cce22d9621 from=translated src=- shape=13649c89 vocab=aad375b7
-/
theorem familyEntropyOf_subadditivity_of_nodup
    {Var : Type u} {alpha : Var -> Type v} {omega : Type w}
    [DecidableEq Var] [forall i, Fintype (alpha i)]
    (p : PMF omega) (X : (i : Var) -> omega -> alpha i)
    (l : List Var) (hl : l.Nodup) :
    familyEntropyOf p X l.toFinset ≤
      ∑ k : Fin l.length, familyEntropyOf p X {l.get k} := by
  exact familyEntropy_subadditivity_of_nodup (familyLawOf p X) l hl

end

end Shannon
end LeanInfoTheory
