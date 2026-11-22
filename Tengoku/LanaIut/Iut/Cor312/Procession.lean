/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Capsules and processions (taxis #43)

Combinatorial backbone of the **large volume container** of the Corollary 3.12 variant
(taxis #33): capsules of labels and processions of capsules, together with the standard
label sets `S_{j+1} = {0, 1, …, j}` of the procession of tensor-packets of log-shells.

## Source correspondence

* Capsules and processions of label sets: IUT I, §§4–6 (in particular the processions of
  ±-label capsules of IUT I, Proposition 6.9).
* The label sets `S_{j+1}` and the procession whose `j`-th capsule has label set
  `S_{j+1}` (`j = 1, …, ℓ*`): IUT III, Propositions 3.1–3.3; Hoshi, *Introduction to
  inter-universal Teichmüller theory (continued)*, §13.

This module records only the combinatorics: the tensor-packets themselves are built on
top of these labels in `Iut.Cor312.Container`. Nothing here asserts any statement of the
IUT papers; the definitions are plain finite combinatorics.

## Main definitions

* `Iut.procLabels j`: the label set `S_{j+1} = {0, …, j}` as a `Finset ℕ`.
* `Iut.Capsule`: a capsule of labels, i.e. a finite set of labels.
* `Iut.Procession`: an increasing chain of capsules together with its inclusion maps.
* `Iut.Procession.standard n`: the standard procession `S_2 ⊆ S_3 ⊆ ⋯ ⊆ S_{n+1}` of the
  tensor-packet construction, with `n = ℓ* = (ℓ - 1)/2` in the intended instantiation.
-/

namespace Iut

/-- The label set `S_{j+1} = {0, 1, …, j}` of IUT III, Propositions 3.1–3.3, a finite
set of `j + 1` labels. The index convention follows the papers: the *subscript* of `S`
is the cardinality, so `procLabels j` is the set called `S_{j+1}`. -/
def procLabels (j : ℕ) : Finset ℕ := Finset.Iic j

/--
@isnad1 id=eq.0h1v.s4.5d9c01c30434 from=translated src=- shape=2957bb08 vocab=2258fb47
-/
@[simp]
lemma card_procLabels (j : ℕ) : (procLabels j).card = j + 1 := Nat.card_Iic j

/--
@isnad1 id=iff.0h2v.s4.9964fd77ab5e from=translated src=- shape=0a5e357a vocab=f313c788
-/
@[simp]
lemma mem_procLabels {i j : ℕ} : i ∈ procLabels j ↔ i ≤ j := Finset.mem_Iic

/--
@isnad1 id=le.1h2v.s4.24ae11baef6f from=translated src=- shape=1e5c1409 vocab=b666589f
-/
lemma procLabels_mono {i j : ℕ} (h : i ≤ j) : procLabels i ⊆ procLabels j :=
  Finset.Iic_subset_Iic.mpr h

/-- A **capsule** of labels drawn from `ι`: a finite collection of labels
(IUT I, §4). The objects indexed by a capsule (prime strips, log-shells, …) are
attached on top of this combinatorial datum by the container modules. -/
structure Capsule (ι : Type*) where
  /-- The finite set of labels of the capsule. -/
  labels : Finset ι

namespace Capsule

variable {ι : Type*}

/-- The number of labels of a capsule. -/
def card (S : Capsule ι) : ℕ := S.labels.card

/-- The label set of a capsule, as a type. -/
def LabelType (S : Capsule ι) : Type _ := S.labels

instance [DecidableEq ι] (S : Capsule ι) : DecidableEq S.LabelType :=
  inferInstanceAs (DecidableEq S.labels)

instance (S : Capsule ι) : Fintype S.LabelType :=
  inferInstanceAs (Fintype S.labels)

end Capsule

/-- A **procession** of capsules (IUT I, §§4–6): a finite increasing chain of capsules.
The inclusion maps of the chain are recorded by `labels_mono`; see
`Procession.inclusion` for the induced maps of label types. -/
structure Procession (ι : Type*) where
  /-- The number of capsules in the procession. -/
  length : ℕ
  /-- The capsules of the procession. -/
  capsule : Fin length → Capsule ι
  /-- Monotonicity: the labels of the capsules form an increasing chain. This datum
  encodes the inclusion maps of the procession. -/
  labels_mono : ∀ ⦃i j : Fin length⦄, i ≤ j → (capsule i).labels ⊆ (capsule j).labels

namespace Procession

variable {ι : Type*} (P : Procession ι)

/-- The inclusion map between the label types of two capsules of a procession. -/
def inclusion {i j : Fin P.length} (h : i ≤ j) :
    (P.capsule i).LabelType → (P.capsule j).LabelType :=
  fun a => ⟨a.1, P.labels_mono h a.2⟩

/--
@isnad1 id=eq.1h5v.s6.bdf3a9180857 from=translated src=- shape=8e1db1f5 vocab=24b99035
-/
@[simp]
lemma inclusion_coe {i j : Fin P.length} (h : i ≤ j) (a : (P.capsule i).LabelType) :
    (P.inclusion h a).1 = a.1 := rfl

/-- The **standard procession** of the tensor-packet construction: the chain
`S_2 ⊆ S_3 ⊆ ⋯ ⊆ S_{n+1}` of label sets, where the `i`-th capsule (`i = 0, …, n-1`,
corresponding to the paper's index `j = i + 1 ∈ {1, …, ℓ*}`) has label set
`S_{j+1} = {0, 1, …, j}`. In the intended instantiation `n = ℓ* = (ℓ - 1)/2` for the
prime `ℓ` of the initial Θ-data (IUT III, Propositions 3.1–3.3). -/
def standard (n : ℕ) : Procession ℕ where
  length := n
  capsule i := ⟨procLabels (i + 1)⟩
  labels_mono i j h := procLabels_mono (by exact Nat.add_le_add_right h 1)

/--
@isnad1 id=eq.0h1v.s3.a214124a1ebc from=translated src=- shape=9baae94e vocab=ce116da2
-/
@[simp]
lemma standard_length (n : ℕ) : (standard n).length = n := rfl

/--
@isnad1 id=eq.0h2v.s4.72874f5234bf from=translated src=- shape=d0dada2c vocab=3c714104
-/
@[simp]
lemma standard_capsule_labels (n : ℕ) (i : Fin n) :
    ((standard n).capsule i).labels = procLabels (i + 1) := rfl

/-- The `i`-th capsule of the standard procession has `i + 2` labels: it is the label
set `S_{j+1}` with `j = i + 1`, of cardinality `j + 1`.
@isnad1 id=eq.0h2v.s4.ddbb71cee097 from=translated src=- shape=4e121a63 vocab=5a90598d
-/
lemma standard_capsule_card (n : ℕ) (i : Fin n) :
    ((standard n).capsule i).card = i + 2 := by
  simp [Capsule.card, standard]

end Procession

end Iut
