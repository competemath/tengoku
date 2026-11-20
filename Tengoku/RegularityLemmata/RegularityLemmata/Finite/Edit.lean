/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.Density
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.Injective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Edit sets and edit distance

The edit set of two relations on a box is the finset of tuples where they disagree; the
edit distance is its cardinality (a raw `ℕ` count), and the relative edit distance its
density. Disagreement is phrased as `¬ (R₁ x ↔ R₂ x)`, which is decidable from
`DecidablePred` instances, so edit sets and distances are computable.

Besides the metric laws (symmetry, triangle inequality), the file provides the budget
lemmas used by removal arguments: monotonicity in the box, summation along a chain of
relations, and the split of the full-box edit distance into an injective part plus the
collision count from `RegularityLemmata.Finite.Injective`.

It also provides the **bridges to tuple counting**: when one relation is constant on the box
the edit distance is a plain `tupleCount`, and a `tupleDensity` bound on the other becomes a
count bound against the box mass. These relate two pinned definitions and introduce no second
counting layer — every counting primitive they use comes from
`RegularityLemmata.Finite.Density`.

Coordinates are indexed by an **arbitrary** finite type `ι` with decidable equality, matching
`RegularityLemmata.Finite.Density`. Nothing here uses the order structure of `Fin k`; the
chain-summation lemma indexes its *chain* by `Fin (m + 1)`, which is a separate index and
stays as it is.
-/

namespace RegularityLemmata

variable {α : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R₁ R₂ R₃ : (ι → α) → Prop}
  [DecidablePred R₁] [DecidablePred R₂] [DecidablePred R₃]
variable {A B : ι → Finset α}

/-! ### Edit sets -/

/-- The tuples of the box `A` on which `R₁` and `R₂` disagree.-/
def editSet (R₁ R₂ : (ι → α) → Prop) [DecidablePred R₁] [DecidablePred R₂]
    (A : ι → Finset α) : Finset (ι → α) :=
  (Fintype.piFinset A).filter fun x => ¬ (R₁ x ↔ R₂ x)

/--
@isnad1 id=iff.0h6v.s6.3f896fa2e29c from=translated src=- shape=19c95cc4 vocab=933c4bbd
-/
@[simp] theorem mem_editSet {x : ι → α} :
    x ∈ editSet R₁ R₂ A ↔ x ∈ Fintype.piFinset A ∧ ¬ (R₁ x ↔ R₂ x) := by
  simp [editSet]

/--
@isnad1 id=eq.0h5v.s6.7c9c30d95b6a from=translated src=- shape=0533bdc6 vocab=4bbeffd3
-/
theorem editSet_comm : editSet R₁ R₂ A = editSet R₂ R₁ A := by
  simp only [editSet]
  exact Finset.filter_congr fun x _ => by tauto

/-! ### Edit distance -/

/-- The number of tuples of the box on which the relations disagree.-/
def editDistance (R₁ R₂ : (ι → α) → Prop) [DecidablePred R₁] [DecidablePred R₂]
    (A : ι → Finset α) : ℕ :=
  (editSet R₁ R₂ A).card

/--
@isnad1 id=eq.0h5v.s5.3336a8f278c2 from=translated src=- shape=53e16e43 vocab=d2731d1a
-/
theorem editDistance_comm : editDistance R₁ R₂ A = editDistance R₂ R₁ A := by
  rw [editDistance, editDistance, editSet_comm]

/--
@isnad1 id=eq.0h4v.s5.a37a1d249f40 from=translated src=- shape=9a4cd4af vocab=d2731d1a
-/
@[simp] theorem editDistance_self : editDistance R₁ R₁ A = 0 := by
  simp [editDistance, editSet]

/--
@isnad1 id=le.0h5v.s6.21563adc1918 from=translated src=- shape=900b5581 vocab=c6644327
-/
theorem editDistance_le_card :
    editDistance R₁ R₂ A ≤ (Fintype.piFinset A).card :=
  Finset.card_filter_le _ _

/--
@isnad1 id=le.0h6v.s6.8bcad69d1e3a from=translated src=- shape=78840c6c vocab=596ed669
-/
theorem editDistance_triangle :
    editDistance R₁ R₃ A ≤ editDistance R₁ R₂ A + editDistance R₂ R₃ A := by
  classical
  have hsub : editSet R₁ R₃ A ⊆ editSet R₁ R₂ A ∪ editSet R₂ R₃ A := by
    intro x hx
    rw [mem_editSet] at hx
    rw [Finset.mem_union, mem_editSet, mem_editSet]
    by_cases h12 : R₁ x ↔ R₂ x
    · exact Or.inr ⟨hx.1, fun h23 => hx.2 (h12.trans h23)⟩
    · exact Or.inl ⟨hx.1, h12⟩
  calc editDistance R₁ R₃ A ≤ (editSet R₁ R₂ A ∪ editSet R₂ R₃ A).card :=
        Finset.card_le_card hsub
    _ ≤ editDistance R₁ R₂ A + editDistance R₂ R₃ A := Finset.card_union_le _ _

/-- Edit distance grows with the box.
@isnad1 id=le.1h6v.s6.fe248591c455 from=translated src=- shape=0fa2750e vocab=41f38b97
-/
theorem editDistance_mono_box (h : ∀ i, A i ⊆ B i) :
    editDistance R₁ R₂ A ≤ editDistance R₁ R₂ B := by
  refine Finset.card_le_card fun x hx => ?_
  rw [mem_editSet] at hx ⊢
  exact ⟨Fintype.mem_piFinset.mpr fun i => h i (Fintype.mem_piFinset.mp hx.1 i), hx.2⟩

/-- Edit-budget summation along a chain of relations.
@isnad1 id=le.0h5v.s7.c49634b987d1 from=translated src=- shape=4e873a0e vocab=cc1ad94d
-/
theorem editDistance_le_sum_chain {m : ℕ}
    (Rs : Fin (m + 1) → (ι → α) → Prop) [∀ i, DecidablePred (Rs i)]
    (A : ι → Finset α) :
    editDistance (Rs 0) (Rs (Fin.last m)) A
      ≤ ∑ i : Fin m, editDistance (Rs i.castSucc) (Rs i.succ) A := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc editDistance (Rs 0) (Rs (Fin.last (m + 1))) A
        ≤ editDistance (Rs 0) (Rs (Fin.last m).castSucc) A
            + editDistance (Rs (Fin.last m).castSucc) (Rs (Fin.last (m + 1))) A :=
          editDistance_triangle
      _ ≤ (∑ i : Fin m, editDistance (Rs i.castSucc.castSucc) (Rs i.succ.castSucc) A)
            + editDistance (Rs (Fin.last m).castSucc) (Rs (Fin.last (m + 1))) A := by
          have hih := ih (fun i : Fin (m + 1) => Rs i.castSucc)
          rw [Fin.castSucc_zero] at hih
          exact Nat.add_le_add_right hih _
      _ = ∑ i : Fin (m + 1), editDistance (Rs i.castSucc) (Rs i.succ) A := by
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.succ_castSucc, Fin.succ_last, Nat.succ_eq_add_one]

/-- Diagonal control on the full box: the edit distance splits into its injective part
plus at most the collision count.
@isnad1 id=le.0h4v.s6.567d81742800 from=translated src=- shape=174a5fba vocab=f9224f4f
-/
theorem editDistance_univ_le_injective_add_nonInjective [Fintype α] [DecidableEq α] :
    editDistance R₁ R₂ (fun _ => Finset.univ)
      ≤ ((editSet R₁ R₂ fun _ => Finset.univ).filter Function.Injective).card
        + (nonInjectiveMaps ι α).card := by
  rw [editDistance,
    ← Finset.card_filter_add_card_filter_not
      (s := editSet R₁ R₂ fun _ => Finset.univ) Function.Injective]
  refine Nat.add_le_add_left (Finset.card_le_card fun f hf => ?_) _
  rw [Finset.mem_filter] at hf
  exact mem_nonInjectiveMaps.mpr hf.2

/-! ### Bridges to tuple counting

If one of the two relations is constant on the box, the edit set is exactly the truth set (or
the falsity set) of the other, so the edit distance collapses to a `tupleCount` and a
`tupleDensity` bound converts into a count bound against the box mass.

The two count bounds are deliberately asymmetric. The sparse form is guard-free; the dense form
requires every side of the box to be nonempty, because that is what the pinned
`tupleDensity_neg` requires. The same asymmetry is recorded in
`RegularityLemmata.Finite.HomogeneousCell`'s frozen conventions and is not an artefact here. -/

/-- If `R₂` is false on every tuple of the box, the edit distance counts the tuples
satisfying `R₁`.
@isnad1 id=eq.1h5v.s6.bc59271e12e3 from=translated src=- shape=4b62c77c vocab=dabad974
-/
theorem editDistance_eq_tupleCount_of_forall_not (h : ∀ x ∈ Fintype.piFinset A, ¬ R₂ x) :
    editDistance R₁ R₂ A = tupleCount R₁ A :=
  congrArg Finset.card (Finset.filter_congr fun x hx ↦ by simp [h x hx])

/-- If `R₂` is true on every tuple of the box, the edit distance counts the tuples where `R₁`
fails.
@isnad1 id=eq.0h6v.s6.4de85ee67a85 from=translated src=- shape=058fc2c8 vocab=dabad974
-/
theorem editDistance_eq_tupleCount_not_of_forall (h : ∀ x ∈ Fintype.piFinset A, R₂ x) :
    editDistance R₁ R₂ A = tupleCount (fun x ↦ ¬ R₁ x) A :=
  congrArg Finset.card (Finset.filter_congr fun x hx ↦ by simp [h x hx])

/-- **Sparse branch.** Against a relation that is constantly false on the box, a density upper
bound on `R₁` bounds the edit distance by that fraction of the box mass. Guard-free: with an
empty side both sides are `0`.
@isnad1 id=le.2h6v.s7.082fba50c46e from=translated src=- shape=0296052b vocab=4dd88361
-/
theorem editDistance_le_of_tupleDensity_le {ε : ℝ} (hd : tupleDensity R₁ A ≤ ε)
    (hconst : ∀ x ∈ Fintype.piFinset A, ¬ R₂ x) :
    (editDistance R₁ R₂ A : ℝ) ≤ ε * ∏ i, ((A i).card : ℝ) := by
  rw [editDistance_eq_tupleCount_of_forall_not hconst]
  exact card_filter_le_of_tupleDensity_le hd

/-- **Dense branch.** Against a relation that is constantly true on the box, a density lower
bound `1 - ε ≤ d` on `R₁` bounds the edit distance by an `ε` fraction of the box mass. The
nonemptiness hypothesis is the one `tupleDensity_neg` carries.
@isnad1 id=le.2h7v.s7.430caae69744 from=translated src=- shape=3e2cc4d5 vocab=33f1fb10
-/
theorem editDistance_le_of_le_tupleDensity {ε : ℝ} (hd : 1 - ε ≤ tupleDensity R₁ A)
    (hconst : ∀ x ∈ Fintype.piFinset A, R₂ x) (hne : ∀ i, (A i).Nonempty) :
    (editDistance R₁ R₂ A : ℝ) ≤ ε * ∏ i, ((A i).card : ℝ) := by
  rw [editDistance_eq_tupleCount_not_of_forall hconst]
  refine card_filter_le_of_tupleDensity_le ?_
  rw [tupleDensity_neg hne]
  linarith

/-! ### Relative edit distance -/

/-- Normalized edit distance: the density of disagreement on the box.-/
noncomputable def relativeEditDistance (R₁ R₂ : (ι → α) → Prop) [DecidablePred R₁]
    [DecidablePred R₂] (A : ι → Finset α) : ℝ :=
  densityOn (Fintype.piFinset A) fun x => ¬ (R₁ x ↔ R₂ x)

/-- The bridge between relative and raw edit distance.
@isnad1 id=eq.0h5v.s6.824daa499632 from=translated src=- shape=3e1eb058 vocab=a833703b
-/
theorem relativeEditDistance_eq :
    relativeEditDistance R₁ R₂ A
      = (editDistance R₁ R₂ A : ℝ) / ((Fintype.piFinset A).card : ℝ) := rfl

/--
@isnad1 id=le.0h5v.s5.58d5aacc4fa2 from=translated src=- shape=b1e3d7f4 vocab=3ba9b6a8
-/
theorem relativeEditDistance_nonneg : 0 ≤ relativeEditDistance R₁ R₂ A :=
  densityOn_nonneg

/--
@isnad1 id=le.0h5v.s5.75304a5a47eb from=translated src=- shape=a99bf9c5 vocab=3ba9b6a8
-/
theorem relativeEditDistance_le_one : relativeEditDistance R₁ R₂ A ≤ 1 :=
  densityOn_le_one

/--
@isnad1 id=eq.0h5v.s5.70bd1f9768a8 from=translated src=- shape=53e16e43 vocab=6d6367bc
-/
theorem relativeEditDistance_comm :
    relativeEditDistance R₁ R₂ A = relativeEditDistance R₂ R₁ A := by
  rw [relativeEditDistance_eq, relativeEditDistance_eq, editDistance_comm]

/-! ### Tests and adversarial examples -/

-- Full flip: the relations disagree everywhere on the box.

end RegularityLemmata
