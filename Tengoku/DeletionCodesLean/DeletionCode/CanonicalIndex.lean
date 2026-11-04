import Tengoku.DeletionCodesLean.DeletionCode.CatalogueWords
import Tengoku.DeletionCodesLean.DeletionCode.RuleReconstruction
import Tengoku.Seed.Logic.Equiv.Fin.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms indexEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms unflatten_flatten` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms flatten_unflatten` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms group_fiber_card` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms group_sum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms flat_rule_spectrum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rulesOf_flatten` (it only prints; the queue checks the axioms of every declaration). -/

/-!
The manuscript's fixed occurrence labels (rule position, within-rule position).
Flattening is a bijective change of indexing, has exactly 2t labels per rule,
and preserves every per-rule spectrum sum and the underlying signed rule set.
The grouping is fixed by t and R, so it is not additional description data.
-/
namespace DeletionCode.CanonicalIndex

open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport RuleReconstruction
open scoped BigOperators

def indexEquiv (t R : ℕ) : Fin (2 * t * R) ≃ Fin R × Fin (2 * t) :=
  (Equiv.cast (congrArg Fin (Nat.mul_comm (2 * t) R))).trans
    (@finProdFinEquiv R (2 * t)).symm

def group (t R : ℕ) (b : Fin (2 * t * R)) : Fin R := (indexEquiv t R b).1

def flatten {α : Type*} (t R : ℕ) (words : Fin R → Fin (2 * t) → α) :
    Fin (2 * t * R) → α :=
  fun b => words (indexEquiv t R b).1 (indexEquiv t R b).2

def unflatten {α : Type*} (t R : ℕ) (family : Fin (2 * t * R) → α) :
    Fin R → Fin (2 * t) → α :=
  fun r j => family ((indexEquiv t R).symm (r, j))

/--
@isnad1 id=eq.0h6v.s8.6fdfb132d02d from=translated src=- shape=5fef06b6 vocab=cbee773f
-/
theorem flatten_at_pair {α : Type*} (t R : ℕ) (words : Fin R → Fin (2 * t) → α)
    (r : Fin R) (j : Fin (2 * t)) :
    flatten t R words ((indexEquiv t R).symm (r, j)) = words r j := by
  simp [flatten]

/--
@isnad1 id=eq.0h4v.s5.c1cf97d2ce84 from=translated src=- shape=dba7b00f vocab=f2a3b47a
-/
theorem unflatten_flatten {α : Type*} (t R : ℕ) (words : Fin R → Fin (2 * t) → α) :
    unflatten t R (flatten t R words) = words := by
  funext r j
  exact flatten_at_pair t R words r j

/--
@isnad1 id=eq.0h4v.s6.dc4095bd8fd0 from=translated src=- shape=996c5c1d vocab=f2a3b47a
-/
theorem flatten_unflatten {α : Type*} (t R : ℕ) (family : Fin (2 * t * R) → α) :
    flatten t R (unflatten t R family) = family := by
  funext b
  simp [flatten, unflatten]

def familyEquiv (α : Type*) (t R : ℕ) :
    (Fin (2 * t * R) → α) ≃ (Fin R → Fin (2 * t) → α) where
  toFun := unflatten t R
  invFun := flatten t R
  left_inv := flatten_unflatten t R
  right_inv := unflatten_flatten t R

/--
@isnad1 id=ex.0h4v.s6.366d83b1e31c from=translated src=- shape=e79b6d06 vocab=3e694e7d
-/
theorem every_family_is_flattened {α : Type*} (t R : ℕ) (family : Fin (2 * t * R) → α) :
    ∃ words : Fin R → Fin (2 * t) → α, flatten t R words = family :=
  ⟨unflatten t R family, flatten_unflatten t R family⟩

def groupFiberEquiv (t R : ℕ) (r : Fin R) :
    {b : Fin (2 * t * R) // group t R b = r} ≃ Fin (2 * t) where
  toFun b := (indexEquiv t R b.val).2
  invFun j := ⟨(indexEquiv t R).symm (r, j), by simp [group]⟩
  left_inv b := by
    apply Subtype.ext
    apply (indexEquiv t R).injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext b.property.symm rfl
  right_inv j := by simp

/--
@isnad1 id=eq.0h3v.s7.eacb88efaaab from=translated src=- shape=5f74a621 vocab=cfae01c0
-/
theorem group_fiber_card (t R : ℕ) (r : Fin R) :
    Fintype.card {b : Fin (2 * t * R) // group t R b = r} = 2 * t := by
  simpa using Fintype.card_congr (groupFiberEquiv t R r)

/--
@isnad1 id=eq.0h3v.s7.c388f572ef54 from=translated src=- shape=cf2cbd53 vocab=fd7ed59a
-/
theorem group_filter_card (t R : ℕ) (r : Fin R) :
    (Finset.univ.filter (fun b : Fin (2 * t * R) => group t R b = r)).card = 2 * t := by
  rw [← Fintype.card_subtype]
  exact group_fiber_card t R r

/-- Sums over one flat-index group are exactly sums over its within-rule indices.
@isnad1 id=eq.0h5v.s9.4e06950206ef from=translated src=- shape=7e8e3b74 vocab=31d5ccd3
-/
theorem group_sum {A : Type*} [AddCommMonoid A] (t R : ℕ) (r : Fin R)
    (f : Fin (2 * t * R) → A) :
    (∑ b ∈ Finset.univ.filter (fun b => group t R b = r), f b) =
      ∑ j : Fin (2 * t), f ((indexEquiv t R).symm (r, j)) := by
  classical
  apply Finset.sum_bij (fun b _ => (indexEquiv t R b).2)
  · intro b hb
    exact Finset.mem_univ _
  · intro a ha b hb hab
    apply (indexEquiv t R).injective
    apply Prod.ext
    · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    · exact hab
  · intro j hj
    refine ⟨(indexEquiv t R).symm (r, j), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change (indexEquiv t R ((indexEquiv t R).symm (r, j))).1 = r
      rw [Equiv.apply_symm_apply]
    · simp
  · intro b hb
    apply congrArg f
    apply (indexEquiv t R).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext (Finset.mem_filter.mp hb).2 rfl

def pairFamily {k : ℕ} (t R : ℕ) (words : Fin R → Fin (2 * t) → BubbleWord k) :
    EditedFamily (Fin R × Fin (2 * t)) k :=
  editedFamily (fun p => words p.1 p.2) (fun p => p.1.val)

def flatFamily {k : ℕ} (t R : ℕ) (words : Fin R → Fin (2 * t) → BubbleWord k) :
    EditedFamily (Fin (2 * t * R)) k :=
  editedFamily (flatten t R words) (fun b => (group t R b).val)

/--
@isnad1 id=eq.0h5v.s8.4e3d26016cb5 from=translated src=- shape=22a8b86b vocab=3ae2ba8e
-/
theorem flat_bubble_spectrum {k : ℕ} (t R : ℕ)
    (words : Fin R → Fin (2 * t) → BubbleWord k) (b : Fin (2 * t * R)) :
    bubbleSpectrum (flatFamily t R words).family (windowLength k) b =
      bubbleSpectrum (pairFamily t R words).family (windowLength k) (indexEquiv t R b) := rfl

/--
@isnad1 id=eq.0h5v.s7.c23a329b0178 from=translated src=- shape=3b5fd7ac vocab=990d2c7f
-/
theorem flat_rule_spectrum {k : ℕ} (t R : ℕ)
    (words : Fin R → Fin (2 * t) → BubbleWord k) (r : Fin R) :
    ruleSpectrum (flatFamily t R words).family (windowLength k) (groupBubbles (group t R) r) =
      fun g => ∑ j : Fin (2 * t), bubbleSpectrum (pairFamily t R words).family
        (windowLength k) (r, j) g := by
  classical
  funext g
  unfold ruleSpectrum groupBubbles
  rw [group_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have h := congrFun (flat_bubble_spectrum t R words ((indexEquiv t R).symm (r, j))) g
  simpa only [Equiv.apply_symm_apply] using h

/-- The flattened decoder output determines precisely the set of the R per-rule sums.
@isnad1 id=eq.0h4v.s8.e3d8ce8d319c from=translated src=- shape=ee0f0a55 vocab=59387779
-/
theorem rulesOf_flatten {k : ℕ} (t R : ℕ) (words : Fin R → Fin (2 * t) → BubbleWord k) :
    rulesOfFamily (flatFamily t R words) (group t R) =
      Finset.univ.image (fun r : Fin R => fun g =>
        ∑ j : Fin (2 * t), bubbleSpectrum (pairFamily t R words).family (windowLength k) (r, j) g) := by
  classical
  unfold rulesOfFamily
  apply Finset.image_congr
  intro r hr
  exact flat_rule_spectrum t R words r

end DeletionCode.CanonicalIndex
