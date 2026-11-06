/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude
-/
module

public import Tengoku.Compply.CompPoly.Data.List.Lemmas
public import Tengoku.Seed.Algebra.Order.Ring.Nat
public import Tengoku.Seed.Algebra.Order.Star.Basic
public import Tengoku.Seed.Data.Nat.Log

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Auxiliary lemmas for `Array`
-/

@[expose] public section
universe u

namespace Array

variable {α : Type*} {unit : α}

lemma rightpad_toList {a : Array α} {n : Nat} {unit : α} :
    a.rightpad n unit = mk (a.toList.rightpad n unit) := by
  cases a
  simp

lemma rightpad_getElem_eq_getD {a : Array α} {n : Nat} {unit : α} {i : Nat}
    (h : i < (a.rightpad n unit).size) : (a.rightpad n unit)[i] = a.getD i unit := by
  simp_rw [rightpad_toList] at h ⊢
  -- By definition of `rightpad`, the element at position `i` in the right-padded array is
  -- the same as the element at position `i` in the original list `a` if `i` is within
  -- the bounds of `a`.
  have h_rightpad_getElem_eq_getD : (a.toList.rightpad n unit)[i] = a.toList.getD i unit := by
    grind
  cases a
  aesop

/-- `Array` version of `List.matchSize`, which rightpads the arrays to the same length.-/
@[reducible]
def matchSize (a b : Array α) (unit : α) : Array α × Array α :=
  (a.rightpad (b.size) unit, b.rightpad (a.size) unit)

attribute [simp] Array.getElem?_eq_getElem

-- @[simp] theorem matchSize_comm (a : Array α) (b : Array α) (unit : α) :
--     matchSize a b unit = (matchSize b a unit).swap := by
--   simp [matchSize, List.matchSize]

/-- find index from the end of an array-/
def findIdxRev? (cond : α → Bool) (as : Array α) : Option (Fin as.size) :=
  find ⟨ as.size, Nat.lt_succ_self _ ⟩
where
  find : Fin (as.size + 1) → Option (Fin as.size)
    | 0 => none
    | ⟨ i+1, h ⟩ =>
      if (cond as[i]) then
        some ⟨ i, Nat.lt_of_succ_lt_succ h ⟩
      else
        find ⟨ i, Nat.lt_of_succ_lt h ⟩

/-- if findIdxRev? finds an index, the condition is satisfied on that element-/
lemma findIdxRev?_def {cond} {as : Array α} {k : Fin as.size} :
    findIdxRev? cond as = some k → cond as[k] := by
  suffices aux : ∀ i, findIdxRev?.find cond as i = some k → cond as[k] by apply aux
  intro i
  unfold findIdxRev?.find
  induction i using findIdxRev?.find.induct cond as with
  | case1 => simp
  | case2 => simp [*]; rintro rfl; assumption
  | case3 => unfold findIdxRev?.find; simp [*]; assumption

/-- if findIdxRev? finds an index, then for every greater index the condition doesn't hold-/
lemma findIdxRev?_maximal {cond} {as : Array α} {k : Fin as.size} :
    findIdxRev? cond as = some k → ∀ j : Fin as.size, j > k → ¬ cond as[j] := by
  suffices aux : ∀ i, findIdxRev?.find cond as i = some k →
    ∀ j : Fin as.size, j > k → j.val < i → ¬ cond as[j] by
    intro h j j_gt_k
    exact aux ⟨ as.size, Nat.lt_succ_self _ ⟩ h j j_gt_k j.is_lt
  intro i
  unfold findIdxRev?.find
  induction i using findIdxRev?.find.induct cond as with
  | case1 => simp
  | case2 i =>
    simp [*]
    rintro rfl j (_: j > i) (_: j < i + 1) -- contradiction
    omega
  | case3 i _ not_true ih =>
    simp [*]
    unfold findIdxRev?.find
    intro h j j_gt_k j_lt_isucc
    specialize ih h j j_gt_k
    rcases (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ j_lt_isucc): j < i ∨ j = i) with (j_lt_i | rfl)
    · specialize ih j_lt_i
      rwa [Bool.not_eq_true] at ih
    · simp only [not_true]

/-- if the condition is false on all elements, then findIdxRev? finds nothing-/
lemma findIdxRev?_eq_none {cond} {as : Array α} (h : ∀ i, (hi : i < as.size) → ¬ cond as[i]) :
    findIdxRev? cond as = none := by
  apply aux
where
  aux i : findIdxRev?.find cond as i = none := by
    unfold findIdxRev?.find
    split
    next => tauto
    next _ j _ =>
      split -- then/else cases inside .find
      next cond_true =>
        have cond_false : ¬ cond as[j] := h j _
        have : False := cond_false cond_true
        contradiction
      -- recursively invoke the theorem we are proving!
      apply aux

lemma findIdxRev?_empty_none {cond} {as : Array α} (h : as = #[]) :
    findIdxRev? cond as = none := by
  rw [h]
  apply findIdxRev?_eq_none
  simp

/-- if the condition is true on some element, then findIdxRev? finds something-/
lemma findIdxRev?_eq_some {cond} {as : Array α} (h : ∃ i, ∃ hi : i < as.size, cond as[i]) :
    ∃ k : Fin as.size, findIdxRev? cond as = some k := by
  obtain ⟨ i, hi, hcond ⟩ := h
  apply aux ⟨ as.size, Nat.lt_succ_self _ ⟩ ⟨ .mk i hi, hi, hcond ⟩
where
  aux (i : Fin (as.size + 1)) (h': ∃ i' : Fin as.size, i' < i.val ∧ cond as[i']) :
    ∃ k, findIdxRev?.find cond as i = some k := by
    unfold findIdxRev?.find
    split
    next => tauto
    next _ j hj =>
      split -- then/else cases inside .find
      · use .mk j (by omega)
      · obtain ⟨ k, hk : k < j + 1, hcond ⟩ := h'
        apply aux -- recursively invoke the theorem we are proving!
        have : k.val ≠ j := by rintro rfl; contradiction
        have : k.val < j := by omega
        use k

/-- Get the last element of an array, assuming the array is non-empty.-/
def getLast (a : Array α) (h : a.size > 0) : α := a[a.size - 1]

/-- Get the last element of an array, or `v₀` if the array is empty.-/
def getLastD (a : Array α) (v₀ : α) : α := a.getD (a.size - 1) v₀

end Array
