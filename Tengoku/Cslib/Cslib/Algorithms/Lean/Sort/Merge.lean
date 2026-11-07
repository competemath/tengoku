/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Eric Wieser
-/
module

public import Tengoku.Cslib.Cslib.Foundations.Control.Monad.IsMonadHom

import all Init.Data.List.Sort.Basic
import Tengoku.Cslib.Cslib.Init

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A Monadic version of the builtin `List.mergeSort`

This can be instantiated with `Id` to recover the original, or with `TimeM` or `FreeM` for
algorithmic analysis.
-/

public section

open Cslib (IsMonadHom)

namespace List

variable {m n} [Monad m] [Monad n]

/-- A monadic version of `List.merge`-/
def mergeM (xs ys : List α) (le : α → α → m Bool) : m (List α) := do
  match xs, ys with
  | [], ys => return ys
  | xs, [] => return xs
  | x :: xs, y :: ys =>
    if ← le x y then
      return x :: (← mergeM xs (y :: ys) le)
    else
      return y :: (← mergeM (x :: xs) ys le)

/--
@isnad1 id=eq.0h4v.s5.2552cb465705 from=translated src=- shape=ad4ae799 vocab=86efd548
-/
@[simp, grind =]
theorem nil_mergeM (ys : List α) (le : α → α → m Bool) : mergeM [] ys le = pure ys := by
  simp [mergeM]
/--
@isnad1 id=eq.0h4v.s5.ceab522e069b from=translated src=- shape=f69c6a5b vocab=86efd548
-/
@[simp, grind =]
theorem mergeM_right (xs : List α) (le : α → α → m Bool) : mergeM xs [] le = pure xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [mergeM]
/--
@isnad1 id=eq.0h7v.s7.58a8d7167a1c from=translated src=- shape=e6d108cf vocab=0d0bda00
-/
@[simp] theorem cons_mergeM_cons (x y : α) (xs ys : List α) (le : α → α → m Bool) :
    mergeM (x :: xs) (y :: ys) le = do
      if ← le x y then
        return x :: (← mergeM xs (y :: ys) le)
      else
        return y :: (← mergeM (x :: xs) ys le) := by
  simp [mergeM]

/--
@isnad1 id=eq.0h5v.s6.bcf380c1fca7 from=translated src=- shape=951fb61e vocab=fb4e041e
-/
@[simp↓]
theorem mergeM_pure [LawfulMonad m] (xs ys : List α) (le : α → α → Bool) :
    mergeM xs ys (fun x y => (pure (le x y) : m Bool)) = pure (merge xs ys le) := by
  fun_induction mergeM with grind [merge]

/--
@isnad1 id=eq.0h4v.s5.6445a98de5dc from=translated src=- shape=7ded23df vocab=98261591
-/
@[simp]
theorem idRun_mergeM (xs ys : List α) (le : α → α → Id Bool) :
    Id.run (mergeM xs ys le) = merge xs ys (fun x y => Id.run <| le x y) :=
  mergeM_pure _ _ _

/--
@isnad1 id=eq.1h7v.s6.6f4da9ecdc20 from=translated src=- shape=0a707a1b vocab=dcbc75b3
-/
@[grind .]
theorem _root_.Cslib.IsMonadHom.map_listMergeM {f : {β : Type} → m β → n β}
    (hf : IsMonadHom m n f) (xs ys : List α) (le : α → α → m Bool) :
    f (mergeM xs ys le) = mergeM xs ys (fun x y => f (le x y)) := by
  fun_induction mergeM xs ys le with
  | case1 | case2 => grind
  | case3 x xs y ys ihx ihy => simp [hf.map_bind, hf.map_pure, apply_ite f, ihx, ihy]

/-- A monadic version of `List.mergeSortM`-/
def mergeSortM (xs : List α) (le : α → α → m Bool) : m (List α) :=
  match xs with
  | [] => return []
  | [a] => return [a]
  | a :: b :: xs => do
    let lr := MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩
    mergeM (← mergeSortM lr.1 le) (← mergeSortM lr.2 le) le
termination_by xs.length

/--
@isnad1 id=eq.0h3v.s5.7d394570ece2 from=translated src=- shape=d24bfe74 vocab=4ea8f839
-/
@[simp] theorem mergeSortM_nil (le : α → α → m Bool) : mergeSortM [] le = pure [] := by
  simp [mergeSortM]
/--
@isnad1 id=eq.0h4v.s5.32184c1ec36d from=translated src=- shape=262656c3 vocab=c4f0c85a
-/
@[simp] theorem mergeSortM_singleton (a : α) (le : α → α → m Bool) :
    mergeSortM [a] le = pure [a] := by
  simp [mergeSortM]

/--
@isnad1 id=eq.0h4v.s5.70f6f97f895c from=translated src=- shape=d742f2bb vocab=c080664c
-/
@[simp↓]
theorem mergeSortM_pure [LawfulMonad m] (xs : List α) (le : α → α → Bool) :
    mergeSortM xs (fun x y => (pure (le x y) : m Bool)) = pure (mergeSort xs le) := by
  fun_induction mergeSort with
  | case1 | case2 => simp
  | case3 a b xs le lr _ _ ih1 ih2 =>
    simp only [mergeSortM]
    rw [ih1, ih2]
    simp

/--
@isnad1 id=eq.0h3v.s5.e2d315931614 from=translated src=- shape=ee18e82a vocab=204ddaa4
-/
@[simp]
theorem idRun_mergeSortM (xs : List α) (le : α → α → Id Bool) :
    Id.run (mergeSortM xs le) = mergeSort xs (fun x y => Id.run <| le x y) :=
  mergeSortM_pure _ _

/--
@isnad1 id=eq.1h6v.s6.78f21b0c4d19 from=translated src=- shape=6f1e1168 vocab=74e39a82
-/
@[grind .]
theorem _root_.Cslib.IsMonadHom.map_listMergeSortM {f : {β : Type} → m β → n β}
    (hf : IsMonadHom m n f) (xs : List α) (le : α → α → m Bool) :
    f (mergeSortM xs le) = mergeSortM xs (fun x y => f (le x y)) := by
  fun_induction mergeSortM xs le with
  | case1 | case2 => simp [hf.map_pure]
  | case3 a b xs le ih1 ih2 => simp only [mergeSortM, hf.map_bind, ih1, ih2, hf.map_listMergeM, le]

end List
