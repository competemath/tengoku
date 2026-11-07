/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Eric Wieser
-/
module

public import Tengoku.Seed.Data.List.Sort
public import Tengoku.Cslib.Cslib.Foundations.Control.Monad.IsMonadHom

import Tengoku.Cslib.Cslib.Init

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A Monadic version of Mathlib's `List.insertionSort`

This can be instantiated with `Id` to recover the original, or with `TimeM` or `FreeM` for
algorithmic analysis.
-/

public section

open Cslib (IsMonadHom)

namespace List

variable {m n} [Monad m] [Monad n] (r : α → α → m Bool)

/-- A monadic version of `List.orderedInsert`.-/
def orderedInsertM (a : α) : List α → m (List α)
  | [] => return [a]
  | b :: l => do if ← r a b then return a :: b :: l else return b :: (← orderedInsertM a l)

/--
@isnad1 id=eq.0h4v.s5.74ef63267c61 from=translated src=- shape=ba9372af vocab=9efa1427
-/
@[simp, grind =] theorem orderedInsertM_nil (a : α) : orderedInsertM r a [] = pure [a] := by
  rfl
/--
@isnad1 id=eq.0h6v.s6.bfb2e4a2629d from=translated src=- shape=8200144f vocab=148422aa
-/
@[simp, grind =] theorem orderedInsertM_cons (a b : α) (l : List α) :
    orderedInsertM r a (b :: l) = do
      if ← r a b then return a :: b :: l else return b :: (← orderedInsertM r a l) := by
  rfl

/--
@isnad1 id=eq.0h5v.s6.9ffd4cb1c9ca from=translated src=- shape=81f344d4 vocab=0eb2d5e8
-/
@[simp]
theorem orderedInsertM_pure [LawfulMonad m] (r : α → α → Bool) (a : α) (xs : List α) :
    orderedInsertM (fun x y => (pure (r x y) : m Bool)) a xs =
      pure (orderedInsert (r · ·) a xs) := by
  fun_induction orderedInsertM with grind [orderedInsertM]

/--
@isnad1 id=eq.0h4v.s5.12bcf945968b from=translated src=- shape=5053b656 vocab=7ea85285
-/
@[simp]
theorem idRun_orderedInsertM (r : α → α → Id Bool) (a : α) (xs : List α) :
    Id.run (orderedInsertM r a xs) = orderedInsert (fun x y => Id.run <| r x y) a xs :=
  orderedInsertM_pure _ _ _

/--
@isnad1 id=eq.1h7v.s6.ef543228848a from=translated src=- shape=1f265b11 vocab=7cdccd46
-/
@[grind .]
theorem _root_.Cslib.IsMonadHom.map_orderedInsertM {f : {β : Type} → m β → n β}
    (hf : IsMonadHom m n f) (r : α → α → m Bool) (a : α) (xs : List α) :
    f (orderedInsertM r a xs) = orderedInsertM (fun x y => f (r x y)) a xs := by
  fun_induction orderedInsertM r a xs with grind

/-- A monadic version of `List.insertionSort`.-/
def insertionSortM : List α → m (List α)
  | [] => return []
  | b :: l => do orderedInsertM r b (← insertionSortM l)

/--
@isnad1 id=eq.0h3v.s5.0f52cf120b9e from=translated src=- shape=db158976 vocab=ca73de66
-/
@[simp] theorem insertionSortM_nil : insertionSortM r [] = pure [] := by
  rfl
/--
@isnad1 id=eq.0h5v.s5.454cf98c16a0 from=translated src=- shape=70fa1b37 vocab=50d369c8
-/
@[simp] theorem insertionSortM_cons (b : α) (l : List α) :
    insertionSortM r (b :: l) = (do orderedInsertM r b (← insertionSortM r l)) := by
  rfl

/--
@isnad1 id=eq.0h4v.s6.867161dc3b62 from=translated src=- shape=547fc0f4 vocab=843a7596
-/
@[simp]
theorem insertionSortM_pure [LawfulMonad m] (xs : List α) (r : α → α → Bool) :
    insertionSortM (fun x y => (pure (r x y) : m Bool)) xs = pure (insertionSort (r · ·) xs) := by
  fun_induction insertionSortM with simp_all

/--
@isnad1 id=eq.0h3v.s5.19e12a3ebe17 from=translated src=- shape=4a28fd2f vocab=b6e997a3
-/
@[simp]
theorem idRun_insertionSortM (xs : List α) (r : α → α → Id Bool) :
    Id.run (insertionSortM r xs) = insertionSort (fun x y => Id.run <| r x y) xs :=
  insertionSortM_pure _ _

/--
@isnad1 id=eq.1h6v.s6.85c8b4d2e78a from=translated src=- shape=475d8194 vocab=f49ff0eb
-/
@[grind .]
theorem _root_.Cslib.IsMonadHom.map_listInsertionSortM {f : {β : Type} → m β → n β}
    (hf : IsMonadHom m n f) (r : α → α → m Bool) (xs : List α) :
    f (insertionSortM r xs) = insertionSortM (fun x y => f (r x y)) xs := by
  fun_induction insertionSortM r xs with simp [hf.map_pure, hf.map_bind, hf.map_orderedInsertM, *]

end List
