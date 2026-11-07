/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/
module

public import Tengoku.Seed.Data.Finset.Defs
public import Tengoku.Seed.Data.Finset.Empty
public import Tengoku.Seed.Data.Finset.Dedup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# ArkLib.ToMathlib.Finset.ToListWithProof

Definitions and results for this component of ArkLib.
-/

@[expose] public section

namespace Finset

/-- A helper to convert a finset into
  a list whose elements are the members of the finset,
  i.e. come with a proof that they belong to the finset.-/
noncomputable def toListWithProof.{u} {α : Type u} [DecidableEq α] (s : Finset α) :
  List s :=
  let list := s.toList
  List.reduceOption <|
    list.map (fun x ↦ if h : x ∈ s then some ⟨x, h⟩ else none)

/--
@isnad1 id=eq.0h1v.s5.f15bb5b3a72a from=translated src=- shape=5a3e888a vocab=20db793f
-/
@[simp]
lemma toListWithProof_empty.{u} {α : Type u} [DecidableEq α] :
    toListWithProof (∅ : Finset α) = [] := by
  simp [toListWithProof, List.reduceOption]

private lemma list_reduceOption_helper
  {α : Type*} [DecidableEq α] {s : Finset α}
  {l : List α} (h : ∀ x ∈ l, x ∈ s) :
    List.map Subtype.val
      (List.reduceOption (l.map (fun x ↦ if hx : x ∈ s then some ⟨x, hx⟩ else none)))
        = l := by
  induction l with
  | nil => simp [List.reduceOption]
  | cons a t ih =>
    have ha := h a (by simp)
    simp only [List.map_cons, ha, dite_true, List.reduceOption, List.filterMap_cons, id]
    change a :: List.map Subtype.val _ = a :: t
    congr 1
    exact ih (fun x hx ↦ h x (List.mem_cons_of_mem a hx))

/--
@isnad1 id=eq.0h2v.s6.15fe92762c24 from=translated src=- shape=d3ecc36e vocab=7c86eb37
-/
@[simp]
lemma toListWithProof_eq_toList.{u} {α : Type u} [DecidableEq α]
    {s : Finset α} :
  (toListWithProof s).map (fun x ↦ x.1) =
    s.toList := by
  simp only [toListWithProof]
  exact list_reduceOption_helper (fun x hx ↦ Finset.mem_toList.mp hx)

end Finset
