/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Tengoku.Cslib.Cslib.Init
public import Tengoku.Cslib.Cslib.Foundations.Control.Monad.IsMonadHom
public import Tengoku.Seed.Data.List.Monad

import all Init.Data.List.Control
import Tengoku.Seed.Data.List.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# List operations and monad morphisms

This file proves that monadic operations on lists commute with monad homomorphisms
(and applicative homomorphisms), and that `List.reverse` is a monad homomorphism on `List`.
-/

public section

namespace Cslib

universe u um un v
variable {m : Type u → Type um} {n : Type u → Type un}

/-! ### Preservation of list operations under applicative homomorphisms -/

namespace IsApplicativeHom
variable [Applicative m] [Applicative n]

/--
@isnad1 id=eq.1h7v.s6.6752b46dc15d from=translated src=- shape=826e4a8a vocab=3088dd16
-/
@[grind .]
theorem map_listMapA {F : ∀ {α}, m α → n α} (hf : IsApplicativeHom m n F)
    {α : Type v} {β : Type u} (f : α → m β) (l : List α) :
    F (l.mapA f) = l.mapA (F ∘ f) := by
  induction l with grind [List.mapA]

/--
@isnad1 id=eq.1h6v.s6.33d551758365 from=translated src=- shape=fb2c2127 vocab=04708ef3
-/
@[grind .]
theorem map_listForA {F : ∀ {α}, m α → n α} (hf : IsApplicativeHom m n F)
    {α : Type v} (l : List α) (f : α → m PUnit) :
    F (l.forA f) = l.forA (F ∘ f) := by
  induction l with grind [List.forA]

end IsApplicativeHom

/-! ### Preservation of list operations under monad homomorphisms -/

namespace IsMonadHom
variable [Monad m] [Monad n]

/--
@isnad1 id=eq.1h7v.s6.f41e8ff01f4a from=translated src=- shape=826e4a8a vocab=7179031d
-/
@[grind .]
theorem map_listMapM'
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type v} {β : Type u} (f : α → m β) (l : List α) :
    F (l.mapM' f) = l.mapM' (F ∘ f) := by
  induction l with grind [List.mapM']

/--
@isnad1 id=eq.1h8v.s6.14dd00e88899 from=translated src=- shape=bef229a8 vocab=3e1e3911
-/
@[grind .]
theorem map_listMapMLoop
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type v} {β : Type u} (f : α → m β) (l : List α) (acc : List β) :
    F (List.mapM.loop f l acc) = List.mapM.loop (F ∘ f) l acc := by
  induction l generalizing acc with
  | nil => exact hf.map_pure _
  | cons a l ih => simp only [List.mapM.loop, hf.map_bind, ih, Function.comp_def]

/--
@isnad1 id=eq.1h7v.s6.d4bf34751c9a from=translated src=- shape=826e4a8a vocab=c857cbb2
-/
@[grind .]
theorem map_listMapM
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type v} {β : Type u} (f : α → m β) (l : List α) :
    F (l.mapM f) = l.mapM (F ∘ f) := by
  grind [List.mapM]

/--
@isnad1 id=eq.1h6v.s6.c36a83e8a01f from=translated src=- shape=fb2c2127 vocab=74281738
-/
@[grind .]
theorem map_listForM {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type v} (l : List α) (f : α → m PUnit) :
    F (l.forM f) = l.forM (F ∘ f) := by
  induction l with grind [List.forM]

/--
@isnad1 id=eq.1h8v.s6.bcbda3f5af31 from=translated src=- shape=10086462 vocab=d7923e2d
-/
@[grind .]
theorem map_listFoldlM {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {s : Type u} {α : Type v} (f : s → α → m s) (init : s) (l : List α) :
    F (l.foldlM f init) = l.foldlM (fun s a => F (f s a)) init := by
  induction l generalizing init with grind [List.foldlM]

/--
@isnad1 id=eq.1h8v.s6.b311ec5dc876 from=translated src=- shape=aab6395e vocab=2fb299ec
-/
@[grind .]
theorem map_listFoldrM {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {s : Type u} {α : Type v} (f : α → s → m s) (init : s) (l : List α) :
    F (l.foldrM f init) = l.foldrM (fun a s => F (f a s)) init := by
  simp only [List.foldrM]
  exact hf.map_listFoldlM (fun s a => f a s) init l.reverse

/--
@isnad1 id=eq.1h7v.s6.f5920bcdb9d6 from=translated src=- shape=8c80d09c vocab=a3cf41b8
-/
@[grind .]
theorem map_listFindSomeM?
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type v} {β : Type u} (f : α → m (Option β)) (l : List α) :
    F (l.findSomeM? f) = l.findSomeM? (F ∘ f) := by
  induction l with grind

/--
@isnad1 id=eq.1h6v.s6.3770d25f10ad from=translated src=- shape=96960a10 vocab=e98ce942
-/
@[grind .]
theorem map_listFindM? {m n : Type → Type v} [Monad m] [Monad n]
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type} (p : α → m Bool) (l : List α) :
    F (l.findM? p) = l.findM? (F ∘ p) := by
  induction l with grind [List.findM?]

/--
@isnad1 id=eq.1h6v.s6.fd3aadc807fb from=translated src=- shape=cb6b3981 vocab=610f0292
-/
@[grind .]
theorem map_listAnyM {m n : Type → Type v} [Monad m] [Monad n]
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type v} (p : α → m Bool) (l : List α) :
    F (l.anyM p) = l.anyM (F ∘ p) := by
  induction l with grind [List.anyM]

/--
@isnad1 id=eq.1h6v.s6.c119812113e9 from=translated src=- shape=cb6b3981 vocab=80d79d98
-/
@[grind .]
theorem map_listAllM {m n : Type → Type v} [Monad m] [Monad n]
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type v} (p : α → m Bool) (l : List α) :
    F (l.allM p) = l.allM (F ∘ p) := by
  induction l with grind [List.allM]

/--
@isnad1 id=eq.1h7v.s6.69ccf161c780 from=translated src=- shape=ecd70e23 vocab=e1959bc7
-/
@[grind .]
theorem map_listFilterAuxM {m n : Type → Type v} [Monad m] [Monad n]
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type} (p : α → m Bool) (l acc : List α) :
    F (List.filterAuxM p l acc) = List.filterAuxM (F ∘ p) l acc := by
  induction l generalizing acc with grind [List.filterAuxM]

/--
@isnad1 id=eq.1h6v.s6.b9250af8d4b4 from=translated src=- shape=25348d92 vocab=cc54c6cf
-/
@[grind .]
theorem map_listFilterM {m n : Type → Type v} [Monad m] [Monad n]
    {F : ∀ {α}, m α → n α} (hf : IsMonadHom m n F)
    {α : Type} (p : α → m Bool) (l : List α) :
    F (l.filterM p) = l.filterM (F ∘ p) := by
  grind [List.filterM]

end IsMonadHom

/-! ### Preservation of list operations under alternative homomorphisms -/

namespace IsAlternativeHom
variable [Alternative m] [Alternative n]

/--
@isnad1 id=eq.1h7v.s6.449bdc41addb from=translated src=- shape=a5cd36c4 vocab=1607287d
-/
@[grind .]
theorem map_listFirstM {F : ∀ {α}, m α → n α} (hf : IsAlternativeHom m n F)
    {α : Type v} {β : Type u} (f : α → m β) (l : List α) :
    F (l.firstM f) = l.firstM (F ∘ f) := by
  induction l with grind [List.firstM]

end IsAlternativeHom

/-! ### Monad homomorphisms on the `List` monad -/

/--
@isnad1 id=eq.1h3v.s5.c62422c00072 from=translated src=- shape=8752951f vocab=9548ad2b
-/
@[grind .]
theorem IsApplicativeHom.map_listSingleton
    {F : ∀ {α}, List α → List α} (hf : IsApplicativeHom List List F) {α} (a : α) :
    F ([a] : List α) = [a] := hf.map_pure _

/--
@isnad1 id=eq.1h5v.s5.a12b96f1f179 from=translated src=- shape=4212ef57 vocab=39da3642
-/
theorem IsMonadHom.map_listFlatMap
    {F : ∀ {α}, List α → List α} (hf : IsMonadHom List List F) {α β} (l : List α) (g : α → List β) :
    F (l.flatMap g) = (F l).flatMap (F <| g ·) := hf.map_bind _ _

/--
@isnad1 id=eq.1h2v.s4.6b15f4c1b1aa from=translated src=- shape=39e427e7 vocab=37cf0efd
-/
@[grind .]
theorem IsFunctorHom.map_listNil {F : ∀ {α}, List α → List α} (hf : IsFunctorHom List List F) {α} :
    F ([] : List α) = [] := by
  simpa [Subsingleton.elim (F ([] : List PEmpty)) []]
    using (hf.map_map PEmpty.elim []).symm

/--
@isnad1 id=ismonadh.0h0v.s3.7a718e0d1794 from=translated src=- shape=43b661f2 vocab=0d7f821e
-/
protected theorem _root_.List.isMonadHom_reverse : IsMonadHom List List List.reverse :=
  .mk' (fun _ => rfl) (fun _ _ => List.reverse_flatMap)

section uniqueness

/-- A property holds on all lists if it holds on the nil list, the singleton list,
and concatenations thereof.-/
private theorem List.nil_singleton_append_induction {α : Type*} {motive : List α → Prop}
    (nil : motive []) (singleton : ∀ a, motive [a])
    (append : ∀ xs ys, motive xs → motive ys → motive (xs ++ ys)) :
    ∀ l, motive l
  | [] => nil
  | x :: xs => append [x] xs (singleton x) (nil_singleton_append_induction nil singleton append xs)

/-- Universe-generic type with two elements. This is used only internally in a proof, and keeps
things more concise than `ULift Bool`.-/
private inductive Two : Type u | a | b

private theorem eq_ab_or_ba : ∀ (l : List Two),
    l.flatMap (fun | .a => [.a] | .b => []) = [Two.a] →
    l.flatMap (fun | .a => [] | .b => [.b]) = [Two.b] →
    l = [Two.a, Two.b] ∨ l = [Two.b, Two.a]
  | [.a, .b], _, _ => .inl rfl
  | [.b, .a], _, _ => .inr rfl

/-- The only monad morphisms on lists are the identity and reversal.
@isnad1 id=iff.0h1v.s5.0c733294e55a from=translated src=- shape=dfc5c2cf vocab=4c694010
-/
theorem isMonadHom_list_iff (f : ∀ {α : Type u}, List α → List α) :
    IsMonadHom List List @f ↔ @f = (@id <| List ·) ∨ @f = @List.reverse := by
  refine ⟨fun h => ?_, ?_⟩
  · have h_append {α} (xs ys : List α) :
        f (xs ++ ys) = (f [Two.a, Two.b]).flatMap (fun | .a => f xs | .b => f ys) := by
      have : xs ++ ys = [Two.a, Two.b].flatMap (fun | .a => xs | .b => ys) := by
        simp
      rw [this, h.map_listFlatMap]
      congr 1; funext x; cases x <;> rfl
    refine (eq_ab_or_ba (f [Two.a, Two.b]) ?_ ?_).imp (fun hL => ?_) (fun hL => ?_)
    · simpa [h.map_listNil, h.map_listSingleton] using (h_append [Two.a] []).symm
    · simpa [h.map_listNil, h.map_listSingleton] using (h_append [] [Two.b]).symm
    · funext α l
      induction l using List.nil_singleton_append_induction with grind
    · funext α l
      induction l using List.nil_singleton_append_induction with grind
  · rintro (rfl | rfl)
    · exact .id _
    · exact List.isMonadHom_reverse

end uniqueness

end Cslib
