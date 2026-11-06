/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Tengoku.Compply.CompPoly.Data.ExtTreeMap.ExtDTreeMap
public import Std.Data.ExtTreeMap.Lemmas
public import Tengoku.Seed.Std.Tactic.GeneralizeProofs
public import Tengoku.Seed.Tactic.Lemma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Auxiliary lemmas for `Std.ExtTreeMap`

`mergeWith` and `filter` lemmas for `Std.ExtTreeMap`, used by the multivariate
polynomial representation in `CompPoly.Multivariate.Unlawful`.

Vendored from
[`Verified-zkEVM/ExtTreeMapLemmas`](https://github.com/Verified-zkEVM/ExtTreeMapLemmas)
(tag `v4.29.1`, commit `3fee686227f18dca03bb7fc42ca5a9275d6cfda6`). The original
imported `Mathlib.Tactic` wholesale; here we narrow to the specific tactic
modules actually needed by the proofs below.
-/

@[expose] public section

namespace Std.ExtTreeMap

universe u v

variable {α : Type u} {β : Type v}

attribute [local instance low] beqOfOrd
attribute [grind ext] ExtTreeMap.ext_getElem?
attribute [grind .] ExtTreeMap.distinct_keys_toList ExtTreeMap.getElem?_ofList_of_mem

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}
variable {k : α} {m m₁ m₂ : Std.ExtTreeMap α β cmp} {f : α → β → β → β}

variable [TransCmp cmp] [LawfulEqCmp cmp]

-- Pointwise characterization of `mergeWith` on optional access at a key.
/--
@isnad1 id=eq.0h7v.s7.498954427f92 from=translated src=- shape=abff2c36 vocab=8da2be81
-/
theorem getElem?_mergeWith_at
    {m₁ m₂ : ExtTreeMap α β cmp} {f : α → β → β → β} {k : α} :
  (m₁.mergeWith f m₂)[k]? =
  match m₁[k]?, m₂[k]? with
  | .some v₁, .some v₂ => .some (f k v₁ v₂)
  | .some v₁, .none    => .some v₁
  | .none,    .some v₂ => .some v₂
  | .none,    .none    => .none := by
  let mergeValues : Option β → Option β → Option β := fun
    | .some v₁, .some v₂ => .some (f k v₁ v₂)
    | .some v₁, .none    => .some v₁
    | .none,    .some v₂ => .some v₂
    | .none,    .none    => .none
  change _ = mergeValues _ _
  match m₁ with
  | ExtTreeMap.mk t₁ =>
    match m₂ with
    | ExtTreeMap.mk t₂ =>
      induction t₁, t₂ using ExtDTreeMap.inductionOn₂ with
      | mk t₁ t₂ =>
        change DTreeMap.Const.get? (DTreeMap.Const.mergeWith f t₁ t₂) k =
          mergeValues (DTreeMap.Const.get? t₁ k) (DTreeMap.Const.get? t₂ k)
        cases h₁ : DTreeMap.Const.get? t₁ k <;>
          cases h₂ : DTreeMap.Const.get? t₂ k <;>
          simp only [mergeValues, DTreeMap.Const.get?_mergeWith, h₁, h₂]

/--
@isnad1 id=eq.2h7v.s7.2b3eb303fca2 from=translated src=- shape=5ef790eb vocab=3478e3ea
-/
lemma mergeWith_of_mem_mem (h₁ : k ∈ m₁) (h₂ : k ∈ m₂) :
    (m₁.mergeWith f m₂)[k]? = .some (f k m₁[k] m₂[k]) := by
  have h₁' : m₁[k]? = .some m₁[k] :=
    getElem?_eq_some_getElem (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .some m₂[k] :=
    getElem?_eq_some_getElem (t := m₂) (a := k) h₂
  simp only [getElem?_mergeWith_at, h₁', h₂']

/--
@isnad1 id=eq.2h7v.s7.1c724bbbc611 from=translated src=- shape=71959c55 vocab=b0561a72
-/
lemma mergeWith_of_mem_left (h₁ : k ∈ m₁) (h₂ : k ∉ m₂) :
    (m₁.mergeWith f m₂)[k]? = m₁[k]? := by
  have h₁' : m₁[k]? = .some m₁[k] :=
    getElem?_eq_some_getElem (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .none :=
    getElem?_eq_none (t := m₂) (a := k) h₂
  simp only [getElem?_mergeWith_at, h₁', h₂']

/--
@isnad1 id=eq.2h7v.s7.c4891741a376 from=translated src=- shape=3836ad0a vocab=b0561a72
-/
lemma mergeWith_of_mem_right (h₁ : k ∉ m₁) (h₂ : k ∈ m₂) :
    (m₁.mergeWith f m₂)[k]? = m₂[k]? := by
  have h₁' : m₁[k]? = .none :=
    getElem?_eq_none (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .some m₂[k] :=
    getElem?_eq_some_getElem (t := m₂) (a := k) h₂
  simp only [getElem?_mergeWith_at, h₁', h₂']

/--
@isnad1 id=eq.2h7v.s6.9f940c655c20 from=translated src=- shape=f4cad81f vocab=08e72048
-/
lemma mergeWith_of_not_mem (h₁ : k ∉ m₁) (h₂ : k ∉ m₂) :
    (m₁.mergeWith f m₂)[k]? = .none := by
  have h₁' : m₁[k]? = .none :=
    getElem?_eq_none (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .none :=
    getElem?_eq_none (t := m₂) (a := k) h₂
  simp only [getElem?_mergeWith_at, h₁', h₂']

grind_pattern mergeWith_of_mem_mem => k ∈ m₁, k ∈ m₂, ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith_of_mem_left => k ∈ m₁, ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith_of_mem_right => k ∈ m₂, ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith_of_not_mem => (ExtTreeMap.mergeWith f m₁ m₂)[k]?

variable {f : α → β → Bool}

end Std.ExtTreeMap
