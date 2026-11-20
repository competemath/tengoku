/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Seed.Data.Finmap
import Tengoku.Seed.Data.Fintype.EquivFin
import Tengoku.Forcing.Forcing.Order.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Forcing-ordered finite partial functions

Finite partial functions `∀ i, β i`, ordered by reverse inclusion: a stronger condition decides
at least as much, the same way. This is the shared carrier of the finite-condition forcing
notions — Cohen forcing `Fn(ω, 2)` is `FinitePartialFunction (fun _ : ℕ => Bool)`, and
`Add(ω, κ)` and collapse forcing reuse it at other index and value types.

Conditions are backed by `Finmap` (see `docs/decisions/0001-cohen-carrier.md`), wrapped in a
one-field structure rather than exposed as an abbreviation: the order instance then belongs to
this wrapper rather than to mathlib's `Finmap`, so the forcing orientation is not leaked
globally. The representation stays behind this file's API — downstream files use `lookup`,
`insert`, `keys`, and the lemmas here, never `toFinmap`.

Note that `union` is *not* given a lattice instance: it is a common strengthening only under
agreement, and globally it is left-biased, noncommutative, and not a forcing meet.

## Main definitions

* `Forcing.FinitePartialFunction β`: a finite partial section of `β`.
* `Forcing.FinitePartialFunction.lookup`, `insert`, `keys`, `union`: the basic operations.
* `Forcing.FinitePartialFunction.Agree`: two conditions agree wherever both are defined.

## Main results

* `Forcing.FinitePartialFunction.instPartialOrder`, `instOrderTop`: the order structure, with
  the empty condition as `⊤` (the weakest condition, deciding nothing).
* `Forcing.FinitePartialFunction.compatible_iff_agree`: compatibility is agreement, witnessed by
  the union.
* `Forcing.FinitePartialFunction.insert_le_iff`: `insert` strengthens exactly when the
  coordinate is fresh or the value agrees — it is an operation, not unconditionally a
  strengthening; `insert_eq_self` covers the value-agreement case exactly.
* `Forcing.FinitePartialFunction.exists_lookup_eq_none`: over an infinite index type, every
  condition leaves some coordinate undecided.
-/

universe u v

namespace Forcing

/-- A *finite partial function*: a finite partial section of `β`, thought of as a finite amount
of information about a total section. Ordered by reverse inclusion (`instPartialOrder`), this is
the carrier of the finite-condition forcing notions.-/
@[ext] structure FinitePartialFunction {ι : Type u} (β : ι → Type v) where
  /-- The underlying finite map. Downstream files use `lookup`/`insert`/`keys` instead.-/
  toFinmap : Finmap β

namespace FinitePartialFunction

variable {ι : Type u} {β : ι → Type v} [DecidableEq ι]
variable {p q : FinitePartialFunction β} {i j : ι} {b b' : β i}

/-- The value a condition assigns to a coordinate, if any.-/
def lookup (p : FinitePartialFunction β) (i : ι) : Option (β i) :=
  p.toFinmap.lookup i

/-- The coordinates a condition decides.-/
def keys (p : FinitePartialFunction β) : Finset ι :=
  p.toFinmap.keys

instance : Membership ι (FinitePartialFunction β) :=
  ⟨fun p i ↦ i ∈ p.keys⟩

omit [DecidableEq ι] in
/--
@isnad1 id=iff.0h4v.s5.b9a6e5f53a0b from=translated src=- shape=c1970ec0 vocab=8b7911b2
-/
theorem mem_def : i ∈ p ↔ i ∈ p.keys :=
  .rfl

/--
@isnad1 id=iff.0h4v.s5.3c4d364ce443 from=translated src=- shape=39cd728b vocab=3dfae1ac
-/
@[simp] theorem mem_keys : i ∈ p.keys ↔ (p.lookup i).isSome := by
  rw [keys, Finmap.mem_keys, lookup, ← Finmap.lookup_isSome]

/--
@isnad1 id=iff.0h4v.s5.4cbd18436ed2 from=translated src=- shape=81f281f0 vocab=2566e38a
-/
theorem mem_iff_isSome : i ∈ p ↔ (p.lookup i).isSome := by
  rw [mem_def, mem_keys]

/--
@isnad1 id=iff.0h4v.s5.1af76f975afc from=translated src=- shape=3573aed3 vocab=eccddc54
-/
theorem lookup_eq_none_iff : p.lookup i = none ↔ i ∉ p := by
  simp [mem_iff_isSome, Option.isSome_iff_ne_none]

/-- Conditions are determined by their lookups.
@isnad1 id=eq.1h4v.s5.d1508f1f8a19 from=translated src=- shape=50abc3c2 vocab=d7f37484
-/
theorem ext_lookup (h : ∀ i, p.lookup i = q.lookup i) : p = q :=
  FinitePartialFunction.ext (Finmap.ext_lookup h)

/--
@isnad1 id=iff.0h4v.s5.9f8643747a50 from=translated src=- shape=75620299 vocab=d7f37484
-/
theorem ext_lookup_iff : p = q ↔ ∀ i, p.lookup i = q.lookup i :=
  ⟨fun h _ ↦ h ▸ rfl, ext_lookup⟩

/-- The empty condition, deciding nothing.-/
instance : EmptyCollection (FinitePartialFunction β) :=
  ⟨⟨∅⟩⟩

/--
@isnad1 id=eq.0h3v.s5.02aaaf731587 from=translated src=- shape=4e27d8f1 vocab=8cc04a58
-/
@[simp] theorem lookup_empty : (∅ : FinitePartialFunction β).lookup i = none :=
  Finmap.lookup_empty i

/-- Extend a condition by deciding one coordinate. This is an *operation*: whether it
strengthens the original condition depends on the coordinate being fresh or the value agreeing
(see `insert_le_iff`).-/
def insert (p : FinitePartialFunction β) (i : ι) (b : β i) : FinitePartialFunction β :=
  ⟨p.toFinmap.insert i b⟩

/--
@isnad1 id=eq.0h5v.s5.563f33691cee from=translated src=- shape=a01949b5 vocab=0e4173b2
-/
@[simp] theorem lookup_insert_self : (p.insert i b).lookup i = some b :=
  Finmap.lookup_insert _

/--
@isnad1 id=eq.1h6v.s5.89d0f4f9b08e from=translated src=- shape=1e5d34bf vocab=207b47be
-/
@[simp] theorem lookup_insert_of_ne (h : j ≠ i) : (p.insert i b).lookup j = p.lookup j :=
  Finmap.lookup_insert_of_ne _ h

omit [DecidableEq ι] in
/--
@isnad1 id=eq.0h2v.s4.4477cd9a8137 from=translated src=- shape=dfb3ebfc vocab=37e570da
-/
@[simp] theorem keys_empty : (∅ : FinitePartialFunction β).keys = ∅ :=
  Finmap.keys_empty

/--
@isnad1 id=eq.0h5v.s5.e024b034cffc from=translated src=- shape=d0a63aae vocab=df83bc9d
-/
@[simp] theorem keys_insert : (p.insert i b).keys = Insert.insert i p.keys := by
  ext j
  rcases eq_or_ne j i with rfl | hne
  · simp
  · simp [mem_keys, lookup_insert_of_ne hne, hne]

/-- Reverse inclusion: `q ≤ p` means `q` decides everything `p` decides, the same way.-/
instance instPartialOrder : PartialOrder (FinitePartialFunction β) where
  le q p := ∀ ⦃i⦄ ⦃b : β i⦄, p.lookup i = some b → q.lookup i = some b
  le_refl _ _ _ h := h
  le_trans _ _ _ hab hbc _ _ h := hab (hbc h)
  le_antisymm _ _ hpq hqp :=
    ext_lookup fun _ ↦ Option.ext fun _ ↦ ⟨fun h ↦ hqp h, fun h ↦ hpq h⟩

/--
@isnad1 id=iff.0h4v.s6.9117acac88f1 from=translated src=- shape=50791cf4 vocab=3f133070
-/
theorem le_def : q ≤ p ↔ ∀ ⦃i⦄ ⦃b : β i⦄, p.lookup i = some b → q.lookup i = some b :=
  .rfl

/--
@isnad1 id=le.1h4v.s6.73910eaae85d from=translated src=- shape=fc927e27 vocab=3f133070
-/
theorem le_of_lookup (h : ∀ ⦃i⦄ ⦃b : β i⦄, p.lookup i = some b → q.lookup i = some b) : q ≤ p :=
  h

/-- A stronger condition decides every coordinate the weaker one decides.
@isnad1 id=mem.2h5v.s5.0aa4168fddec from=translated src=- shape=53d8918a vocab=5073d7c3
-/
theorem mem_mono (h : q ≤ p) (hi : i ∈ p) : i ∈ q := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (mem_iff_isSome.1 hi)
  exact mem_iff_isSome.2 (by rw [h hb]; rfl)

/--
@isnad1 id=le.1h4v.s5.49e3855ec54a from=translated src=- shape=0ceef3b6 vocab=942172d4
-/
theorem keys_mono (h : q ≤ p) : p.keys ⊆ q.keys :=
  fun _ hi ↦ mem_def.1 (mem_mono h (mem_def.2 hi))

/-- The empty condition is the weakest: it decides nothing, so every condition strengthens it.
Note the orientation — with smaller-is-stronger, `⊤` is the *weakest* condition.-/
instance instOrderTop : OrderTop (FinitePartialFunction β) where
  top := ∅
  le_top _ := fun _ _ h ↦ by rw [lookup_empty] at h; simp at h

/--
@isnad1 id=eq.0h2v.s5.22c3996bf825 from=translated src=- shape=f684cc77 vocab=101e66b9
-/
@[simp] theorem top_eq_empty : (⊤ : FinitePartialFunction β) = ∅ :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.9cb9a8af749b from=translated src=- shape=4e27d8f1 vocab=846feaa7
-/
@[simp] theorem lookup_top : (⊤ : FinitePartialFunction β).lookup i = none :=
  lookup_empty

/-- `insert` strengthens exactly when the coordinate is fresh or the value agrees.
@isnad1 id=iff.0h5v.s6.8db5be2c6f23 from=translated src=- shape=e9a09f22 vocab=ce51b0a4
-/
theorem insert_le_iff : p.insert i b ≤ p ↔ p.lookup i = none ∨ p.lookup i = some b := by
  constructor
  · intro h
    cases hp : p.lookup i with
    | none => exact Or.inl rfl
    | some b' =>
      have h1 := h hp
      rw [lookup_insert_self] at h1
      exact Or.inr h1.symm
  · intro h j c hj
    rcases eq_or_ne j i with rfl | hne
    · rcases h with h | h
      · rw [h] at hj
        simp at hj
      · rw [lookup_insert_self]
        exact h.symm.trans hj
    · rwa [lookup_insert_of_ne hne]

/-- Deciding a fresh coordinate strengthens the condition.
@isnad1 id=le.1h5v.s5.f640e7455430 from=translated src=- shape=4c55f36b vocab=cfd51add
-/
theorem insert_le_of_notMem (h : i ∉ p) : p.insert i b ≤ p :=
  insert_le_iff.2 (Or.inl (lookup_eq_none_iff.2 h))

/-- Re-deciding a coordinate the same way does not change the condition.
@isnad1 id=eq.1h5v.s5.248bdb60fa5c from=translated src=- shape=389284a0 vocab=0e4173b2
-/
@[simp] theorem insert_eq_self (h : p.lookup i = some b) : p.insert i b = p := by
  refine ext_lookup fun j ↦ ?_
  rcases eq_or_ne j i with rfl | hne
  · rw [lookup_insert_self, h]
  · rw [lookup_insert_of_ne hne]

/-- Re-deciding a coordinate the same way strengthens the condition — indeed leaves it
unchanged (`insert_eq_self`).
@isnad1 id=le.1h5v.s5.a5b6b9071577 from=translated src=- shape=36025dbe vocab=e86d45b4
-/
theorem insert_le_of_lookup_eq (h : p.lookup i = some b) : p.insert i b ≤ p :=
  insert_le_iff.2 (Or.inr h)

/-- Over an infinite index type, every condition leaves some coordinate undecided: `keys` is
finite.
@isnad1 id=ex.0h3v.s5.21fbe70c37a0 from=translated src=- shape=4cd63b5b vocab=8f40398c
-/
theorem exists_lookup_eq_none [Infinite ι] (p : FinitePartialFunction β) :
    ∃ i, p.lookup i = none := by
  obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset p.keys
  exact ⟨i, lookup_eq_none_iff.2 fun h ↦ hi (mem_def.1 h)⟩

/-- Two conditions *agree* if they assign the same value wherever both are defined.-/
def Agree (p q : FinitePartialFunction β) : Prop :=
  ∀ ⦃i⦄ ⦃b b' : β i⦄, p.lookup i = some b → q.lookup i = some b' → b = b'

/--
@isnad1 id=agree.1h4v.s4.c082d882b235 from=translated src=- shape=67bad3be vocab=c4f3c915
-/
theorem Agree.symm (h : Agree p q) : Agree q p :=
  fun _ _ _ hp hq ↦ (h hq hp).symm

/-- The union of two conditions, left-biased. It is the canonical common strengthening of
compatible conditions (`union_le_left`, `union_le_right`). It is deliberately given no lattice
instance: it is a common strengthening only under agreement, and globally it is left-biased,
noncommutative, and not a forcing meet.-/
def union (p q : FinitePartialFunction β) : FinitePartialFunction β :=
  ⟨p.toFinmap ∪ q.toFinmap⟩

/--
@isnad1 id=eq.0h4v.s5.951fdacf52c0 from=translated src=- shape=9af5f32c vocab=152825e8
-/
@[simp] theorem keys_union : (p.union q).keys = p.keys ∪ q.keys :=
  Finmap.keys_union

/--
@isnad1 id=iff.0h6v.s6.f9f3930b2fda from=translated src=- shape=0ca94be5 vocab=a4376f6a
-/
theorem lookup_union_eq_some_iff :
    (p.union q).lookup i = some b ↔ p.lookup i = some b ∨ (i ∉ p ∧ q.lookup i = some b) :=
  Finmap.mem_lookup_union

/--
@isnad1 id=le.0h4v.s5.919a434dad5d from=translated src=- shape=3512d591 vocab=384a7cb3
-/
theorem union_le_left (p q : FinitePartialFunction β) : p.union q ≤ p :=
  fun _ _ h ↦ lookup_union_eq_some_iff.2 (Or.inl h)

/--
@isnad1 id=le.1h4v.s5.130d21cdad72 from=translated src=- shape=bcf7bd58 vocab=33e2dc50
-/
theorem union_le_right (h : Agree p q) : p.union q ≤ q := by
  intro i b hb
  by_cases hi : i ∈ p
  · obtain ⟨b'', hb''⟩ := Finmap.mem_iff.1 hi
    rw [h (show p.lookup i = some b'' from hb'') hb] at hb''
    exact lookup_union_eq_some_iff.2 (Or.inl hb'')
  · exact lookup_union_eq_some_iff.2 (Or.inr ⟨hi, hb⟩)

/-- Compatibility is agreement: two conditions have a common strengthening exactly when they
assign the same values wherever both are defined, and the union witnesses it.
@isnad1 id=iff.0h4v.s5.dd8e90bb9692 from=translated src=- shape=6b6dfbf3 vocab=1c4178ea
-/
theorem compatible_iff_agree : Compatible p q ↔ Agree p q := by
  constructor
  · rintro ⟨r, hrp, hrq⟩ i b b' hp hq
    exact Option.some.inj ((hrp hp).symm.trans (hrq hq))
  · exact fun h ↦ ⟨p.union q, union_le_left p q, union_le_right h⟩

/--
@isnad1 id=compatib.1h4v.s5.e4876d8ae862 from=translated src=- shape=f5646a8f vocab=1c4178ea
-/
theorem Agree.compatible (h : Agree p q) : Compatible p q :=
  compatible_iff_agree.2 h

end FinitePartialFunction

end Forcing
