/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.ExampleB
public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Exercise318
import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Exercise319Sum
public import Tengoku

/-!
# Example 6.2 (Scott 1981, PRG-19, §6) — the generalisation `A ≅ Aⁿ + Aⁿ`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19
(1981), Lecture VI.
After the staple equations `B ≅ B + B` and `C ≅ {{Λ}} + C + C` (see
`Example62.lean`/`Example62C.lean`),
Scott proposes "a simple, yet interesting generalization of `B`": for any `n`, the
domain equation

`A ≅ Aⁿ + Aⁿ`,

where `Aⁿ` is the `n`-fold cartesian power. He solves it concretely over `Σ* =
{0,1}*` as the least
family

`A = {Σ*} ∪ ⋃_{i∈{0,1}} { i ⋃_{j<n} 1ʲ0 X_j ∣ X_j ∈ A for all j < n }`,

so a neighbourhood (other than the master `Σ*`) is a tag bit `i` (Scott's `+/−`,
here `true`/`false`)
followed by `n` slots, slot `j` reached behind the self-delimiting prefix `1ʲ0`.
An element of `A`
(other than `⊥`) is thus `±⟨a₀, …, a_{n-1}⟩`: an `n`-tuple of elements of `A`, in
one of two copies.

This module delivers:

* **`npow V n`** — the flat `n`-fold product `Vⁿ` over `Fin n × β`, with
neighbourhoods the proper
  products `prodN X = ⋃_j {j} × X_j`. (Closure under intersection is componentwise
  — no tags, so no
  non-emptiness needed.)
* **`Asys n hn`** — Scott's domain `A` over `{0,1}*` (the inductive family
`MemA`), a neighbourhood
  system under `0 < n` (so there is a coordinate to witness non-emptiness, Scott's
  `∅ ∉ A`). The slot
  encoding is `embTuple`, parsed via the uniqueness lemma `slotPre_inj`.
* **`A_domain_equation`** — the order-isomorphism `aaEquiv : |A| ≃o |Aⁿ + Aⁿ|`,
i.e.
  `Asys n hn ≅ᴰ sum (npow A n) (npow A n) …`, mirroring `Example61.dsharpEquiv`.

For `n = 1` this recovers `B ≅ B + B` (one slot per copy); the tree picture and
the automata-theory
aside (eventually-periodic trees ↔ regular events) are formalised in
`Example62Regular.lean`.

All *data* is choice-free (`#print axioms ⊆ {propext, Quot.sound}`).
-/

@[expose] public section

namespace Domain.Neighborhood

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

/-! ### The flat `n`-fold product `Vⁿ` over `Fin n × β`. -/

variable {β : Type*} {n : ℕ}

/-- The *proper product* neighbourhood `⋃_{j<n} {j} × X_j`: token `(j, b)` lies in
it iff `b ∈ X_j`.
This is the `n`-ary analogue of `prodNbhd` (Definition 3.1). -/
def prodN (X : Fin n → Set β) : Set (Fin n × β) := {p | p.2 ∈ X p.1}

/--
@isnad1 id=iff.0h4v.s5.220b81bae7d8 from=translated src=- shape=67038a0f vocab=3658245f
-/
@[simp] theorem mem_prodN {X : Fin n → Set β} {p : Fin n × β} : p ∈ prodN X ↔ p.2 ∈ X p.1 := Iff.rfl

/--
@isnad1 id=iff.0h4v.s5.80d3ad3df726 from=translated src=- shape=39844f3e vocab=119ffa33
-/
theorem prodN_subset {X X' : Fin n → Set β} : prodN X ⊆ prodN X' ↔ ∀ j, X j ⊆ X' j := by
  constructor
  · intro h j b hb; exact h (show (j, b) ∈ prodN X from hb)
  · intro h p hp; exact h p.1 hp

/--
@isnad1 id=eq.0h4v.s5.e1e46a3d13f3 from=translated src=- shape=58bac87d vocab=91091892
-/
theorem prodN_inter {X X' : Fin n → Set β} :
    prodN X ∩ prodN X' = prodN (fun j => X j ∩ X' j) := by
  ext p; simp only [Set.mem_inter_iff, mem_prodN]

/--
@isnad1 id=eq.1h5v.s5.df1083fe8f09 from=translated src=- shape=f2f15740 vocab=6b04409a
-/
theorem prodN_injective {X X' : Fin n → Set β} (h : prodN X = prodN X') : ∀ j, X j = X' j := by
  intro j; ext b
  have := Set.ext_iff.mp h (j, b)
  simpa only [mem_prodN] using this

/-- **The `n`-fold product `Vⁿ`** of a neighbourhood system `V`, over `Fin n × β`.
Its
neighbourhoods
are exactly the proper products `prodN X` with each component `X j ∈ V`. Closure
under intersection is
componentwise (no tags to disambiguate, so no non-emptiness is needed here). -/
def npow (V : NeighborhoodSystem β) (n : ℕ) : NeighborhoodSystem (Fin n × β) where
  mem W := ∃ X : Fin n → Set β, (∀ j, V.mem (X j)) ∧ W = prodN X
  master := prodN (fun _ => V.master)
  master_mem := ⟨_, fun _ => V.master_mem, rfl⟩
  inter_mem := by
    rintro W W' Z ⟨X, hX, rfl⟩ ⟨X', hX', rfl⟩ ⟨Zw, hZw, rfl⟩ hsub
    refine ⟨fun j => X j ∩ X' j, ?_, prodN_inter⟩
    intro j
    rw [prodN_inter] at hsub
    exact V.inter_mem (hX j) (hX' j) (hZw j) (prodN_subset.mp hsub j)
  sub_master := by
    rintro W ⟨X, hX, rfl⟩
    exact prodN_subset.mpr (fun j => V.sub_master (hX j))

/--
@isnad1 id=iff.0h4v.s5.8c555f375ef4 from=translated src=- shape=5eb6acc5 vocab=3877aea4
-/
@[simp] theorem npow_mem {V : NeighborhoodSystem β} {W : Set (Fin n × β)} :
    (npow V n).mem W ↔ ∃ X : Fin n → Set β, (∀ j, V.mem (X j)) ∧ W = prodN X := Iff.rfl

/-- Under Scott's standing assumption `∅ ∉ V`, no neighbourhood of `Vⁿ` is empty
(provided `0 < n`,
so there is a coordinate to witness).
@isnad1 id=nonempty.3h4v.s5.330dfcf1cadd from=translated src=- shape=ee3f604f vocab=b6e8be34
-/
theorem npow_nonempty {V : NeighborhoodSystem β} (hn : 0 < n)
    (hV : ∀ X, V.mem X → X.Nonempty) : ∀ W, (npow V n).mem W → W.Nonempty := by
  rintro W ⟨X, hX, rfl⟩
  obtain ⟨b, hb⟩ := hV (X ⟨0, hn⟩) (hX ⟨0, hn⟩)
  exact ⟨(⟨0, hn⟩, b), hb⟩

/-! ### Scott's slot encoding `i ⋃_{j<n} 1ʲ0 X_j` over `{0,1}*`. -/

/-- The slot prefix `i 1ʲ 0`: the leading tag bit `i` (Scott's `+/−`), then `j`
ones, then a zero.
Reaching component `j` of the tag-`i` tuple means matching this prefix. -/
def slotPre (i : Bool) (j : ℕ) : Str := i :: (List.replicate j true ++ [false])

/-- Parsing the `1ʲ0` body: the position of the first `false` pins down `j` and
the remainder.
@isnad1 id=and.1h4v.s5.bc9789bbea89 from=translated src=- shape=e9ae71a0 vocab=7223d16c
-/
theorem slot_list_inj : ∀ (j j' : ℕ) (u v : Str),
    List.replicate j true ++ false :: u = List.replicate j' true ++ false :: v → j = j' ∧ u = v
  | 0, 0, u, v, h => by simpa using h
  | 0, j' + 1, u, v, h => by simp [List.replicate_succ] at h
  | j + 1, 0, u, v, h => by simp [List.replicate_succ] at h
  | j + 1, j' + 1, u, v, h => by
      rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append,
        List.cons.injEq] at h
      obtain ⟨hj, hu⟩ := slot_list_inj j j' u v h.2
      exact ⟨by rw [hj], hu⟩

/-- **Uniqueness of slot decomposition.** A token `i 1ʲ 0 u` determines the tag
`i`, the index `j`,
and the remainder `u`. This is what makes the slots pairwise disjoint.
@isnad1 id=and.1h6v.s5.8703221c2159 from=translated src=- shape=d47453da vocab=3e8eac1a
-/
theorem slotPre_inj {i i' : Bool} {j j' : ℕ} {u v : Str}
    (h : slotPre i j ++ u = slotPre i' j' ++ v) : i = i' ∧ j = j' ∧ u = v := by
  rw [slotPre, slotPre, List.cons_append, List.cons_append, List.cons.injEq] at h
  obtain ⟨hi, hrest⟩ := h
  rw [List.append_assoc, List.append_assoc, List.singleton_append, List.singleton_append] at hrest
  obtain ⟨hj, huv⟩ := slot_list_inj j j' u v hrest
  exact ⟨hi, hj, huv⟩

variable {n : ℕ}

/-- **Scott's tag-`i` tuple neighbourhood** `i ⋃_{j<n} 1ʲ0 X_j`: the union of the
`n` slots,
slot `j`
holding `X j` behind the prefix `i 1ʲ 0`. (For `i = false`/`true` these are
Scott's left/right
copies, the `−`/`+` summands.) -/
def embTuple (i : Bool) (X : Fin n → Set Str) : Set Str :=
  {w | ∃ j : Fin n, ∃ w', w = slotPre i (j : ℕ) ++ w' ∧ w' ∈ X j}

/--
@isnad1 id=iff.0h4v.s5.3aa5291d01a0 from=translated src=- shape=e98560e2 vocab=6a456972
-/
@[simp] theorem mem_embTuple {i : Bool} {X : Fin n → Set Str} {w : Str} :
    w ∈ embTuple i X ↔ ∃ j : Fin n, ∃ w', w = slotPre i (j : ℕ) ++ w' ∧ w' ∈ X j := Iff.rfl

/--
@isnad1 id=not.0h3v.s4.67b9d3f236e8 from=translated src=- shape=ebaf8112 vocab=0da280b4
-/
theorem nil_not_mem_embTuple {i : Bool} {X : Fin n → Set Str} : ([] : Str) ∉ embTuple i X := by
  rintro ⟨j, a, heq, -⟩
  rw [slotPre, List.cons_append] at heq
  exact List.cons_ne_nil _ _ heq.symm

/--
@isnad1 id=ne.0h3v.s4.fba335928651 from=translated src=- shape=4037676e vocab=f866a9f6
-/
theorem embTuple_ne_univ {i : Bool} (X : Fin n → Set Str) : embTuple i X ≠ Set.univ := by
  intro h
  have : ([] : Str) ∈ embTuple i X := by rw [h]; exact Set.mem_univ []
  exact nil_not_mem_embTuple this

/--
@isnad1 id=eq.0h4v.s5.6c0e35cf3bdd from=translated src=- shape=74fec8d6 vocab=9722986e
-/
theorem embTuple_inter {i : Bool} (X X' : Fin n → Set Str) :
    embTuple i X ∩ embTuple i X' = embTuple i (fun j => X j ∩ X' j) := by
  ext w
  simp only [Set.mem_inter_iff, mem_embTuple]
  constructor
  · rintro ⟨⟨j, a, rfl, ha⟩, ⟨j', a', heq, ha'⟩⟩
    obtain ⟨-, hjj, rfl⟩ := slotPre_inj heq
    obtain rfl : j = j' := Fin.ext hjj
    exact ⟨j, a, rfl, ha, ha'⟩
  · rintro ⟨j, a, rfl, ha, ha'⟩
    exact ⟨⟨j, a, rfl, ha⟩, ⟨j, a, rfl, ha'⟩⟩

/--
@isnad1 id=eq.1h5v.s5.ae584d48cd84 from=translated src=- shape=cccbc49c vocab=2b215d7c
-/
theorem embTuple_inter_ne {i i' : Bool} (h : i ≠ i') (X X' : Fin n → Set Str) :
    embTuple i X ∩ embTuple i' X' = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, mem_embTuple, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨j, a, rfl, ha⟩ ⟨j', a', heq, ha'⟩
  exact h (slotPre_inj heq).1

/--
@isnad1 id=iff.0h4v.s5.c92f257a6406 from=translated src=- shape=04173d64 vocab=08f9420b
-/
theorem embTuple_subset {i : Bool} {X X' : Fin n → Set Str} :
    embTuple i X ⊆ embTuple i X' ↔ ∀ j, X j ⊆ X' j := by
  constructor
  · intro h j a ha
    obtain ⟨j', a', heq, ha'⟩ := h ⟨j, a, rfl, ha⟩
    obtain ⟨-, hjj, rfl⟩ := slotPre_inj heq
    obtain rfl : j = j' := Fin.ext hjj
    exact ha'
  · rintro h w ⟨j, a, rfl, ha⟩
    exact ⟨j, a, rfl, h j ha⟩

/--
@isnad1 id=eq.1h5v.s5.d3b886040098 from=translated src=- shape=c6d598ba vocab=7ada536a
-/
theorem embTuple_injective {i : Bool} {X X' : Fin n → Set Str}
    (h : embTuple i X = embTuple i X') : ∀ j, X j = X' j := by
  intro j
  exact Set.Subset.antisymm (embTuple_subset.mp h.subset j) (embTuple_subset.mp h.symm.subset j)

/--
@isnad1 id=nonempty.1h4v.s4.466b1ad0d37f from=translated src=- shape=a0e41425 vocab=c0dca7e7
-/
theorem embTuple_nonempty {i : Bool} {X : Fin n → Set Str} (j : Fin n) (h : (X j).Nonempty) :
    (embTuple i X).Nonempty := by
  obtain ⟨a, ha⟩ := h
  exact ⟨slotPre i (j : ℕ) ++ a, j, a, rfl, ha⟩

/--
@isnad1 id=ne.2h6v.s5.4a8bb21ca629 from=translated src=- shape=a657d66a vocab=c0dca7e7
-/
theorem embTuple_ne {i i' : Bool} (h : i ≠ i') {X Y : Fin n → Set Str} (j : Fin n)
    (hX : (X j).Nonempty) : embTuple i X ≠ embTuple i' Y := by
  intro heq
  obtain ⟨a, ha⟩ := hX
  have hmem : slotPre i (j : ℕ) ++ a ∈ embTuple i' Y := heq ▸ (⟨j, a, rfl, ha⟩ : _ ∈ embTuple i X)
  obtain ⟨j', a', he, -⟩ := hmem
  exact h (slotPre_inj he).1

/-! ### The neighbourhood system `A` solving `A ≅ Aⁿ + Aⁿ`. -/

/-- **Scott's domain `A`** as the *least* family of subsets of `Σ* = {0,1}*`
containing (i) the
master
`Σ*` and (ii) every tag-`i` tuple `i ⋃_{j<n} 1ʲ0 X_j` built from components `X j`
already in `A`:

`A = {Σ*} ∪ ⋃_{i∈{0,1}} { i ⋃_{j<n} 1ʲ0 X_j ∣ X_j ∈ A }`. -/
inductive MemA (n : ℕ) : Set Str → Prop
  | univ : MemA n Set.univ
  | tuple (i : Bool) {X : Fin n → Set Str} : (∀ j, MemA n (X j)) → MemA n (embTuple i X)

/-- Under `0 < n` every neighbourhood of `A` is non-empty (Scott's `∅ ∉ A`).
@isnad1 id=nonempty.2h2v.s4.8146214b35f9 from=translated src=- shape=2eafa2dc vocab=6ca81e89
-/
theorem memA_nonempty (hn : 0 < n) : ∀ {W}, MemA n W → W.Nonempty := by
  intro W hW
  induction hW with
  | univ => exact ⟨[], Set.mem_univ []⟩
  | tuple i hX ih => exact embTuple_nonempty ⟨0, hn⟩ (ih ⟨0, hn⟩)

/-- A non-empty witness contained in a tag-`i'` tuple must carry the tag `i'`.
@isnad1 id=eq.3h5v.s5.9f467962d28b from=translated src=- shape=f57a5719 vocab=06d8c567
-/
theorem tag_eq_of_subset (hn : 0 < n) {i i' : Bool} {Z V : Fin n → Set Str}
    (hZ : ∀ j, MemA n (Z j)) (hsub : embTuple i Z ⊆ embTuple i' V) : i = i' := by
  obtain ⟨a, ha⟩ := memA_nonempty hn (hZ ⟨0, hn⟩)
  obtain ⟨j', v, he, -⟩ := hsub ⟨⟨0, hn⟩, a, rfl, ha⟩
  exact (slotPre_inj he).1

/-- Inversion: the components of a tuple-shaped neighbourhood of `A` are
themselves in `A`.
@isnad1 id=mema.2h4v.s5.426edc042a5f from=translated src=- shape=6bb62c5a vocab=923a1d30
-/
theorem memA_tuple_inv (hn : 0 < n) {i : Bool} {X : Fin n → Set Str}
    (h : MemA n (embTuple i X)) : ∀ j, MemA n (X j) := by
  generalize hW : embTuple i X = W at h
  cases h with
  | univ =>
    exfalso
    have : ([] : Str) ∈ embTuple i X := by rw [hW]; exact Set.mem_univ []
    exact nil_not_mem_embTuple this
  | @tuple i' X' hX' =>
    have hne : (embTuple i' X').Nonempty :=
      embTuple_nonempty ⟨0, hn⟩ (memA_nonempty hn (hX' ⟨0, hn⟩))
    rw [← hW] at hne
    obtain ⟨w, j, a, rfl, ha⟩ := hne
    have hmem : slotPre i (j : ℕ) ++ a ∈ embTuple i' X' := hW ▸ (⟨j, a, rfl, ha⟩ : _ ∈ embTuple i X)
    obtain ⟨j', a', he, -⟩ := hmem
    have hii : i = i' := (slotPre_inj he).1
    subst hii
    intro k; rw [embTuple_injective hW k]; exact hX' k

/-- **`A` is closed under consistent intersection.** Scott's verification, by
induction on the
way `X`
entered `A`: the cross case `embTuple false · ∩ embTuple true ·` collapses to `∅`
(killed by the
non-empty witness), the same-tag case combines componentwise (recursing on the
consistency witness's
slots).
@isnad1 id=mema.5h4v.s5.399305cdd452 from=translated src=- shape=efb261c8 vocab=ba79ab30
-/
theorem memA_inter (hn : 0 < n) :
    ∀ {X}, MemA n X → ∀ {Y}, MemA n Y → ∀ {Z}, MemA n Z → Z ⊆ X ∩ Y → MemA n (X ∩ Y) := by
  intro X hX
  induction hX with
  | univ =>
    simp_all
  | @tuple i X hX ih =>
    intro Y hY Z hZ hsub
    cases hY with
    | univ =>
      rw [Set.inter_univ]; exact MemA.tuple i hX
    | @tuple i' X' hX' =>
      by_cases hii : i = i'
      · rw [hii, embTuple_inter] at hsub ⊢
        cases hZ with
        | univ => exact absurd (hsub (Set.mem_univ [])) nil_not_mem_embTuple
        | @tuple i'' ZW hZW =>
          have htag : i'' = i' := tag_eq_of_subset hn hZW hsub
          rw [htag] at hsub
          have hZsub := embTuple_subset.mp hsub
          exact MemA.tuple i' (fun j => ih j (hX' j) (hZW j) (hZsub j))
      · rw [embTuple_inter_ne hii] at hsub ⊢
        simp_all

/-- **Scott's domain `A`** packaged as a neighbourhood system over `{0,1}*` (needs
`0 < n`). -/
def Asys (n : ℕ) (hn : 0 < n) : NeighborhoodSystem Str where
  mem := MemA n
  master := Set.univ
  master_mem := MemA.univ
  inter_mem := fun hX hY hZ hsub => memA_inter hn hX hY hZ hsub
  sub_master := fun _ => Set.subset_univ _

/--
@isnad1 id=iff.1h2v.s4.bb83b3b61f6f from=translated src=- shape=1d825a5a vocab=1d7b4671
-/
@[simp] theorem Asys_mem {hn : 0 < n} {W : Set Str} : (Asys n hn).mem W ↔ MemA n W := Iff.rfl

/--
@isnad1 id=eq.1h1v.s4.176a6773c79a from=translated src=- shape=0967440a vocab=955233ae
-/
@[simp] theorem Asys_master {hn : 0 < n} : (Asys n hn).master = Set.univ := rfl

/-! ### The domain equation `A ≅ Aⁿ + Aⁿ`. -/

/-- The `n`-fold product `Aⁿ = npow A n`. -/
abbrev Apow (hn : 0 < n) : NeighborhoodSystem (Fin n × Str) := npow (Asys n hn) n

/--
@isnad1 id=nonempty.2h2v.s5.cd9ce74ee148 from=translated src=- shape=a9cea76a vocab=53a9d84f
-/
theorem apowNe (hn : 0 < n) : ∀ W, (Apow hn).mem W → W.Nonempty :=
  npow_nonempty hn (fun _ h => memA_nonempty hn h)

/-- The right-hand side of Scott's equation: the separated sum `Aⁿ + Aⁿ`. -/
abbrev AAsys (hn : 0 < n) : NeighborhoodSystem (Option ((Fin n × Str) ⊕ (Fin n × Str))) :=
  sum (Apow hn) (Apow hn) (apowNe hn) (apowNe hn)

/--
@isnad1 id=mem.2h2v.s5.5e9f615a62f8 from=translated src=- shape=db5a8a5c vocab=0edd31ec
-/
theorem apow_mem_prodN (hn : 0 < n) {X : Fin n → Set Str} (hX : ∀ j, MemA n (X j)) :
    (Apow hn).mem (prodN X) := ⟨X, hX, rfl⟩

/--
@isnad1 id=mema.2h3v.s5.39de4b4dd7d4 from=translated src=- shape=866e6e1d vocab=0edd31ec
-/
theorem apow_mem_prodN_inv (hn : 0 < n) {X : Fin n → Set Str} (h : (Apow hn).mem (prodN X)) :
    ∀ j, MemA n (X j) := by
  obtain ⟨X', hX', heq⟩ := h
  intro j; rw [prodN_injective heq j]; exact hX' j

/--
@isnad1 id=mem.2h2v.s5.d36ea87c77e5 from=translated src=- shape=79bfe0dd vocab=1ff1966a
-/
theorem aa_mem_inj₀ (hn : 0 < n) {X : Fin n → Set Str} (hX : ∀ j, MemA n (X j)) :
    (AAsys hn).mem (inj₀ (prodN X)) := Or.inr (Or.inl ⟨prodN X, apow_mem_prodN hn hX, rfl⟩)

/--
@isnad1 id=mem.2h2v.s5.5558a107a1d8 from=translated src=- shape=79bfe0dd vocab=db5c0319
-/
theorem aa_mem_inj₁ (hn : 0 < n) {Y : Fin n → Set Str} (hY : ∀ j, MemA n (Y j)) :
    (AAsys hn).mem (inj₁ (prodN Y)) := Or.inr (Or.inr ⟨prodN Y, apow_mem_prodN hn hY, rfl⟩)

/--
@isnad1 id=mem.2h2v.s5.d99bec8e2b82 from=translated src=- shape=1a5a0978 vocab=8befe479
-/
theorem aa_mem_inj₀_inv (hn : 0 < n) {V : Set (Fin n × Str)}
    (h : (AAsys hn).mem (inj₀ V)) : (Apow hn).mem V := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
  · rw [inj₀_injective heq]; exact hX'
  · obtain ⟨b, hb⟩ := apowNe hn _ hY'
    exact absurd (heq ▸ ir_mem_inj₁.mpr hb) ir_mem_inj₀

/--
@isnad1 id=mem.2h2v.s5.852ec62dfd91 from=translated src=- shape=1a5a0978 vocab=e7fd4428
-/
theorem aa_mem_inj₁_inv (hn : 0 < n) {V : Set (Fin n × Str)}
    (h : (AAsys hn).mem (inj₁ V)) : (Apow hn).mem V := by
  rcases h with h0 | ⟨X', hX', heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := apowNe hn _ hX'
    exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · rw [inj₁_injective heq]; exact hY'

/--
@isnad1 id=nonempty.2h2v.s5.8c0b69557922 from=translated src=- shape=52dd5244 vocab=6e6a8470
-/
theorem aa_mem_nonempty (hn : 0 < n) {W : Set (Option ((Fin n × Str) ⊕ (Fin n × Str)))}
    (h : (AAsys hn).mem W) : W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨none, none_mem_sumMaster⟩
  · exact inj₀_nonempty (apowNe hn _ hX)
  · exact inj₁_nonempty (apowNe hn _ hY)

/-- **Forward half of `A ≅ Aⁿ + Aⁿ`.** An element `z` of `A` is sent to the sum
element
recording, for
each branch, whether `z` reaches the left copy `0X` (left summand `Aⁿ`) or the
right copy `1Y` (right
summand `Aⁿ`). -/
def toAA (hn : 0 < n) (z : (Asys n hn).Element) : (AAsys hn).Element where
  mem W := W = sumMaster (Apow hn) (Apow hn)
    ∨ (∃ X, (∀ j, MemA n (X j)) ∧ W = inj₀ (prodN X) ∧ z.mem (embTuple false X))
    ∨ (∃ Y, (∀ j, MemA n (Y j)) ∧ W = inj₁ (prodN Y) ∧ z.mem (embTuple true Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact (AAsys hn).master_mem
    · exact aa_mem_inj₀ hn hX
    · exact aa_mem_inj₁ hn hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨Y', hY', rfl, hzY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumMaster_inter_inj₀ (apow_mem_prodN hn hX')], hzX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumMaster_inter_inj₁ (apow_mem_prodN hn hY')], hzY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX,
        by rw [Set.inter_comm, sumMaster_inter_inj₀ (apow_mem_prodN hn hX)], hzX⟩)
    · refine Or.inr (Or.inl ⟨fun j => X j ∩ X' j, ?_, by rw [inj₀_inter, prodN_inter], ?_⟩)
      · have hz := z.inter_mem hzX hzX'; rw [embTuple_inter] at hz
        exact memA_tuple_inv hn (z.sub hz)
      · have hz := z.inter_mem hzX hzX'; rwa [embTuple_inter] at hz
    · exfalso
      have hz := z.inter_mem hzX hzY'
      rw [embTuple_inter_ne (by decide : (false : Bool) ≠ true)] at hz
      obtain ⟨t, ht⟩ := memA_nonempty hn (z.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY,
        by rw [Set.inter_comm, sumMaster_inter_inj₁ (apow_mem_prodN hn hY)], hzY⟩)
    · exfalso
      have hz := z.inter_mem hzY hzX'
      rw [embTuple_inter_ne (by decide : (true : Bool) ≠ false)] at hz
      obtain ⟨t, ht⟩ := memA_nonempty hn (z.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨fun j => Y j ∩ Y' j, ?_, by rw [inj₁_inter, prodN_inter], ?_⟩)
      · have hz := z.inter_mem hzY hzY'; rw [embTuple_inter] at hz
        exact memA_tuple_inv hn (z.sub hz)
      · have hz := z.inter_mem hzY hzY'; rwa [embTuple_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩) hW' hsub
    · exact Or.inl (eq_sumMaster_of_subset hW' hsub)
    · rcases hW' with rfl | ⟨V', hV', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨X', hX', rfl⟩ := hV'
        refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact z.up_mem hzX (MemA.tuple false hX')
          (embTuple_subset.mpr (prodN_subset.mp (inj₀_subset_inj₀.mp hsub)))
      · obtain ⟨b, hb⟩ := apowNe hn (prodN X) (apow_mem_prodN hn hX)
        exact absurd (hsub (il_mem_inj₀.mpr hb)) il_mem_inj₁
    · rcases hW' with rfl | ⟨V', hV', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := apowNe hn (prodN Y) (apow_mem_prodN hn hY)
        exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · obtain ⟨Y', hY', rfl⟩ := hV'
        refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact z.up_mem hzY (MemA.tuple true hY')
          (embTuple_subset.mpr (prodN_subset.mp (inj₁_subset_inj₁.mp hsub)))

/--
@isnad1 id=iff.2h3v.s6.5e36282f3d70 from=translated src=- shape=71db8498 vocab=9f5deacb
-/
@[simp] theorem toAA_mem_inj₀ (hn : 0 < n) {z : (Asys n hn).Element} {X : Fin n → Set Str}
    (hX : ∀ j, MemA n (X j)) :
    (toAA hn z).mem (inj₀ (prodN X)) ↔ z.mem (embTuple false X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
    · rw [funext (prodN_injective (inj₀_injective heq))]; exact hz
    · obtain ⟨b, hb⟩ := apowNe hn (prodN X) (apow_mem_prodN hn hX)
      exact absurd (heq ▸ il_mem_inj₀.mpr hb) il_mem_inj₁
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

/--
@isnad1 id=iff.2h3v.s6.b7d1878ae053 from=translated src=- shape=71db8498 vocab=bcd34ddd
-/
@[simp] theorem toAA_mem_inj₁ (hn : 0 < n) {z : (Asys n hn).Element} {Y : Fin n → Set Str}
    (hY : ∀ j, MemA n (Y j)) :
    (toAA hn z).mem (inj₁ (prodN Y)) ↔ z.mem (embTuple true Y) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
    · obtain ⟨a, ha⟩ := apowNe hn (prodN X') (apow_mem_prodN hn hX')
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
    · rw [funext (prodN_injective (inj₁_injective heq))]; exact hz
  · intro hz; exact Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩)

/-- **Inverse half of `A ≅ Aⁿ + Aⁿ`.** -/
def fromAA (hn : 0 < n) (s : (AAsys hn).Element) : (Asys n hn).Element where
  mem W := W = Set.univ
    ∨ (∃ X, (∀ j, MemA n (X j)) ∧ W = embTuple false X ∧ s.mem (inj₀ (prodN X)))
    ∨ (∃ Y, (∀ j, MemA n (Y j)) ∧ W = embTuple true Y ∧ s.mem (inj₁ (prodN Y)))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact MemA.univ
    · exact MemA.tuple false hX
    · exact MemA.tuple true hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨Y', hY', rfl, hsY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [Set.univ_inter], hsX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [Set.univ_inter], hsY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_univ], hsX⟩)
    · have hs := s.inter_mem hsX hsX'
      rw [inj₀_inter, prodN_inter] at hs
      exact Or.inr (Or.inl ⟨fun j => X j ∩ X' j,
        apow_mem_prodN_inv hn (aa_mem_inj₀_inv hn (s.sub hs)), by rw [embTuple_inter], hs⟩)
    · exfalso
      have hs := s.inter_mem hsX hsY'; rw [inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := aa_mem_nonempty hn (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_univ], hsY⟩)
    · exfalso
      have hs := s.inter_mem hsY hsX'; rw [Set.inter_comm, inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := aa_mem_nonempty hn (s.sub hs); exact Set.notMem_empty t ht
    · have hs := s.inter_mem hsY hsY'
      rw [inj₁_inter, prodN_inter] at hs
      exact Or.inr (Or.inr ⟨fun j => Y j ∩ Y' j,
        apow_mem_prodN_inv hn (aa_mem_inj₁_inv hn (s.sub hs)), by rw [embTuple_inter], hs⟩)
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · cases hW' with
      | univ => exact Or.inl rfl
      | @tuple i'' V hV =>
        have htag : false = i'' := tag_eq_of_subset hn hX hsub
        subst htag
        refine Or.inr (Or.inl ⟨V, hV, rfl, ?_⟩)
        exact s.up_mem hsX (aa_mem_inj₀ hn hV)
          (inj₀_subset_inj₀.mpr (prodN_subset.mpr (embTuple_subset.mp hsub)))
    · cases hW' with
      | univ => exact Or.inl rfl
      | @tuple i'' V hV =>
        have htag : true = i'' := tag_eq_of_subset hn hY hsub
        subst htag
        refine Or.inr (Or.inr ⟨V, hV, rfl, ?_⟩)
        exact s.up_mem hsY (aa_mem_inj₁ hn hV)
          (inj₁_subset_inj₁.mpr (prodN_subset.mpr (embTuple_subset.mp hsub)))

/--
@isnad1 id=iff.2h3v.s6.871980344c21 from=translated src=- shape=251ed1b6 vocab=812b796e
-/
@[simp] theorem fromAA_mem_embF (hn : 0 < n) {s : (AAsys hn).Element} {X : Fin n → Set Str}
    (hX : ∀ j, MemA n (X j)) :
    (fromAA hn s).mem (embTuple false X) ↔ s.mem (inj₀ (prodN X)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embTuple_ne_univ X)
    · rw [funext (embTuple_injective heq)]; exact hs
    · exact absurd heq
        (embTuple_ne (by decide : (false : Bool) ≠ true) ⟨0, hn⟩ (memA_nonempty hn (hX ⟨0, hn⟩)))
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

/--
@isnad1 id=iff.2h3v.s6.619794cbb75b from=translated src=- shape=251ed1b6 vocab=fd42f422
-/
@[simp] theorem fromAA_mem_embT (hn : 0 < n) {s : (AAsys hn).Element} {Y : Fin n → Set Str}
    (hY : ∀ j, MemA n (Y j)) :
    (fromAA hn s).mem (embTuple true Y) ↔ s.mem (inj₁ (prodN Y)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 (embTuple_ne_univ Y)
    · exact absurd heq.symm
        (embTuple_ne (by decide : (false : Bool) ≠ true) ⟨0, hn⟩ (memA_nonempty hn (hX' ⟨0, hn⟩)))
    · rw [funext (embTuple_injective heq)]; exact hs
  · intro hs; exact Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩)

/--
@isnad1 id=eq.1h2v.s5.4ba089367e29 from=translated src=- shape=decdc1a2 vocab=b10dfc9c
-/
theorem fromAA_toAA (hn : 0 < n) (z : (Asys n hn).Element) : fromAA hn (toAA hn z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact z.master_mem
    · exact (toAA_mem_inj₀ hn hX).mp hs
    · exact (toAA_mem_inj₁ hn hY).mp hs
  · intro hW
    cases z.sub hW with
    | univ => exact Or.inl rfl
    | @tuple i X hX =>
      cases i with
      | false => exact Or.inr (Or.inl ⟨X, hX, rfl, (toAA_mem_inj₀ hn hX).mpr hW⟩)
      | true => exact Or.inr (Or.inr ⟨X, hX, rfl, (toAA_mem_inj₁ hn hX).mpr hW⟩)

/--
@isnad1 id=eq.1h2v.s5.c2a612ad6287 from=translated src=- shape=f716fda9 vocab=13d912dc
-/
theorem toAA_fromAA (hn : 0 < n) (s : (AAsys hn).Element) : toAA hn (fromAA hn s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromAA_mem_embF hn hX).mp hs
    · exact (fromAA_mem_embT hn hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨V, hV, rfl⟩ | ⟨V, hV, rfl⟩
    · exact Or.inl rfl
    · obtain ⟨X, hX, rfl⟩ := hV
      exact Or.inr (Or.inl ⟨X, hX, rfl, (fromAA_mem_embF hn hX).mpr hW⟩)
    · obtain ⟨Y, hY, rfl⟩ := hV
      exact Or.inr (Or.inr ⟨Y, hY, rfl, (fromAA_mem_embT hn hY).mpr hW⟩)

/-- **The isomorphism `|A| ≃o |Aⁿ + Aⁿ|`.** -/
def aaEquiv (hn : 0 < n) : (Asys n hn).Element ≃o (AAsys hn).Element where
  toFun := toAA hn
  invFun := fromAA hn
  left_inv := fromAA_toAA hn
  right_inv := toAA_fromAA hn
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hW
      cases z.sub hW with
      | univ => exact z'.master_mem
      | @tuple i X hX =>
        cases i with
        | false => exact (toAA_mem_inj₀ hn hX).mp (h _ (Or.inr (Or.inl ⟨X, hX, rfl, hW⟩)))
        | true => exact (toAA_mem_inj₁ hn hX).mp (h _ (Or.inr (Or.inr ⟨X, hX, rfl, hW⟩)))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨Y, hY, rfl, h _ hzY⟩)

/-- **Example 6.2 (Scott 1981, PRG-19) — the domain equation `A ≅ Aⁿ + Aⁿ`.**
Scott's "simple, yet
interesting generalization of `B`": the domain `A` over `{0,1}*` (whose non-`⊥`
elements are the two
copies — left `−` and right `+` — of an `n`-tuple of elements of `A`) is
isomorphic to the separated
sum `Aⁿ + Aⁿ` of two copies of its own `n`-fold cartesian power.
@isnad1 id=isomorph.1h1v.s4.b15bac5ae0e1 from=translated src=- shape=25675b78 vocab=c5f147b6
-/
theorem A_domain_equation (hn : 0 < n) : Asys n hn ≅ᴰ AAsys hn := ⟨aaEquiv hn⟩

end Example62A

end Domain.Neighborhood
