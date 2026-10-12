/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Tengoku

/-!
# The graphs `G_S(2^ℕ)` and Miller's independence lemma

This file defines the graphs `G_S` on Cantor space associated to a set `S` of finite binary
words, and proves Miller's Proposition 6 ["The graph-theoretic approach to descriptive set
theory", BSL 18(4), 2012]: for *dense* `S` (every word extends into `S`), a non-meager set
with the Baire property contains a `G_S`-edge. Consequently every class of an equivalence
relation avoiding `G_S` is meager (`isMeagre_class_of_gSGraph_disjoint`), and in pullback
form (`isMeagre_pullback_class_of_gSGraph_hom`): a continuous `φ : 2^ℕ → α` that is a graph
homomorphism from `G_S` to the complement of a Borel equivalence relation `E` makes every
section `{b | E (φ a) (φ b)}` meager.

This is step 2 of the classical category route to Silver's theorem
(`InfinitaryLogic/Conditional/SilverCategoryRoute.lean`; see `docs/silver-phase2-route.md`):
combined with Kuratowski–Ulam (`isMeagre_of_isMeagre_sections`) and Mycielski
(`mycielski_cantor`), it reduces `CategoryReductionHypothesis` to exactly the classical
`G₀`-dichotomy.

## Definitions

* `prependWord w x`: the element of Cantor space starting with the word `w` and continuing
  with `x`; `wordCylinder w` is its range, the basic clopen set of sequences extending `w`.
* `GSGraph S y z`: `y = s ⌢ i ⌢ x` and `z = s ⌢ !i ⌢ x` for some `s ∈ S`, `i`, `x` — the
  two sequences extend the same `s ∈ S`, differ at position `s.length`, and share the tail.
* `DenseWords S`: every finite word has an extension in `S`.

## Proof of the independence lemma

By the Baire property, a non-meager `B` is comeager in some nonempty open set, hence in some
word cylinder `wordCylinder r`; pick `s ∈ S` extending `r`. The two injections
`prependWord (s ++ [i]) : 2^ℕ → wordCylinder (s ++ [i])` are continuous open maps, so the
sets of `x` with `prependWord (s ++ [i]) x ∉ B` are meager (`IsMeagre.preimage_of_isOpenMap`
applied to the part of the symmetric difference inside each child cylinder). A common point
`x` outside both meager sets yields the edge
`(prependWord (s ++ [false]) x, prependWord (s ++ [true]) x)` inside `B`.
-/

@[expose] public section

open Set Filter Topology

/-! ### Words and word cylinders -/

/-- The element of Cantor space that starts with the finite word `w` and continues with `x`. -/
def prependWord (w : List Bool) (x : ℕ → Bool) : ℕ → Bool := fun n =>
  if n < w.length then w.getD n false else x (n - w.length)

theorem prependWord_apply_of_lt {w : List Bool} {n : ℕ} (h : n < w.length) (x : ℕ → Bool) :
    prependWord w x n = w.getD n false := ite_eq_left h

theorem prependWord_apply_of_le {w : List Bool} {n : ℕ} (h : w.length ≤ n) (x : ℕ → Bool) :
    prependWord w x n = x (n - w.length) := ite_eq_right (not_lt.mpr h)

/-- The basic clopen set of sequences extending the word `w`. -/
private def wordCylinder (w : List Bool) : Set (ℕ → Bool) := Set.range (prependWord w)

/-- The word formed by the first `n` values of `x`. -/
def wordOf (x : ℕ → Bool) (n : ℕ) : List Bool := List.ofFn fun i : Fin n => x i

@[simp] theorem length_wordOf (x : ℕ → Bool) (n : ℕ) : (wordOf x n).length = n :=
  List.length_ofFn

/-! ### The graphs `G_S` -/

/-- The graph `G_S(2^ℕ)` on Cantor space associated to a set `S` of finite binary words:
edges connect `s ⌢ i ⌢ x` and `s ⌢ !i ⌢ x` for `s ∈ S`. -/
def GSGraph (S : Set (List Bool)) (y z : ℕ → Bool) : Prop :=
  ∃ s ∈ S, ∃ i : Bool, ∃ x : ℕ → Bool,
    y = prependWord (s ++ [i]) x ∧ z = prependWord (s ++ [!i]) x

/-- A set of words is dense if every word has an extension in it. -/
def DenseWords (S : Set (List Bool)) : Prop :=
  ∀ r : List Bool, ∃ s ∈ S, r <+: s

/-! ### A canonical dense and sparse set of words -/

/-- An enumeration of all finite binary words. -/
def wordEnum (n : ℕ) : List Bool := (Encodable.decode (α := List Bool) n).getD []

private theorem wordEnum_encode (w : List Bool) : wordEnum (Encodable.encode w) = w := by
  simp [wordEnum, Encodable.encodek]

/-- Pad a word with `false` up to length `n`. -/
def padTo (w : List Bool) (n : ℕ) : List Bool := w ++ List.replicate (n - w.length) false

private theorem length_padTo {w : List Bool} {n : ℕ} (h : w.length ≤ n) : (padTo w n).length
  = n := by
  simp only [padTo, List.length_append, List.length_replicate]
  omega

private theorem prefix_padTo (w : List Bool) (n : ℕ) : w <+: padTo w n := ⟨_, rfl⟩

/-- A strictly increasing length schedule dominating the word enumeration. -/
def canonicalLen : ℕ → ℕ
  | 0 => (wordEnum 0).length
  | n + 1 => max (wordEnum (n + 1)).length (canonicalLen n + 1)

private theorem le_canonicalLen (n : ℕ) : (wordEnum n).length ≤ canonicalLen n := by
  cases n with
  | zero => exact le_rfl
  | succ _ => exact le_max_left _ _

theorem canonicalLen_strictMono : StrictMono canonicalLen :=
  strictMono_nat_of_lt_succ fun _ =>
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)

/-- The `n`-th canonical word: the `n`-th word of the enumeration, padded to the `n`-th
length of the schedule. -/
def canonicalWord (n : ℕ) : List Bool := padTo (wordEnum n) (canonicalLen n)

theorem length_canonicalWord (n : ℕ) : (canonicalWord n).length = canonicalLen n :=
  length_padTo (le_canonicalLen n)

/-- The canonical dense and sparse set of finite binary words. -/
def canonicalS : Set (List Bool) := Set.range canonicalWord

theorem denseWords_canonicalS : DenseWords canonicalS := by
  intro r
  refine ⟨canonicalWord (Encodable.encode r), ⟨_, rfl⟩, ?_⟩
  rw [canonicalWord, wordEnum_encode]
  exact prefix_padTo _ _

/-! ### Miller's independence lemma (Prop. 6) -/
