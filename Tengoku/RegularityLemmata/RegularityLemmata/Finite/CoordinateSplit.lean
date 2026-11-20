/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.Seed.Data.Fintype.Pi
import Tengoku.Seed.Data.Fintype.BigOperators
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Logic.Equiv.Basic
import Tengoku.Seed.Order.Disjoint
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Splitting tuple coordinates into two groups

A `CoordinateSplit n` chooses a set of coordinates; the rest are its complement. Tuples over
a **dependent** carrier family `V : Fin n → Type*` then factor as a pair of half-tuples
(`splitEquiv`), and relations on tuples become relations between the halves (`splitRel`).

This is ordinary finite combinatorics. Nothing here mentions weights, regularity, or
stability, and nothing imports a relational model — which is what lets the weighted-box and
hypergraph layers consume it.

## Two representation decisions

**Only the chosen coordinate set is data.** The complement, the two index subtypes, and
properness are all derived. In particular `IsProper` is a **predicate, not a field**: empty
and full splits are legal neutral endpoints here, and a consumer needing a genuine two-sided
split asks for `σ.IsProper` itself. Bundling nonemptiness proofs would tax every neutral
consumer.

**Reindexing transports the carrier family too.** For `π : Equiv.Perm (Fin n)` the reindexed
tuple `fun i => x (π i)` has type `∀ i, V (π i)`, not `∀ i, V i`. Rather than insert casts,
the naturality statements are indexed by the transported family `fun i => V (π i)`, and the
correspondence between the two index subtypes is carried by an explicit `Equiv`
(`reindexLeftEquiv`, `reindexRightEquiv`). Every public statement is then cast-free and
holds by `rfl`. The membership equation

  `i ∈ (σ.reindex π).left ↔ π i ∈ σ.left`

is the canonical statement of the reindexing direction; all naturality is derived from it, so
the direction cannot drift.

The only cast in the file is inside `oneVsRest`, where reconstructing a full tuple from a
value at coordinate `i` needs `h : j = i` to move `V i` to `V j`. It is quarantined in that
definition and its evaluation lemma.
-/

namespace RegularityLemmata

/-- A split of the coordinates `Fin n` into a chosen set and its complement. Only the chosen
set is data.-/
structure CoordinateSplit (n : ℕ) where
  /-- The chosen coordinates.-/
  left : Finset (Fin n)

namespace CoordinateSplit

variable {n : ℕ} {V : Fin n → Type*}

/-! ### The two sides -/

/-- The complementary coordinates.-/
def right (σ : CoordinateSplit n) : Finset (Fin n) := Finset.univ \ σ.left

/--
@isnad1 id=iff.0h3v.s5.9ca8fc5c88a7 from=translated src=- shape=6da60c4a vocab=d6cb43af
-/
@[simp] theorem mem_right_iff {σ : CoordinateSplit n} {i : Fin n} :
    i ∈ σ.right ↔ i ∉ σ.left := by
  rw [right, Finset.mem_sdiff]
  simp

/-- The chosen index type.-/
abbrev Left (σ : CoordinateSplit n) := {i : Fin n // i ∈ σ.left}

/-- The complementary index type.-/
abbrev Right (σ : CoordinateSplit n) := {i : Fin n // i ∉ σ.left}

/-- A split is **proper** when both sides are inhabited. A predicate, deliberately not a
field: the empty and full splits are legal here.-/
def IsProper (σ : CoordinateSplit n) : Prop := σ.left.Nonempty ∧ σ.right.Nonempty

/--
@isnad1 id=iff.0h2v.s5.088a7bd438ca from=translated src=- shape=6a795a2b vocab=dfcdf7be
-/
theorem isProper_iff {σ : CoordinateSplit n} :
    σ.IsProper ↔ σ.left.Nonempty ∧ ∃ i, i ∉ σ.left := by
  rw [IsProper]
  constructor
  · rintro ⟨h1, i, hi⟩
    exact ⟨h1, i, mem_right_iff.mp hi⟩
  · rintro ⟨h1, i, hi⟩
    exact ⟨h1, i, mem_right_iff.mpr hi⟩

/-! ### Restriction and gluing, for dependent carriers -/

/-- The half-tuple on the chosen coordinates.-/
def restrictLeft (σ : CoordinateSplit n) (x : ∀ i, V i) : ∀ i : σ.Left, V i.1 :=
  fun i => x i.1

/-- The half-tuple on the complementary coordinates.-/
def restrictRight (σ : CoordinateSplit n) (x : ∀ i, V i) : ∀ i : σ.Right, V i.1 :=
  fun i => x i.1

/-- Reassemble a tuple from its two halves.-/
def glue (σ : CoordinateSplit n) (xL : ∀ i : σ.Left, V i.1) (xR : ∀ i : σ.Right, V i.1) :
    ∀ i, V i :=
  fun i => if hi : i ∈ σ.left then xL ⟨i, hi⟩ else xR ⟨i, hi⟩

variable {σ : CoordinateSplit n}

/--
@isnad1 id=eq.1h6v.s7.fff04a51f0d3 from=translated src=- shape=eb99003e vocab=73609518
-/
@[simp] theorem glue_apply_left {xL : ∀ i : σ.Left, V i.1} {xR : ∀ i : σ.Right, V i.1}
    {i : Fin n} (hi : i ∈ σ.left) : σ.glue xL xR i = xL ⟨i, hi⟩ := dite_eq_left hi

/--
@isnad1 id=eq.1h6v.s7.e350604879e3 from=translated src=- shape=f840b048 vocab=73609518
-/
@[simp] theorem glue_apply_right {xL : ∀ i : σ.Left, V i.1} {xR : ∀ i : σ.Right, V i.1}
    {i : Fin n} (hi : i ∉ σ.left) : σ.glue xL xR i = xR ⟨i, hi⟩ := dite_eq_right hi

/--
@isnad1 id=eq.0h5v.s6.260ee8365383 from=translated src=- shape=24bf0ff4 vocab=77a9a533
-/
@[simp] theorem restrictLeft_glue (xL : ∀ i : σ.Left, V i.1) (xR : ∀ i : σ.Right, V i.1) :
    σ.restrictLeft (σ.glue xL xR) = xL := by
  funext i
  rw [restrictLeft, glue_apply_left i.2]

/--
@isnad1 id=eq.0h5v.s6.de16a3b7f438 from=translated src=- shape=7dadb553 vocab=f473537a
-/
@[simp] theorem restrictRight_glue (xL : ∀ i : σ.Left, V i.1) (xR : ∀ i : σ.Right, V i.1) :
    σ.restrictRight (σ.glue xL xR) = xR := by
  funext i
  rw [restrictRight, glue_apply_right i.2]

/--
@isnad1 id=eq.0h4v.s5.0acb9bbd2346 from=translated src=- shape=84b74311 vocab=cebb1a59
-/
@[simp] theorem glue_restrict (x : ∀ i, V i) :
    σ.glue (σ.restrictLeft x) (σ.restrictRight x) = x := by
  funext i
  by_cases hi : i ∈ σ.left
  · rw [glue_apply_left hi, restrictLeft]
  · rw [glue_apply_right hi, restrictRight]

/-! ### The factorization equivalence -/

/-- **Tuples factor along a split.** Computable, with both round trips proved.-/
def splitEquiv (σ : CoordinateSplit n) (V : Fin n → Type*) :
    (∀ i, V i) ≃ ((∀ i : σ.Left, V i.1) × (∀ i : σ.Right, V i.1)) where
  toFun x := (σ.restrictLeft x, σ.restrictRight x)
  invFun p := σ.glue p.1 p.2
  left_inv x := glue_restrict x
  right_inv p := Prod.ext (restrictLeft_glue p.1 p.2) (restrictRight_glue p.1 p.2)

/--
@isnad1 id=eq.0h4v.s9.25cc13e1a9e0 from=translated src=- shape=8ff3c038 vocab=a1e8218c
-/
@[simp] theorem splitEquiv_apply (x : ∀ i, V i) :
    σ.splitEquiv V x = (σ.restrictLeft x, σ.restrictRight x) := rfl

/--
@isnad1 id=eq.0h4v.s9.7559bbbfbe2f from=translated src=- shape=34477714 vocab=a6d6b3cf
-/
@[simp] theorem splitEquiv_symm_apply
    (p : (∀ i : σ.Left, V i.1) × (∀ i : σ.Right, V i.1)) :
    (σ.splitEquiv V).symm p = σ.glue p.1 p.2 := rfl

/-! ### The complementary split -/

/-- Exchanging the two sides.-/
def swap (σ : CoordinateSplit n) : CoordinateSplit n := ⟨σ.right⟩

/--
@isnad1 id=eq.0h2v.s4.2e82ea7f5017 from=translated src=- shape=d8898af0 vocab=2f35ae79
-/
@[simp] theorem swap_left (σ : CoordinateSplit n) : σ.swap.left = σ.right := rfl

/--
@isnad1 id=eq.0h2v.s3.4bf5e84c7eda from=translated src=- shape=6ddf6d3e vocab=13ec25a7
-/
@[simp] theorem swap_swap (σ : CoordinateSplit n) : σ.swap.swap = σ := by
  refine congrArg CoordinateSplit.mk ?_
  ext i
  simp [swap, right]

/-- The complementary split's chosen indices are the original's complementary indices.-/
def swapLeftEquiv (σ : CoordinateSplit n) : σ.swap.Left ≃ σ.Right where
  toFun i := ⟨i.1, mem_right_iff.mp i.2⟩
  invFun i := ⟨i.1, mem_right_iff.mpr i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- …and conversely.-/
def swapRightEquiv (σ : CoordinateSplit n) : σ.swap.Right ≃ σ.Left where
  toFun i := ⟨i.1, by
    by_contra h
    exact i.2 (mem_right_iff.mpr h)⟩
  invFun i := ⟨i.1, fun h => (mem_right_iff.mp h) i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
@isnad1 id=eq.0h3v.s6.aef88593bfd1 from=translated src=- shape=7faec61e vocab=64d688c6
-/
@[simp] theorem swapLeftEquiv_val (σ : CoordinateSplit n) (i : σ.swap.Left) :
    (σ.swapLeftEquiv i).1 = i.1 := rfl

/--
@isnad1 id=eq.0h3v.s6.cd90b6795bd6 from=translated src=- shape=69ab7002 vocab=a36c7138
-/
@[simp] theorem swapRightEquiv_val (σ : CoordinateSplit n) (i : σ.swap.Right) :
    (σ.swapRightEquiv i).1 = i.1 := rfl

/-- **Complement coherence**: gluing over the complementary split is gluing over the
original with the two halves exchanged. This is the `Prod.swap` statement, with the index
correspondence carried by the two equivalences rather than by a cast.
@isnad1 id=eq.0h5v.s8.f736ec5512e6 from=translated src=- shape=04fd275c vocab=9299484a
-/
theorem swap_glue (σ : CoordinateSplit n) (xL : ∀ i : σ.swap.Left, V i.1)
    (xR : ∀ i : σ.swap.Right, V i.1) :
    σ.swap.glue xL xR
      = σ.glue (fun i => xR ⟨i.1, fun h => (mem_right_iff.mp h) i.2⟩)
          (fun i => xL ⟨i.1, mem_right_iff.mpr i.2⟩) := by
  funext i
  by_cases hi : i ∈ σ.left
  · rw [glue_apply_left hi,
      glue_apply_right (show i ∉ σ.swap.left from fun h => (mem_right_iff.mp h) hi)]
  · rw [glue_apply_right hi,
      glue_apply_left (show i ∈ σ.swap.left from mem_right_iff.mpr hi)]

/-- **Pointwise restriction under swap**, left half. Both sides read the same coordinate of
`x`; the index correspondence is carried by `swapLeftEquiv`, not a cast. Stated pointwise so
it applies without unfolding `restrictLeft`.
@isnad1 id=eq.0h5v.s6.766abda833b5 from=translated src=- shape=ac74cb13 vocab=a78ef4fe
-/
@[simp] theorem restrictLeft_swap (σ : CoordinateSplit n) (x : ∀ i, V i) (i : σ.swap.Left) :
    σ.swap.restrictLeft x i = σ.restrictRight x (σ.swapLeftEquiv i) := rfl

/-- …and the right half.
@isnad1 id=eq.0h5v.s6.989936f41317 from=translated src=- shape=f90e649f vocab=1ee60f8d
-/
@[simp] theorem restrictRight_swap (σ : CoordinateSplit n) (x : ∀ i, V i) (i : σ.swap.Right) :
    σ.swap.restrictRight x i = σ.restrictLeft x (σ.swapRightEquiv i) := rfl

/-! ### Reindexing

The membership equation below is the canonical statement of the direction. Naturality is
stated over the **transported** carrier family `fun i => V (π i)`, which is what keeps every
public statement cast-free. -/

/-- Pull a split back along a permutation.-/
def reindex (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n)) : CoordinateSplit n :=
  ⟨σ.left.image π.symm⟩

/-- **The canonical direction statement.** Everything about `reindex` follows from this.
@isnad1 id=iff.0h4v.s6.fd823f03c31f from=translated src=- shape=74d20e06 vocab=f10ff13f
-/
@[simp] theorem mem_reindex_left {σ : CoordinateSplit n} {π : Equiv.Perm (Fin n)}
    {i : Fin n} : i ∈ (σ.reindex π).left ↔ π i ∈ σ.left := by
  rw [reindex, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rwa [Equiv.apply_symm_apply]
  · intro h
    exact ⟨π i, h, π.symm_apply_apply i⟩

/-- The index correspondence on the chosen side: `i ↦ π i`.-/
def reindexLeftEquiv (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n)) :
    (σ.reindex π).Left ≃ σ.Left where
  toFun i := ⟨π i.1, mem_reindex_left.mp i.2⟩
  invFun j := ⟨π.symm j.1, mem_reindex_left.mpr (by rw [Equiv.apply_symm_apply]; exact j.2)⟩
  left_inv i := Subtype.ext (π.symm_apply_apply i.1)
  right_inv j := Subtype.ext (π.apply_symm_apply j.1)

/-- The index correspondence on the complementary side.-/
def reindexRightEquiv (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n)) :
    (σ.reindex π).Right ≃ σ.Right where
  toFun i := ⟨π i.1, fun h => i.2 (mem_reindex_left.mpr h)⟩
  invFun j := ⟨π.symm j.1, by
    intro h
    have h' := mem_reindex_left.mp h
    rw [Equiv.apply_symm_apply] at h'
    exact j.2 h'⟩
  left_inv i := Subtype.ext (π.symm_apply_apply i.1)
  right_inv j := Subtype.ext (π.apply_symm_apply j.1)

/--
@isnad1 id=eq.0h4v.s7.b737c73fecf3 from=translated src=- shape=fe90502f vocab=513c0741
-/
@[simp] theorem reindexLeftEquiv_val (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n))
    (i : (σ.reindex π).Left) : (σ.reindexLeftEquiv π i).1 = π i.1 := rfl

/--
@isnad1 id=eq.0h4v.s7.42b48a74c1fd from=translated src=- shape=693ebb19 vocab=2565dc39
-/
@[simp] theorem reindexRightEquiv_val (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n))
    (i : (σ.reindex π).Right) : (σ.reindexRightEquiv π i).1 = π i.1 := rfl

/-- **Naturality of the chosen-side restriction.** Cast-free, because the reindexed tuple is
taken over the transported carrier family.
@isnad1 id=eq.0h5v.s7.3229b967e981 from=translated src=- shape=5728ce7c vocab=0affcd7f
-/
theorem restrictLeft_reindex (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n))
    (x : ∀ i, V i) :
    (σ.reindex π).restrictLeft (V := fun i => V (π i)) (fun i => x (π i))
      = fun i => σ.restrictLeft x (σ.reindexLeftEquiv π i) := rfl

/-- Naturality of the complementary-side restriction.
@isnad1 id=eq.0h5v.s7.51dc76f39deb from=translated src=- shape=3e77b6d8 vocab=8798a130
-/
theorem restrictRight_reindex (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n))
    (x : ∀ i, V i) :
    (σ.reindex π).restrictRight (V := fun i => V (π i)) (fun i => x (π i))
      = fun i => σ.restrictRight x (σ.reindexRightEquiv π i) := rfl

/-- Naturality of gluing: reassembling the transported halves is the transport of the
reassembled tuple.
@isnad1 id=eq.0h6v.s8.5648c7dfb364 from=translated src=- shape=65b07f08 vocab=ccf35454
-/
theorem glue_reindex (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n))
    (xL : ∀ i : σ.Left, V i.1) (xR : ∀ i : σ.Right, V i.1) :
    (σ.reindex π).glue (V := fun i => V (π i))
        (fun i => xL ⟨π i.1, mem_reindex_left.mp i.2⟩)
        (fun i => xR ⟨π i.1, fun h => i.2 (mem_reindex_left.mpr h)⟩)
      = fun i => σ.glue xL xR (π i) := by
  funext i
  by_cases hi : π i ∈ σ.left
  · rw [glue_apply_left (mem_reindex_left.mpr hi), glue_apply_left hi]
  · rw [glue_apply_right (fun h => hi (mem_reindex_left.mp h)), glue_apply_right hi]

/-! ### Split relations -/

/-- A relation on tuples, viewed as a relation between the two halves.-/
def splitRel (σ : CoordinateSplit n) (R : (∀ i, V i) → Prop) :
    (∀ i : σ.Left, V i.1) → (∀ i : σ.Right, V i.1) → Prop :=
  fun xL xR => R (σ.glue xL xR)

/--
@isnad1 id=iff.0h6v.s6.6ec62bb81691 from=translated src=- shape=d9bf08f5 vocab=6f6b9a1c
-/
@[simp] theorem splitRel_apply (R : (∀ i, V i) → Prop) (xL : ∀ i : σ.Left, V i.1)
    (xR : ∀ i : σ.Right, V i.1) : σ.splitRel R xL xR ↔ R (σ.glue xL xR) := Iff.rfl

/-- **Transport of a relation along a permutation.** The relation on transported tuples that
corresponds to `R`, obtained by moving the tuple back along Mathlib's dependent Pi
equivalence. The equivalence is what handles the dependent carrier indices explicitly.-/
def reindexRel (π : Equiv.Perm (Fin n)) (R : (∀ i, V i) → Prop) :
    (∀ i, V (π i)) → Prop :=
  fun y => R (Equiv.piCongrLeft V π y)

/--
@isnad1 id=iff.0h5v.s8.5c1feddfa328 from=translated src=- shape=5db7870f vocab=c0695a50
-/
@[simp] theorem reindexRel_apply (π : Equiv.Perm (Fin n)) (R : (∀ i, V i) → Prop)
    (y : ∀ i, V (π i)) : reindexRel π R y ↔ R (Equiv.piCongrLeft V π y) := Iff.rfl

/-- Transporting a tuple and then the relation recovers the original test.
@isnad1 id=iff.0h5v.s6.255efcb16b85 from=translated src=- shape=d0cb5988 vocab=ea5370bf
-/
theorem reindexRel_comp (π : Equiv.Perm (Fin n)) (R : (∀ i, V i) → Prop)
    (x : ∀ i, V i) : reindexRel π R (fun i => x (π i)) ↔ R x := by
  rw [reindexRel, show (fun i => x (π i)) = (Equiv.piCongrLeft V π).symm x from rfl,
    Equiv.apply_symm_apply]

/-- **Naturality of `splitRel` under reindexing.** The relation genuinely consumes the
transported tuple — `reindexRel π R` is a relation on `∀ i, V (π i)`, not a constant — so
this is a transport statement rather than a tautology.
@isnad1 id=iff.0h7v.s8.e2673016c47b from=translated src=- shape=4dfe8ce5 vocab=68d44356
-/
theorem splitRel_reindex (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n))
    (R : (∀ i, V i) → Prop) (xL : ∀ i : σ.Left, V i.1) (xR : ∀ i : σ.Right, V i.1) :
    (σ.reindex π).splitRel (V := fun i => V (π i)) (reindexRel π R)
        (fun i => xL ⟨π i.1, mem_reindex_left.mp i.2⟩)
        (fun i => xR ⟨π i.1, fun h => i.2 (mem_reindex_left.mpr h)⟩)
      ↔ σ.splitRel R xL xR := by
  rw [splitRel_apply, splitRel_apply, glue_reindex]
  exact reindexRel_comp π R (σ.glue xL xR)

/-- **Naturality of `splitRel` under swap.** Reading a relation through the complementary
split is reading it through the original with the two halves exchanged — the `Prod.swap`
statement at the level of relations, completing `swap_glue`.

Like `splitRel_reindex` this is a genuine transport rather than a tautology: the two halves
are exchanged on the right-hand side, so a relation that distinguishes its coordinates
distinguishes the two sides. The order-sensitive test below would be unprovable if the
exchange were dropped.

Explicit subtype constructors keep the dependent carrier indices syntactically aligned,
matching `swap_glue`.
@isnad1 id=iff.0h6v.s8.cd83fa98ca81 from=translated src=- shape=13936fd2 vocab=14784ca1
-/
theorem splitRel_swap (σ : CoordinateSplit n) (R : (∀ i, V i) → Prop)
    (xL : ∀ i : σ.swap.Left, V i.1) (xR : ∀ i : σ.swap.Right, V i.1) :
    -- Routing the indices through `swapLeftEquiv.symm` instead would make the carrier read
    -- `V ↑(e.symm i)` rather than `V ↑i`. The two are `rfl`-equal but not syntactically
    -- aligned, and elaborating the dependent application can reject that mismatch.
    σ.swap.splitRel R xL xR
      ↔ σ.splitRel R (fun i => xR ⟨i.1, fun h => (mem_right_iff.mp h) i.2⟩)
          (fun i => xL ⟨i.1, mem_right_iff.mpr i.2⟩) := by
  rw [splitRel_apply, splitRel_apply, swap_glue]

/-! ### Properness under the structural operations -/

/--
@isnad1 id=eq.0h2v.s4.089727498b2c from=translated src=- shape=d8898af0 vocab=2f35ae79
-/
theorem swap_right (σ : CoordinateSplit n) : σ.swap.right = σ.left := by
  ext i
  simp [swap, right]

/-- Properness is symmetric in the two sides.
@isnad1 id=iff.0h2v.s3.27f06cfc7439 from=translated src=- shape=d0788cef vocab=d709f88d
-/
theorem swap_isProper (σ : CoordinateSplit n) : σ.swap.IsProper ↔ σ.IsProper := by
  rw [IsProper, IsProper, swap_left, swap_right]
  exact and_comm

/-- Reindexing preserves properness: it permutes the coordinates without merging sides.
@isnad1 id=iff.0h3v.s4.9153bb285c43 from=translated src=- shape=054148bb vocab=3aeb0342
-/
theorem reindex_isProper (σ : CoordinateSplit n) (π : Equiv.Perm (Fin n)) :
    (σ.reindex π).IsProper ↔ σ.IsProper := by
  rw [IsProper, IsProper]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨⟨π i, mem_reindex_left.mp hi⟩,
      ⟨π j, mem_right_iff.mpr fun h => (mem_right_iff.mp hj) (mem_reindex_left.mpr h)⟩⟩
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    refine ⟨⟨π.symm i, mem_reindex_left.mpr ?_⟩, ⟨π.symm j, mem_right_iff.mpr ?_⟩⟩
    · rwa [Equiv.apply_symm_apply]
    · intro h
      have := mem_reindex_left.mp h
      rw [Equiv.apply_symm_apply] at this
      exact (mem_right_iff.mp hj) this

/-! ### One versus rest -/

/-- The split isolating a single coordinate.-/
def singleton (i : Fin n) : CoordinateSplit n := ⟨{i}⟩

/--
@isnad1 id=iff.0h3v.s5.b108b6e2519f from=translated src=- shape=86025b85 vocab=fecc34ab
-/
@[simp] theorem mem_singleton_left {i j : Fin n} : j ∈ ((singleton i : CoordinateSplit n)).left ↔ j = i := by
  rw [singleton, Finset.mem_singleton]

/-- A relation on tuples, viewed as a relation between the value at one coordinate and the
remaining tuple. The `h ▸ v` cast is the only one in this file, quarantined here and in the
evaluation lemma below.-/
def oneVsRest (R : (∀ i, V i) → Prop) (i : Fin n) :
    V i → (∀ j : {j : Fin n // j ≠ i}, V j.1) → Prop :=
  fun v rest => R fun j => if h : j = i then h ▸ v else rest ⟨j, h⟩

/-- The evaluation lemma, displaying the reconstructed tuple explicitly.
@isnad1 id=iff.0h6v.s6.78f49305beaa from=translated src=- shape=0dd90de1 vocab=b10e0bf6
-/
theorem oneVsRest_apply (R : (∀ i, V i) → Prop) (i : Fin n) (v : V i)
    (rest : ∀ j : {j : Fin n // j ≠ i}, V j.1) :
    oneVsRest R i v rest ↔ R (fun j => if h : j = i then h ▸ v else rest ⟨j, h⟩) := Iff.rfl

/-- A singleton split is proper exactly when some other coordinate exists.
@isnad1 id=iff.0h2v.s4.7edfdf9c511d from=translated src=- shape=b60a95aa vocab=9e2128e6
-/
theorem singleton_isProper (i : Fin n) : (singleton i).IsProper ↔ ∃ j, j ≠ i := by
  rw [IsProper]
  constructor
  · rintro ⟨-, j, hj⟩
    exact ⟨j, fun h => (mem_right_iff.mp hj) (mem_singleton_left.mpr h)⟩
  · rintro ⟨j, hj⟩
    exact ⟨⟨i, mem_singleton_left.mpr rfl⟩,
      ⟨j, mem_right_iff.mpr fun h => hj (mem_singleton_left.mp h)⟩⟩

/-! ### Singleton index equivalences -/

/-- The chosen side of a singleton split is a point.-/
def singletonLeftEquiv (i : Fin n) : (singleton i).Left ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := ⟨i, mem_singleton_left.mpr rfl⟩
  left_inv j := Subtype.ext (mem_singleton_left.mp j.2).symm
  right_inv _ := rfl

/--
@isnad1 id=eq.0h3v.s6.f4a013d09540 from=translated src=- shape=407fb4f5 vocab=ae2f1042
-/
@[simp] theorem singletonLeftEquiv_symm_val (i : Fin n) (u : PUnit.{1}) :
    ((singletonLeftEquiv i).symm u).1 = i := rfl

/-- The complementary side of a singleton split is the other coordinates. Cast-free: the
underlying value is unchanged.-/
def singletonRightEquiv (i : Fin n) : (singleton i).Right ≃ {j : Fin n // j ≠ i} where
  toFun j := ⟨j.1, fun h => j.2 (mem_singleton_left.mpr h)⟩
  invFun j := ⟨j.1, fun h => j.2 (mem_singleton_left.mp h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
@isnad1 id=eq.0h3v.s7.46a03a7319be from=translated src=- shape=032b885c vocab=f29c2250
-/
@[simp] theorem singletonRightEquiv_val (i : Fin n) (j : (singleton i).Right) :
    (singletonRightEquiv i j).1 = j.1 := rfl

/--
@isnad1 id=eq.0h3v.s7.12a8a8b7cd72 from=translated src=- shape=85a90049 vocab=bbf56744
-/
@[simp] theorem singletonRightEquiv_symm_val (i : Fin n) (j : {j : Fin n // j ≠ i}) :
    ((singletonRightEquiv i).symm j).1 = j.1 := rfl

/-! ### Injectivity across a split

Only meaningful for a constant carrier, where `Function.Injective` typechecks. -/

/-- **Injectivity of a glued tuple.** The cross-range disjointness clause is load-bearing:
individually injective halves do **not** give an injective glued tuple.
@isnad1 id=iff.0h5v.s6.835c8c9832a2 from=translated src=- shape=d4587856 vocab=a3f7bded
-/
theorem glue_injective_iff {α : Type*} (σ : CoordinateSplit n) (xL : σ.Left → α)
    (xR : σ.Right → α) :
    Function.Injective (σ.glue (V := fun _ => α) xL xR) ↔
      Function.Injective xL ∧ Function.Injective xR ∧
        Disjoint (Set.range xL) (Set.range xR) := by
  constructor
  · intro h
    refine ⟨fun a b hab => ?_, fun a b hab => ?_, ?_⟩
    · refine Subtype.ext (h ?_)
      rw [glue_apply_left a.2, glue_apply_left b.2]
      simpa using hab
    · refine Subtype.ext (h ?_)
      rw [glue_apply_right a.2, glue_apply_right b.2]
      simpa using hab
    · rw [Set.disjoint_left]
      rintro c ⟨a, rfl⟩ ⟨b, hb⟩
      have hval : σ.glue (V := fun _ => α) xL xR a.1 = σ.glue (V := fun _ => α) xL xR b.1 := by
        rw [glue_apply_left a.2, glue_apply_right b.2]
        simpa using hb.symm
      exact b.2 (h hval ▸ a.2)
  · rintro ⟨hL, hR, hd⟩ i j hij
    by_cases hi : i ∈ σ.left <;> by_cases hj : j ∈ σ.left
    · rw [glue_apply_left hi, glue_apply_left hj] at hij
      exact congrArg Subtype.val (hL hij)
    · rw [glue_apply_left hi, glue_apply_right hj] at hij
      exact absurd (Set.disjoint_left.mp hd ⟨⟨i, hi⟩, rfl⟩ ⟨⟨j, hj⟩, hij.symm⟩) not_false
    · rw [glue_apply_right hi, glue_apply_left hj] at hij
      exact absurd (Set.disjoint_left.mp hd ⟨⟨j, hj⟩, rfl⟩ ⟨⟨i, hi⟩, hij⟩) not_false
    · rw [glue_apply_right hi, glue_apply_right hj] at hij
      exact congrArg Subtype.val (hR hij)

/-- The complementary index type as the coercion of the complementary finset.-/
def rightEquiv (σ : CoordinateSplit n) : σ.Right ≃ {i : Fin n // i ∈ σ.right} where
  toFun i := ⟨i.1, mem_right_iff.mpr i.2⟩
  invFun i := ⟨i.1, mem_right_iff.mp i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Box factorization -/

/-- **`piFinset` factors along a split**, in cardinality. The identity the weighted-box layer
consumes.
@isnad1 id=eq.0h4v.s8.389cfb6fbfdf from=translated src=- shape=d59e0e5e vocab=e4b8aac5
-/
theorem card_piFinset_split [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (σ : CoordinateSplit n) (A : ∀ i, Finset (V i)) :
    (Fintype.piFinset A).card
      = (Fintype.piFinset fun i : σ.Left => A i.1).card
        * (Fintype.piFinset fun i : σ.Right => A i.1).card := by
  classical
  rw [Fintype.card_piFinset, Fintype.card_piFinset, Fintype.card_piFinset]
  have hL : (∏ i : σ.Left, (A i.1).card) = ∏ i ∈ σ.left, (A i).card :=
    Finset.prod_coe_sort σ.left (fun i => (A i).card)
  have hR : (∏ i : σ.Right, (A i.1).card) = ∏ i ∈ σ.right, (A i).card := by
    rw [← Finset.prod_coe_sort σ.right (fun i => (A i).card)]
    exact Fintype.prod_equiv σ.rightEquiv _ _ (fun _ => rfl)
  have hsplit : (∏ i, (A i).card)
      = (∏ i ∈ σ.left, (A i).card) * (∏ i ∈ σ.right, (A i).card) := by
    rw [right, ← Finset.prod_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  rw [hsplit, hL, hR]

end CoordinateSplit

/-! ### Tests and adversarial examples -/

section Tests

open CoordinateSplit

/-- A genuinely dependent carrier family.-/
private def W : Fin 3 → Type := ![Fin 2, Fin 3, Bool]

-- **Empty and full splits are legal** — the whole point of `IsProper` being a predicate.

end Tests

end RegularityLemmata
