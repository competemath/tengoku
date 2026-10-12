/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.Model

/-!
# The simply connected root datum of type `Bₙ`

This file assembles the coordinate model of
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.Model` into the pinned integral root
datum of type `Bₙ`, uniformly in the rank `n`, on the character and cocharacter lattices
`Fin n → ℤ`. The character lattice is written in the fundamental-weight basis and the cocharacter
lattice in the simple-coroot basis, so the `i`-th simple root is the `i`-th row of the
Bourbaki-numbered Cartan matrix `CartanMatrix.B n` and the `i`-th simple coroot is the `i`-th
standard basis vector.

## The enumeration

The roots are indexed by `Fin (2 * n ^ 2)`, which is `TauCeti.DynkinType.numRoots (.B n)`. The
model names a root by a signed basis vector `u` together with a cyclic offset `d`, so the raw index
type is `Fin (2 * n) × Fin n`; the enumeration rotates the first coordinate and reverses the second
so that the Bourbaki simple roots come first. All but the last simple root are long and the last
one is short, so they cannot occupy a single block of a product enumeration: the rotation puts
`α₀, …, α_{n-2}` at indices `0, …, n - 2` and sends the short `α_{n-1}` elsewhere, and a single
transposition then brings that one to index `n - 1`.

Only the coroots are asked to span their lattice, and only that half is recorded, in
`TauCeti.DynkinType.corootSpan_typeBSimplyConnectedRootDatum_eq_top`. The roots span the root
lattice, which for `0 < n` sits inside the weight lattice with index `2` (Bourbaki, Plate II); at
`n = 0` both lattices are trivial and the two coincide. So the datum is a `RootDatum` carrying no
`RootPairing.IsRootSystem` instance. That asymmetry is what "simply connected" means here.

## Main definitions

* `TauCeti.DynkinType.typeBSimplyConnectedRootDatum`: the pinned root datum of type `Bₙ`.
* `TauCeti.DynkinType.typeBSimpleIndex`: the first `n` root indices, the Bourbaki-numbered simple
  roots.
* `TauCeti.DynkinType.typeBSimplyConnectedBase`: the base they form.

Nothing here is `@[expose]`d: the datum, its enumeration and its base are used through the lemmas
below, not by unfolding.

## Main results

* `TauCeti.DynkinType.root_typeBSimpleIndex` and `TauCeti.DynkinType.coroot_typeBSimpleIndex`: the
  `i`-th simple root is the `i`-th row of `CartanMatrix.B n` and the `i`-th simple coroot is
  `Pi.single i 1`, which is what pins the two lattices as the weight and coroot lattices.
* `TauCeti.DynkinType.hasCartanType_typeBSimplyConnectedRootDatum`: the pinned base has Cartan
  type `B n`.
* `TauCeti.DynkinType.corootSpan_typeBSimplyConnectedRootDatum_eq_top`: the coroots span the
  cocharacter lattice, the simply connected condition.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate II, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section
12.1. This is the `Bₙ` branch of the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

public section

namespace TauCeti.DynkinType

open Function Set Submodule TypeB

variable {n : ℕ}

/-! ## Reading off the coordinates of an explicit signed basis vector -/

/-! ## The reflection permutation on the raw index type -/

/-- The reflection in the root indexed by `z`, acting on the raw index type. -/
private def typeBReflIdx (z w : Fin (2 * n) × Fin n) : Fin (2 * n) × Fin n :=
  index (reflMap z.1 (shift z.1 z.2) w.1) (reflMap z.1 (shift z.1 z.2) (shift w.1 w.2))

private lemma typeBReflIdx_involutive (z : Fin (2 * n) × Fin n) : Involutive (typeBReflIdx z) := by
  intro w
  have hpq : IsPair z.1 (shift z.1 z.2) := isPair_shift _ _
  have hw : IsPair w.1 (shift w.1 w.2) := isPair_shift _ _
  have hRw := isPair_reflMap hpq hw
  have hinv := reflMap_involutive hpq
  simp only [typeBReflIdx]
  rcases shift_index hRw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2, h1, hinv, hinv, index_shift]
  · rw [h2, h1, hinv, hinv, ← index_comm hw, index_shift]

/-! ## The enumeration of the roots -/

/-- There is room for the first `n` indices in the type `Bₙ` enumeration of `2 * n ^ 2` roots. -/
private lemma typeB_le_two_mul_sq (n : ℕ) : n ≤ 2 * n ^ 2 :=
  le_trans (Nat.le_self_pow (by norm_num) n) (Nat.le_mul_of_pos_left (n ^ 2) (by norm_num))

private lemma typeB_lt_two_mul_sq {i : ℕ} (hi : i < n) : i < 2 * n ^ 2 :=
  lt_of_lt_of_le hi (typeB_le_two_mul_sq n)

/-- The rotation of the signed basis vectors by `n - 1` steps. Composed with the reversal of the
offsets it moves the long simple roots to the front of the enumeration. -/
private def typeBRot (n : ℕ) : Equiv.Perm (Fin (2 * n)) where
  toFun u := ⟨if (u : ℕ) + (n - 1) < 2 * n then (u : ℕ) + (n - 1) else (u : ℕ) + (n - 1) - 2 * n,
    by have := u.isLt; split <;> omega⟩
  invFun u := ⟨if (u : ℕ) + (n + 1) < 2 * n then (u : ℕ) + (n + 1) else (u : ℕ) + (n + 1) - 2 * n,
    by have := u.isLt; split <;> omega⟩
  left_inv u := by
    have := u.isLt
    refine Fin.ext ?_
    dsimp only
    split_ifs <;> omega
  right_inv u := by
    have := u.isLt
    refine Fin.ext ?_
    dsimp only
    split_ifs <;> omega

private lemma typeB_two_mul_sq (n : ℕ) : n * (2 * n) = 2 * n ^ 2 := by ring

/-- The enumeration of the roots before the final transposition: the offset indexes the block and
the rotated signed basis vector indexes the position inside it. -/
private def typeBEnum₀ (n : ℕ) : Fin (2 * n) × Fin n ≃ Fin (2 * n ^ 2) :=
  (((typeBRot n).prodCongr Fin.revPerm).trans (Equiv.prodComm _ _)).trans
    (finProdFinEquiv.trans (finCongr (typeB_two_mul_sq n)))

/-- The raw index of the short simple root `α_{n-1} = e_{n-1}`. -/
private def typeBShortPair (n : ℕ) (h : 0 < n) : Fin (2 * n) × Fin n :=
  (⟨n - 1, by omega⟩, ⟨0, h⟩)

/-- The transposition bringing the short simple root to index `n - 1`. -/
private def typeBSwapLast (n : ℕ) : Equiv.Perm (Fin (2 * n ^ 2)) :=
  if h : 0 < n then
    Equiv.swap (⟨n - 1, typeB_lt_two_mul_sq (by omega)⟩ : Fin (2 * n ^ 2))
      (typeBEnum₀ n (typeBShortPair n h))
  else Equiv.refl _

/-- The pinned enumeration of the roots of type `Bₙ` by `Fin (2 * n ^ 2)`, arranged so that the
Bourbaki simple roots occupy the first `n` indices. -/
private def typeBEnum (n : ℕ) : Fin (2 * n) × Fin n ≃ Fin (2 * n ^ 2) :=
  (typeBEnum₀ n).trans (typeBSwapLast n)

/-- The raw index of the `i`-th Bourbaki simple root: the short root `e_{n-1}` at the last node,
and the pair `{-e_{i+1}, e_i}` otherwise. -/
private def typeBSimplePair (i : Fin n) : Fin (2 * n) × Fin n :=
  if h : (i : ℕ) + 1 = n then typeBShortPair n (by have := i.isLt; omega)
  else (⟨n + (i : ℕ) + 1, by have := i.isLt; omega⟩, ⟨n - 1, by have := i.isLt; omega⟩)

/-- The `i`-th simple root of type `Bₙ` sits at root index `i`, the Bourbaki node `i + 1`. -/
def typeBSimpleIndex (n : ℕ) (i : Fin n) : Fin (2 * n ^ 2) :=
  Fin.castLE (typeB_le_two_mul_sq n) i

@[simp] lemma typeBSimpleIndex_val (i : Fin n) : (typeBSimpleIndex n i : ℕ) = i := by
  simp [typeBSimpleIndex]

lemma typeBSimpleIndex_injective : Injective (typeBSimpleIndex n) :=
  Fin.castLE_injective (typeB_le_two_mul_sq n)

/-! ## The root datum -/

/-- The reflection in the root at index `k`, transported to the enumerated index type. -/
private def typeBReflPerm (n : ℕ) (k : Fin (2 * n ^ 2)) : Equiv.Perm (Fin (2 * n ^ 2)) :=
  ((typeBEnum n).symm.trans
    (Involutive.toPerm _ (typeBReflIdx_involutive ((typeBEnum n).symm k)))).trans (typeBEnum n)

/-! ## The simple roots and coroots -/

/-! ## The pinned base -/

/-- The covector dual to the simple roots, up to the factor `2`: the simple-coroot coordinates of
`2 (e₀ + ⋯ + e_j)`. -/
private def typeBDualVec (n j : ℕ) : Fin n → ℤ := ∑ b ∈ Finset.range (j + 1), coweight n b

/-- The support of the pinned base of type `Bₙ`: the first `n` root indices. -/
private abbrev typeBSimpleSupport (n : ℕ) : Finset (Fin (2 * n ^ 2)) :=
  simpleSupport (typeBSimpleIndex_injective (n := n))

end TauCeti.DynkinType
