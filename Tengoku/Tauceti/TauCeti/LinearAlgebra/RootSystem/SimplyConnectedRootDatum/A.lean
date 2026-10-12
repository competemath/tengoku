/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Data.Fin.Basic
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.Positive
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.Swap

/-!
# The simply connected root datum of type `Aₙ`

This file constructs, uniformly in the rank `n`, the pinned integral root datum of type `Aₙ` on the
character and cocharacter lattices `Fin n → ℤ`. The character lattice is written in the
fundamental-weight basis and the cocharacter lattice in the simple-coroot basis, so the `i`-th
simple root is the `i`-th row of the Bourbaki-numbered Cartan matrix `CartanMatrix.A n` and the
`i`-th simple coroot is the `i`-th standard basis vector.

## The coordinates

Write `e₀, …, e_n` for the standard basis of the classical model `ℤ ^ (n + 1)`, in which the roots
of type `Aₙ` are the `n * (n + 1)` vectors `e_a - e_b` with `a ≠ b` and the simple roots are
`αᵢ = eᵢ - eᵢ₊₁`. Everything below is the image of that model in the two pinned lattices: a vector
of the character lattice is recorded by its pairings against the simple coroots, and a vector of the
cocharacter lattice by its coordinates in the simple coroots. Although `e_a` itself does not lie in
the coroot lattice, choose a coordinate potential for it so that differences represent coroots:

```text
typeAWeight n a   = (⟨e_a, αₖ^∨⟩)ₖ           = ([a = k] - [a = k + 1])ₖ,
typeACoweight n a = (chosen potential at αₖ^∨)ₖ   = ([a ≤ k])ₖ.
```

For `a ≤ b`, the difference of the chosen potentials has the simple-coroot coordinates of
`e_a - e_b = ∑ a ≤ k < b, αₖ^∨`. The root `e_a - e_b` and its coroot are the corresponding
differences, and the whole construction is a finite calculation with these two families;
`typeAWeight_dotProduct_typeACoweight` is the one identity it rests on.

The roots are indexed by `Fin (n * (n + 1))`, the ordered pairs `(a, b)` of distinct elements of
`Fin (n + 1)` being enumerated by the difference `b - a ≠ 0` first and the source `a` second. The
first `n` indices are therefore the simple roots `α₀, …, α_{n-1}` in Bourbaki order, as
`root_typeASimpleIndex` records.

Only the coroots are asked to span their lattice, and only that half is recorded, in
`corootSpan_typeASimplyConnectedRootDatum_eq_top`. The roots span the root lattice, which sits
inside the weight lattice with index `n + 1` (Bourbaki, Plate I), so the datum is a `RootDatum`
carrying no `RootPairing.IsRootSystem` instance. That asymmetry is what "simply connected" means
here.

## The graph automorphism

The `Aₙ` diagram is a chain, so reversing it is a symmetry, and the last part of this file realizes
that symmetry on the pinned datum itself rather than only on the Cartan matrix. On the classical
model the realization is `e_a ↦ -e_{rev a}`, whose effect on a root is

```text
e_a - e_b ↦ e_{rev b} - e_{rev a},
```

and on both pinned lattices, whose coordinates are indexed by the simple nodes, it is the reversal
of coordinates. So a single linear automorphism of `Fin n → ℤ` serves as both the character and the
cocharacter map, and `TauCeti.DynkinType.typeAGraphAut` bundles it with the induced permutation of
the `n * (n + 1)` root indices as an element of `RootPairing.Aut`. It restricts to the reversal
`Fin.revPerm` on the Bourbaki-numbered simple roots, which is `TauCeti.graphPermA n`, the
permutation that
`TauCeti/LinearAlgebra/RootSystem/DiagramPermutations.lean` pins for the `²Aₙ` family; that module
is deliberately not imported here, since only the `Fin`-level reversal is used.

The sign in `e_a ↦ -e_{rev a}` is forced: `e_a ↦ e_{rev a}` sends `αᵢ = e_i - e_{i+1}` to
`e_{rev i} - e_{rev (i + 1)} = -α_{rev i}`, a negative root, so it does not preserve the base. The
composite with the opposition `-1` is the automorphism below. This is unrelated to
`TauCeti.opposition`, which is built from the longest Weyl element and needs the root-system
hypotheses this simply connected datum does not carry.

## Main definitions

* `TauCeti.DynkinType.typeASimplyConnectedRootDatum`: the pinned root datum of type `Aₙ`.
* `TauCeti.DynkinType.TypeAIndex` and `TauCeti.DynkinType.typeAIndexEquiv`: the ordered pairs
  `(a, b)` of distinct classical indices, and their pinned enumeration as root indices.
* `TauCeti.DynkinType.typeASimpleIndex`: the first `n` root indices, the Bourbaki-numbered simple
  roots.
* `TauCeti.DynkinType.typeASimplyConnectedBase`: the base they form.
* `TauCeti.DynkinType.typeAGraphAut`: the graph automorphism of the pinned datum.

## Main results

* `TauCeti.DynkinType.root_typeAIndexEquiv`, `TauCeti.DynkinType.coroot_typeAIndexEquiv`,
  `TauCeti.DynkinType.pairing_typeAIndexEquiv` and
  `TauCeti.DynkinType.typeAIndexEquiv_symm_reflectionPerm`: the root and coroot `e_a - e_b` in
  coordinates, the Cartan integers, and the reflections as transpositions, all read on ordered
  pairs.
* `TauCeti.DynkinType.root_typeASimpleIndex` and
  `TauCeti.DynkinType.coroot_typeASimpleIndex`: the `i`-th simple root is the `i`-th row of
  `CartanMatrix.A n` and the `i`-th simple coroot is `Pi.single i 1`, which is what pins the two
  lattices as the weight and coroot lattices.
* `TauCeti.DynkinType.hasCartanType_typeASimplyConnectedRootDatum`: the pinned base has Cartan type
  `A n`.
* `TauCeti.DynkinType.corootSpan_typeASimplyConnectedRootDatum_eq_top`: the coroots span the
  cocharacter lattice, the simply connected condition.
* `TauCeti.DynkinType.ncard_posRoots_typeASimplyConnectedRootDatum`: the number of positive roots
  is `(n + 1).choose 2`, for any base.
* `TauCeti.DynkinType.weightMap_typeAGraphAut_apply` and
  `TauCeti.DynkinType.coweightMap_typeAGraphAut_apply`: the graph automorphism reverses the
  coordinates of both lattices.
* `TauCeti.DynkinType.indexEquiv_typeAGraphAut_typeASimpleIndex`: on the Bourbaki-numbered simple
  roots it is the chain reversal.
* `TauCeti.DynkinType.typeAGraphAut_sq` and `TauCeti.DynkinType.typeAGraphAut_ne_one`: it is an
  involution, and is nontrivial as soon as the chain has two nodes.
* `TauCeti.DynkinType.support_map_typeASimplyConnectedBase_typeAGraphAut`: it preserves the pinned
  base.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate I, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section
12.1. This is the `Aₙ` branch of the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The positive-root count is the
corresponding clause of the `Aₙ` worked example in the "Worked examples (acceptance criteria)"
section of that README; it agrees with the count in Bourbaki, Plate I.

The graph automorphism is the root-datum input to the isomorphism theorem for pinned groups in
Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, whose consumer is the graph-twisted
Steinberg map of milestone L1 of `TauCetiRoadmap/CFSGStatement/README.md`. The description of the
type-`A` diagram automorphism as `X ↦ -J Xᵀ J` on `sl_{n+1}`, of which the map below is the
root-datum shadow, is in R. W. Carter, *Simple Groups of Lie Type*, §12.2.
-/

public section

namespace TauCeti

open Function Set Submodule

namespace DynkinType

variable {n : ℕ}

/-! ## The two coordinate families -/

/-- The character-lattice coordinates of the classical basis vector `e_a` of type `Aₙ`: its
pairings `⟨e_a, αₖ^∨⟩ = [a = k] - [a = k + 1]` against the simple coroots. -/
private def typeAWeight (n a : ℕ) : Fin n → ℤ :=
  fun k => (if a = (k : ℕ) then 1 else 0) - (if a = (k : ℕ) + 1 then 1 else 0)

/-- A chosen simple-coroot-coordinate potential for the classical basis vector `e_a` of type `Aₙ`.
Although `e_a` itself does not lie in the coroot lattice, the differences of these potentials give
the coordinates of `e_a - e_b`; the `k`-th potential is `[a ≤ k]`. -/
private def typeACoweight (n a : ℕ) : Fin n → ℤ :=
  fun k => if a ≤ (k : ℕ) then 1 else 0

/-! ## The roots and coroots indexed by ordered pairs -/

/-- The ordered pairs of distinct elements of `Fin (n + 1)`, indexing the roots `e_a - e_b` of type
`Aₙ` before they are enumerated by `Fin (n * (n + 1))`. -/
abbrev TypeAIndex (n : ℕ) := {p : Fin (n + 1) × Fin (n + 1) // p.1 ≠ p.2}

/-- The root `e_a - e_b` in fundamental-weight coordinates. -/
private def typeAPairRoot (p : TypeAIndex n) : Fin n → ℤ :=
  typeAWeight n (p.val.1 : ℕ) - typeAWeight n (p.val.2 : ℕ)

/-- The coroot `(e_a - e_b)^∨ = e_a - e_b` in simple-coroot coordinates. -/
private def typeAPairCoroot (p : TypeAIndex n) : Fin n → ℤ :=
  typeACoweight n (p.val.1 : ℕ) - typeACoweight n (p.val.2 : ℕ)

/-- Reflection in the root indexed by `p`, as the transposition of the two entries of `p` acting on
ordered pairs. -/
private def typeAPairReflection (p : TypeAIndex n) : TypeAIndex n ≃ TypeAIndex n :=
  Equiv.subtypeEquiv ((Equiv.swap p.val.1 p.val.2).prodCongr (Equiv.swap p.val.1 p.val.2))
    (fun q => by simp)

/-! ## The Bourbaki enumeration of the roots -/

private lemma one_le_val_sub (p : TypeAIndex n) : 1 ≤ ((p.val.2 - p.val.1 : Fin (n + 1)) : ℕ) := by
  have h : (p.val.2 - p.val.1 : Fin (n + 1)) ≠ 0 := fun h => p.2 (sub_eq_zero.mp h).symm
  have : ((p.val.2 - p.val.1 : Fin (n + 1)) : ℕ) ≠ 0 := by
    simpa [Fin.val_eq_zero_iff] using h
  omega

/-- The nonzero difference `b - a` of an ordered pair of distinct elements, shifted down to an
index of `Fin n`. -/
private def typeADiff (p : TypeAIndex n) : Fin n :=
  ⟨((p.val.2 - p.val.1 : Fin (n + 1)) : ℕ) - 1, by
    have h1 := one_le_val_sub p
    have h2 : ((p.val.2 - p.val.1 : Fin (n + 1)) : ℕ) < n + 1 := Fin.isLt _
    omega⟩

private lemma typeADiff_val (p : TypeAIndex n) :
    (typeADiff p : ℕ) = ((p.val.2 - p.val.1 : Fin (n + 1)) : ℕ) - 1 := rfl

/-- The shift of a `Fin n` index to the nonzero elements of `Fin (n + 1)`, inverse to
`TauCeti.DynkinType.typeADiff`. -/
private def typeASucc (i : Fin n) : Fin (n + 1) := ⟨(i : ℕ) + 1, by omega⟩

private lemma typeASucc_val (i : Fin n) : (typeASucc i : ℕ) = (i : ℕ) + 1 := rfl

private lemma typeASucc_ne_zero (i : Fin n) : typeASucc i ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  rw [typeASucc_val] at h'
  simp at h'

/-- The enumeration of the ordered pairs of distinct elements of `Fin (n + 1)` by the difference
`b - a ≠ 0` first and the source `a` second. Composed with `finProdFinEquiv` it puts the simple
roots at the first `n` indices. -/
private def typeAPairEquiv (n : ℕ) : TypeAIndex n ≃ Fin n × Fin (n + 1) where
  toFun p := (typeADiff p, p.val.1)
  invFun q := ⟨(q.2, q.2 + typeASucc q.1), by
    intro h
    refine typeASucc_ne_zero q.1 ?_
    have h0 : q.2 + 0 = q.2 + typeASucc q.1 := by simpa using h
    exact (add_left_cancel h0).symm⟩
  left_inv p := by
    have h1 := one_le_val_sub p
    have hx : typeASucc (typeADiff p) = p.val.2 - p.val.1 :=
      Fin.ext (by rw [typeASucc_val, typeADiff_val]; omega)
    refine Subtype.ext (Prod.ext rfl ?_)
    -- Unfold the subtype equivalence to compare its second `Fin (n + 1)` coordinate.
    change p.val.1 + typeASucc (typeADiff p) = p.val.2
    rw [hx]
    abel
  right_inv q := by
    refine Prod.ext (Fin.ext ?_) rfl
    -- Unfold the first coordinate of the product equivalence to compare its natural values.
    change ((q.2 + typeASucc q.1 - q.2 : Fin (n + 1)) : ℕ) - 1 = (q.1 : ℕ)
    rw [add_sub_cancel_left, typeASucc_val]
    omega

/-- The pinned enumeration of the roots of type `Aₙ` by `Fin (n * (n + 1))`. -/
def typeAIndexEquiv (n : ℕ) : TypeAIndex n ≃ Fin (n * (n + 1)) :=
  (typeAPairEquiv n).trans finProdFinEquiv

/-- Reflection in the root indexed by `k`, transported to the pinned enumeration. -/
private def typeAReflectionPerm (n : ℕ) (k : Fin (n * (n + 1))) :
    Fin (n * (n + 1)) ≃ Fin (n * (n + 1)) :=
  ((typeAIndexEquiv n).symm.trans
    (typeAPairReflection ((typeAIndexEquiv n).symm k))).trans (typeAIndexEquiv n)

/-- The `i`-th simple root of type `Aₙ` sits at root index `i`, the Bourbaki node `i + 1`. -/
def typeASimpleIndex (n : ℕ) (i : Fin n) : Fin (n * (n + 1)) :=
  Fin.castLE (Nat.le_mul_of_pos_right n n.succ_pos) i

@[simp] lemma typeASimpleIndex_val (i : Fin n) : (typeASimpleIndex n i : ℕ) = i := by
  simp [typeASimpleIndex]

lemma typeASimpleIndex_injective : Injective (typeASimpleIndex n) :=
  Fin.castLE_injective (Nat.le_mul_of_pos_right n n.succ_pos)

/-- The Bourbaki simple index corresponds to the consecutive pair of matrix indices. -/
@[simp] lemma typeAIndexEquiv_symm_typeASimpleIndex (i : Fin n) :
    (typeAIndexEquiv n).symm (typeASimpleIndex n i) =
      ⟨(⟨i, by omega⟩, ⟨(i : ℕ) + 1, by omega⟩), by simp [Fin.ext_iff]⟩ := by
  have hlt : (i : ℕ) < n + 1 := by omega
  have hlt' : (i : ℕ) + 1 < n + 1 := by omega
  refine Subtype.ext (Prod.ext ?_ ?_) <;>
    · apply Fin.ext
      simp [typeAIndexEquiv, typeAPairEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
        typeASimpleIndex, typeASucc_val, Nat.div_eq_of_lt hlt,
        Nat.mod_eq_of_lt hlt, Fin.add_def, Nat.mod_eq_of_lt hlt']

/-! ## The pinned base -/

/-- The support of the pinned base of type `Aₙ`: the first `n` root indices. -/
private abbrev typeASimpleSupport (n : ℕ) : Finset (Fin (n * (n + 1))) :=
  simpleSupport (typeASimpleIndex_injective (n := n))

/-! ## The graph automorphism -/

/-- The graph automorphism of type `Aₙ` read on the classical ordered pairs: it exchanges the two
entries and reverses each, `(a, b) ↦ (rev b, rev a)`. This is the effect of `e_a ↦ -e_{rev a}` on
the root `e_a - e_b`. -/
private def typeAGraphPairMap (p : TypeAIndex n) : TypeAIndex n :=
  ⟨(p.val.2.rev, p.val.1.rev), fun h => p.2 (Fin.rev_injective h).symm⟩

private lemma typeAGraphPairMap_involutive : Involutive (typeAGraphPairMap (n := n)) :=
  fun _ => Subtype.ext (Prod.ext (Fin.rev_rev _) (Fin.rev_rev _))

/-- The permutation of the pinned root indices induced by the graph automorphism. -/
private def typeAGraphIndexPerm (n : ℕ) : Equiv.Perm (Fin (n * (n + 1))) :=
  ((typeAIndexEquiv n).symm.trans (typeAGraphPairMap_involutive (n := n)).toPerm).trans
    (typeAIndexEquiv n)

/-- Reversing the coordinates of `Fin n → ℤ`, the common character- and cocharacter-lattice map of
the type `Aₙ` graph automorphism. -/
private def typeARevEquiv (n : ℕ) : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) :=
  LinearEquiv.funCongrLeft ℤ ℤ (Fin.revPerm : Equiv.Perm (Fin n))

end DynkinType

end TauCeti
