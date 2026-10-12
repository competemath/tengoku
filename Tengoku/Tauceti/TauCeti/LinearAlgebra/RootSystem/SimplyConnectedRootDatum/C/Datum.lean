/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.C.Model

/-!
# The simply connected root datum of type `Cₙ`

This file constructs, uniformly in the rank `n`, the pinned integral root datum of type `Cₙ` on the
character and cocharacter lattices `Fin n → ℤ`. The character lattice is written in the
fundamental-weight basis and the cocharacter lattice in the simple-coroot basis, so the `i`-th
simple root is the `i`-th row of the Bourbaki-numbered Cartan matrix `CartanMatrix.C n` and the
`i`-th simple coroot is the `i`-th standard basis vector. The coordinates themselves, and the
action of a reflection on the signed classical basis vectors `± e_a` out of which every root of
type `Cₙ` is a sum of two, are `TauCeti.DynkinType.TypeC` in the imported model file.

## The roots and their enumeration

A root index `(a, b, s) : Fin n × Fin n × Bool` denotes the pair of signed basis vectors
`p = (a, s)` and `q = (b, s)` with the sign of `q` flipped exactly when `a < b`; equivalently the
root is `(-1) ^ s * (e_a + e_b)` when `b ≤ a`, including the long root when `b = a`, and
`(-1) ^ s * (e_a - e_b)` when `a < b`. Every root arises from exactly one index, and `typeCMk` names
the index belonging to a given pair, which is how the reflected pair is turned back into an index.
`typeCIndexEquiv` encodes a root index as an index of the datum, and `root_typeCIndexEquiv_of_lt`
and its companions read off the root and the coroot there.

The roots are enumerated by `Fin (2 * n ^ 2)` by the first index `a` fastest, so that the first `n`
indices are the simple roots `α₀, …, α_{n-1}` in Bourbaki order, as `root_typeCSimpleIndex`
records. The `b` of the `a`-th simple root is the Bourbaki successor `min (a + 1) (n - 1)`, which is
`a + 1` except at the last node, where the simple root is the long root `2 e_{n-1}`; `Equiv.swap`
moves that successor to the first slot of the enumeration.

Only the coroots are asked to span their lattice, and only that half is recorded, in
`corootSpan_typeCSimplyConnectedRootDatum_eq_top`. The roots span the root lattice, which sits
inside the weight lattice with index `2` whenever `0 < n` (Bourbaki, Plate III; at `n = 0` both
lattices are trivial and the index is `1`), so the datum is a `RootDatum` carrying no
`RootPairing.IsRootSystem` instance. That asymmetry is what "simply connected" means here.

## Main definitions

* `TauCeti.DynkinType.typeCSimplyConnectedRootDatum`: the pinned root datum of type `Cₙ`.
* `TauCeti.DynkinType.TypeCIndex` and `TauCeti.DynkinType.typeCIndexEquiv`: the root index
  `(a, b, s)` and its pinned encoding as an index of the datum.
* `TauCeti.DynkinType.typeCSimpleIndex`: the first `n` root indices, the Bourbaki-numbered simple
  roots.
* `TauCeti.DynkinType.typeCSimplyConnectedBase`: the base they form.

## Main results

* `TauCeti.DynkinType.root_typeCIndexEquiv_of_lt` and its four companions: which classical vector
  the root and the coroot of the datum at an encoded index are.
* `TauCeti.DynkinType.root_typeCSimpleIndex` and `TauCeti.DynkinType.coroot_typeCSimpleIndex`: the
  `i`-th simple root is the `i`-th row of `CartanMatrix.C n` and the `i`-th simple coroot is
  `Pi.single i 1`, which is what pins the two lattices as the weight and coroot lattices.
* `TauCeti.DynkinType.mem_support_typeCSimplyConnectedBase`: the support of the pinned base is the
  set of the first `n` root indices.
* `TauCeti.DynkinType.hasCartanType_typeCSimplyConnectedRootDatum`: the pinned base has Cartan type
  `C n`.
* `TauCeti.DynkinType.corootSpan_typeCSimplyConnectedRootDatum_eq_top`: the coroots span the
  cocharacter lattice, the simply connected condition.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate III, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section
12.1. This is the `Cₙ` branch of the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

public section

namespace TauCeti

open Function Set Submodule

namespace DynkinType

open TypeC

variable {n : ℕ}

/-! ## The root index type -/

/-- A root index `(a, b, s)` of type `Cₙ`: it denotes the pair of signed basis vectors `(a, s)` and
`(b, s)`, the sign of the second being flipped exactly when `a < b`. Thus the root is
`(-1) ^ s * (e_a + e_b)` when `b ≤ a`, including the long root `(-1) ^ s * 2 e_a` when `b = a`, and
`(-1) ^ s * (e_a - e_b)` when `a < b`. -/
abbrev TypeCIndex (n : ℕ) := Fin n × Fin n × Bool

/-- The first signed basis vector of a root index. -/
private def typeCFst (i : TypeCIndex n) : Signed n := (i.1, i.2.2)

/-- The second signed basis vector of a root index. -/
private def typeCSnd (i : TypeCIndex n) : Signed n :=
  (i.2.1, if i.1 < i.2.1 then !i.2.2 else i.2.2)

private lemma typeCPair_injective :
    Injective (fun i : TypeCIndex n => (typeCFst i, typeCSnd i)) := by
  rintro ⟨a, b, s⟩ ⟨a', b', s'⟩ h
  simp only [typeCFst, typeCSnd, Prod.mk.injEq] at h
  obtain ⟨⟨ha, hs⟩, hb, -⟩ := h
  simp [ha, hb, hs]

private lemma typeCSnd_ne_signedNeg_typeCFst (i : TypeCIndex n) :
    typeCSnd i ≠ signedNeg (typeCFst i) := by
  obtain ⟨a, b, s⟩ := i
  intro hc
  simp only [typeCSnd, typeCFst, signedNeg_mk, Prod.mk.injEq] at hc
  obtain ⟨hba, hs⟩ := hc
  subst hba
  simp at hs

/-- Reading a root index back off its pair of signed basis vectors: the two are exchanged exactly
when the pair is presented in the other order. -/
private lemma typeCPair_swap_eq {i j : TypeCIndex n} (h1 : typeCFst i = typeCSnd j)
    (h2 : typeCSnd i = typeCFst j) : i = j := by
  obtain ⟨a, b, s⟩ := i
  obtain ⟨a', b', s'⟩ := j
  simp only [typeCFst, typeCSnd, Prod.mk.injEq] at h1 h2
  obtain ⟨ha, hs⟩ := h1
  obtain ⟨hb, hs'⟩ := h2
  subst ha
  subst hb
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [ite_eq_left hab] at hs'
    rw [ite_eq_right (not_lt.mpr hab.le)] at hs
    subst hs
    exact absurd hs' (by simp)
  · subst hab
    rw [ite_eq_right (lt_irrefl a)] at hs hs'
    rw [hs]
  · rw [ite_eq_right (not_lt.mpr hab.le)] at hs'
    rw [ite_eq_left hab] at hs
    subst hs'
    exact absurd hs (by simp)

/-- The root of a root index, in fundamental-weight coordinates. -/
private def typeCRoot (i : TypeCIndex n) : Fin n → ℤ := pairRoot (typeCFst i) (typeCSnd i)

/-- The coroot of a root index, in simple-coroot coordinates. -/
private def typeCCoroot (i : TypeCIndex n) : Fin n → ℤ := pairCoroot (typeCFst i) (typeCSnd i)

private lemma typeCRoot_dotProduct_typeCCoroot_self (i : TypeCIndex n) :
    typeCRoot i ⬝ᵥ typeCCoroot i = 2 :=
  pairRoot_dotProduct_pairCoroot_self (typeCSnd_ne_signedNeg_typeCFst i)

/-- The index of the root `x + y`, for a pair of signed basis vectors that are not opposite. -/
private def typeCMk (x y : Signed n) : TypeCIndex n :=
  if x.2 = y.2 then (max x.1 y.1, min x.1 y.1, x.2)
  else if x.1 < y.1 then (x.1, y.1, x.2) else (y.1, x.1, y.2)

private lemma typeCMk_pair {x y : Signed n} (h : y ≠ signedNeg x) :
    (typeCFst (typeCMk x y) = x ∧ typeCSnd (typeCMk x y) = y) ∨
      (typeCFst (typeCMk x y) = y ∧ typeCSnd (typeCMk x y) = x) := by
  obtain ⟨a, s⟩ := x
  obtain ⟨b, t⟩ := y
  by_cases hst : s = t
  · subst hst
    rcases le_or_gt a b with hab | hab
    · have hmk : typeCMk (a, s) (b, s) = (b, a, s) := by
        rw [typeCMk, ite_eq_left rfl, max_eq_right hab, min_eq_left hab]
      refine Or.inr ⟨by rw [hmk]; rfl, ?_⟩
      rw [hmk, typeCSnd, ite_eq_right (not_lt.mpr hab)]
    · have hmk : typeCMk (a, s) (b, s) = (a, b, s) := by
        rw [typeCMk, ite_eq_left rfl, max_eq_left hab.le, min_eq_right hab.le]
      refine Or.inl ⟨by rw [hmk]; rfl, ?_⟩
      rw [hmk, typeCSnd, ite_eq_right (not_lt.mpr hab.le)]
  · have ht : t = !s := by cases s <;> cases t <;> simp_all
    subst ht
    rcases lt_trichotomy a b with hab | hab | hab
    · have hmk : typeCMk (a, s) (b, !s) = (a, b, s) := by
        rw [typeCMk, ite_eq_right hst, ite_eq_left hab]
      refine Or.inl ⟨by rw [hmk]; rfl, ?_⟩
      rw [hmk, typeCSnd, ite_eq_left hab]
    · refine absurd ?_ h
      simp [hab]
    · have hmk : typeCMk (a, s) (b, !s) = (b, a, !s) := by
        rw [typeCMk, ite_eq_right hst, ite_eq_right (not_lt.mpr hab.le)]
      refine Or.inr ⟨by rw [hmk]; rfl, ?_⟩
      rw [hmk, typeCSnd, ite_eq_left hab, Bool.not_not]

private lemma typeCRoot_typeCMk {x y : Signed n} (h : y ≠ signedNeg x) :
    typeCRoot (typeCMk x y) = pairRoot x y := by
  rcases typeCMk_pair h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [typeCRoot, h1, h2]
  exact pairRoot_comm y x

/-! ## Injectivity of the roots and of the coroots -/

private lemma typeCRoot_injective : Injective (typeCRoot (n := n)) := by
  intro i j hij
  have hi := typeCSnd_ne_signedNeg_typeCFst i
  have hj := typeCSnd_ne_signedNeg_typeCFst j
  have hmem : ∀ z, (z = typeCFst i ∨ z = typeCSnd i) ↔ (z = typeCFst j ∨ z = typeCSnd j) := by
    intro z
    rw [← one_le_pairRoot_dotProduct_iff hi z, ← one_le_pairRoot_dotProduct_iff hj z]
    exact Iff.of_eq (congrArg _ (congrArg (· ⬝ᵥ signedCoweight z) hij))
  rcases Set.pair_eq_pair_iff.mp (Set.ext fun z => by simpa using hmem z) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact typeCPair_injective (Prod.ext h1 h2)
  · exact typeCPair_swap_eq h1 h2

/-! ## The reflection on root indices -/

/-- Reflection in the root indexed by `i`, acting on root indices. -/
private def typeCReflectionIdx (i j : TypeCIndex n) : TypeCIndex n :=
  typeCMk (signedReflection (typeCFst i) (typeCSnd i) (typeCFst j))
    (signedReflection (typeCFst i) (typeCSnd i) (typeCSnd j))

private lemma typeCReflectionIdx_pair_ne (i j : TypeCIndex n) :
    signedReflection (typeCFst i) (typeCSnd i) (typeCSnd j) ≠
      signedNeg (signedReflection (typeCFst i) (typeCSnd i) (typeCFst j)) := by
  intro hc
  rw [← signedReflection_signedNeg (typeCSnd_ne_signedNeg_typeCFst i)] at hc
  exact typeCSnd_ne_signedNeg_typeCFst j
    (signedReflection_injective (typeCSnd_ne_signedNeg_typeCFst i) hc)

private lemma typeCRoot_typeCReflectionIdx (i j : TypeCIndex n) :
    typeCRoot j - (typeCRoot j ⬝ᵥ typeCCoroot i) • typeCRoot i
      = typeCRoot (typeCReflectionIdx i j) := by
  rw [typeCReflectionIdx, typeCRoot_typeCMk (typeCReflectionIdx_pair_ne i j)]
  exact pairRoot_reflection (typeCSnd_ne_signedNeg_typeCFst i) (typeCFst j) (typeCSnd j)

private lemma typeCReflectionIdx_involutive (i : TypeCIndex n) :
    Involutive (typeCReflectionIdx i) := by
  intro j
  refine typeCRoot_injective ?_
  rw [← typeCRoot_typeCReflectionIdx, ← typeCRoot_typeCReflectionIdx]
  -- In these coordinates `Module.preReflection` in the `i`-th root is definitionally the map
  -- `v ↦ v - (v ⬝ᵥ typeCCoroot i) • typeCRoot i`, which is the goal left by the two rewrites.
  exact Module.involutive_preReflection (x := typeCRoot i)
    (f := (dotProductBilin ℤ ℤ).flip (typeCCoroot i))
    (typeCRoot_dotProduct_typeCCoroot_self i) (typeCRoot j)

/-- Reflection in the root indexed by `i`, as a permutation of the root indices. -/
private def typeCReflectionPerm (i : TypeCIndex n) : TypeCIndex n ≃ TypeCIndex n :=
  (typeCReflectionIdx_involutive i).toPerm _

@[simp] private lemma typeCReflectionPerm_apply (i j : TypeCIndex n) :
    typeCReflectionPerm i j = typeCReflectionIdx i j := rfl

/-! ## The Bourbaki enumeration of the roots -/

/-- The zero index of `Fin n`, available once a root index is in hand. -/
private def typeCZero (a : Fin n) : Fin n := ⟨0, by have := a.isLt; omega⟩

/-- The Bourbaki successor of a node: the next node, except at the last node, which is its own
successor because its simple root is the long root `2 e_{n-1}`. -/
private def typeCSucc (a : Fin n) : Fin n := ⟨min ((a : ℕ) + 1) (n - 1), by have := a.isLt; omega⟩

/-- The enumeration of the root indices by the first index fastest, with the second index twisted so
that the `a`-th simple root comes first. -/
private def typeCShapeEquiv (n : ℕ) : TypeCIndex n ≃ (Bool × Fin n) × Fin n where
  toFun i := ((i.2.2, Equiv.swap (typeCZero i.1) (typeCSucc i.1) i.2.1), i.1)
  invFun p := (p.2, Equiv.swap (typeCZero p.2) (typeCSucc p.2) p.1.2, p.1.1)
  left_inv i := by simp
  right_inv p := by simp

/-- The pinned enumeration of the roots of type `Cₙ` by `Fin (2 * n ^ 2)`. -/
def typeCIndexEquiv (n : ℕ) : TypeCIndex n ≃ Fin (2 * n ^ 2) :=
  ((typeCShapeEquiv n).trans
      (((finTwoEquiv.symm.prodCongr (Equiv.refl (Fin n))).trans finProdFinEquiv).prodCongr
        (Equiv.refl (Fin n)))).trans (finProdFinEquiv.trans (finCongr (by ring)))

/-! ## The root and the coroot at an arbitrary index

Away from the simple indices, a root of the datum is named by encoding a root index with
`typeCIndexEquiv`, and the five lemmas below say which vector the encoded index denotes. Together
they cover every index, since `typeCIndexEquiv` is a bijection. -/

/-! ## The simple roots and coroots -/

/-- There is room for the first `n` indices in the type `Cₙ` enumeration of `2 * n ^ 2` roots. -/
private lemma typeC_le_two_mul_sq (n : ℕ) : n ≤ 2 * n ^ 2 :=
  le_trans (Nat.le_self_pow (by norm_num) n) (Nat.le_mul_of_pos_left (n ^ 2) (by norm_num))

/-- The `i`-th simple root of type `Cₙ` sits at root index `i`, the Bourbaki node `i + 1`. -/
def typeCSimpleIndex (n : ℕ) (i : Fin n) : Fin (2 * n ^ 2) :=
  Fin.castLE (typeC_le_two_mul_sq n) i

@[simp] lemma typeCSimpleIndex_val (i : Fin n) : (typeCSimpleIndex n i : ℕ) = i := by
  simp [typeCSimpleIndex]

lemma typeCSimpleIndex_injective : Injective (typeCSimpleIndex n) :=
  Fin.castLE_injective (typeC_le_two_mul_sq n)

/-- The `i`-th simple root of type `Cₙ`, in fundamental-weight coordinates. -/
private def typeCSimpleRoot (i : Fin n) : Fin n → ℤ := typeCRoot (i, typeCSucc i, false)

/-- The `i`-th simple coroot of type `Cₙ`, in simple-coroot coordinates. -/
private def typeCSimpleCoroot (i : Fin n) : Fin n → ℤ := typeCCoroot (i, typeCSucc i, false)

/-! ## The pinned base -/

/-- The cumulative classical coweight: the sum of `coweight n b` over `b ≤ j`. For `j < n` this is
the simple-coroot coordinate vector of `e₀ + ⋯ + e_j`; out-of-range coweights vanish, so the value
is constant once `j` reaches `n - 1`.

This mirrors `TauCeti.DynkinType.typeBDualVec` in `B/Datum.lean`, from which the construction and
the independence argument below are adapted; the two are distinct because `TypeB.coweight` and
`TypeC.coweight` are different functions. -/
private def typeCDualVec (n j : ℕ) : Fin n → ℤ := ∑ b ∈ Finset.range (j + 1), coweight n b

/-- The support of the pinned base of type `Cₙ`: the first `n` root indices. -/
private def typeCSimpleSupport (n : ℕ) : Finset (Fin (2 * n ^ 2)) :=
  simpleSupport (typeCSimpleIndex_injective (n := n))

end DynkinType

end TauCeti
