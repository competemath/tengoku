/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov
-/
module

public import Tengoku.Seed.Algebra.Polynomial.Roots

public import Tengoku.Arklib.ArkLib.Data.Domain.CosetFftDomain.Ops
public import Tengoku.Arklib.ArkLib.Data.Domain.FftDomain.Ops

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! This module provides a definition of a block of a
  coset FFT domain (definition 4.16 from [ACFY24]).

## Main definitions

- `block`: A block of a coset FFT domain at a point `x`.
- `blockIdx`: The indices of the elements of a block of
  a coset FFT domain at a point `x`.

## Main results

- `card_block_le`: The cardinality bound of a block.
- `card_blockIdx`: The cardinality of `block` and `blockIdx` coincide.

## References

  * [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
      with Super-Fast Verification*][ACFY24]
-/

@[expose] public section

namespace Domain

variable {ι : Type} [Fintype ι] [AddCommGroup ι]
variable {F : Type} [Field F] [DecidableEq F]

namespace CosetFftDomainClass

variable {n : ℕ}
variable {D : Type} [FunLike D ι F] [CosetFftDomainClass D ι F]
variable {ω : D} {k : ℕ} {x y : F}

open Finset Polynomial

/-- The `2^k`th roots of `x` from the domain `ω`.

  This is the definition 4.16 from [ACFY24].
  Note, we do not require `x` to be from a subdomain.-/
def block (ω : D) (k : ℕ) (x : F) : Finset F :=
  {y ∈ toFinset ω | y ^ 2 ^ k = x}

/-- An equivalent definition of the membership to a block.
@isnad1 id=iff.0h7v.s6.424d5e00f173 from=translated src=- shape=0b350d8a vocab=01d9d3de
-/
@[simp]
lemma mem_block :
    y ∈ block ω k x ↔ y ∈ ω ∧ y ^ 2 ^ k = x := by simp [block]

/--
@isnad1 id=eq.0h5v.s6.b926779373de from=translated src=- shape=219351ec vocab=b33834c3
-/
@[simp]
lemma block_k_0 :
    block ω 0 x = if x ∈ ω then {x} else ∅ := by aesop

section Smooth

variable {n : ℕ}
variable {D : Type} [FunLike D (Fin (2 ^ n)) F] [CosetFftDomainClass D (Fin (2 ^ n)) F]
variable {ω : D} {k : ℕ} {x y : F}

/--
@isnad1 id=mem.2h7v.s8.afe455578b67 from=translated src=- shape=1347c9a4 vocab=f7ddd7c4
-/
lemma neg_mem_block_of_mem [NeZero k] (hy : y ∈ block ω k x) (hk : k ≤ n) :
    -y ∈ block ω k x := by
  aesop
    (add unsafe cases Nat)
    (add simp [Nat.even_pow])

/--
@isnad1 id=iff.1h7v.s8.e79589cdea2e from=translated src=- shape=1183e86f vocab=f7ddd7c4
-/
lemma neg_mem_block_iff_mem [NeZero k] (hk : k ≤ n) :
    -y ∈ block ω k x ↔ y ∈ block ω k x := by
  aesop
    (add unsafe cases Nat)
    (add simp [Nat.even_pow])

end Smooth

/-- An alternative definition of `block` in terms of
  `Polynomial.nthRootsFinset`.
@isnad1 id=eq.0h6v.s6.0a8d497925ab from=translated src=- shape=c2d6fe42 vocab=3a9d2ce2
-/
lemma block_eq_nthRootsFinset :
    block ω k x = nthRootsFinset (2 ^ k) x ∩ toFinset ω := by aesop

/-- The cardinality of a block does not exceed its degree.
@isnad1 id=le.0h6v.s6.e0a40445f4ca from=translated src=- shape=8d10eac6 vocab=e6d0e9ed
-/
@[simp]
lemma card_block_le :
    (block ω k x).card ≤ 2 ^ k := by
  rw [block_eq_nthRootsFinset]
  exact le_trans (card_le_card inter_subset_left) <| by
    simp only [nthRootsFinset, Multiset.toFinset, card_mk]
    exact le_trans
      (@Multiset.toFinset_card_le F (Classical.decEq F) _)
      (card_nthRoots _ _)

/-- Blocks corresponding to different points are disjoint.
@isnad1 id=disjoint.1h7v.s6.bf1139588a71 from=translated src=- shape=5e815c67 vocab=8307f476
-/
theorem disjoint_block {x y : F} (hxy : x ≠ y) :
    Disjoint (block ω k x) (block ω k y) := by aesop (add simp [disjoint_iff])

/--
@isnad1 id=pairwise.0h6v.s5.5998397d4b9b from=translated src=- shape=375716da vocab=405111fb
-/
@[simp]
theorem pairwise_disjoint_block {s : Set F} :
    s.PairwiseDisjoint (block ω k) := fun _ _ _ _ _ ↦ by
  aesop (add simp [Function.onFun, disjoint_block])

/-- The set of indices of a block of `ω` at `x` of the degree `k`.-/
def blockIdx (ω : D) (k : ℕ) (x : F) : Finset ι :=
  {i | ω i ^ 2 ^ k = x}

omit [AddCommGroup ι] [CosetFftDomainClass D ι F] in
/-- The definition of membership to a `blockIdx`.
@isnad1 id=iff.0h7v.s6.5df187a4084f from=translated src=- shape=751c9d35 vocab=d4b67a5a
-/
lemma mem_blockIdx {i : ι} :
    i ∈ blockIdx ω k x ↔ ω i ^ 2 ^ k = x := by simp [blockIdx]

omit [AddCommGroup ι] [CosetFftDomainClass D ι F] in
/--
@isnad1 id=mem.0h6v.s6.17df6d6a4161 from=translated src=- shape=e2a85414 vocab=d4b67a5a
-/
@[simp]
lemma mem_blockIdx_self {i : ι} :
    i ∈ blockIdx ω k (ω i ^ 2 ^ k) := by simp [blockIdx]

/--
@isnad1 id=iff.0h7v.s6.6b6fbfcd0243 from=translated src=- shape=9db5b0d5 vocab=49c82865
-/
lemma mem_blockIdx_iff_mem_block {i : ι} :
    i ∈ blockIdx ω k x ↔ ω i ∈ block ω k x := by simp [blockIdx]

/-- There are no roots of `0` in any domain.
@isnad1 id=eq.0h5v.s6.20bc78ac7ea8 from=translated src=- shape=49c7de0b vocab=d6ff3650
-/
@[simp]
lemma blockIdx_x_0 :
    blockIdx ω k 0 = ∅ := by aesop (add simp [mem_blockIdx_iff_mem_block])

/--
@isnad1 id=eq.1h6v.s6.159873587e79 from=translated src=- shape=a0546143 vocab=cf8f5536
-/
lemma blockIdx_k_0_of_eq {i : ι} (hi : ω i = x) :
    blockIdx ω 0 x = {i} := by
  ext j
  have := CosetFftDomainClass.injective ω (a₁ := i) (a₂ := j)
  aesop (add simp [mem_blockIdx_iff_mem_block])

/--
@isnad1 id=eq.1h5v.s6.c58451ae5856 from=translated src=- shape=07fa810d vocab=5b434628
-/
lemma blockIdx_k_0_of_ne_mem (hx : x ∉ ω) :
    blockIdx ω 0 x = ∅ := by aesop (add simp [mem_blockIdx_iff_mem_block])

/-- `blockIdx` is the preimage of `block`.
@isnad1 id=eq.0h6v.s6.6d7053c59090 from=translated src=- shape=e544ad41 vocab=9e636453
-/
lemma blockIdx_eq_preimage_block :
    blockIdx ω k x =
    preimage
      (block ω k x) ω
      (CosetFftDomainClass.injective ω).injOn := by
  ext i
  rw [mem_blockIdx_iff_mem_block]
  exact Finset.mem_preimage.symm

/-- The cardinality of `blockIdx` is that of `block`.
@isnad1 id=eq.0h6v.s6.f66eb170e9b1 from=translated src=- shape=aa95ebcb vocab=c25cbda3
-/
@[simp]
lemma card_blockIdx :
    (blockIdx ω k x).card = (block ω k x).card := by
  rw [blockIdx_eq_preimage_block, Finset.card_preimage]
  congr 1
  ext y
  simp only [Finset.mem_filter]
  constructor
  · exact And.left
  · intro hy
    refine ⟨hy, ?_⟩
    rw [mem_block] at hy
    rw [CosetFftDomainClass.mem_def] at hy
    exact hy.1

/-- The sets of indices of blocks corresponding to different points are disjoint.
@isnad1 id=disjoint.1h7v.s6.a0bf5656ec30 from=translated src=- shape=53614889 vocab=a31a063e
-/
theorem disjoint_blockIdx {x y : F} (hxy : x ≠ y) :
    Disjoint (blockIdx ω k x) (blockIdx ω k y) := by
  aesop (add simp [disjoint_iff_ne, mem_blockIdx_iff_mem_block])

/--
@isnad1 id=pairwise.0h6v.s5.6faa247d7674 from=translated src=- shape=224f71c5 vocab=f513f1ef
-/
@[simp]
theorem pairwise_disjoint_blockIdx {s : Set F} :
    s.PairwiseDisjoint (blockIdx ω k) := fun _ _ _ _ _ ↦ by
  aesop (add simp [Function.onFun, disjoint_blockIdx])

end CosetFftDomainClass

end Domain
