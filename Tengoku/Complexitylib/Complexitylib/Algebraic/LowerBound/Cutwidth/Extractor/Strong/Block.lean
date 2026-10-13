/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Internal
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Internal.Two

/-!
# Structural laws for finite block sources

A block source satisfies a mass cap for each coordinate after fixing every
earlier coordinate. The caps survive taking prefixes, weakening the entropy
threshold, and mixing sources with normalized nonnegative weights. Zero
blocks impose only normalization; one block gives the usual point-mass cap.
For two blocks the definition is equivalent to the marginal and conditional
caps established by the separate Splitting module. A source with `t` blocks
and threshold `K` satisfies `(K^t)*p x ≤ 1` at every tuple. Using the alphabet
cardinality as the threshold forces the entire tuple to be uniform.

These are finite structural ingredients for the block-source arguments in
Chattopadhyay--Goodman--Liao, Section 5 of *Affine Extractors for Almost
Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/>.
`Block.Condenser` uses these laws to condense all blocks with a shared seed.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Taking all coordinates leaves a tuple unchanged.
@isnad1 id=eq.0h3v.s4.84dc84390117 from=translated src=- shape=ec940ae2 vocab=fc44f270
-/
theorem blockPrefix_self {α : Type*} {t : Nat} (x : Fin t → α) :
    blockPrefix (Nat.le_refl t) x = x :=
  Internal.blockPrefix_self x

/-- Successive restrictions agree with a direct prefix restriction.
@isnad1 id=eq.2h5v.s5.1912a2587f0f from=translated src=- shape=026b6528 vocab=098d7bac
-/
theorem blockPrefix_comp {α : Type*} {i j t : Nat} (hij : i ≤ j) (hjt : j ≤ t)
    (x : Fin t → α) :
    blockPrefix hij (blockPrefix hjt x) = blockPrefix (hij.trans hjt) x :=
  Internal.blockPrefix_comp hij hjt x

/-- The full prefix retains each original point weight.
@isnad1 id=eq.0h3v.s4.85d5172f6d3e from=translated src=- shape=ba35a903 vocab=42d1f796
-/
theorem blockPrefixWeight_self {α : Type*} [Fintype α] {t : Nat}
    (p : (Fin t → α) → ℝ) : blockPrefixWeight p (Nat.le_refl t) = p :=
  Internal.blockPrefixWeight_self p

/-- The unique empty prefix has the source's total mass.
@isnad1 id=eq.1h4v.s6.3ea8035d8e47 from=translated src=- shape=d0a568b2 vocab=56b24436
-/
theorem blockPrefixWeight_zero {α : Type*} [Fintype α] {t : Nat}
    (p : (Fin t → α) → ℝ) (h : 0 ≤ t) (u : Fin 0 → α) :
    blockPrefixWeight p h u = ∑ x, p x :=
  Internal.blockPrefixWeight_zero p h u

/-- Marginalizing a prefix again agrees with marginalizing the original source.
@isnad1 id=eq.2h5v.s5.3d4729c52096 from=translated src=- shape=69ec70fe vocab=78f617f2
-/
theorem blockPrefixWeight_prefix {α : Type*} [Fintype α] {i j t : Nat}
    (p : (Fin t → α) → ℝ) (hij : i ≤ j) (hjt : j ≤ t) :
    blockPrefixWeight (blockPrefixWeight p hjt) hij =
      blockPrefixWeight p (hij.trans hjt) :=
  Internal.blockPrefixWeight_prefix p hij hjt

/-- Prefix weights commute with arbitrary finite linear combinations.
@isnad1 id=eq.1h7v.s6.ce3c12ad7141 from=translated src=- shape=298973ed vocab=f0dec453
-/
theorem blockPrefixWeight_mixture {α ι : Type*} [Fintype α] [Fintype ι] {i t : Nat}
    (p : ι → (Fin t → α) → ℝ) (w : ι → ℝ) (h : i ≤ t) (u : Fin i → α) :
    blockPrefixWeight (fun x => ∑ j, w j * p j x) h u =
      ∑ j, w j * blockPrefixWeight (p j) h u :=
  Internal.blockPrefixWeight_mixture p w h u

/-- A block source is a normalized nonnegative weighting.
@isnad1 id=isprobab.1h4v.s5.dab1a1417ad8 from=translated src=- shape=cab8fa17 vocab=ac4044cc
-/
theorem IsBlockSource.probability {α : Type*} [Fintype α] {t K : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K) : IsProbabilityWeight p :=
  source.1

/-- Every one-block prefix extension obeys the conditional mass cap.
@isnad1 id=le.1h6v.s6.bcb3df4c2bea from=translated src=- shape=c82406d5 vocab=fa0f47fd
-/
theorem IsBlockSource.cap {α : Type*} [Fintype α] {t K : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K)
    (i : Fin t) (u : Fin (i.val + 1) → α) :
    (K : ℝ) * blockPrefixWeight p (Nat.succ_le_of_lt i.isLt) u ≤
      blockPrefixWeight p (Nat.le_of_lt i.isLt) (blockPrefix (Nat.le_succ i.val) u) :=
  source.2 i u

/-- With no blocks, there are no conditional caps to check.
@isnad1 id=iff.0h3v.s6.33fc4edadea0 from=translated src=- shape=5db6864d vocab=ac4044cc
-/
theorem isBlockSource_zero_iff {α : Type*} [Fintype α]
    (p : (Fin 0 → α) → ℝ) (K : Nat) :
    IsBlockSource p K ↔ IsProbabilityWeight p :=
  Internal.blockSource_zero_iff p K

/-- A single block is a probability source with the ordinary point-mass cap.
@isnad1 id=iff.0h3v.s6.a7ce95e8f04c from=translated src=- shape=6beb9767 vocab=7f2a4552
-/
theorem isBlockSource_one_iff {α : Type*} [Fintype α]
    (p : (Fin 1 → α) → ℝ) (K : Nat) :
    IsBlockSource p K ↔ IsProbabilityWeight p ∧ CappedWeight p K :=
  Internal.blockSource_one_iff p K

/-- Pair weights form a two-block source exactly when the first marginal
and every second-coordinate conditional satisfy the same threshold.
@isnad1 id=iff.0h3v.s6.6a929b2bfac0 from=translated src=- shape=6a83e367 vocab=7a43b3f7
-/
theorem isBlockSource_two_iff {α : Type*} [Fintype α] (p : α × α → ℝ) (K : Nat) :
    IsBlockSource (fun x : Fin 2 → α => p (x 0, x 1)) K ↔
      IsProbabilityWeight p ∧ CappedWeight (firstWeight p) K ∧
        ∀ a b, (K : ℝ) * p (a, b) ≤ firstWeight p a :=
  Internal.blockSource_two_iff p K

/-- A smaller threshold weakens every conditional cap.
@isnad1 id=isblocks.2h5v.s5.b902f5b51ea0 from=translated src=- shape=1f6453f9 vocab=9bf9526b
-/
theorem IsBlockSource.mono {α : Type*} [Fintype α] {t K L : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K) (threshold : L ≤ K) :
    IsBlockSource p L :=
  Internal.blockSource_mono source threshold

/-- Every initial sequence of blocks retains the block-source threshold.
@isnad1 id=isblocks.2h5v.s5.78fce6c97482 from=translated src=- shape=ea9e4968 vocab=ad94dfba
-/
theorem IsBlockSource.prefix {α : Type*} [Fintype α] {j t K : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K) (h : j ≤ t) :
    IsBlockSource (blockPrefixWeight p h) K :=
  Internal.blockSource_prefix source h

/-- Conditional caps multiply to give the full tuple a threshold of `K^t`.
@isnad1 id=cappedwe.1h4v.s5.16788a437303 from=translated src=- shape=b6db724a vocab=6e418d2d
-/
theorem IsBlockSource.capped {α : Type*} [Fintype α] {t K : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p K) : CappedWeight p (K ^ t) :=
  Internal.blockSource_capped source

/-- Full conditional entropy in every block forces the full tuple to be uniform. -/
theorem IsBlockSource.eq_uniform {α : Type*} [Fintype α] {t : Nat}
    {p : (Fin t → α) → ℝ} (source : IsBlockSource p (Fintype.card α)) :
    p = uniformWeight (Fin t → α) :=
  Internal.blockSource_eq_uniform source

/-- Normalized nonnegative mixtures preserve all conditional prefix caps.
@isnad1 id=isblocks.2h6v.s6.9ca5fe77331b from=translated src=- shape=e419ca95 vocab=b1ed1988
-/
theorem IsBlockSource.mixture {α ι : Type*} [Fintype α] [Fintype ι] {t K : Nat}
    (p : ι → (Fin t → α) → ℝ) (w : ι → ℝ) (weights : IsProbabilityWeight w)
    (sources : ∀ j, IsBlockSource (p j) K) :
    IsBlockSource (fun x => ∑ j, w j * p j x) K :=
  Internal.blockSource_mixture p w weights sources

end Algebraic.Cutwidth.Extractor
