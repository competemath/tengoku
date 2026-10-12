/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.Internal.BorderRank

/-!
# Basic properties of tensor rank and border rank

For 3-tensors `T : Tensor3 α β γ` (see `Complexitylib.Algebraic.LinearAlgebra.Tensor.Defs`):

* **Rank.** `RankLE` is closed under sums (`RankLE.add`, `RankLE.sum`) and scalar multiples,
  is monotone in the bound (`RankLE.mono`), and every tensor over finite `α`, `β` has rank at most
  `card α * card β` (`rankLE_card_mul_card`), so `tensorRank` is attained
  (`rankLE_tensorRank`, `tensorRank_le_iff`).
* **Border rank.** Rank at most `r` implies border rank at most `r` (`RankLE.borderRankLE`);
  `BorderRankLE` is monotone, closed under sums and scalar multiples, and defines a closed set
  of tensors (`isClosed_setOf_borderRankLE`). `borderRank` is attained, and
  `borderRank T ≤ tensorRank T`.
* **Linear maps on the factors.** `map X Y Z` sends outer products to outer products
  (`map_outer`), is additive and continuous, and composes as matrices multiply (`map_map`), so
  it preserves `RankLE` and `BorderRankLE`: rank and border rank do not increase under
  `X ⊗ Y ⊗ Z` (`tensorRank_map_le`, `borderRank_map_le`). Taking `Y = Z = 1` gives restriction or projection along the first
  factor by any linear map `ℂ^α → ℂ^α'`.
* **Reindexing.** `subtensor` (deleting, permuting, or repeating slices in any factor) also
  preserves `RankLE` and `BorderRankLE`.
-/

@[expose] public section

namespace Algebraic.Tensor3

variable {α β γ α' β' γ' : Type*}

section Rank

/-- A tensor has rank at most `0` exactly when it is zero.
@isnad1 id=iff.0h4v.s6.a64f1bbac73b from=translated src=- shape=b53c68a9 vocab=4c30b893
-/
theorem rankLE_zero_iff {T : Tensor3 α β γ} : T.RankLE 0 ↔ T = 0 :=
  Internal.rankLE_zero_iff

/-- A tensor has rank at most `1` exactly when it is an outer product `u ⊗ v ⊗ w`.
@isnad1 id=iff.0h4v.s5.69c6adbc84e9 from=translated src=- shape=36f510d7 vocab=46c8da8d
-/
theorem rankLE_one_iff {T : Tensor3 α β γ} :
    T.RankLE 1 ↔ ∃ (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ), T = outer u v w :=
  Internal.rankLE_one_iff

/-- An outer product has rank at most one.
@isnad1 id=rankle.0h6v.s5.e006e66fafa5 from=translated src=- shape=fa233384 vocab=f3c45b07
-/
theorem rankLE_outer (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ) : (outer u v w).RankLE 1 :=
  rankLE_one_iff.mpr ⟨u, v, w, rfl⟩

/-- The zero tensor has rank at most `r` for every `r`.
@isnad1 id=rankle.0h4v.s5.281e123bb961 from=translated src=- shape=5645c55b vocab=4c30b893
-/
theorem zero_rankLE (r : ℕ) : (0 : Tensor3 α β γ).RankLE r :=
  Internal.zero_rankLE r

/-- Rank is subadditive.
@isnad1 id=rankle.2h7v.s6.12a9c5f5199f from=translated src=- shape=85e2a8ae vocab=f39f7572
-/
theorem RankLE.add {S T : Tensor3 α β γ} {r r' : ℕ} (hS : S.RankLE r) (hT : T.RankLE r') :
    (S + T).RankLE (r + r') :=
  Internal.rankLE_add hS hT

/-- `RankLE` is monotone in the bound.
@isnad1 id=rankle.2h6v.s5.e474622a34a5 from=translated src=- shape=b260c2fb vocab=3651e308
-/
theorem RankLE.mono {T : Tensor3 α β γ} {r r' : ℕ} (h : T.RankLE r) (hr : r ≤ r') :
    T.RankLE r' :=
  Internal.rankLE_mono h hr

/-- Rank is subadditive over finite sums.
@isnad1 id=rankle.1h7v.s6.1e0f7fd32825 from=translated src=- shape=b79718ac vocab=269efd9b
-/
theorem RankLE.sum {ι : Type*} {s : Finset ι} {T : ι → Tensor3 α β γ} {r : ι → ℕ}
    (h : ∀ x ∈ s, (T x).RankLE (r x)) : (∑ x ∈ s, T x).RankLE (∑ x ∈ s, r x) :=
  Internal.rankLE_sum s T r h

/-- Scalar multiples do not increase rank.
@isnad1 id=rankle.1h6v.s6.32eec0adf890 from=translated src=- shape=120de925 vocab=a87857af
-/
theorem RankLE.smul {T : Tensor3 α β γ} {r : ℕ} (c : ℂ) (h : T.RankLE r) : (c • T).RankLE r :=
  Internal.rankLE_smul c h

/-- Every tensor over finite `α` and `β` is a sum of `card α * card β` outer products.
@isnad1 id=rankle.0h4v.s5.bac5c48bb08c from=translated src=- shape=9a6d70a7 vocab=7a7db7bb
-/
theorem rankLE_card_mul_card [Fintype α] [Fintype β] (T : Tensor3 α β γ) :
    T.RankLE (Fintype.card α * Fintype.card β) :=
  Internal.rankLE_card_mul_card T

/-- The tensor rank is attained.
@isnad1 id=rankle.0h4v.s4.15f43ef13ff0 from=translated src=- shape=a80fa297 vocab=8ff60834
-/
theorem rankLE_tensorRank [Fintype α] [Fintype β] (T : Tensor3 α β γ) :
    T.RankLE T.tensorRank :=
  Internal.rankLE_tensorRank T

/-- `tensorRank T ≤ r` exactly when `T` is a sum of `r` outer products.
@isnad1 id=iff.0h5v.s5.daaac22c7d9e from=translated src=- shape=5c73c7f7 vocab=2d68a4b7
-/
theorem tensorRank_le_iff [Fintype α] [Fintype β] {T : Tensor3 α β γ} {r : ℕ} :
    T.tensorRank ≤ r ↔ T.RankLE r :=
  Internal.tensorRank_le_iff

/-- Tensor rank is subadditive.
@isnad1 id=le.0h5v.s6.50951e85e0e3 from=translated src=- shape=59bf21f3 vocab=82bcfd9c
-/
theorem tensorRank_add_le [Fintype α] [Fintype β] (S T : Tensor3 α β γ) :
    (S + T).tensorRank ≤ S.tensorRank + T.tensorRank :=
  tensorRank_le_iff.mpr ((rankLE_tensorRank S).add (rankLE_tensorRank T))

end Rank

section Border

/-- Rank at most `r` implies border rank at most `r`.
@isnad1 id=borderra.1h5v.s4.6d3c612ad9fe from=translated src=- shape=85466547 vocab=b9fafa64
-/
theorem RankLE.borderRankLE {T : Tensor3 α β γ} {r : ℕ} (h : T.RankLE r) : T.BorderRankLE r :=
  Internal.borderRankLE_of_rankLE h

/-- `BorderRankLE` is monotone in the bound.
@isnad1 id=borderra.2h6v.s5.d02fa77d57ca from=translated src=- shape=b260c2fb vocab=2756e1c0
-/
theorem BorderRankLE.mono {T : Tensor3 α β γ} {r r' : ℕ} (h : T.BorderRankLE r)
    (hr : r ≤ r') : T.BorderRankLE r' :=
  Internal.borderRankLE_mono h hr

/-- The tensors of border rank at most `r` form a closed set.
@isnad1 id=isclosed.0h4v.s6.162d37e5c259 from=translated src=- shape=42344d13 vocab=2f021e05
-/
theorem isClosed_setOf_borderRankLE (r : ℕ) : IsClosed {T : Tensor3 α β γ | T.BorderRankLE r} :=
  Internal.isClosed_setOf_borderRankLE r

/-- Border rank is subadditive.
@isnad1 id=borderra.2h7v.s6.d6e84beffe34 from=translated src=- shape=85e2a8ae vocab=c75f05b0
-/
theorem BorderRankLE.add {S T : Tensor3 α β γ} {r r' : ℕ} (hS : S.BorderRankLE r)
    (hT : T.BorderRankLE r') : (S + T).BorderRankLE (r + r') :=
  Internal.borderRankLE_add hS hT

/-- Scalar multiples do not increase border rank.
@isnad1 id=borderra.1h6v.s6.cdfefd7983d2 from=translated src=- shape=120de925 vocab=048906ff
-/
theorem BorderRankLE.smul {T : Tensor3 α β γ} {r : ℕ} (c : ℂ) (h : T.BorderRankLE r) :
    (c • T).BorderRankLE r :=
  Internal.borderRankLE_smul c h

/-- A tensor has border rank at most `0` exactly when it is zero.
@isnad1 id=iff.0h4v.s6.0461629b7935 from=translated src=- shape=b53c68a9 vocab=a5cd1bfb
-/
theorem borderRankLE_zero_iff {T : Tensor3 α β γ} : T.BorderRankLE 0 ↔ T = 0 :=
  Internal.borderRankLE_zero_iff

/-- The border rank is attained.
@isnad1 id=borderra.0h4v.s4.ad9cc6d0832d from=translated src=- shape=a80fa297 vocab=4ae7c25f
-/
theorem borderRankLE_borderRank [Fintype α] [Fintype β] (T : Tensor3 α β γ) :
    T.BorderRankLE T.borderRank :=
  Internal.borderRankLE_borderRank T

/-- `borderRank T ≤ r` exactly when `T` is a limit of tensors of rank at most `r`.
@isnad1 id=iff.0h5v.s5.d07f09803613 from=translated src=- shape=5c73c7f7 vocab=ee71a0ae
-/
theorem borderRank_le_iff [Fintype α] [Fintype β] {T : Tensor3 α β γ} {r : ℕ} :
    T.borderRank ≤ r ↔ T.BorderRankLE r :=
  Internal.borderRank_le_iff

/-- Border rank is at most rank.
@isnad1 id=le.0h4v.s4.549fe4f4dada from=translated src=- shape=f75f5bd5 vocab=6ea0a6c2
-/
theorem borderRank_le_tensorRank [Fintype α] [Fintype β] (T : Tensor3 α β γ) :
    T.borderRank ≤ T.tensorRank :=
  borderRank_le_iff.mpr (rankLE_tensorRank T).borderRankLE

/-- Border rank is subadditive.
@isnad1 id=le.0h5v.s6.41a165ed28ed from=translated src=- shape=59bf21f3 vocab=dcffbfb3
-/
theorem borderRank_add_le [Fintype α] [Fintype β] (S T : Tensor3 α β γ) :
    (S + T).borderRank ≤ S.borderRank + T.borderRank :=
  borderRank_le_iff.mpr ((borderRankLE_borderRank S).add (borderRankLE_borderRank T))

end Border

section Map

variable [Fintype α] [Fintype β] [Fintype γ]
variable (X : Matrix α' α ℂ) (Y : Matrix β' β ℂ) (Z : Matrix γ' γ ℂ)

/-- `X ⊗ Y ⊗ Z` sends `u ⊗ v ⊗ w` to `Xu ⊗ Yv ⊗ Zw`.
@isnad1 id=eq.0h12v.s6.77f2a8e12d7d from=translated src=- shape=61817620 vocab=9e34eacc
-/
theorem map_outer (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ) :
    map X Y Z (outer u v w) = outer (X.mulVec u) (Y.mulVec v) (Z.mulVec w) :=
  Internal.map_outer X Y Z u v w

/--
@isnad1 id=eq.0h11v.s7.5b1faa4b9f44 from=translated src=- shape=30bd6ec8 vocab=e5fe8d95
-/
theorem map_add (S T : Tensor3 α β γ) : map X Y Z (S + T) = map X Y Z S + map X Y Z T :=
  Internal.map_add X Y Z S T

/--
@isnad1 id=eq.0h9v.s7.ecc3d9cb807a from=translated src=- shape=fb6cc8b6 vocab=d252fa56
-/
theorem map_zero : map X Y Z (0 : Tensor3 α β γ) = 0 :=
  Internal.map_zero X Y Z

/--
@isnad1 id=eq.0h11v.s7.53defc133f52 from=translated src=- shape=07c82d87 vocab=c87ba023
-/
theorem map_smul (c : ℂ) (T : Tensor3 α β γ) : map X Y Z (c • T) = c • map X Y Z T :=
  Internal.map_smul X Y Z c T

/--
@isnad1 id=eq.0h12v.s7.c1f77803412c from=translated src=- shape=27808d64 vocab=ad6f3228
-/
theorem map_sum {ι : Type*} (s : Finset ι) (T : ι → Tensor3 α β γ) :
    map X Y Z (∑ x ∈ s, T x) = ∑ x ∈ s, map X Y Z (T x) :=
  Internal.map_finset_sum X Y Z s T

/--
@isnad1 id=continuo.0h9v.s7.9efed2ad4c14 from=translated src=- shape=025dd94e vocab=910cc145
-/
theorem continuous_map : Continuous (map X Y Z : Tensor3 α β γ → Tensor3 α' β' γ') :=
  Internal.continuous_map X Y Z

/-- Diagonal matrices scale the coordinates.
@isnad1 id=eq.0h7v.s6.ab8caebd7b83 from=translated src=- shape=a3cd78e2 vocab=deda420f
-/
theorem map_diagonal [DecidableEq α] [DecidableEq β] [DecidableEq γ] (a : α → ℂ) (b : β → ℂ)
    (c : γ → ℂ) (T : Tensor3 α β γ) :
    map (Matrix.diagonal a) (Matrix.diagonal b) (Matrix.diagonal c) T =
      fun i j k => a i * b j * c k * T i j k :=
  Internal.map_diagonal a b c T

/-- The identity maps fix every tensor.
@isnad1 id=eq.0h4v.s6.2c9801af96fc from=translated src=- shape=60f5f7bb vocab=226a6f7c
-/
theorem map_one [DecidableEq α] [DecidableEq β] [DecidableEq γ] (T : Tensor3 α β γ) :
    map 1 1 1 T = T :=
  Internal.map_one T

/-- Applying `X ⊗ Y ⊗ Z` and then `X' ⊗ Y' ⊗ Z'` is applying `X'X ⊗ Y'Y ⊗ Z'Z`.
@isnad1 id=eq.0h16v.s7.ce84845d88ea from=translated src=- shape=635c3104 vocab=b69a12be
-/
theorem map_map [Fintype α'] [Fintype β'] [Fintype γ'] {α'' β'' γ'' : Type*}
    (X' : Matrix α'' α' ℂ) (Y' : Matrix β'' β' ℂ) (Z' : Matrix γ'' γ' ℂ) (T : Tensor3 α β γ) :
    map X' Y' Z' (map X Y Z T) = map (X' * X) (Y' * Y) (Z' * Z) T :=
  Internal.map_map X Y Z X' Y' Z' T

/-- Linear maps on the factors do not increase rank.
@isnad1 id=rankle.1h11v.s6.cfcecc467bb1 from=translated src=- shape=04fe5370 vocab=03f3e26e
-/
theorem RankLE.map {T : Tensor3 α β γ} {r : ℕ} (h : T.RankLE r) : (map X Y Z T).RankLE r :=
  Internal.rankLE_map X Y Z h

/-- Linear maps on the factors do not increase border rank.
@isnad1 id=borderra.1h11v.s6.07af0750c9bf from=translated src=- shape=04fe5370 vocab=fc9cd2a2
-/
theorem BorderRankLE.map {T : Tensor3 α β γ} {r : ℕ} (h : T.BorderRankLE r) :
    (map X Y Z T).BorderRankLE r :=
  Internal.borderRankLE_map X Y Z h

/-- Linear maps on the factors do not increase tensor rank.
@isnad1 id=le.0h10v.s6.59c6cc70bec2 from=translated src=- shape=5f72f1e6 vocab=d16b07d5
-/
theorem tensorRank_map_le [Fintype α'] [Fintype β'] (T : Tensor3 α β γ) :
    (map X Y Z T).tensorRank ≤ T.tensorRank :=
  tensorRank_le_iff.mpr ((rankLE_tensorRank T).map X Y Z)

/-- Linear maps on the factors do not increase border rank.
@isnad1 id=le.0h10v.s6.425e1d5585e2 from=translated src=- shape=5f72f1e6 vocab=97f331b6
-/
theorem borderRank_map_le [Fintype α'] [Fintype β'] (T : Tensor3 α β γ) :
    (map X Y Z T).borderRank ≤ T.borderRank :=
  borderRank_le_iff.mpr ((borderRankLE_borderRank T).map X Y Z)

end Map

section Subtensor

variable (f : α' → α) (g : β' → β) (h : γ' → γ)

/--
@isnad1 id=eq.0h12v.s6.4868bae85415 from=translated src=- shape=7a91ac4b vocab=3d07179c
-/
theorem subtensor_outer (u : α → ℂ) (v : β → ℂ) (w : γ → ℂ) :
    (outer u v w).subtensor f g h = outer (u ∘ f) (v ∘ g) (w ∘ h) :=
  Internal.subtensor_outer f g h u v w

/--
@isnad1 id=continuo.0h9v.s7.8d9a4f9c3009 from=translated src=- shape=36d2d4db vocab=2ab82cc6
-/
theorem continuous_subtensor : Continuous fun T : Tensor3 α β γ => T.subtensor f g h :=
  Internal.continuous_subtensor f g h

/-- Reindexing does not increase rank.
@isnad1 id=rankle.1h11v.s5.ddc19618feb6 from=translated src=- shape=c2388ba8 vocab=4c82d9a3
-/
theorem RankLE.subtensor {T : Tensor3 α β γ} {r : ℕ} (hT : T.RankLE r) :
    (T.subtensor f g h).RankLE r :=
  Internal.rankLE_subtensor f g h hT

/-- Reindexing, in particular deleting or permuting slices, does not increase border rank.
@isnad1 id=borderra.1h11v.s5.4d22d589e1e5 from=translated src=- shape=c2388ba8 vocab=b128e296
-/
theorem BorderRankLE.subtensor {T : Tensor3 α β γ} {r : ℕ} (hT : T.BorderRankLE r) :
    (T.subtensor f g h).BorderRankLE r :=
  Internal.borderRankLE_subtensor f g h hT

/-- Reindexing does not increase tensor rank.
@isnad1 id=le.0h10v.s6.facc3700ac91 from=translated src=- shape=419414c0 vocab=85b0829c
-/
theorem tensorRank_subtensor_le [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    (T : Tensor3 α β γ) : (T.subtensor f g h).tensorRank ≤ T.tensorRank :=
  tensorRank_le_iff.mpr ((rankLE_tensorRank T).subtensor f g h)

/-- Reindexing, in particular deleting or permuting slices, does not increase border rank.
@isnad1 id=le.0h10v.s6.cfa8adab913a from=translated src=- shape=419414c0 vocab=53a09207
-/
theorem borderRank_subtensor_le [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    (T : Tensor3 α β γ) : (T.subtensor f g h).borderRank ≤ T.borderRank :=
  borderRank_le_iff.mpr ((borderRankLE_borderRank T).subtensor f g h)

end Subtensor

end Algebraic.Tensor3
