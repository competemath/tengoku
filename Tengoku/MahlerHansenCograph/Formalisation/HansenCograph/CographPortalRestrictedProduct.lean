/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.CographPortalFlags

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite restricted-product chain shuffles

This module is a geometry-free counting interface for the restricted-product
step in the portal-vector argument.  The arguments `a` and `b` are supplied
numbers of compatible component-chain choices; no claim here identifies them
with chains in a particular face lattice.
-/

open scoped BigOperators

namespace HansenCograph

/-- A pair of component portal ranks is compatible with parent rank `s`.-/
def PortalRankCompatible (s k l : ℕ) : Prop := k + l = s

instance portalRankCompatibleDecidable (s k l : ℕ) :
    Decidable (PortalRankCompatible s k l) := by
  unfold PortalRankCompatible
  infer_instance

/--
@isnad1 id=iff.0h3v.s4.1cd3eb89dbdc from=translated src=- shape=396687f5 vocab=0b693c2c
-/
theorem portalRankCompatible_iff (s k l : ℕ) :
    PortalRankCompatible s k l ↔ k + l = s := Iff.rfl

/-- The finite index type of lower-interval shuffles of `k` and `l` steps.-/
abbrev LowerPortalShuffle (k l : ℕ) : Type := Fin (Nat.choose (k + l) k)

/-- The finite index type of upper-interval shuffles after the portal.-/
abbrev UpperPortalShuffle (n m s k : ℕ) : Type :=
  Fin (Nat.choose (n + m - s) (n - k))

/-- A finite model of a restricted-product chain through compatible portal
ranks.  The first two factors select component chains; the last two select
their lower and upper interleavings.-/
abbrev RestrictedProductPortalChain
    (n m s k l a b : ℕ) : Type :=
  Fin a × Fin b × LowerPortalShuffle k l × UpperPortalShuffle n m s k

/-- Compatibility supplies the parent rank as the sum of the two component
ranks.
@isnad1 id=eq.1h3v.s4.5039d18e30ed from=translated src=- shape=3d83f9b2 vocab=0b693c2c
-/
theorem restrictedProduct_rank_sum
    {s k l : ℕ} (h : PortalRankCompatible s k l) : k + l = s := h

/-- Under the bounded-rank and compatibility hypotheses, the upper interval
has the expected sum of remaining component ranks.
@isnad1 id=eq.3h5v.s6.c453307da1d3 from=translated src=- shape=2f09e252 vocab=8463d652
-/
theorem restrictedProduct_upper_rank_sum
    {n m s k l : ℕ}
    (hk : k ≤ n) (hl : l ≤ m) (h : PortalRankCompatible s k l) :
    n + m - s = (n - k) + (m - l) := by
  dsimp [PortalRankCompatible] at h
  omega

/-- The cardinality of the finite restricted-product chain model is the
product of component-chain counts and the two binomial shuffle counts.
@isnad1 id=eq.0h7v.s7.96781f990dc7 from=translated src=- shape=7b3334f1 vocab=0d7d3e2a
-/
theorem card_restrictedProductPortalChain
    (n m s k l a b : ℕ) :
    Fintype.card (RestrictedProductPortalChain n m s k l a b) =
      a * b * Nat.choose (k + l) k * Nat.choose (n + m - s) (n - k) := by
  simp [Nat.mul_assoc]

/-- Sum the compatible restricted-product chain counts over bounded portal
ranks.  This is the finite count identity used before any geometric
identification of component chain numbers.-/
noncomputable def restrictedProductPortalCount
    (n m s : ℕ) (a b : ℕ → ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
    if PortalRankCompatible s k l then
      Fintype.card (RestrictedProductPortalChain n m s k l (a k) (b l))
    else 0

/-- The rank-filtered count is exactly the finite double sum with the two
shuffle coefficients exposed.
@isnad1 id=eq.0h5v.s7.6fff1c4cf8f7 from=translated src=- shape=5af86bbe vocab=84299d97
-/
theorem restrictedProductPortalCount_eq
    (n m s : ℕ) (a b : ℕ → ℕ) :
    restrictedProductPortalCount n m s a b =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        if PortalRankCompatible s k l then
          a k * b l * Nat.choose (k + l) k *
            Nat.choose (n + m - s) (n - k)
        else 0 := by
  unfold restrictedProductPortalCount
  simp_rw [card_restrictedProductPortalChain]

/- The finite natural-valued chain model and the real-valued convolution use
the same restricted-product kernel after casting cardinalities. -/
/--
@isnad1 id=eq.0h5v.s5.cc740b8f0e6c from=translated src=- shape=62d5f024 vocab=cb94b229
-/
theorem restrictedProductPortalCount_cast_eq_portalShuffleConvolution
    (n m s : ℕ) (a b : ℕ → ℕ) :
    (restrictedProductPortalCount n m s a b : ℝ) =
      portalShuffleConvolution n m (fun k ↦ (a k : ℝ))
        (fun l ↦ (b l : ℝ)) s := by
  rw [restrictedProductPortalCount_eq]
  unfold portalShuffleConvolution portalShuffleKernel
  simp only [Nat.cast_sum, Nat.cast_zero, Nat.cast_ite, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  by_cases h : k + l = s
  · simp [PortalRankCompatible, h]
    ring
  · simp [PortalRankCompatible, h]

end HansenCograph
