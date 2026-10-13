/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Internal

/-!
# Finite two-block entropy repair

A point-mass bound on a joint source gives a nearby block source by replacing
small rows with uniform rows of the same mass. This preserves the first
marginal exactly. Conditional caps are stated without division by the row
mass, so they apply to zero-mass rows as well. Row averaging retains the
original joint point-mass cap, allowing the repair to feed later splitting
steps at the same input threshold.

The power-of-two corollary is a finite marginal-preserving version of
Chattopadhyay--Goodman--Liao, Lemma 5.3 of *Affine Extractors for Almost
Logarithmic Entropy*, <https://eccc.weizmann.ac.il/report/2021/075/>,
which attributes the splitting lemma to Goldreich--Wigderson (1997).
The explicit repair and the sharper bound by the mass of the replaced rows
are proved here. This module concerns probability weights; a recursive
extractor and its seed-reuse argument require further results.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Row averaging preserves any original joint cap, without probability,
nonnegativity, or nonempty-alphabet assumptions.
@isnad1 id=cappedwe.1h6v.s5.7316f5917785 from=translated src=- shape=c2d4ff06 vocab=cd46e3b5
-/
theorem twoBlockRepair_capped {α β : Type*} [Fintype β]
    (p : α × β → ℝ) (N K : Nat) (μ : ℝ) (cap : CappedWeight p N) :
    CappedWeight (twoBlockRepair p K μ) N :=
  Internal.twoBlockRepair_capped p N K μ cap

/-- Uniformizing small rows preserves every first-coordinate mass exactly.
@isnad1 id=eq.0h5v.s5.31c98dfb7493 from=translated src=- shape=ff51695b vocab=3c32beb7
-/
theorem twoBlockRepair_firstWeight {α β : Type*} [Fintype β] [Nonempty β]
    (p : α × β → ℝ) (K : Nat) (μ : ℝ) :
    firstWeight (twoBlockRepair p K μ) = firstWeight p :=
  Internal.twoBlockRepair_firstWeight p K μ

/-- The repaired weights remain a probability distribution.
@isnad1 id=isprobab.1h5v.s5.3f4d58eeb76c from=translated src=- shape=450f2266 vocab=f9abe111
-/
theorem twoBlockRepair_probability {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (p : α × β → ℝ) (probability : IsProbabilityWeight p) (K : Nat) (μ : ℝ) :
    IsProbabilityWeight (twoBlockRepair p K μ) :=
  Internal.twoBlockRepair_probability p probability K μ

/-- Every repaired row satisfies the conditional cap, including rows of mass zero.
@isnad1 id=le.3h7v.s6.688d341a054e from=translated src=- shape=e26b2569 vocab=8cef8e6b
-/
theorem twoBlockRepair_conditional_cap {α β : Type*} [Fintype β] [Nonempty β]
    (p : α × β → ℝ) (nonnegative : ∀ x, 0 ≤ p x) {K : Nat} {μ : ℝ}
    (size : K ≤ Fintype.card β) (cap : ∀ x, p x ≤ μ) :
    ∀ a b, (K : ℝ) * twoBlockRepair p K μ (a, b) ≤
      firstWeight (twoBlockRepair p K μ) a :=
  Internal.twoBlockRepair_conditional_cap p nonnegative size cap

/-- The original joint point cap also controls the unchanged first marginal.
@isnad1 id=cappedwe.2h5v.s6.7d7000eb254d from=translated src=- shape=7692b04c vocab=0e471ce6
-/
theorem twoBlockRepair_first_cap {α β : Type*} [Fintype β] [Nonempty β]
    (p : α × β → ℝ) {K : Nat} {μ : ℝ} (cap : ∀ x, p x ≤ μ)
    (budget : (K : ℝ) * Fintype.card β * μ ≤ 1) :
    CappedWeight (firstWeight (twoBlockRepair p K μ)) K :=
  Internal.twoBlockRepair_first_cap p cap budget

open scoped Classical in
/-- The repair costs at most the total mass of the rows it replaces.
@isnad1 id=le.1h5v.s6.ff4c71f121a3 from=translated src=- shape=674e3184 vocab=48606a4f
-/
theorem twoBlockRepair_dist_le_low_mass {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty β]
    (p : α × β → ℝ) (nonnegative : ∀ x, 0 ≤ p x) (K : Nat) (μ : ℝ) :
    weightDist p (twoBlockRepair p K μ) ≤
      ∑ a, if firstWeight p a < (K : ℝ) * μ then firstWeight p a else 0 :=
  Internal.twoBlockRepair_dist_le_low_mass p nonnegative K μ

/-- Each replaced row has mass less than `K*μ`, giving a cardinality bound.
@isnad1 id=le.2h5v.s6.deab2b923dd2 from=translated src=- shape=28e6581d vocab=1dd103f2
-/
theorem twoBlockRepair_dist_le {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty β]
    (p : α × β → ℝ) (probability : IsProbabilityWeight p) {K : Nat} {μ : ℝ}
    (cap : ∀ x, p x ≤ μ) :
    weightDist p (twoBlockRepair p K μ) ≤ (Fintype.card α : ℝ) * K * μ :=
  Internal.twoBlockRepair_dist_le p probability cap

/-- Repair a joint source into a two-block source with threshold `K`,
preserving its first marginal and paying at most `card α*K*μ` in distance.
@isnad1 id=ex.5h5v.s7.99b4c3a45e01 from=translated src=- shape=5b6112a6 vocab=252f19e7
-/
theorem exists_twoBlock_repair {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (probability : IsProbabilityWeight p) {K : Nat} {μ : ℝ}
    (positive : 0 < K) (size : K ≤ Fintype.card β) (cap : ∀ x, p x ≤ μ)
    (budget : (K : ℝ) * Fintype.card β * μ ≤ 1) :
    ∃ q : α × β → ℝ, IsProbabilityWeight q ∧ firstWeight q = firstWeight p ∧
      CappedWeight (firstWeight q) K ∧
      (∀ a b, (K : ℝ) * q (a, b) ≤ firstWeight q a) ∧
      weightDist p q ≤ (Fintype.card α : ℝ) * K * μ :=
  Internal.exists_twoBlock_repair p probability positive size cap budget

/-- For equal `m`-bit alphabets, joint entropy at least `m+t+e` can be
repaired to two blocks of entropy at least `t` with error at most `2^(-e)`.
@isnad1 id=ex.6h7v.s8.5fe40ae9fe99 from=translated src=- shape=ac5730db vocab=348eee0b
-/
theorem exists_twoBlock_repair_pow_two {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (probability : IsProbabilityWeight p) {m t k e : Nat}
    (card_first : Fintype.card α = 2 ^ m) (card_second : Fintype.card β = 2 ^ m)
    (cap : CappedWeight p (2 ^ k)) (width : t ≤ m) (entropy : m + t + e ≤ k) :
    ∃ q : α × β → ℝ, IsProbabilityWeight q ∧ firstWeight q = firstWeight p ∧
      CappedWeight (firstWeight q) (2 ^ t) ∧
      (∀ a b, ((2 ^ t : Nat) : ℝ) * q (a, b) ≤ firstWeight q a) ∧
      weightDist p q ≤ ((2 : ℝ) ^ e)⁻¹ :=
  Internal.exists_twoBlock_repair_pow_two p probability card_first card_second cap width entropy

/-- The explicit power-of-two repair also retains the original joint cap,
while producing two blocks at the smaller threshold and preserving their first marginal.
@isnad1 id=ex.5h6v.s8.7e0479107ce7 from=translated src=- shape=1c949bdf vocab=f7d64e1f
-/
theorem exists_twoBlock_repair_pow_two_capped {α : Type*} [Fintype α]
    (p : α × α → ℝ) (probability : IsProbabilityWeight p) {m s k e : Nat}
    (card : Fintype.card α = 2 ^ m) (cap : CappedWeight p (2 ^ k))
    (width : s ≤ m) (entropy : m + s + e ≤ k) :
    ∃ q : α × α → ℝ, IsProbabilityWeight q ∧ CappedWeight q (2 ^ k) ∧
      IsBlockSource (fun x : Fin 2 → α => q (x 0, x 1)) (2 ^ s) ∧
      firstWeight q = firstWeight p ∧ weightDist p q ≤ ((2 : ℝ) ^ e)⁻¹ :=
  Internal.exists_twoBlock_repair_pow_two_capped p probability card cap width entropy

end Algebraic.Cutwidth.Extractor
