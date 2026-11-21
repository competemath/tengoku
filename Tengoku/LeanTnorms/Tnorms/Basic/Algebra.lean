/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Tengoku
import Tengoku.LeanTnorms.Tnorms.Basic.Defs
import Tengoku.LeanTnorms.Tnorms.Util.Mathlib

/-!
This file proves some basic relationships between properties of T-norms.  In addition to the stuff
from (Triangular Norms I, Sec 6), we also connect these notions to existing typeclasses in Mathlib.
-/
namespace Tengoku.LeanTnorms end Tengoku.LeanTnorms open Tengoku.LeanTnorms
local infixl:60 " ⇒ " => LImp

variable {M : Type*}

section NontrivialZeroOne

variable [Zero M] [One M]

instance [NontrivialZeroOne M] : Nontrivial M where
  exists_pair_ne := by
    obtain ⟨a, ha0, ha1⟩ := NontrivialZeroOne.exists_ne (M := M)
    use a, 0

instance [Infinite M] : NontrivialZeroOne M where
  exists_ne := by
    classical obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset {(0 : M), (1 : M)}
    simp at ha
    use a

/--
@isnad1 id=nontrivi.1h1v.s4.d068622daf60 from=translated src=- shape=7894e3b2 vocab=0e7b50d1
-/
theorem _root_.Tengoku.LeanTnorms.nontrivialZeroOne_of_card_ge_three [Fintype M] (h : 2 < Fintype.card M) :
    NontrivialZeroOne M := by
  rw [Fintype.two_lt_card_iff] at h
  refine NontrivialZeroOne.mk ?_
  obtain ⟨a, b, c, hab, hac, hbc⟩ := h
  by_cases! ha : a ≠ 0 ∧ a ≠ 1
  · use a
  by_cases! hb : b ≠ 0 ∧ b ≠ 1
  · use b
  use c
  grind

instance [SubsingletonZeroOne M] [DecidableEq M] : Fintype M where
  elems := {(0 : M), (1 : M)}
  complete := by simp [SubsingletonZeroOne.allEq_zero_or_one]

/--
@isnad1 id=iff.0h1v.s4.780c52b41b84 from=translated src=- shape=ec580384 vocab=e6b88d2d
-/
theorem _root_.Tengoku.LeanTnorms.nontrivialZeroOne_iff_not_subsingletonZeroOne :
    NontrivialZeroOne M ↔ ¬ SubsingletonZeroOne M := by
  simp [subsingletonZeroOne_iff, nontrivialZeroOne_iff]

/--
@isnad1 id=iff.0h1v.s4.c7eec5120f75 from=translated src=- shape=ec580384 vocab=e6b88d2d
-/
theorem _root_.Tengoku.LeanTnorms.subsingletonZeroOne_iff_not_nontrivialZeroOne :
    SubsingletonZeroOne M ↔ ¬ NontrivialZeroOne M := by
  rw [nontrivialZeroOne_iff_not_subsingletonZeroOne, not_not]

/--
@isnad1 id=iff.0h1v.s4.72e4a63c49a9 from=translated src=- shape=1de50875 vocab=203daf99
-/
theorem _root_.Tengoku.LeanTnorms.nontrivialZeroOne_iff_exists_isNontrivial :
    NontrivialZeroOne M ↔ ∃ a : M, IsNontrivial a := nontrivialZeroOne_iff M

/--
@isnad1 id=iff.0h1v.s4.e67463aaff03 from=translated src=- shape=49021acd vocab=04ba9739
-/
theorem _root_.Tengoku.LeanTnorms.subsingletonZeroOne_iff_not_isNontrivial :
    SubsingletonZeroOne M ↔ ∀ a : M, ¬IsNontrivial a := by
  simp [subsingletonZeroOne_iff_not_nontrivialZeroOne, nontrivialZeroOne_iff_exists_isNontrivial]

end NontrivialZeroOne

section Cancel

-- Example 2.10 (ii)
instance [MulZeroClass M] [IsCancelMulZero M] : ConditionalCancellative M where
  right_cancel_of_mul_ne_zero := by
    intro p q r hrp h
    rwa [mul_left_inj' (right_ne_zero_of_mul hrp)] at h
  left_cancel_of_mul_ne_zero := by
    intro p q r hrp h
    rwa [mul_right_inj' (left_ne_zero_of_mul hrp)] at h

/--
@isnad1 id=infinite.0h1v.s6.c1a3ecf0fef7 from=translated src=- shape=4ff572b6 vocab=dddb3910
-/
theorem MulPosStrictMon.toInfinite [PartialOrder M] [MulZeroOneClass M]
    [MulLeftMono M] [PosMulStrictMono M]
    [IsTopOneClass M] [NontrivialZeroOne M] :
    Infinite M where
  not_finite fin := by
    obtain ⟨a, ha0, ha⟩ := exists_covBy_of_wellFoundedLT (isBot_zero.not_isMax (α := M))
    have ha1 : a < 1 := by
      obtain ⟨b, hb⟩ := NontrivialZeroOne.exists_ne (M := M)
      rw [lt_one_iff_ne_one]
      contrapose! ha
      use b
      rwa [ha, pos_iff_ne_zero, lt_one_iff_ne_one]
    have ha02 : 0 < a * a := mul_pos ha0 ha0
    have ha2 : a * a < a := by
      conv_rhs => rw [← mul_one a]
      exact mul_lt_mul_of_pos_left ha1 ha0
    exact ha ha02 ha2

variable [Mul M] [Zero M] [Preorder M] [Subsingleton M]

variable {M : Type*} [Preorder M] [MulZeroOneClass M] [SubsingletonZeroOne M]

instance : PosMulStrictMono M where
  mul_lt_mul_of_pos_left := by
    intro a ha b c h
    by_cases! ha0 : a = 0
    · grind
    simp [eq_one_of_ne_zero ha0, h]

instance : IsCancelMulZero M where
  mul_left_cancel_of_ne_zero := by
    intro a ha
    apply eq_one_of_ne_zero at ha
    exact ha ▸ isRegular_one.left
  mul_right_cancel_of_ne_zero := by
    intro a ha
    apply eq_one_of_ne_zero at ha
    exact ha ▸ isRegular_one.right

end Cancel

section Archimedean

/--
@isnad1 id=tendsto.1h2v.s7.ef4e15275664 from=translated src=- shape=02b0c323 vocab=c27cf15b
-/
lemma _root_.Tengoku.LeanTnorms.npow_tendsto_bot [TopologicalSpace M] [PartialOrder M] [OrderBot M]
    [OrderTopology M] [MonoidWithZero M] [PosMulMono M] [MulLeftMono M] [IsTopOneClass M]
    [MulArchimedeanDualWithZero M]
    (p : M) (hp : p ≠ 1) :
    Filter.Tendsto (fun n : ℕ ↦ p ^ n) Filter.atTop (nhds ⊥) := by
  simp only [tendsto_order, not_lt_bot, Filter.eventually_atTop, IsEmpty.forall_iff, implies_true,
    gt_iff_lt, true_and]
  intro q hq
  rw [← lt_one_iff_ne_one] at hp
  rw [bot_eq_zero] at hq
  obtain ⟨n, hn⟩ := MulArchimedeanDualWithZero.arch hq hp
  use n
  intro k hk
  exact lt_of_le_of_lt (pow_right_anti₀ zero_le le_one hk) hn

-- Theorem 2.12
/--
@isnad1 id=iff.0h1v.s6.266c60d92f2e from=translated src=- shape=18dc428b vocab=63421573
-/
theorem _root_.Tengoku.LeanTnorms.arch_iff_lim_prop [PartialOrder M] [CommMonoidWithZero M] [TopologicalSpace M]
    [OrderTopology M] [IsOrderedMonoid M] [IsBotZeroClass M] :
    MulArchimedeanDualWithZero M ↔ ∀ {p : M}, p < 1 →
    Filter.Tendsto (p ^ ·) Filter.atTop (nhds 0) := by
  refine ⟨fun _ p hp1 ↦ ?_, fun h ↦ MulArchimedeanDualWithZero.mk ?_⟩
  · simp only [tendsto_order, not_lt_zero, Filter.eventually_atTop, IsEmpty.forall_iff,
      implies_true, gt_iff_lt, true_and]
    intro q hq
    obtain ⟨n, hn⟩ := MulArchimedeanDualWithZero.arch hq hp1
    use n
    intro m hnm
    refine lt_of_le_of_lt ?_ hn
    exact pow_le_pow_right_of_le_one' (le_of_lt hp1) hnm
  · intro x y hx hy
    specialize h hy
    simp only [tendsto_order, Filter.eventually_atTop, gt_iff_lt] at h
    obtain ⟨n, hn⟩ := h.2 x hx
    use n
    grind

-- Proposition 2.15 (v)
/--
@isnad1 id=mularchi.1h1v.s5.101ef697587a from=translated src=- shape=84de81f4 vocab=e539b470
-/
lemma _root_.Tengoku.LeanTnorms.arch_of_all_nilpt_els [PartialOrder M] [MonoidWithZero M]
    (h : ∀ p : M, p ≠ 1 → IsNilpotent p) : MulArchimedeanDualWithZero M where
  arch := by
    intro x y hx hy
    obtain ⟨n, hn⟩ := h y (ne_of_lt hy)
    grind

/--
@isnad1 id=iff.0h1v.s6.27d8fdea83de from=translated src=- shape=cd973e87 vocab=565a4cf6
-/
theorem _root_.Tengoku.LeanTnorms.isReduced_iff_noZeroDivisors_of_arch [SemilatticeInf M]
    [MonoidWithZero M] [MulLeftMono M] [MulRightMono M] [IsTopOneClass M]
    [MulArchimedeanDualWithZero M] :
    IsReduced M ↔ NoZeroDivisors M := by
  refine ⟨fun h ↦ NoZeroDivisors.mk ?_, fun h ↦ isReduced_of_noZeroDivisors⟩
  intro p q hpq
  suffices p ⊓ q = 0 by
    rw [isReduced_iff] at h
    contrapose! h
    obtain ⟨hp, hq⟩ := h
    use p
    constructor
    · have hp1 : p < 1 := by
        rw [lt_one_iff_ne_one]
        contrapose! hpq
        rwa [hpq, one_mul]
      have hq0 : 0 < q := by rwa [pos_iff_ne_zero]
      obtain ⟨n, hn⟩ := MulArchimedeanDualWithZero.arch hq0 hp1
      use n
      rw [← le_zero_iff, ← this]
      refine le_inf ?_ ?_
      · conv_rhs => rw [← pow_one p]
        have hn : n ≠ 0 := by
          contrapose! hn
          simp [hn, pow_zero]
        exact pow_right_anti₀ zero_le le_one (by lia)
      · exact hn.le
    · exact hp
  rw [isReduced_iff] at h
  refine h _ ?_
  use 2
  rw [pow_two, ← le_zero_iff, ← hpq]
  exact mul_le_mul' inf_le_left inf_le_right

end Archimedean

section NoNontrivialIdempotents

-- Proposition 2.11 (ii)
instance [MonoidWithZero M] [IsLeftCancelMulZero M] : NoNontrivialIdempotents M where
  no_idem := by
    simp only [not_and_or, not_not, ← IsIdempotentElem.iff_eq_zero_or_one,
      IsIdempotentElem, imp_self, implies_true]

instance [MonoidWithZero M] [ConditionalCancellative M] : NoNontrivialIdempotents M where
  no_idem := by
    intro p hp
    unfold IsIdempotentElem at hp
    simp only [not_and, ne_eq, not_not]
    intro hp0
    have hp10 : p * 1 ≠ 0 := by grind
    conv_rhs at hp => rw [← mul_one p]
    exact ConditionalCancellative.left_cancel_of_mul_ne_zero hp10 hp

end NoNontrivialIdempotents
-- Tengoku: root names of this library moved to Tengoku.LeanTnorms so they do not collide with other libraries (generated)
