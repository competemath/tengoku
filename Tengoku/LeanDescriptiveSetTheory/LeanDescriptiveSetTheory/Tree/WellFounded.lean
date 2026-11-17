/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.Basic
import Tengoku.Seed.Order.WellFounded

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Well-founded descriptive-set-theoretic trees

This file equips the nodes of a `Descriptive.tree A` with the immediate-child relation. The
relation is oriented so that a child is below its parent, matching Lean's convention for
well-founded recursion.

The main result identifies relation-theoretic well-foundedness with the usual descriptive set
theory condition that the tree has no infinite branch. In the nontrivial direction, an infinite
child chain has compatible, steadily lengthening nodes; reading their stable coordinates produces
a branch through the original tree.
-/

open Set

universe u

namespace DescriptiveSetTheory.Tree

variable {A : Type u} {T : Descriptive.tree A}

/-- `s` is an immediate child of `t` when it appends exactly one symbol to `t`.-/
def Child (T : Descriptive.tree A) (s t : T) : Prop :=
  ∃ a, s.1 = t.1 ++ [a]

/-- A parent node is a prefix of each of its immediate children.-/
theorem Child.isPrefix {s t : T} (h : Child T s t) : t.1 <+: s.1 := by
  obtain ⟨a, ha⟩ := h
  exact ⟨[a], ha.symm⟩

/-- An immediate child is strictly longer than its parent.-/
theorem Child.length_lt {s t : T} (h : Child T s t) : t.1.length < s.1.length := by
  obtain ⟨a, ha⟩ := h
  rw [ha]
  simp

namespace ChildChain

private theorem length_lower (f : ℕ → T) (hf : ∀ n, Child T (f (n + 1)) (f n))
    (n : ℕ) : n ≤ (f n).1.length := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      exact (Nat.succ_le_succ ih).trans (Nat.succ_le_of_lt (Child.length_lt (hf n)))

private theorem isPrefix (f : ℕ → T) (hf : ∀ n, Child T (f (n + 1)) (f n))
    {m n : ℕ} (hmn : m ≤ n) : (f m).1 <+: (f n).1 := by
  induction n, hmn using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (Child.isPrefix (hf n))

private def sequence (f : ℕ → T) (hf : ∀ n, Child T (f (n + 1)) (f n)) (n : ℕ) : A :=
  (f (n + 1)).1[n]'(by
    have := length_lower f hf (n + 1)
    omega)

private theorem initialSegment_sequence (f : ℕ → T)
    (hf : ∀ n, Child T (f (n + 1)) (f n)) (n : ℕ) :
    initialSegment (sequence f hf) n = (f n).1.take n := by
  apply List.ext_getElem
  · simp [length_initialSegment, List.length_take, Nat.min_eq_left (length_lower f hf n)]
  · intro i hi₁ hi₂
    have hi : i < n := by simpa using hi₁
    have hfi : i < (f (i + 1)).1.length := by
      have := length_lower f hf (i + 1)
      omega
    have hfn : i < (f n).1.length := hi.trans_le (length_lower f hf n)
    have hcoord : (f (i + 1)).1[i]'hfi = (f n).1[i]'hfn :=
      (isPrefix f hf (Nat.succ_le_iff.mpr hi)).getElem hfi
    simpa [initialSegment, sequence] using hcoord

private theorem initialSegment_mem (f : ℕ → T)
    (hf : ∀ n, Child T (f (n + 1)) (f n)) (n : ℕ) :
    initialSegment (sequence f hf) n ∈ T := by
  rw [initialSegment_sequence]
  exact Descriptive.Tree.take_mem (f n)

end ChildChain

/-- A tree is well-founded when its immediate-child relation is well-founded.-/
def IsWellFounded (T : Descriptive.tree A) : Prop :=
  WellFounded (Child T)

/-- A descriptive-set-theoretic tree is well-founded exactly when it has no infinite branch.-/
theorem isWellFounded_iff_body_eq_empty : IsWellFounded T ↔ body T = ∅ := by
  constructor
  · intro hT
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hchain : ∀ n, Child T
        (⟨initialSegment x (n + 1), hx (n + 1)⟩ : T)
        (⟨initialSegment x n, hx n⟩ : T) := fun n =>
      ⟨x n, initialSegment_succ x n⟩
    exact (wellFounded_iff_isEmpty_descending_chain.mp hT).false
      ⟨fun n => ⟨initialSegment x n, hx n⟩, hchain⟩
  · intro hbody
    change WellFounded (Child T)
    rw [wellFounded_iff_isEmpty_descending_chain]
    constructor
    rintro ⟨f, hf⟩
    have hx : ChildChain.sequence f hf ∈ body T := fun n =>
      ChildChain.initialSegment_mem f hf n
    rw [hbody] at hx
    exact hx

end DescriptiveSetTheory.Tree
