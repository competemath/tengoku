/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku

/-!
# IMO 2017 A3

Let $S$ be a finite set, and fix some $f : S → S$.
Suppose that for any $g : S → S$, $f ∘ g ∘ f = g ∘ f ∘ g$ implies $g = f$.
Prove that $f^2(S) = f(S)$.
-/

@[expose] public section

namespace IMOSL
namespace IMO2017A3

/--
@isnad1 id=eq.1h5v.s5.eb9cb81ec778 from=translated src=- shape=649543d9 vocab=f141370e
-/
lemma iterate_add_mul_eq {S : Type*} {f : S → S} (h : f^[n + k] = f^[n]) :
    ∀ t, f^[n + k * t] = f^[n]
  | 0 => rfl
  | t + 1 => by rw [k.mul_succ, ← Nat.add_assoc, f.iterate_add,
               iterate_add_mul_eq h t, ← f.iterate_add, h]

/--
@isnad1 id=eq.2h3v.s5.6c7d4413da2a from=translated src=- shape=1c4c47bd vocab=78e039e7
-/
theorem range_iter_two_eq_of_exists_iter_eq_self
    {f : S → S} (h : 2 ≤ m) (h0 : f^[m] = f) :
    Set.range f^[2] = Set.range f := by
  apply (Set.range_comp_subset_range f f).antisymm
  rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
  nth_rw 1 [← h0, f.iterate_add]; exact Set.range_comp_subset_range _ _

variable [Fintype S]

/--
@isnad1 id=ex.0h2v.s5.31e9f5be131a from=translated src=- shape=e6a854df vocab=24c87b5a
-/
theorem exists_lt_iterate_eq (f : S → S) : ∃ a b, a < b ∧ f^[a] = f^[b] := by
  obtain ⟨a, b, h, h0⟩ : ∃ a b : ℕ, a ≠ b ∧ f^[a] = f^[b] :=
    Finite.exists_ne_map_eq_of_infinite _
  exact h.lt_or_gt.elim (λ h ↦ ⟨a, b, h, h0⟩) (λ h ↦ ⟨b, a, h, h0.symm⟩)

/--
@isnad1 id=ex.0h2v.s5.3df406e9f3d2 from=translated src=- shape=97bcb821 vocab=a67f03a1
-/
theorem exists_iterate_idempotent (f : S → S) :
    ∃ n, 0 < n ∧ f^[2 * n] = f^[n] := by
  obtain ⟨a, b, h, h0⟩ := exists_lt_iterate_eq f
  rcases Nat.exists_eq_add_of_le h.le with ⟨c, rfl⟩
  rw [Nat.lt_add_right_iff_pos] at h
  refine ⟨c * a.succ, Nat.mul_pos h a.succ_pos, ?_⟩
  rw [Nat.two_mul]; refine iterate_add_mul_eq ?_ _
  obtain ⟨k, h1⟩ := Nat.exists_eq_add_of_le
    (Nat.le_mul_of_pos_left a.succ h)
  rw [h1, Nat.add_right_comm, f.iterate_add, Nat.succ_add,
    f.iterate_succ, ← h0, ← f.iterate_succ, f.iterate_add]

/-- Final solution
@isnad1 id=eq.1h2v.s6.85e38820284a from=translated src=- shape=ffea1905 vocab=ee6b0d1f
-/
theorem final_solution (h : ∀ g : S → S, f ∘ g ∘ f = g ∘ f ∘ g → g = f) :
    Set.range f^[2] = Set.range f := by
  rcases exists_iterate_idempotent f with ⟨n, h0, h1⟩
  refine range_iter_two_eq_of_exists_iter_eq_self
    (Nat.lt_add_of_pos_left h0) (h _ ?_)
  rw [← f.iterate_succ', ← f.iterate_add]
  change (f ∘ f^[n]) ∘ f^[2] = f^[n + 1 + n] ∘ f^[2]
  rw [Nat.succ_add, ← Nat.two_mul, f.iterate_succ' (2 * n), h1]
