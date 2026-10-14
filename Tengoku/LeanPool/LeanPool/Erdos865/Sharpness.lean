/-
Copyright (c) 2026 Ricky Cipollini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ricky Cipollini
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos865.Defs
public import Tengoku

/-!
# Sharpness of the 5/8 bound (Erdős 865, §5)

The construction `A = [M,2M] ∪ [4M,8M]` is triple-free of size `5M + 2`, so for `N = 8M`
one has `8·|A| = 5·N + 16`, showing the constant `5/8` is optimal.
-/

@[expose] public section

open Finset

namespace Erdos865

/-- The sharpness construction `A = [M, 2M] ∪ [4M, 8M]`. -/
def sharpSet (M : ℕ) : Finset ℕ := Finset.Icc M (2 * M) ∪ Finset.Icc (4 * M) (8 * M)

/-- The construction sits inside `[1, 8M]` (for `M ≥ 1`).
@isnad1 id=le.1h1v.s5.b3e447ebddc8 from=translated src=- shape=568e7699 vocab=0547bdf5
-/
theorem sharpSet_subset {M : ℕ} (hM : 1 ≤ M) : sharpSet M ⊆ Finset.Icc 1 (8 * M) :=
  Finset.union_subset (Finset.Icc_subset_Icc (by linarith) (by linarith))
    (Finset.Icc_subset_Icc (by linarith) (by linarith))

/-- The construction has `5M + 2` elements.
@isnad1 id=eq.1h1v.s5.dfac04e6ea6d from=translated src=- shape=d3f46844 vocab=0bb79978
-/
theorem sharpSet_card {M : ℕ} (hM : 1 ≤ M) : (sharpSet M).card = 5 * M + 2 := by
  have hdisj : Disjoint (Finset.Icc M (2 * M)) (Finset.Icc (4 * M) (8 * M)) :=
    Finset.disjoint_left.mpr fun x hx₁ hx₂ => by
      simp only [Finset.mem_Icc] at hx₁ hx₂; omega
  rw [sharpSet, Finset.card_union_of_disjoint hdisj, Nat.card_Icc, Nat.card_Icc]
  omega

/-- The construction is triple-free.
@isnad1 id=istriple.0h1v.s2.322094fbae3a from=translated src=- shape=76a08d12 vocab=87a7e54a
-/
theorem sharpSet_tripleFree (M : ℕ) : IsTripleFree (sharpSet M) := by
  intro h;
  obtain ⟨ a, ha, b, hb, c, hc, hab, hac, hbc, hab', hac', hbc' ⟩ := h;
  unfold sharpSet at *;
  grind

/-- Sharpness: for `N = 8M` with `M ≥ 1` there is a triple-free subset of `[1,N]`
of size `5M + 2`, i.e. with `8 * card = 5 * N + 16`.
@isnad1 id=ex.1h1v.s6.d504262f42ec from=translated src=- shape=7a61c9a0 vocab=61bbdf11
-/
theorem sharpness {M : ℕ} (hM : 1 ≤ M) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (8 * M) ∧ IsTripleFree A ∧
      8 * A.card = 5 * (8 * M) + 16 := by
  refine ⟨sharpSet M, sharpSet_subset hM, sharpSet_tripleFree M, ?_⟩
  rw [sharpSet_card hM]; ring

end Erdos865
