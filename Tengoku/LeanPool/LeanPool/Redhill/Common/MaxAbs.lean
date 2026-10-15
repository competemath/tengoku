/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Tengoku

/-!
# Maximum absolute value of a tuple of integers
-/

@[expose] public section

open Finset

variable {n : ℕ}

/-- The maximum absolute value of a tuple of integers (0 if empty). -/
def maxAbs (a : Fin n → ℤ) : ℕ :=
  univ.sup fun i ↦ (a i).natAbs

/--
@isnad1 id=eq.0h1v.s4.c8fd95da1212 from=translated src=- shape=37c53032 vocab=15645812
-/
lemma maxAbs_zero {a : Fin 0 → ℤ} : maxAbs a = 0 := by simp [maxAbs]

/--
@isnad1 id=eq.0h1v.s5.9013dccce9be from=translated src=- shape=cb7e9f4f vocab=600ec528
-/
lemma maxAbs_one {a : Fin 1 → ℤ} : maxAbs a = (a 0).natAbs := by simp [maxAbs]

variable {a : Fin n → ℤ}

/--
@isnad1 id=eq.0h2v.s5.4528b64889dd from=translated src=- shape=22ada091 vocab=f53aabcd
-/
lemma maxAbs_eq_foldr : maxAbs a = (List.ofFn fun i ↦ (a i).natAbs).foldr max 0 := by
  rw [← Nat.bot_eq_zero, List.foldr_sup_eq_sup_toFinset, maxAbs,
    ← (fun i ↦ (a i).natAbs).id_comp, ← sup_image]
  congr; ext; simp

/--
@isnad1 id=eq.1h3v.s5.30a3879a071e from=translated src=- shape=3515265a vocab=6d4021a9
-/
lemma maxAbs_eq_of_forall_le {i : Fin n} (hi : ∀ j, (a j).natAbs ≤ (a i).natAbs) :
    maxAbs a = (a i).natAbs :=
  le_antisymm (Finset.sup_le (by simp_all)) (le_sup (f := fun i ↦ (a i).natAbs) (mem_univ _))
