/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.OrderedTwoPointInduction
public import Tengoku

/-!
# Reindexing and sorting finite two-point systems
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace Feige

noncomputable section

/-- Permutation which arranges `γ` in nonincreasing order. -/
noncomputable def descendingPerm {m : ℕ} (γ : Fin m → ℝ) :
    Equiv.Perm (Fin m) :=
  Tuple.sort (fun i => -γ i)

/--
@isnad1 id=antitone.0h2v.s5.79b268805f7e from=translated src=- shape=87db8c73 vocab=aa9ff342
-/
theorem antitone_comp_descendingPerm {m : ℕ} (γ : Fin m → ℝ) :
    Antitone (γ ∘ descendingPerm γ) := by
  have hmono := Tuple.monotone_sort (fun i : Fin m => -γ i)
  intro i j hij
  have h := hmono hij
  dsimp [descendingPerm] at h ⊢
  linarith

/--
@isnad1 id=eq.0h4v.s6.94ead73dc29d from=translated src=- shape=c25ddb00 vocab=e6036868
-/
theorem highSetMass_comp_perm {m : ℕ}
    (p : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (S : Finset (Fin m)) :
    highSetMass (p ∘ σ) S =
      highSetMass p (S.map σ.toEmbedding) := by
  classical
  unfold highSetMass
  congr 1
  · rw [Finset.prod_map]
    rfl
  · have hcompl :
        Finset.univ \ S.map σ.toEmbedding =
          (Finset.univ \ S).map σ.toEmbedding := by
      ext i
      simp
    rw [hcompl, Finset.prod_map]
    rfl

end

end Feige
