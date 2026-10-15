/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.InsertionCommonLaw
public import Tengoku.LeanPool.LeanPool.Feige.InsertionK
public import Tengoku.LeanPool.LeanPool.Feige.Lemma43Insertion
import Tengoku.LeanPool.LeanPool.Feige.InsertionLastCoordinateLaw
import Tengoku.LeanPool.LeanPool.Feige.Lemma43Endpoints
import Tengoku.LeanPool.LeanPool.Feige.Lemma43Relations

/-!
# Realizing the genuine edges of an insertion chain

At every old chain level, the three numerical sequences `F`, `B`, and `A`
are respectively the nonnegative-tail probability of the old state law,
the positive shift by the new low-side scale, and the negative shift by the
new high-side scale.  This identifies every nonterminal edge with the
finite signed-exponential instance of the local transfer step.
-/

@[expose] public section

open MeasureTheory

namespace Feige

noncomputable section

/--
@isnad1 id=eq.0h5v.s6.3ab39022d9a5 from=translated src=- shape=4c5d2273 vocab=446889ff
-/
theorem insertionOldK_eq_F_stateLaw {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) :
    insertionOldK γ β σ r.val =
      Lemma43.F
        (stateLaw (fun i : Fin n ↦ γ i.castSucc)
          (fun i : Fin n ↦ β i.castSucc) (chainState σ r)) := by
  unfold insertionOldK
  rw [booleanChainK_of_lt _ _ _ r.isLt]
  simpa only [Lemma43.F] using
    (twoPointKFinset_eq_stateLaw
      (fun i : Fin n ↦ γ i.castSucc)
      (fun i : Fin n ↦ β i.castSucc) (chainState σ r))

end

end Feige
