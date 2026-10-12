/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku

/-!
# Finite folds

Small order-theoretic facts about folds indexed by `Fin`.
-/

@[expose] public section

namespace Algebraic.Fin

/-- Every folded value is at most the maximum accumulated by `Fin.foldl`.
@isnad1 id=le.0h5v.s5.c16eb7daf1ca from=translated src=- shape=b9562660 vocab=af2df947
-/
theorem le_foldl_max [LinearOrder α]
    (values : Fin n → α)
    (initial : α)
    (i : Fin n) :
    values i ≤ Fin.foldl n (fun result j => max result (values j)) initial := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Fin.foldl_succ_last]
        exact le_max_right _ _
      · rw [Fin.foldl_succ_last]
        exact (ih (fun i => values i.castSucc) i).trans (le_max_left _ _)

/-- A finite maximum is bounded above when its initial value and every folded
value are bounded above.
@isnad1 id=le.2h5v.s6.4b2992ec33ff from=translated src=- shape=d41e36cc vocab=af2df947
-/
theorem foldl_max_le [LinearOrder α]
    (values : Fin n -> α)
    (initial bound : α)
    (initial_le : initial <= bound)
    (values_le : forall i, values i <= bound) :
    Fin.foldl n (fun result i => max result (values i)) initial <= bound := by
  induction n with
  | zero => simpa using initial_le
  | succ n inductionHypothesis =>
      rw [Fin.foldl_succ_last]
      apply max_le
      · apply inductionHypothesis
        intro i
        exact values_le i.castSucc
      · exact values_le (Fin.last n)

end Algebraic.Fin
