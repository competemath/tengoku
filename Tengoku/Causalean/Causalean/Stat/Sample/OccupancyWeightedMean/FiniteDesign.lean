/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku.Causalean.Causalean.Stat.Sample.OccupancyWeightedMean.Basic
public import Tengoku.Causalean.Causalean.Stat.Sample.OccupancyWeightedMean.BinomialDesign

/-!
# Finite enumeration for occupancy-weighted design factors

This module assembles groupwise inverse-arm bounds into an algebraic comparison
between the expected occupancy design variance factor and reciprocal usable
occupancy. Zero-mass group fibers vanish before any conditional arm probability
is formed.
-/

@[expose] public section

namespace Causalean.Stat

open scoped BigOperators

section FiniteDesign

variable {n : Nat} {κ : Type*} [Fintype κ] [DecidableEq κ]

private def fdArmCount (x : Fin n → κ) (b : Fin n → Bool)
    (a : Bool) (k : κ) : Nat :=
  (Finset.univ.filter fun i => x i = k ∧ b i = a).card

private def fdGroupCount (x : Fin n → κ) (k : κ) : Nat :=
  (Finset.univ.filter fun i => x i = k).card

private def fdUsable (x : Fin n → κ) (b : Fin n → Bool) (k : κ) : Prop :=
  0 < fdArmCount x b false k ∧ 0 < fdArmCount x b true k

private noncomputable def fdTotal (x : Fin n → κ) (b : Fin n → Bool) : Nat :=
  by
    classical
    exact ∑ k, if fdUsable x b k then fdGroupCount x k else 0

private noncomputable def fdInverse (x : Fin n → κ) (b : Fin n → Bool) : Real :=
  if 0 < fdTotal x b then (fdTotal x b : Real)⁻¹ else 0

private noncomputable def fdVariance (x : Fin n → κ) (b : Fin n → Bool) : Real :=
  by
    classical
    exact if 0 < fdTotal x b then
      (fdTotal x b : Real)⁻¹ ^ 2 *
        ∑ k, if fdUsable x b k then
          (fdGroupCount x k : Real) ^ 2 *
            ((fdArmCount x b true k : Real)⁻¹ +
              (fdArmCount x b false k : Real)⁻¹)
        else 0
    else 0

private def fdWeight (p : κ → Real) (x : Fin n → κ) (b : Fin n → Bool) : Real :=
  ∏ i, if b i then p (x i) else 1 - p (x i)

private noncomputable def fdOtherTotal (x : Fin n → κ) (b : Fin n → Bool) (k : κ) : Nat :=
  by
    classical
    exact ∑ l, if l ≠ k ∧ fdUsable x b l then fdGroupCount x l else 0

private noncomputable def fdLocalVariance
    (x : Fin n → κ) (b : Fin n → Bool) (k : κ) : Real :=
  by
    classical
    exact if fdUsable x b k then
      (fdGroupCount x k : Real) ^ 2 *
        (((fdOtherTotal x b k + fdGroupCount x k : Nat) : Real)⁻¹ ^ 2) *
        ((fdArmCount x b true k : Real)⁻¹ +
          (fdArmCount x b false k : Real)⁻¹)
    else 0

private noncomputable def fdLocalShare
    (x : Fin n → κ) (b : Fin n → Bool) (k : κ) : Real :=
  by
    classical
    exact if fdUsable x b k then
      (fdGroupCount x k : Real) *
        (((fdOtherTotal x b k + fdGroupCount x k : Nat) : Real)⁻¹ ^ 2)
    else 0

private def fdSplit (x : Fin n → κ) (k : κ) :
    (Fin n → Bool) ≃
      (({i : Fin n // x i = k} → Bool) × ({i : Fin n // x i ≠ k} → Bool)) where
  toFun b := (fun i => b i, fun i => b i)
  invFun bc := fun i => if h : x i = k then bc.1 ⟨i, h⟩ else bc.2 ⟨i, h⟩
  left_inv b := by
    funext i
    by_cases h : x i = k <;> simp [h]
  right_inv bc := by
    apply Prod.ext
    · funext i
      simp [i.2]
    · funext i
      simp [i.2]

private def fdDesignSplit :
    (Fin n → κ × Bool) ≃ ((Fin n → κ) × (Fin n → Bool)) where
  toFun d := (fun i => (d i).1, fun i => (d i).2)
  invFun xb := fun i => (xb.1 i, xb.2 i)
  left_inv d := by funext i; exact Prod.eta (d i)
  right_inv xb := rfl

end FiniteDesign

end Causalean.Stat
