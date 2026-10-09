/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku.Complexitylib.Complexitylib.Cslib.Circuit.Boolean.Complexity
public import Tengoku

/-!
# Shared pattern tables

A Boolean matrix is synthesized by sharing its column patterns across rows.
The leading cost is one OR per selected pattern; input tests and the pattern
bank are built only once. This is the elementary table construction used in
the sparse and partial-function specializations of local coding.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open scoped BigOperators

/-- Binary numbering of all assignments to `width` input bits. -/
def assignmentIndex (width : ℕ) : (Fin width → Bool) ≃ Fin (2 ^ width) :=
  (Equiv.arrowCongr (Equiv.refl (Fin width)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- Column index selected by the first `k` input bits. -/
def columnAt {k l : ℕ} (x : Fin (k + l) → Bool) : Fin (2 ^ k) :=
  assignmentIndex k (fun i => x (Fin.castAdd l i))

/-- Row index selected by the remaining `l` input bits. -/
def rowAt {k l : ℕ} (x : Fin (k + l) → Bool) : Fin (2 ^ l) :=
  assignmentIndex l (fun i => x (Fin.natAdd k i))

/-- Reconstruct an input from its row and column indices. -/
def matrixInput {k l : ℕ} (row : Fin (2 ^ l)) (column : Fin (2 ^ k)) :
    Fin (k + l) → Bool :=
  Fin.append ((assignmentIndex k).symm column) ((assignmentIndex l).symm row)

@[simp] theorem columnAt_matrixInput {k l : ℕ} (r : Fin (2 ^ l)) (c : Fin (2 ^ k)) :
    columnAt (matrixInput r c) = c := by simp [columnAt, matrixInput]

@[simp] theorem rowAt_matrixInput {k l : ℕ} (r : Fin (2 ^ l)) (c : Fin (2 ^ k)) :
    rowAt (matrixInput r c) = r := by simp [rowAt, matrixInput]

@[simp] theorem matrixInput_rowAt_columnAt {k l : ℕ} (x : Fin (k + l) → Bool) :
    matrixInput (rowAt x) (columnAt x) = x := by
  simp [matrixInput, rowAt, columnAt, Fin.append_castAdd_natAdd]

/-- The truth-table indexing equivalence used to sum support sizes over rows. -/
def matrixEquiv (k l : ℕ) : (Fin (k + l) → Bool) ≃ Fin (2 ^ l) × Fin (2 ^ k) where
  toFun x := (rowAt x, columnAt x)
  invFun rc := matrixInput rc.1 rc.2
  left_inv := matrixInput_rowAt_columnAt
  right_inv rc := by simp

/-- Columns of one row whose corresponding inputs belong to the domain. -/
def rowDomain {k l : ℕ} (domain : Finset (Fin (k + l) → Bool)) (r : Fin (2 ^ l)) :
    Finset (Fin (2 ^ k)) :=
  Finset.univ.filter fun c => matrixInput r c ∈ domain

theorem sum_rowDomain_card {k l : ℕ} (domain : Finset (Fin (k + l) → Bool)) :
    ∑ r, (rowDomain domain r).card = domain.card := by
  classical
  have h := Fintype.sum_equiv (matrixEquiv k l)
    (fun x => if x ∈ domain then (1 : ℕ) else 0)
    (fun rc => if matrixInput rc.1 rc.2 ∈ domain then 1 else 0)
    (fun x => by simp [matrixEquiv])
  calc
    _ = ∑ rc : Fin (2 ^ l) × Fin (2 ^ k),
        if matrixInput rc.1 rc.2 ∈ domain then (1 : ℕ) else 0 := by
      simp only [rowDomain, Finset.card_eq_sum_ones, Finset.sum_filter,
        Fintype.sum_prod_type]
    _ = ∑ x, if x ∈ domain then (1 : ℕ) else 0 := h.symm
    _ = domain.card := by simp

/-- Shared equality tests for every column and row index. -/
def matrixMinterm {k l : ℕ} : Fin (2 ^ k) ⊕ Fin (2 ^ l) → BooleanFunction (k + l)
  | .inl c => fun x => decide (columnAt x = c)
  | .inr r => fun x => decide (rowAt x = r)

end Complexity.CircuitSparseSynthesis.Internal
