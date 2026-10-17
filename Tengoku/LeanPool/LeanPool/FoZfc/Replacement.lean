/-
Copyright (c) 2026 Tetsuya Ishiu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Ishiu
-/
module

public import Tengoku.LeanPool.LeanPool.FoZfc.Axioms

/-!
# The Replacement Axiom

## Main Definitions

- A `FirstOrder.ZFC.RelByFormula` defines the relation defined by a formula.
- A `FirstOrder.ZFC.intIsFunctFormula` defines a formula for ϕ describes
  a function. A `FirstOrder.ZFC.EntIsFunctFormula` defines ϕ describes
  a function externally.
- A `FirstOrder.ZFC.intIsImage` defines the formula for fv 1 is the image of
  the function defined by ϕ of fv 0.
- A `FirstOrder.ZFC.ModelReplacement` is a class of models of Set Theory
  with the replacement schema.
- A `FirstOrder.ZFC.ModelZF` is a class of models of ZF.

## Main Statements

- Various "realize" theorems are proved.

-/

@[expose] public section
open scoped FirstOrder.ZFC


open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.BoundedFormula

open ReplaceFV
open ZFC
open FixedSnoc

universe u v

namespace FirstOrder.ZFC

variable {V : Type u}

/-- Make a formula for ϕ describes a function. -/
def intIsFunctFormula {n : ℕ} (ϕ : LZFC.BoundedFormula ℕ n) :
    LZFC.BoundedFormula ℕ n :=
  let ϕ' := liftAt 3 n ϕ
  let tsN1 := makeTsN ![bv'' n, bv'' (n+1)]
  let tsN2 := makeTsN ![bv'' n, bv'' (n+2)]
  (∀'∀'∀'(BoundedFormula.replaceFV ϕ' tsN1 ⟹
  BoundedFormula.replaceFV ϕ' tsN2 ⟹ bv'' (n+1) =' bv'' (n+2)))

/-- Find the (k+1)-ary relation defined by a formula. -/
def RelByFormula [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
    (ϕ : LZFC.BoundedFormula ℕ n) {k : ℕ} (xs1 : Fin (k + 1) → V) : Prop :=
  ϕ.Realize (replaceInitialValues s xs1) xs

/-- Dexcribe ϕ describes a function. -/
def ExtIsFunctFormula [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
    (ϕ : LZFC.BoundedFormula ℕ n) : Prop :=
  let R : (Fin 2 → V) → Prop := RelByFormula s xs ϕ
  ∀ (x : V) (y₁ : V) (y₂ : V), (R ![x, y₁] → R ![x, y₂] → y₁ = y₂)

/-- Make a formula for fv 1 is the image of fv 0 under the relation defined by ϕ. -/
def intIsImage {n : ℕ} (ϕ : LZFC.BoundedFormula ℕ n) :
    LZFC.BoundedFormula ℕ n := (∀'(bv'' n ∈' fv (n+1) 1 ⇔
    ∃'((bv'' (n+1)) ∈' fv' 0 ∧' (BoundedFormula.replaceFV (liftAt 2 n ϕ)
    (makeTsN ![bv'' (n+1), bv'' n])))))

/-- Describe b is the image of a under the relation defined by ϕ. -/
def ExtIsImage [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
    (ϕ : LZFC.BoundedFormula ℕ n) (a b : V) := ∀ (y : V),
  (y ∈ b ↔ ∃ (x : V), x ∈ a ∧ ϕ.Realize (replaceInitialValues s ![x, y]) xs)

/-- `replaceInitialValues` composed with a larger replacement collapses.
@isnad1 id=eq.1h6v.s6.6cd00633d21a from=translated src=- shape=4b6e2c59 vocab=7502b714
-/
@[simp]
theorem replaceInitialValues_replaceInitialValues {n m : ℕ} {h : n ≤ m}
    {s : ℕ → V} {xs1 : Fin (n + 1) → V} {xs2 : Fin (m + 1) → V} :
    replaceInitialValues (replaceInitialValues s xs1) xs2 =
    replaceInitialValues s xs2 := by
  funext k
  unfold replaceInitialValues
  by_cases h_k_le_m : k < m + 1
  · rw [ite_eq_left h_k_le_m, ite_eq_left h_k_le_m]
  · rw [ite_eq_right h_k_le_m, ite_eq_right (by omega : ¬ k < n + 1), ite_eq_right h_k_le_m]

/-- Model with the Replacement schema. -/
class ModelReplacement (V : Type u) extends ModelSets V where
  /-- The model satisfies the replacement schema. -/
  replacement_schema : ∀ {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
    (ϕ : LZFC.BoundedFormula ℕ n), (intIsFunctFormula ϕ ⟹
    ∀'∃'(BoundedFormula.replaceFV (liftAt 2 n (intIsImage ϕ))
    (makeTsN ![bv'' n, bv'' (n+1)]))).Realize s xs

/-- Model with pairing and replacement. -/
class ModelPR (V : Type u) extends ModelPairing V, ModelReplacement V

/-- Model of ZF: all the standard axioms together. -/
class ModelZF (V : Type u) extends ModelEmptyset V, ModelPairing V,
    ModelUnion V, ModelPowerset V, ModelInfinity V, ModelRegularity V,
    ModelComprehension V, ModelReplacement V

end FirstOrder.ZFC
