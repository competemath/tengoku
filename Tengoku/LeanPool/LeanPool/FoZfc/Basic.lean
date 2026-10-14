/-
Copyright (c) 2026 Tetsuya Ishiu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Ishiu
-/
module

public import Tengoku

/-!
# The Basics of First Order Language of ZFC set theory

## Main Definitions

- A `FirstOrder.Language.LZFC` defines the language of ZFC set theory.
  It consists only of the binary relation ∈'.
- A `FirstOrder.ZFC.fv'` defines the free variable with index k.
  The first argument is implicitly determined.
- A `FirstOrder.ZFC.bv'` defines the bounded variable with index (k : Fin n).
  The first argument is implicitly determined.
- A `FirstOrder.ZFC.bv''` defines the bounded variable with index (k : ℕ).
  The first argument is implicitly determined.
- A `FirsOrder.ZFC.ModelSets` is a class of models of set theory.

## Notations

- ∈' is the symbol to mean "is an element of".
- ∉' is the symbol to mean "is not an element of".
- ≠' is the symbol to mean "is not equal to".
  Recall that =' is defined as FirstOrder.Language.Term.bdEqual.
- ∈ is the actual relation to mean "is an element of".
- ∉ is the actual relation to mean "is not an element of".

## Implimentation notes

- Most of the relations have the theorems named "realize_*".
  They prove the relationship between the internal and external expressions.

-/

@[expose] public section

namespace FirstOrder
open FirstOrder.Language
open FirstOrder.Language.BoundedFormula

-- u for universe, v for free variable indexes
universe u v

/-- Relation symbols for LSet. -/
inductive LSetRel : ℕ → Type
| isEltOf : LSetRel 2
deriving DecidableEq

-- Instead of defining Relations n for each n,
-- define the entire Relations
namespace Language

/-- Language of Set Theory. -/
def LZFC : Language :=
{
  Functions := fun _ => Empty
  Relations := LSetRel
}

end Language

namespace ZFC

variable {V : Type u} [Language.LZFC.Structure V]

/-- The version of isEltOf with the type LSet.Relations 2. -/
def isEltOfTwo : Language.LZFC.Relations 2 := LSetRel.isEltOf

-- Language.BoundedFormula.falsum is the bot.
/-- The formula ⊥ -/
def ϕbot : Language.LZFC.Formula  ℕ:= Language.BoundedFormula.falsum

/-- Make an atomic formula t1 ∈ t2. -/
def ϕelt {n : ℕ} (t₁ t₂ : Language.LZFC.Term (ℕ ⊕ Fin n)) :=
  Language.Relations.boundedFormula₂ isEltOfTwo t₁ t₂

-- I added ' to distinguish the outside and inside ∈
@[inherit_doc] scoped[FirstOrder] infixl : 120 " ∈' " => FirstOrder.ZFC.ϕelt

/-- Make an atomic formula t1 ∉ t2. -/
def ϕnotElt {n : ℕ} (t₁ t₂ : Language.LZFC.Term (ℕ ⊕ Fin n)) :=
  ∼(Language.Relations.boundedFormula₂ isEltOfTwo t₁ t₂)

@[inherit_doc] scoped[FirstOrder] infixl : 120 " ∉' " => FirstOrder.ZFC.ϕnotElt

/-- The negation of the equality of two terms as a bounded formula. -/
def intNotEqual {n : ℕ} (t₁ t₂ : Language.LZFC.Term (ℕ ⊕ Fin n)) :=
    ∼(FirstOrder.Language.Term.bdEqual t₁ t₂)

@[inherit_doc] scoped[FirstOrder] infixl: 88 " ≠' " => FirstOrder.ZFC.intNotEqual

/-- Make a free variable in LSet. -/
def fv (n : ℕ) (k : ℕ) : Language.LZFC.Term (ℕ ⊕ Fin n) := Language.Term.var (Sum.inl k)

/-- Make a to-be bounded variable indexed by k, in which free variables are indexed by ℕ. -/
def bv (n : ℕ) (k : Fin n) : Language.LZFC.Term (ℕ ⊕ Fin n) := Language.Term.var (Sum.inr k)

/-- Model of set theory. -/
class ModelSets (V : Type u) extends LZFC.Structure V, Inhabited V where
  /-- The external membership relation interpreting the language's ∈ symbol. -/
  isEltOf : V → V → Prop
  /-- The external relation matches the language's `RelMap`. -/
  interpret_is_elt_of : ∀ {a b : V}, isEltOf a b ↔ RelMap isEltOfTwo ![a, b]
  /-- Extensionality: sets with the same elements are equal. -/
  extensionality : ∀ {a b : V}, (∀(z : V), (isEltOf z a) ↔ isEltOf z b) → a = b

variable {V : Type u}

/-- The negation of `ModelSets.isEltOf`. -/
def notIsEltOf [ModelSets V] (a b : V) : Prop :=
  ¬ (ModelSets.isEltOf a b)

@[inherit_doc ModelSets.isEltOf] infix : 120 " ∈ " => ModelSets.isEltOf
@[inherit_doc notIsEltOf] infix : 120 " ∉ " => notIsEltOf

/-- Realize a free varaible.
@isnad1 id=eq.0h5v.s5.e21bbe2014a0 from=translated src=- shape=222569a3 vocab=da9bec93
-/
@[simp]
theorem realize_fv [ModelSets V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V} (k : ℕ) :
    Language.Term.realize (Sum.elim s xs) (fv n k) = s k := by
  exact rfl

/-- Realize a bounded variable with the type ℕ.
@isnad1 id=eq.0h5v.s5.acd43fc86b72 from=translated src=- shape=316dda68 vocab=b5192ebd
-/
@[simp]
theorem realize_bv [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V) (k : Fin n) :
    Language.Term.realize (Sum.elim s xs) (bv n k) = xs k := by
  simp [bv]

/--
@isnad1 id=iff.0h6v.s6.2389696d6220 from=translated src=- shape=d254951d vocab=0e43a598
-/
@[simp]
theorem realize_in [ModelSets V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V}
    {t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)} :
    (t₁∈'t₂).Realize s xs ↔
      Term.realize (Sum.elim s xs) t₁ ∈ Term.realize (Sum.elim s xs) t₂ := by
  rw [ModelSets.interpret_is_elt_of]
  apply realize_rel₂

/--
@isnad1 id=iff.0h6v.s6.59d50646ed13 from=translated src=- shape=d254951d vocab=907ca2e2
-/
@[simp]
theorem realize_nin [ModelSets V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V}
    {t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)} :
    (t₁∉'t₂).Realize s xs ↔
      Term.realize (Sum.elim s xs) t₁ ∉ Term.realize (Sum.elim s xs) t₂ := by
  apply not_congr realize_in

/--
@isnad1 id=iff.0h6v.s6.905bf376573e from=translated src=- shape=d254951d vocab=20d3ff78
-/
@[simp]
theorem realize_neq [ModelSets V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V}
    {t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)} :
    (t₁≠'t₂).Realize s xs ↔
      Term.realize (Sum.elim s xs) t₁ ≠ Term.realize (Sum.elim s xs) t₂ := by
  simp [intNotEqual]

/-- Make a free variable in LSet with n implicit. -/
def fv' {n : ℕ} (k : ℕ) : Language.LZFC.Term (ℕ ⊕ Fin n) := Language.Term.var (Sum.inl k)

/-- Make a to-be bounded variable indexed by (k : Fin n),
  in which free variables are indexed by ℕ with n implicit. -/
def bv' {n : ℕ} (k : Fin n) : Language.LZFC.Term (ℕ ⊕ Fin n) := Language.Term.var (Sum.inr k)

/-- Make a to-be bounded variable indexed by (k : ℕ),
  in which free variables are indexed by ℕ with n implicit. -/
def bv'' {n : ℕ} [NeZero n] (k : ℕ) : Language.LZFC.Term (ℕ ⊕ Fin n) :=
    Language.Term.var (Sum.inr (Fin.ofNat n k))

/-- Realize a free varaible.
@isnad1 id=eq.0h5v.s5.dd6d159e7cd3 from=translated src=- shape=222569a3 vocab=60b4007d
-/
@[simp]
theorem realize_fv' [ModelSets V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V} (k : ℕ) :
    Language.Term.realize (Sum.elim s xs) (fv' k) = s k := by
  exact rfl

/-- Realize bv' with the type ℕ.
@isnad1 id=eq.0h5v.s5.9feed7891a55 from=translated src=- shape=316dda68 vocab=c95a12c8
-/
@[simp]
theorem realize_bv' [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V) (k : Fin n) :
    Language.Term.realize (Sum.elim s xs) (bv' k) = xs k := by
  simp [bv']

/-- Realize bv'' with the type ℕ.
@isnad1 id=eq.0h5v.s5.c940524acfbe from=translated src=- shape=a0cce457 vocab=7875a644
-/
@[simp]
theorem realize_bv'' [ModelSets V] {n : ℕ} [NeZero n] (s : ℕ → V) (xs : Fin n → V) (k : ℕ) :
    Language.Term.realize (Sum.elim s xs) (bv'' k) = xs (Fin.ofNat n k) := by
  simp [bv'']

end ZFC
end FirstOrder
