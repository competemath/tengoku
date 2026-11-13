/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Tengoku.Seed.Logic.Equiv.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Comonads

This file defines the `Comonad` typeclass hierarchy, dual to `Monad`.

It follows the structure of the `Monad` hierarchy:
`Extract` (`pure`), `Extend` (`bind`), `Coseq` (`seq`),
`Coapplicative` (`Applicative`), `Comonad` (`Monad`).

## Hierarchy

* `Extract (w)`: Provides `extract : w α → α`.
* `Extend (w)`: Provides `extend : w α → (w α → β) → w β`.
* `Coseq (w)`: Provides `coseq : w α → w β → w (α × β)` (operator `<@>`).
* `CoseqLeft (w)`: Provides `coseqLeft : w α → w β → w α` (operator `<@`).
* `CoseqRight (w)`: Provides `coseqRight : w α → w β → w β` (operator `@>`).
* `Coapplicative (w)`: Extends `Functor`, `Extract`, `Coseq`, `CoseqLeft`, `CoseqRight`.
* `Comonad (w)`: Extends `Coapplicative`, `Extend`. Provides default `map`.
* `Lawful` variants mirroring `LawfulFunctor`, `LawfulApplicative`, `LawfulMonad`.

-/

@[expose] public section
namespace Tengoku.Polyfun end Tengoku.Polyfun open Tengoku.Polyfun 
universe u v

/-- The `Extract` typeclass provides the `extract` operation, dual to `Pure.pure`.-/
class _root_.Tengoku.Polyfun.Extract (w : Type u → Type v) where
  /-- Extract a value from the comonadic context.-/
  extract {α : Type u} : w α → α

/-- The `Extend` typeclass provides the `extend` operation, dual to `Bind.bind`.-/
class _root_.Tengoku.Polyfun.Extend (w : Type u → Type v) where
  /-- Extend a function across the comonadic context.-/
  extend {α β : Type u} : w α → (w α → β) → w β

/-- The `Coseq` typeclass provides the `coseq` operation (`<@>`), dual to `Seq.seq` (`<*>`).
    It combines two comonadic contexts, pairing their results.-/
class _root_.Tengoku.Polyfun.Coseq (w : Type u → Type v) where
  /-- Combine two comonadic contexts.-/
  coseq : {α β : Type u} → w α → w β → w (α × β)

/-- The `CoseqLeft` typeclass provides the `coseqLeft` operation (`<@`), dual to `SeqLeft.seqLeft`
  (`<*`). Evaluates two contexts but returns the result of the first.-/
class _root_.Tengoku.Polyfun.CoseqLeft (w : Type u → Type v) where
  /-- Evaluate two contexts, returning the first result.-/
  coseqLeft : {α β : Type u} → w α → w β → w α

/-- The `CoseqRight` typeclass provides the `coseqRight` operation (`@>`), dual to
  `SeqRight.seqRight` (`*>`). Evaluates two contexts but returns the result of the second.-/
class _root_.Tengoku.Polyfun.CoseqRight (w : Type u → Type v) where
  /-- Evaluate two contexts, returning the second result.-/
  coseqRight : {α β : Type u} → w α → w β → w β

export Extract (extract)
export Extend (extend)
export Coseq (coseq)
export CoseqLeft (coseqLeft)
export CoseqRight (coseqRight)

/-- Cosequencing `Coseq.coseq`, pairing two comonadic contexts.-/
local infixl:60 " <@> " => Coseq.coseq
/-- Left cosequencing `CoseqLeft.coseqLeft`, keeping the left context's result.-/
local infixl:60 " <@ "  => CoseqLeft.coseqLeft
/-- Right cosequencing `CoseqRight.coseqRight`, keeping the right context's result.-/
local infixl:60 " @> "  => CoseqRight.coseqRight

/-- `Coapplicative` functor. Dual to `Applicative`.
    Combines `Functor`, `Extract`, and `Coseq` operations.-/
class _root_.Tengoku.Polyfun.Coapplicative (w : Type u → Type v) extends
    Functor w, Extract w, Coseq w, CoseqLeft w, CoseqRight w where
  /-- Default implementation for `coseqLeft` using `coseq` and `map`.-/
  coseqLeft wa wb := Functor.map Prod.fst (coseq wa wb)
  /-- Default implementation for `coseqRight` using `coseq` and `map`.-/
  coseqRight wa wb := Functor.map Prod.snd (coseq wa wb)

/-- `Comonad`. Dual to `Monad`.
    Combines `Coapplicative` structure with `Extend`.-/
class _root_.Tengoku.Polyfun.Comonad (w : Type u → Type v) extends Coapplicative w, Extend w where
  /-- Default implementation for `map` using `extend` and `extract`.
      Note: This requires that the `Functor` instance provided to `Coapplicative`
      is compatible with this definition. `LawfulComonad` ensures this.-/
  map f wa := extend wa (f ∘ extract)
  /-- Default `coseq` built only from `extend` and `extract`.

      For two contexts `wa : w α`, `wb : w β` we:
      1. `extend` over the first context, so we may look inside it,
      2. pair its extracted value with the *already* extracted value of `wb`.

      This yields `w (α × β)` as required.-/
  coseq wa wb := extend wa (fun wa' => (extract wa', extract wb))

/-! ## Lawful hierarchy -/

/-- Lawful `Coapplicative` functor. Dual to `LawfulApplicative`.-/
class _root_.Tengoku.Polyfun.LawfulCoapplicative (w : Type u → Type v) [Coapplicative w] extends LawfulFunctor w where
  /-- Ensure default `coseqLeft` law holds even if overridden.-/
  coseqLeft_eq : ∀ {α β : Type u} (wa : w α) (wb : w β),
    @coseqLeft w _ α β wa wb = Functor.map (@Prod.fst α β) (coseq wa wb)
  /-- Ensure default `coseqRight` law holds even if overridden.-/
  coseqRight_eq : ∀ {α β : Type u} (wa : w α) (wb : w β),
    coseqRight wa wb = Functor.map (@Prod.snd α β) (coseq wa wb)
  /-- Associativity law for `coseq`. `assoc` maps `(α × β) × γ` to `α × (β × γ)`.-/
  coseq_assoc : ∀ {α β γ : Type u} (wa : w α) (wb : w β) (wc : w γ),
    Functor.map (Equiv.prodAssoc α β γ) (coseq (coseq wa wb) wc) = coseq wa (coseq wb wc)
  /-- Naturality of `coseq` in both arguments.-/
  map_coseq : ∀ {α β α' β' : Type u} (f : α → α') (g : β → β')
    (wa : w α) (wb : w β),
    Functor.map (fun p : α × β => (f p.1, g p.2)) (coseq wa wb) =
      coseq (Functor.map f wa) (Functor.map g wb)
  -- Other potential laws like extract_coseq : extract (wa <@> wb) = (extract wa, extract wb)
  -- are often added but require `w (α × β)` structure, so omitted here for generality.

export LawfulCoapplicative (coseqLeft_eq coseqRight_eq coseq_assoc map_coseq)

/-- Lawful `Comonad`. Dual to `LawfulMonad`.-/
class _root_.Tengoku.Polyfun.LawfulComonad (w : Type u → Type v) [Comonad w] extends LawfulCoapplicative w where
  /-- Compatibility between `map` and `extend`/`extract`.
      Since `Comonad.map` defines map this way, this law ensures the `Functor` instance
      used by `LawfulCoapplicative` (and `LawfulFunctor`) is consistent.-/
  map_eq_extend_extract : ∀ {α β : Type u} (f : α → β) (wa : w α),
    Functor.map f wa = extend wa (f ∘ extract)
  /-- Extending with `extract` is the identity (Left identity dual).-/
  extend_extract : ∀ {α : Type u} (wa : w α), extend wa (@extract w _ α) = wa
  /-- Extracting after extending yields the original function application (Right identity dual).-/
  extract_extend : ∀ {α β : Type u} (wa : w α) (f : w α → β),
    extract (extend wa f) = f wa
  /-- Extend is associative (Associativity dual).-/
  extend_assoc : ∀ {α β γ : Type u} (wa : w α) (f : w α → β) (g : w β → γ),
    extend (extend wa f) g = extend wa (fun w'a => g (extend w'a f))

export LawfulComonad (map_eq_extend_extract extend_extract extract_extend extend_assoc)

/-! ## Theorems derived from lawful classes -/

section LawfulnessProofs
variable {w : Type u → Type v} [Comonad w] [LawfulComonad w]

/--
@isnad1 id=eq.0h3v.s5.d67b199c1249 from=translated src=- shape=bd69cac0 vocab=70711cd9
-/
theorem _root_.Tengoku.Polyfun.comonad_id_map {α : Type u} (wa : w α) : Functor.map id wa = wa :=
  id_map wa

/--
@isnad1 id=eq.0h7v.s6.209b85560f16 from=translated src=- shape=086d07bd vocab=a1ec3c10
-/
@[simp] theorem _root_.Tengoku.Polyfun.comonad_comp_map {α β γ : Type u} (f : β → γ) (g : α → β) (wa : w α) :
    Functor.map (f ∘ g) wa = Functor.map f (Functor.map g wa) :=
  comp_map g f wa

/--
@isnad1 id=eq.0h5v.s5.521f9d4a7acb from=translated src=- shape=4278d538 vocab=d59eb031
-/
@[simp] theorem _root_.Tengoku.Polyfun.extract_map {α β : Type u} (f : α → β) (wa : w α) :
    extract (Functor.map f wa) = f (extract wa) := by
  rw [map_eq_extend_extract, extract_extend, Function.comp_apply]

end LawfulnessProofs

/-! ## Duplicate and derived laws

These require `w : Type u → Type u`, so the comonadic context can be nested. -/

section Duplicate
variable {w : Type u → Type u} [Comonad w]

/-- Duplicate the comonadic context. Defined via `extend`.-/
@[simp]
def _root_.Tengoku.Polyfun.duplicate {α : Type u} (wa : w α) : w (w α) :=
  extend wa id

variable [LawfulComonad w]
variable {α : Type u} (wa : w α)

/--
@isnad1 id=eq.0h3v.s5.1cc7ea424af8 from=translated src=- shape=062c1ca2 vocab=43405045
-/
theorem _root_.Tengoku.Polyfun.extract_duplicate_eq_id : extract (duplicate wa) = wa :=
  extract_extend wa id

/--
@isnad1 id=eq.0h3v.s5.d15459464527 from=translated src=- shape=7d1b4b08 vocab=4582cb8e
-/
theorem _root_.Tengoku.Polyfun.map_extract_duplicate_eq_id : Functor.map extract (duplicate wa) = wa := by
  rw [duplicate, map_eq_extend_extract, extend_assoc]
  simp only [Function.comp_apply, extract_extend, id_def]
  rw [extend_extract]

/--
@isnad1 id=eq.0h5v.s5.8456d9130076 from=translated src=- shape=01bbb692 vocab=d3c048f9
-/
theorem _root_.Tengoku.Polyfun.extend_eq_map_duplicate {β : Type u} (f : w α → β) :
    extend wa f = Functor.map f (duplicate wa) := by
  rw [duplicate, map_eq_extend_extract, extend_assoc]
  simp only [Function.comp_apply, extract_extend, id_def]

/--
@isnad1 id=eq.0h3v.s5.d1d567e489b7 from=translated src=- shape=37531ff2 vocab=7083df5b
-/
theorem _root_.Tengoku.Polyfun.duplicate_duplicate_eq_map_duplicate :
    duplicate (duplicate wa) = Functor.map duplicate (duplicate wa) := by
  have h_lhs : duplicate (duplicate wa) = extend wa duplicate := by
    rw [duplicate, duplicate, extend_assoc]
    simp only [id_def]
    rfl
  have h_rhs : Functor.map duplicate (duplicate wa) = extend wa duplicate := by
    rw [duplicate, map_eq_extend_extract, extend_assoc]
    simp only [Function.comp_apply, extract_extend, id_def]
  rw [h_lhs, h_rhs]

end Duplicate
-- Tengoku: 3 notation(s) of this module made local so they do not change other libraries (generated)
-- Tengoku: root names of this library moved to Tengoku.Polyfun so they do not collide with other libraries (generated)
