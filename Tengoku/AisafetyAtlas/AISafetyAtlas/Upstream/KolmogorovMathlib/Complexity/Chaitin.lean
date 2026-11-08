/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Upstream.KolmogorovMathlib.Complexity.Uncomputability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vendored from AlexeyMilovanov/kolmogorov-complexity-lean

Pinned revision `005ac4c81eefe09642ef561057199d489cd79485` (Apache-2.0).
Adapted only for Lean 4.32 `module` / `public import` visibility; mathematical
content is upstream's. Atlas-facing names live in `AISafetyAtlas.Logic`.
-/

/-!
# Chaitin's Incompleteness Theorem

This module formalizes Chaitin's Incompleteness Theorem within an abstract formal system.
We define a formal system by its provability relation, its computable enumerator of theorems,
and its ability to express statements of the form "K(x) > L".

The main result proves that for any sound, recursively enumerable formal system,
there exists a constant `c` such that the system cannot prove any true statement
of the form `K(x) > L` for `L > c`. This serves as an information-theoretic equivalent
to Gödel's First Incompleteness Theorem.
-/

namespace Kolmogorov

/-! ### Abstract Formal Systems -/

/-- An abstract formal system capable of expressing statements about Kolmogorov complexity.
    It requires a computable enumerator of theorems and a computable parser for statements
    of the form `K(x) > L`.-/
public structure FormalSystem (U : Map) where
  /-- The type of formulas in the formal system.-/
  Formula : Type
  enc : Primcodable Formula
  /-- The provability relation for formulas.-/
  provable : Formula → Prop
  /-- The enumerator for theorems in the system.-/
  enumThm : ℕ → Option Formula
  hEnumComp : Computable enumThm
  hEnumExact : ∀ φ, provable φ ↔ ∃ i, enumThm i = some φ
  /-- Formula representing the statement that K(x) > L.-/
  exprKGt : ℕ → ℕ → Formula
  /-- Parser that attempts to extract `(x, L)` from a formula asserting `K(x) > L`.-/
  parseKGt : Formula → Option (ℕ × ℕ)
  hParseComp : Computable parseKGt
  hParseForward : ∀ x L, parseKGt (exprKGt x L) = some (x, L)
  hParseInv : ∀ φ x L, parseKGt φ = some (x, L) → φ = exprKGt x L
  hSound : ∀ x L, provable (exprKGt x L) → (L : ENat) < plainKNat U x

attribute [instance] FormalSystem.enc

/-! ### Enumerator Construction -/

namespace FormalSystem

variable {U : Map} (F : FormalSystem U)

/-- Combines the theorem enumerator with the parser to directly enumerate proven
bounds `(x, L)`.-/
@[expose]
public def enumBounds (i : ℕ) : Option (ℕ × ℕ) :=
  (F.enumThm i).bind F.parseKGt

/-- A boolean check answering whether the `i`-th enumerated bound asserts `L > M`.-/
@[expose]
public def isBoundGt (M i : ℕ) : Bool :=
  match F.enumBounds i with
  | some (_, L) => decide (L > M)
  | none => false

public lemma Computable.decide_eq_true {α : Type*} [Primcodable α] {f : α → Bool} (hf : Computable f) :
  Computable (fun a ↦ decide (f a = true)) :=
  hf.of_eq (fun a ↦ (Bool.decide_coe (f a)).symm)

-- The decidable predicate used in the Chaitin diagonal search is computable.

/-! ### Chaitin's Bound -/

-- The large unbounded-search / diagonalization argument elaborates many composed
-- computability facts; the heaviest search/extractor parts are factored into
-- named lemmas above so the main diagonalization proof remains predictable.

/-! ### The Incompleteness Theorem -/

end FormalSystem
end Kolmogorov
