/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.GeneratedCode
import Tengoku.Seed.MeasureTheory.MeasurableSpace.Card

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Construction rank of generated codes

This file assigns a countable ordinal rank to each concrete `GeneratedCode`. Basic and empty codes
have rank zero, complementation takes a successor, and a countable union has rank equal to the least
strict upper bound of the ranks of its children.

The result is a *construction rank*: it measures the syntax tree of one particular code. It is not
the minimum Borel rank of the set denoted by that code. The semantic theorem in this file is only an
upper bound, placing the interpretation in mathlib's `generateMeasurableRec` at the construction
rank.

The return type is explicitly `Ordinal.{0}`. Thus the rank is independent of the universes of the
underlying space and generating family.
-/

open Cardinal MeasurableSpace Ordinal Set

universe u v

namespace DescriptiveSetTheory

variable {X : Type u} {ι : Type v} {g : ι → Set X}

namespace GeneratedCode

/-- The ordinal construction rank of a concrete generated code.-/
noncomputable def constructionRank : GeneratedCode g → Ordinal.{0}
  | .basic _ => 0
  | .empty => 0
  | .compl c => constructionRank c + 1
  | .iUnion c => ⨆ n, constructionRank (c n) + 1

/-- A basic code has construction rank zero.-/
@[simp] theorem constructionRank_basic (i : ι) :
    constructionRank (.basic i : GeneratedCode g) = 0 := rfl

/-- The empty code has construction rank zero.-/
@[simp] theorem constructionRank_empty :
    constructionRank (.empty : GeneratedCode g) = 0 := rfl

/-- Complementation raises construction rank by one.-/
@[simp] theorem constructionRank_compl (c : GeneratedCode g) :
    constructionRank (.compl c) = constructionRank c + 1 := rfl

/-- The rank of a countable-union code is the least strict upper bound of its child ranks.-/
@[simp] theorem constructionRank_iUnion (c : ℕ → GeneratedCode g) :
    constructionRank (.iUnion c) = ⨆ n, constructionRank (c n) + 1 := rfl

/-- Every child has strictly smaller rank than the countable-union code containing it.-/
theorem constructionRank_lt_iUnion (c : ℕ → GeneratedCode g) (n : ℕ) :
    constructionRank (c n) < constructionRank (.iUnion c) :=
  Ordinal.lt_iSup_add_one (fun n => constructionRank (c n)) n

/-- The construction rank of every generated code is a countable ordinal.-/
theorem constructionRank_lt_omega_one (c : GeneratedCode g) : constructionRank c < ω₁ := by
  induction c with
  | basic i => exact omega_pos 1
  | empty => exact omega_pos 1
  | compl c ih => exact (isSuccLimit_omega 1).succ_lt ih
  | iUnion c ih =>
      apply Ordinal.iSup_lt_omega_one
      intro n
      exact (isSuccLimit_omega 1).succ_lt (ih n)

/-- A code's interpretation appears by its construction rank in mathlib's transfinite generator.-/
theorem eval_mem_generateMeasurableRec (c : GeneratedCode g) :
    c.eval ∈ generateMeasurableRec (range g) c.constructionRank := by
  induction c with
  | basic i => exact self_subset_generateMeasurableRec (range g) 0 ⟨i, rfl⟩
  | empty => exact empty_mem_generateMeasurableRec (range g) 0
  | compl c ih => exact compl_mem_generateMeasurableRec (lt_add_one _) ih
  | iUnion c ih =>
      exact iUnion_mem_generateMeasurableRec fun n =>
        ⟨constructionRank (c n), constructionRank_lt_iUnion c n, ih n⟩

end GeneratedCode
end DescriptiveSetTheory
