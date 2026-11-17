/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.GeneratedCode
import Tengoku.Seed.MeasureTheory.Constructions.BorelSpace.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Borel codes

This file specializes `DescriptiveSetTheory.GeneratedCode` to the family of all open sets. The
resulting `BorelCode` API is independent of any ambient measurable-space instance.
-/

open MeasurableSpace Set

universe u v

namespace DescriptiveSetTheory

/-- The family of all open subsets of a topological space.-/
def openGenerator (X : Type u) [TopologicalSpace X] : {s : Set X // IsOpen s} → Set X := (↑)

/-- The range of `openGenerator` is precisely the collection of open sets.-/
@[simp] theorem range_openGenerator (X : Type u) [TopologicalSpace X] :
    range (openGenerator X) = {s : Set X | IsOpen s} := by
  ext s
  simp [openGenerator]

/-- A Borel code is a generated code whose basic sets are all open subsets of `X`.-/
abbrev BorelCode (X : Type u) [TopologicalSpace X] := GeneratedCode (openGenerator X)

namespace BorelCode

variable {X : Type u} [TopologicalSpace X]

/-- A code for an open set.-/
def basic (s : Set X) (hs : IsOpen s) : BorelCode X := GeneratedCode.basic ⟨s, hs⟩

/-- A code for the empty set.-/
def empty : BorelCode X := GeneratedCode.empty

/-- The complement of a Borel code.-/
def compl (c : BorelCode X) : BorelCode X := GeneratedCode.compl c

/-- A countable union of Borel codes.-/
def iUnion (c : ℕ → BorelCode X) : BorelCode X := GeneratedCode.iUnion c

/-- Interpret a Borel code as a subset of its topological space.-/
def eval (c : BorelCode X) : Set X := GeneratedCode.eval c

/-- The interpretation of a basic Borel code is its open set.-/
@[simp] theorem eval_basic (s : Set X) (hs : IsOpen s) : eval (basic s hs) = s := rfl

/-- The interpretation of the empty Borel code is the empty set.-/
@[simp] theorem eval_empty : eval (empty : BorelCode X) = ∅ := rfl

/-- Interpretation commutes with complement.-/
@[simp] theorem eval_compl (c : BorelCode X) : eval (compl c) = (eval c)ᶜ := rfl

/-- Interpretation commutes with countable union.-/
@[simp] theorem eval_iUnion (c : ℕ → BorelCode X) : eval (iUnion c) = ⋃ n, eval (c n) := rfl

/-- A code for the union of two Borel sets.-/
def union (c d : BorelCode X) : BorelCode X := GeneratedCode.union c d

/-- Interpretation commutes with binary union.-/
@[simp] theorem eval_union (c d : BorelCode X) : eval (union c d) = eval c ∪ eval d := by
  change GeneratedCode.eval (GeneratedCode.union c d) =
    GeneratedCode.eval c ∪ GeneratedCode.eval d
  exact GeneratedCode.eval_union c d

/-- A code for the intersection of two Borel sets.-/
def inter (c d : BorelCode X) : BorelCode X := GeneratedCode.inter c d

/-- Interpretation commutes with binary intersection.-/
@[simp] theorem eval_inter (c d : BorelCode X) : eval (inter c d) = eval c ∩ eval d := by
  change GeneratedCode.eval (GeneratedCode.inter c d) =
    GeneratedCode.eval c ∩ GeneratedCode.eval d
  exact GeneratedCode.eval_inter c d

/-- A code for the difference of two Borel sets.-/
def diff (c d : BorelCode X) : BorelCode X := GeneratedCode.diff c d

/-- Interpretation commutes with set difference.-/
@[simp] theorem eval_diff (c d : BorelCode X) : eval (diff c d) = eval c \ eval d := by
  change GeneratedCode.eval (GeneratedCode.diff c d) =
    GeneratedCode.eval c \ GeneratedCode.eval d
  exact GeneratedCode.eval_diff c d

/-- A code for a countable intersection of Borel sets.-/
def iInter (c : ℕ → BorelCode X) : BorelCode X := GeneratedCode.iInter c

/-- Interpretation commutes with countable intersection.-/
@[simp] theorem eval_iInter (c : ℕ → BorelCode X) : eval (iInter c) = ⋂ n, eval (c n) := by
  change GeneratedCode.eval (GeneratedCode.iInter c) = ⋂ n, GeneratedCode.eval (c n)
  exact GeneratedCode.eval_iInter c

/-- Semantic equivalence of Borel codes is equality of interpretations.-/
theorem equiv_iff (c d : BorelCode X) : c ≈ d ↔ eval c = eval d := Iff.rfl

/-- Pull a Borel code back along a continuous map.-/
def comap {Y : Type v} [TopologicalSpace Y] (f : X → Y) (hf : Continuous f) :
    BorelCode Y → BorelCode X
  | GeneratedCode.basic U =>
      BorelCode.basic (X := X) (f ⁻¹' (U : Set Y)) (U.property.preimage hf)
  | GeneratedCode.empty => BorelCode.empty
  | GeneratedCode.compl c => BorelCode.compl (comap f hf c)
  | GeneratedCode.iUnion c => BorelCode.iUnion fun n => comap f hf (c n)

/-- Interpretation of `comap` is set-theoretic preimage.-/
@[simp] theorem eval_comap {Y : Type v} [TopologicalSpace Y] (f : X → Y) (hf : Continuous f)
    (c : BorelCode Y) : eval (comap f hf c) = f ⁻¹' eval c := by
  induction c with
  | basic U => rfl
  | empty => rfl
  | compl c ih =>
      change (GeneratedCode.eval (comap f hf c))ᶜ = f ⁻¹' (GeneratedCode.eval c)ᶜ
      rw [preimage_compl]
      exact congrArg (fun s : Set X => sᶜ) ih
  | iUnion c ih =>
      change (⋃ n, GeneratedCode.eval (comap f hf (c n))) =
        f ⁻¹' ⋃ n, GeneratedCode.eval (c n)
      rw [preimage_iUnion]
      exact iUnion_congr ih

/-- Every Borel code denotes a set measurable in the Borel measurable space.-/
theorem measurableSet_eval (c : BorelCode X) : @MeasurableSet X (borel X) c.eval := by
  change GenerateMeasurable {s : Set X | IsOpen s} c.eval
  rw [← range_openGenerator X]
  exact GeneratedCode.generateMeasurable_eval c

/-- A set is Borel measurable exactly when it is the interpretation of a Borel code.-/
theorem borelMeasurableSet_iff_exists_code {s : Set X} :
    @MeasurableSet X (borel X) s ↔ ∃ c : BorelCode X, c.eval = s := by
  change GenerateMeasurable {s : Set X | IsOpen s} s ↔ _
  rw [← range_openGenerator X]
  exact GeneratedCode.generateMeasurable_iff_exists_code

/-- In a `BorelSpace`, measurable sets are exactly the interpretations of Borel codes.-/
theorem measurableSet_iff_exists_code [m : MeasurableSpace X] [BorelSpace X] {s : Set X} :
    MeasurableSet s ↔ ∃ c : BorelCode X, c.eval = s := by
  have h : m = borel X := BorelSpace.measurable_eq
  rw [h]
  exact borelMeasurableSet_iff_exists_code

end BorelCode
end DescriptiveSetTheory
