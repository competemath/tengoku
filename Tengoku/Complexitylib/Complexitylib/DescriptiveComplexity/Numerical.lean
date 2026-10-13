/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.Numerical.Defs
import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.Numerical.Internal

/-!
# First-order logic with canonical numerical predicates

Canonical expansions make order, BIT, addition, and multiplication available to
the existing FO syntax. Numerical atoms have their specified natural-number
semantics; input formulas embed without changing truth. The computable expansion
agrees with its propositional counterpart, so the existing Boolean evaluator can
check formulas on these expansions.

This supplies the semantic interfaces for FO[BIT] and FO[ADD, MUL]. Their equality
of expressive power, formula definitions of one arithmetic basis from the other,
and the uniform circuit capture theorem remain separate results.
-/

public section

namespace Complexity.DescriptiveComplexity

variable {V : Vocabulary} {n : Nat}

/-- Canonical numerical expansion preserves the universe exactly.
@isnad1 id=eq.0h3v.s4.ef4f57e91e2e from=translated src=- shape=2d2d7f91 vocab=8ed4831e
-/
@[simp] theorem FinStruct.withNumerical_card (A : FinStruct V)
    (predicates : List NumericalPredicate) : (A.withNumerical predicates).card = A.card := rfl

/-- Forgetting the added symbols recovers the original structure.
@isnad1 id=eq.0h3v.s4.51d09e7579c6 from=translated src=- shape=f79caca0 vocab=06e7b5bd
-/
@[simp] theorem FOInterpretation.forgetNumerical_apply (A : FinStruct V)
    (predicates : List NumericalPredicate) :
    (forgetNumerical V predicates).apply (A.withNumerical predicates) = A :=
  forgetNumerical_apply_internal A predicates

/-- Embedding an input formula into the numerical vocabulary preserves satisfaction.
@isnad1 id=iff.0h6v.s5.0dd97407695b from=translated src=- shape=adcc99d2 vocab=5ba6c96e
-/
@[simp] theorem Formula.withNumerical_sat (A : FinStruct V) (φ : Formula V n)
    (predicates : List NumericalPredicate) (σ : Env A.card n) :
    (φ.withNumerical predicates).Sat (A.withNumerical predicates) σ ↔ φ.Sat A σ :=
  withNumerical_sat_internal A φ predicates σ

/-- A designated numerical atom has its canonical meaning on the evaluated arguments.
@isnad1 id=iff.0h7v.s6.d48b399ef3ca from=translated src=- shape=8c3d7bc5 vocab=25783a7e
-/
@[simp] theorem Formula.numerical_sat (A : FinStruct V)
    (predicates : List NumericalPredicate) (r : Fin predicates.length)
    (args : Fin (predicates.get r).arity → Term (V.withNumerical predicates) n)
    (σ : Env A.card n) :
    (numerical predicates r args).Sat (A.withNumerical predicates) σ ↔
      (predicates.get r).Holds (fun i => (Term.eval (A.withNumerical predicates) σ (args i)).val) :=
  numerical_sat_internal A predicates r args σ

/-- The order atom compares the natural indices of its two elements.
@isnad1 id=iff.0h6v.s6.49f46efe08d2 from=translated src=- shape=cb9debb9 vocab=0b427af5
-/
@[simp] theorem Formula.orderLt_sat (A : FinStruct V) (x y : Term V.withOrder n)
    (σ : Env A.card n) :
    (orderLt x y).Sat (A.withNumerical [.lt]) σ ↔
      (x.eval (A.withNumerical [.lt]) σ).val < (y.eval (A.withNumerical [.lt]) σ).val := by
  simp [orderLt, NumericalPredicate.Holds]

/-- BIT reads the indicated zero-based bit of the element's natural index.
@isnad1 id=iff.0h6v.s6.78420f785429 from=translated src=- shape=605d7478 vocab=beac1e5b
-/
@[simp] theorem Formula.bit_sat (A : FinStruct V) (x i : Term V.withBit n)
    (σ : Env A.card n) :
    (bit x i).Sat (A.withNumerical [.bit]) σ ↔
      (x.eval (A.withNumerical [.bit]) σ).val.testBit
        (i.eval (A.withNumerical [.bit]) σ).val = true := by
  simp [bit, NumericalPredicate.Holds]

/-- ADD is the graph of natural addition, with all three elements in the finite universe.
@isnad1 id=iff.0h7v.s7.d5af26decce0 from=translated src=- shape=70e1c4a7 vocab=7448bd44
-/
@[simp] theorem Formula.add_sat (A : FinStruct V) (x y z : Term V.withArithmetic n)
    (σ : Env A.card n) :
    (add x y z).Sat (A.withNumerical [.add, .mul]) σ ↔
      (x.eval (A.withNumerical [.add, .mul]) σ).val +
        (y.eval (A.withNumerical [.add, .mul]) σ).val =
          (z.eval (A.withNumerical [.add, .mul]) σ).val := by
  simp [add, NumericalPredicate.Holds]

/-- MUL is the graph of natural multiplication, without modular wraparound.
@isnad1 id=iff.0h7v.s7.7000a0bfdb28 from=translated src=- shape=70e1c4a7 vocab=3d4cda9e
-/
@[simp] theorem Formula.mul_sat (A : FinStruct V) (x y z : Term V.withArithmetic n)
    (σ : Env A.card n) :
    (mul x y z).Sat (A.withNumerical [.add, .mul]) σ ↔
      (x.eval (A.withNumerical [.add, .mul]) σ).val *
        (y.eval (A.withNumerical [.add, .mul]) σ).val =
          (z.eval (A.withNumerical [.add, .mul]) σ).val := by
  simp [mul, NumericalPredicate.Holds]

/-- The computable expansion has exactly the specified propositional semantics.
@isnad1 id=eq.0h3v.s4.a81255be3506 from=translated src=- shape=57a4bae6 vocab=e1e2ce8d
-/
@[simp] theorem DecFinStruct.withNumerical_toFinStruct (A : DecFinStruct V)
    (predicates : List NumericalPredicate) :
    (A.withNumerical predicates).toFinStruct = A.toFinStruct.withNumerical predicates :=
  withNumerical_toFinStruct_internal A predicates

/-- Every input FO definition remains a definition after adding numerical predicates.
@isnad1 id=fodefina.1h3v.s4.ca07f0b9cfab from=translated src=- shape=2c7c7b17 vocab=26c997f2
-/
theorem FODefinable.withNumerical {Q : BooleanQuery V} (hQ : FODefinable Q)
    (predicates : List NumericalPredicate) : FODefinableWithNumerical predicates Q := by
  obtain ⟨φ, hφ⟩ := hQ
  refine ⟨φ.withNumerical predicates, fun A => ?_⟩
  exact (hφ A).trans (Formula.withNumerical_sat A φ predicates (emptyEnv A.card)).symm

end Complexity.DescriptiveComplexity
