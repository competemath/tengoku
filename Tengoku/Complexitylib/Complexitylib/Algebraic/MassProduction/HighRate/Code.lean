/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.MassProduction.HighRate.DigitMonomials
public import Tengoku.Complexitylib.Complexitylib.Algebraic.MassProduction.HighRate.Independence
public import Tengoku.Complexitylib.Complexitylib.Algebraic.MassProduction.HighRate.Systematic

/-!
# A high-rate systematic code with punctured-line recovery

The retained common-zero-block monomials are distinct reduced monomials, so
their evaluation tables are independent. Choosing a basis among evaluation
rows gives a systematic information set of exactly the retained cardinality.
Every codeword preserves punctured-line recovery by linearity.

The information set and encoding matrices are chosen offline. No efficient
uniform procedure for finding them is asserted.
-/

@[expose] public section

namespace Algebraic.MassProduction.HighRate

open scoped BigOperators LinearAlgebra.Projectivization

/-- A systematic field-valued code whose symbols are recoverable from every
punctured projective line through the target point. -/
structure LineCode (K Coordinate : Type*)
    [Field K] [Finite K] [Fintype Coordinate] where
  /-- The information positions, chosen once for the code. -/
  information : Set (Coordinate → K)
  /-- Encoding an arbitrary assignment to the information positions. -/
  encode : (information → K) → (Coordinate → K) → K
  /-- Encoding preserves the assigned information symbols. -/
  systematic : ∀ message index, encode message index.val = message index
  /-- Every nonzero projective direction supplies a recovery set. -/
  lineRecovery : ∀ message target (direction : ℙ K (Coordinate → K)),
    encode message target = ∑ point ∈ puncturedLine target direction, encode message point

/-- Digit matrices have distinct natural exponent vectors. -/
theorem digitDegrees_injective (Coordinate : Type*) (blockWidth blocks : Nat) :
    Function.Injective (digitDegrees (Coordinate := Coordinate)
      (blockWidth := blockWidth) (blocks := blocks)) := by
  intro left right equalDegrees
  apply (digitExponentEquiv Coordinate blockWidth blocks).injective
  funext coordinate
  exact Fin.ext (congrFun equalDegrees coordinate)

end Algebraic.MassProduction.HighRate
