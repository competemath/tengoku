/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `ParenFreeCoeff` and `ParenFreeVar`: typeclass assertions that a
  `ParsableCoeff` / `ParsableVar` instance's character-list representation
  never contains a `(` or `)`.

  These enable nested-polynomial serialization (`AzPolynomial.MvCoeffParse`)
  where coefficients are wrapped in `(...)`: the outer parser can reliably
  locate the closing paren because no inner character is itself a paren.

  Instances are provided for all stock coefficient types (`ℕ`, `ℤ`, `ℚ`,
  `ZMod m`) and all stock variable types (`IndexedVar`, `IndexedCapsVar`,
  `AbcVar`, `AbcCapsVar`, `XyzVar`, `XyzCapsVar`, `GreekVar`, `GreekCapsVar`).
-/
import Tengoku.Azurite.Azurite.AzMvPolynomial.Var
import Tengoku.Azurite.Azurite.AzMvPolynomial.ParsableCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite

open AzPolynomial

/-- Typeclass assertion that a `ParsableCoeff` instance's character-list
    representation never contains `(` or `)`.  Combined with `ParenFreeVar`
    this lifts to `AzMvPolynomial.toCharsWith F` via
    `AzMvPolynomial.char_notin_toCharsWith`.-/
class ParenFreeCoeff (R : Type _) [Semiring R] [NeZero (1 : R)] [ParsableCoeff R] : Prop where
  toChars_no_lparen : ∀ r : R, '(' ∉ ParsableCoeff.toChars r
  toChars_no_rparen : ∀ r : R, ')' ∉ ParsableCoeff.toChars r

/-- Typeclass assertion that a `ParsableVar` instance's character-list
    representation never contains `(` or `)`.-/
class ParenFreeVar (α : Type _) (n : outParam ℕ) [LinearOrder α] [ParsableVar α n] : Prop where
  toChars_no_lparen : ∀ v : α, '(' ∉ ParsableVar.toChars v
  toChars_no_rparen : ∀ v : α, ')' ∉ ParsableVar.toChars v

/-! ### ParenFreeCoeff instances -/

/- `ParenFreeCoeff` instances for the non-Az types `ℕ`, `ℤ`, `ℚ`, and `ZMod` have
   been removed along with their `ParsableCoeff` instances; use the Az
   coefficient types instead. -/

/-! ### ParenFreeVar instances -/

end Azurite
