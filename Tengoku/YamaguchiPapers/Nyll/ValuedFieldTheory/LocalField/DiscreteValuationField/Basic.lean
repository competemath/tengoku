/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
import Tengoku.Seed.Algebra.CharP.Algebra
import Tengoku.Seed.Algebra.CharP.Lemmas
import Tengoku.Seed.Data.Rat.Cast.CharZero
import Tengoku.Seed.Data.Rat.Lemmas
import Tengoku.Seed.FieldTheory.Perfect
import Tengoku.Seed.NumberTheory.LocalField.Basic
import Tengoku.Seed.NumberTheory.Padics.PadicNumbers
import Tengoku.Seed.RingTheory.Algebraic.Integral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local fields

A local-field package here is a chosen complete discretely valued field with
finite residue field.  The topology-first mathlib class remains available
through imports; this file only adds the chosen-valuation API needed downstream.
-/

universe u v w x

namespace LocalFieldTheory.DiscreteValuationField

open ValuationTheory.DiscreteValuationField

/-- A local field with a chosen complete discrete valuation and finite residue field.-/
structure LocalField (K : Type u) [Field K] extends CompleteDVF.{u, v} K where
  /-- The residue field of the chosen complete discrete valuation is finite.-/
  [residueFinite : Finite toCompleteDVF.residueField]

attribute [instance] LocalField.residueFinite

namespace LocalField

variable {K : Type u} [Field K]

/-- The residue field of a local field package.-/
abbrev residueField (F : LocalField.{u, v} K) : Type u :=
  F.toCompleteDVF.residueField

/-- The valuation subring of a local field package.-/
abbrev valuationSubring (F : LocalField.{u, v} K) : Type u :=
  F.toCompleteDVF.valuationSubring

/-- The maximal ideal of the valuation subring.-/
abbrev maximalIdeal (F : LocalField.{u, v} K) : Ideal F.valuationSubring :=
  F.toCompleteDVF.maximalIdeal

/-- The residue map of a local field package.-/
abbrev residueMap (F : LocalField.{u, v} K) :
    RingHom F.valuationSubring F.residueField :=
  F.toCompleteDVF.residueMap

/-- A local field package has a uniformizer.
@isnad1 id=ex.0h2v.s6.4d961b12c694 from=translated src=- shape=31e035f9 vocab=8cfe70ce
-/
theorem exists_uniformizer (F : LocalField.{u, v} K) :
    ∃ pi : F.valuationSubring, F.toCompleteDVF.valuation.IsUniformizer (pi : K) :=
  F.toCompleteDVF.exists_uniformizer

/-- The residue characteristic of a local field.-/
noncomputable abbrev residueCharacteristic (F : LocalField.{u, v} K) : ℕ :=
  ringChar F.residueField

end LocalField
end LocalFieldTheory.DiscreteValuationField
