/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants
import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.FieldTheory.IntegralClosureTorsion
import Tengoku.Seed.NumberTheory.NumberField.Units.Basic
import Tengoku.Seed.FieldTheory.PrimeField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Roots of unity in finitely generated fields of characteristic zero
-/

namespace FieldTheory

universe u v

/-- Finitely generated fields of characteristic zero are finitely generated
extensions of the rational numbers.
@isnad1 id=essfinit.1h1v.s5.0780fba90ef1 from=translated src=- shape=a97491eb vocab=898ff47c
-/
theorem essFiniteType_rat_of_fg
    (K : Type u) [Field K] [CharZero K] (hfg : Field.FG K) :
    Algebra.EssFiniteType ℚ K := by
  let F := (⊥ : Subfield K)
  have hs : Function.Surjective (algebraMap ℚ F) := by
    intro x
    have hx : (x : K) ∈ (algebraMap ℚ K).fieldRange := by
      rw [← Subfield.bot_eq_of_charZero]
      exact x.property
    obtain ⟨r, hr⟩ := hx
    exact ⟨r, Subtype.ext hr⟩
  have : Module.Finite ℚ F := Module.Finite.of_surjective (Algebra.linearMap ℚ F) hs
  have : Algebra.EssFiniteType ℚ F := Algebra.EssFiniteType.of_finiteType ℚ F
  have : Algebra.EssFiniteType F K := Field.fg_iff_essFiniteType.mp hfg
  exact Algebra.EssFiniteType.comp ℚ F K

/-- The roots of unity of a number field are exactly the torsion units of its
ring of integers, hence form a finite group.
@isnad1 id=finite.0h1v.s7.9e1d62b77ead from=translated src=- shape=6a3c6ed5 vocab=1fbb4d6e
-/
theorem finite_torsion_units_numberField
    (K : Type u) [Field K] [NumberField K] : Finite (CommGroup.torsion Kˣ) := by
  have : Finite (CommGroup.torsion (integralClosure ℤ K)ˣ) :=
    inferInstanceAs (Finite (NumberField.Units.torsion K))
  exact Finite.of_injective (torsionUnitsIntegralClosureEquiv ℤ K)
    (torsionUnitsIntegralClosureEquiv ℤ K).injective

end FieldTheory
