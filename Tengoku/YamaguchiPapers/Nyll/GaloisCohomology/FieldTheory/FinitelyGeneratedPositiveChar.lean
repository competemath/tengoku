/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants
import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.FieldTheory.FiniteConstants
import Tengoku.Seed.FieldTheory.Finite.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Constants in finitely generated fields of positive characteristic
-/

namespace FieldTheory

universe u v

/-- The prime subfield of a field of positive characteristic is finite.
@isnad1 id=finite.1h1v.s7.adad4dc44bfd from=translated src=- shape=26b84a72 vocab=e223d967
-/
theorem finite_primeSubfield_of_ringChar_ne_zero
    (K : Type u) [Field K] (hchar : ringChar K ≠ 0) :
    Finite (⊥ : Subfield K) := by
  have : Fact (ringChar K).Prime :=
    ⟨(CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hchar⟩
  rw [← ZMod.fieldRange_castHom_eq_bot (ringChar K)]
  exact Finite.of_surjective (ZMod.castHom (m := ringChar K) dvd_rfl K).rangeRestrictField
    (ZMod.castHom (m := ringChar K) dvd_rfl K).rangeRestrictField_bijective.surjective

/-- The algebraic constants in a finitely generated field of positive
characteristic form a finite field.
@isnad1 id=finite.2h1v.s10.d47206b88cae from=translated src=- shape=97ebff85 vocab=cd6ddb2a
-/
theorem finite_constants_of_fg_posChar
    (K : Type u) [Field K] (hfg : Field.FG K) (hchar : ringChar K ≠ 0) :
    Finite (algebraicClosure (⊥ : Subfield K) K) := by
  have : Finite (⊥ : Subfield K) := finite_primeSubfield_of_ringChar_ne_zero K hchar
  have : Algebra.EssFiniteType (⊥ : Subfield K) K := Field.fg_iff_essFiniteType.mp hfg
  exact finite_algebraicClosure_of_finite_base (⊥ : Subfield K) K

/-- Every root of unity is contained in the finite field of algebraic constants.
@isnad1 id=finite.2h1v.s7.c571e4f1300b from=translated src=- shape=d13699a8 vocab=927f8866
-/
theorem finite_torsion_units_of_fg_posChar
    (K : Type u) [Field K] (hfg : Field.FG K) (hchar : ringChar K ≠ 0) :
    Finite (CommGroup.torsion Kˣ) := by
  have : Finite (algebraicClosure (⊥ : Subfield K) K) :=
    finite_constants_of_fg_posChar K hfg hchar
  exact finite_torsion_units_of_finite_algebraicClosure (⊥ : Subfield K) K

/-- The Artin--Schreier map on a finitely generated field of positive
characteristic is not surjective.
@isnad1 id=ex.2h1v.s6.caf3e0828ea3 from=translated src=- shape=adc4fa77 vocab=7e13df2a
-/
theorem exists_not_artinSchreier_of_fg_posChar
    (K : Type u) [Field K] (hfg : Field.FG K) (hchar : ringChar K ≠ 0) :
    ∃ a : K, ∀ x : K, x ^ ringChar K - x ≠ a := by
  have : Finite (algebraicClosure (⊥ : Subfield K) K) :=
    finite_constants_of_fg_posChar K hfg hchar
  exact exists_not_pow_sub_of_finite_algebraicClosure (⊥ : Subfield K) K (ringChar K)
    ((CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hchar).one_lt

/-- The primary roots of unity in every finite extension are finite.
@isnad1 id=finite.2h3v.s7.037a46bc2924 from=translated src=- shape=7c674afa vocab=64b6c6f4
-/
theorem finite_primaryComponent_finiteExtension_of_fg_posChar
    (K : Type u) [Field K] (hfg : Field.FG K) (hchar : ringChar K ≠ 0)
    (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]
    (p : ℕ) [Fact p.Prime] : Finite (CommGroup.primaryComponent Lˣ p) := by
  let F := (⊥ : Subfield K)
  have : Finite F := finite_primeSubfield_of_ringChar_ne_zero K hchar
  have : Algebra.EssFiniteType F K := Field.fg_iff_essFiniteType.mp hfg
  have : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_finiteType K L
  have : Algebra.EssFiniteType F L := Algebra.EssFiniteType.comp F K L
  have : Finite (algebraicClosure F L) := finite_algebraicClosure_of_finite_base F L
  exact finite_primaryComponent_of_finite_algebraicClosure F L p

end FieldTheory
