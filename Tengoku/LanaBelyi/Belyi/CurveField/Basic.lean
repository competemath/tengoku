/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.Seed.Algebra.Algebra.Rat
import Tengoku.Seed.FieldTheory.IntermediateField.Adjoin.Algebra
import Tengoku.Seed.FieldTheory.IntermediateField.Adjoin.Basic
import Tengoku.Seed.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Tengoku.Seed.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Function fields of curves over number fields

A smooth proper geometrically connected curve over a number field is determined by its
function field. We represent such curves by their function fields: a field `K` of
characteristic `0` which is a finite extension of `ℚ(t)` for some `t ∈ K` transcendental
over `ℚ` (class `Belyi.CurveField.IsCurveField`). The `ℚ`-algebra structure on `K` is the
canonical one of a field of characteristic zero.

## Main definitions and results

* `Belyi.CurveField.IsCurveField K`: `K` is finite over `ℚ⟮t⟯` for some transcendental `t`.
* `Belyi.CurveField.exists_transcendental`: a curve field has a transcendental element.
* `Belyi.CurveField.trdeg_eq_one`: its transcendence degree over `ℚ` is `1`.
* `Belyi.CurveField.isAlgebraic_adjoin`, `Belyi.CurveField.finiteDimensional_adjoin`:
  for *every* `s ∈ K` transcendental over `ℚ`, `K` is a finite extension of `ℚ⟮s⟯`.
-/

open scoped IntermediateField

namespace Belyi.CurveField

/-- `K` is the function field of a curve over a number field: `K` is finite over `ℚ⟮t⟯` for
some `t ∈ K` transcendental over `ℚ`. -/
class IsCurveField (K : Type*) [Field K] [CharZero K] : Prop where
  exists_finite : ∃ t : K, Transcendental ℚ t ∧ FiniteDimensional ℚ⟮t⟯ K

variable {K : Type*} [Field K] [CharZero K]

/--
@isnad1 id=iff.0h2v.s6.0bdc105e7d50 from=translated src=- shape=8d96be7a vocab=10183e71
-/
theorem transcendental_inv_iff {t : K} : Transcendental ℚ t⁻¹ ↔ Transcendental ℚ t :=
  not_congr IsAlgebraic.inv_iff

/--
@isnad1 id=transcen.1h2v.s6.2d7af7c5c4a6 from=translated src=- shape=5504a1b5 vocab=10183e71
-/
theorem transcendental_inv {t : K} (ht : Transcendental ℚ t) : Transcendental ℚ t⁻¹ :=
  transcendental_inv_iff.mpr ht

/--
@isnad1 id=ne.1h2v.s5.2c6e191f4165 from=translated src=- shape=144f36d7 vocab=fe74cb2e
-/
theorem ne_zero_of_transcendental {t : K} (ht : Transcendental ℚ t) : t ≠ 0 := by
  rintro rfl
  exact ht isAlgebraic_zero

/-- If `K` is finite over `ℚ⟮t⟯`, then `{t}` is a transcendence basis of `K / ℚ`.
@isnad1 id=istransc.1h2v.s8.c25728f46bd6 from=translated src=- shape=9f0f04d6 vocab=165c8a62
-/
theorem isTranscendenceBasis_of_finiteDimensional {t : K} (ht : Transcendental ℚ t)
    [FiniteDimensional ℚ⟮t⟯ K] : IsTranscendenceBasis ℚ (fun _ : Unit ↦ t) := by
  refine (algebraicIndependent_unique_type_iff.mpr ht).isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  rw [Set.range_const, ← IntermediateField.isAlgebraic_adjoin_iff_top]
  infer_instance

variable [IsCurveField K]

variable (K) in
/-- A curve field contains an element transcendental over `ℚ`.
@isnad1 id=ex.0h1v.s5.1301069884cd from=translated src=- shape=815d2e9b vocab=167e64c1
-/
theorem exists_transcendental : ∃ t : K, Transcendental ℚ t :=
  let ⟨t, ht, _⟩ := IsCurveField.exists_finite (K := K); ⟨t, ht⟩

variable (K) in
/-- A curve field has transcendence degree one over `ℚ`.
@isnad1 id=eq.0h1v.s5.1e92bd12b590 from=translated src=- shape=665e1df8 vocab=04989840
-/
theorem trdeg_eq_one : Algebra.trdeg ℚ K = 1 := by
  obtain ⟨t, ht, _⟩ := IsCurveField.exists_finite (K := K)
  have := (isTranscendenceBasis_of_finiteDimensional ht).lift_cardinalMk_eq_trdeg
  simpa using this.symm

/-- Every transcendental element of a curve field is a transcendence basis.
@isnad1 id=istransc.1h2v.s5.35f19ef3f217 from=translated src=- shape=00829a21 vocab=eb4c15ee
-/
theorem isTranscendenceBasis {s : K} (hs : Transcendental ℚ s) :
    IsTranscendenceBasis ℚ (fun _ : Unit ↦ s) :=
  (algebraicIndependent_unique_type_iff.mpr hs).isTranscendenceBasis_of_lift_trdeg_le_of_finite
    (by rw [trdeg_eq_one K]; simp)

/-- A curve field is algebraic over `ℚ⟮s⟯` for every transcendental `s`.
@isnad1 id=isalgebr.1h2v.s7.53f1bca5d9d2 from=translated src=- shape=56a94811 vocab=af344560
-/
theorem isAlgebraic_adjoin {s : K} (hs : Transcendental ℚ s) : Algebra.IsAlgebraic ℚ⟮s⟯ K := by
  have := (isTranscendenceBasis hs).isAlgebraic_field
  rwa [Set.range_const] at this

variable (K) in
/-- A curve field is finitely generated as a field over `ℚ`.
@isnad1 id=ex.0h1v.s8.821ae65e89f2 from=translated src=- shape=7db00112 vocab=4b1c98dc
-/
theorem exists_finset_adjoin_eq_top :
    ∃ S : Finset K, IntermediateField.adjoin ℚ (S : Set K) = ⊤ := by
  obtain ⟨t, ht, _⟩ := IsCurveField.exists_finite (K := K)
  obtain ⟨S, hS⟩ := IntermediateField.fg_top (F := ℚ⟮t⟯) (E := K)
  classical
  refine ⟨insert t S, ?_⟩
  have := congrArg (IntermediateField.restrictScalars ℚ) hS
  have h2 := IntermediateField.adjoin_adjoin_left ℚ (S := {t}) (S : Set K)
  rw [IntermediateField.restrictScalars_top] at this
  rw [Finset.coe_insert, Set.insert_eq, ← h2]
  exact this

/-- A curve field is a finite extension of `ℚ⟮s⟯` for every transcendental `s`.
@isnad1 id=finitedi.1h2v.s7.b4eeeab411a3 from=translated src=- shape=56a94811 vocab=f91b1acb
-/
theorem finiteDimensional_adjoin {s : K} (hs : Transcendental ℚ s) :
    FiniteDimensional ℚ⟮s⟯ K := by
  have := isAlgebraic_adjoin hs
  obtain ⟨S, hS⟩ := exists_finset_adjoin_eq_top K
  have htop : IntermediateField.adjoin ℚ⟮s⟯ (S : Set K) = ⊤ := by
    rw [← IntermediateField.restrictScalars_eq_top_iff (K := ℚ), eq_top_iff, ← hS,
      IntermediateField.adjoin_le_iff]
    exact IntermediateField.subset_adjoin _ _
  have := IntermediateField.finiteDimensional_adjoin (K := ℚ⟮s⟯) (S := (S : Set K))
    (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  rw [htop] at this
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end Belyi.CurveField
