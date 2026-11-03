/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Core.Definitions
import Tengoku.Seed.Algebra.DirectSum.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The point, as a consistency witness for Layer A

`NumericalVarietyData` is an explicit presentation of the graded structure, characteristic
data, and Euler characteristic. Its compatibility matters only if the separately stated
`SatisfiesHRR` property has a model.

This file supplies one: a point, in dimension zero. `A^•(pt)_ℚ = ℚ` concentrated in
codimension zero, `N(pt) = ℤ`, `ch(E) = rank E`, `td(pt) = 1`, and Riemann–Roch degenerates
to `χ(E) = rank E`.

It is a *witness*, not a working example: nothing interesting is true in dimension zero.
The K3 presentation is the first positive-dimensional model in which Riemann--Roch has content.
-/

namespace AlgebraicGeometry.Numerical

namespace Examples

open NumericalRingData

/-- The graded pieces of `A^•(pt)_ℚ`: everything sits in codimension zero.-/
def pointPiece : ℕ → Submodule ℚ ℚ := fun i => if i = 0 then ⊤ else ⊥

/--
@isnad1 id=eq.0h0v.s5.366850f58373 from=translated src=- shape=6ef34aee vocab=65bd648e
-/
theorem pointPiece_zero : pointPiece 0 = ⊤ := by simp [pointPiece]

/--
@isnad1 id=eq.1h1v.s5.f2f7c1383164 from=translated src=- shape=c7e25de0 vocab=7e6a8921
-/
theorem pointPiece_eq_bot {i : ℕ} (hi : i ≠ 0) : pointPiece i = ⊥ := by
  simp [pointPiece, hi]

/--
@isnad1 id=isintern.0h0v.s4.ee288b5c528f from=translated src=- shape=4079ef20 vocab=77376d66
-/
theorem pointPiece_isInternal : DirectSum.IsInternal pointPiece := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨fun i => ?_, ?_⟩
  · by_cases hi : i = 0
    · subst hi
      have h : (⨆ j, ⨆ _ : j ≠ 0, pointPiece j) = ⊥ :=
        iSup_eq_bot.mpr fun j => iSup_eq_bot.mpr fun hj => pointPiece_eq_bot hj
      rw [h]
      exact disjoint_bot_right
    · rw [pointPiece_eq_bot hi]
      exact disjoint_bot_left
  · exact le_antisymm le_top (le_iSup_of_le 0 (by rw [pointPiece_zero]))

/-- `A^•(pt)_ℚ = ℚ`, in dimension zero.-/
noncomputable def pointNumericalRing : NumericalRingData 0 ℚ where
  piece := pointPiece
  isInternal := pointPiece_isInternal
  piece_eq_bot_of_lt := fun _ hi => pointPiece_eq_bot (by omega)
  one_mem_piece_zero := by rw [pointPiece_zero]; trivial
  mul_mem_piece := by
    intro i j x y hx hy
    by_cases hij : i + j = 0
    · have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      subst hi; subst hj
      rw [pointPiece_zero]; trivial
    · rw [pointPiece_eq_bot hij, Submodule.mem_bot]
      rcases Nat.eq_zero_or_pos i with hi | hi
      · have hj : j ≠ 0 := by omega
        rw [pointPiece_eq_bot hj, Submodule.mem_bot] at hy
        simp [hy]
      · have hi' : i ≠ 0 := by omega
        rw [pointPiece_eq_bot hi', Submodule.mem_bot] at hx
        simp [hx]
  degree := LinearMap.id
  degree_eq_zero_of_mem := by
    intro i x hi hx
    rw [pointPiece_eq_bot hi, Submodule.mem_bot] at hx
    simp [hx]

/-- The Chern character on a point: `ch₀(E) = rank E`, and nothing above.-/
def pointCh (E : ℤ) : ℕ → ℚ := fun i => if i = 0 then (E : ℚ) else 0

/-- The Todd class of a point: `td₀ = 1`, and nothing above.-/
def pointTodd : ℕ → ℚ := fun i => if i = 0 then 1 else 0

/--
@isnad1 id=mem.0h2v.s5.953e6498b00f from=translated src=- shape=bca6378e vocab=3a4389ab
-/
theorem pointCh_mem (E : ℤ) (i : ℕ) : pointCh E i ∈ pointPiece i := by
  by_cases hi : i = 0
  · subst hi; rw [pointPiece_zero]; trivial
  · rw [pointPiece_eq_bot hi, Submodule.mem_bot]
    simp [pointCh, hi]

/--
@isnad1 id=mem.0h1v.s5.a682318b0f34 from=translated src=- shape=d652a4e3 vocab=389c9f0c
-/
theorem pointTodd_mem (i : ℕ) : pointTodd i ∈ pointPiece i := by
  by_cases hi : i = 0
  · subst hi; rw [pointPiece_zero]; trivial
  · rw [pointPiece_eq_bot hi, Submodule.mem_bot]
    simp [pointTodd, hi]

/-- `N(pt) = ℤ`, with `ch = rank` and `td = 1`. Riemann–Roch reads `χ(E) = rank E`.-/
noncomputable def pointNumericalVariety : NumericalVarietyData 0 ℚ ℤ where
  ring := pointNumericalRing
  rank := AddMonoidHom.id ℤ
  chComp := pointCh
  chComp_mem := pointCh_mem
  chComp_zero := by intro E; simp [pointCh]
  chComp_add := by intro E F i; by_cases hi : i = 0 <;> simp [pointCh, hi]
  toddComp := pointTodd
  toddComp_mem := pointTodd_mem
  toddComp_zero := by simp [pointTodd]
  chi := AddMonoidHom.id ℤ

/-- Riemann--Roch for the explicit point presentation.
@isnad1 id=satisfie.0h0v.s3.0bc60f72a7ff from=translated src=- shape=8c01f280 vocab=15a25543
-/
theorem pointNumericalVariety_satisfiesHRR : pointNumericalVariety.SatisfiesHRR where
  eq E := by
    simp [pointNumericalVariety, pointNumericalRing, pointCh, pointTodd]

end Examples

end AlgebraicGeometry.Numerical
