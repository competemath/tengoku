/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.RepresentativeCarrier
public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.CanonicalWords
public import Tengoku

/-!
# Carrier coordinates for canonical normal-form words

This file computes the closed-disk boundary coordinates of every canonical word position.
It reconciles the canonical positive boundary-block ordering with the trusted Eval relations'
negative angles using `Fin.rev` and integral periodicity. The resulting theorems send each of the
five canonical pairing families into the corresponding trusted equivalence closure.
-/

@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces.NormalForm

open Complex
open SurfaceCellComplex

/-- The point on occurrence `i` of the canonical orientable one-face presentation. -/
noncomputable def orientableOccurrencePoint (p n : ℕ)
    (i : Fin (orientableBoundaryWord p n).length) (t : unitInterval) :
    (orientableCellComplex p n).PolygonalPreRealization :=
  PolygonGluing.Side.point
    ((orientableCellComplex p n).occurrenceSide
      ⟨PUnit.unit, i⟩) t

/-- The carrier bridge sends occurrence `i` to the boundary parameter `(i+t)/|word|`.
@isnad1 id=eq.0h4v.s8.2ed0c4f6286e from=translated src=- shape=fe1bfd7f vocab=70155c51
-/
theorem orientableCarrier_occurrencePoint (p n : ℕ)
    (i : Fin (orientableBoundaryWord p n).length) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n i t) =
      ClosedUnitDisc.bdyPtOfReal
        (((i.val : ℝ) + (t : ℝ)) / (orientableBoundaryWord p n).length) := by
  simpa [orientableCellComplex, orientableOccurrencePoint] using
    oneFacePolygonalPreRealizationHomeomorph_sidePoint
      (orientableBoundaryWord p n) i t

/--
@isnad1 id=eq.0h4v.s9.ded8d318237c from=translated src=- shape=32975658 vocab=697d129a
-/
theorem orientableCarrier_handle_a_pos {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 0) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (i : ℝ) + (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableHandlePosition_val, orientableBoundaryWord_length]
  push_cast
  norm_num
  ring

/--
@isnad1 id=eq.0h4v.s9.95da2063729b from=translated src=- shape=73ecfaed vocab=561d0090
-/
theorem orientableCarrier_handle_a_neg {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 2)
          (unitInterval.symm t)) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (i : ℝ) + 3 - (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableHandlePosition_val, orientableBoundaryWord_length,
    unitInterval.coe_symm_eq]
  push_cast
  norm_num
  ring

/--
@isnad1 id=eq.0h4v.s9.84bf831b4e26 from=translated src=- shape=eb80ce19 vocab=697d129a
-/
theorem orientableCarrier_handle_b_pos {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 1) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (i : ℝ) + 1 + (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableHandlePosition_val, orientableBoundaryWord_length]
  push_cast
  norm_num
  ring

/--
@isnad1 id=eq.0h4v.s9.92fefaf9f075 from=translated src=- shape=73ecfaed vocab=561d0090
-/
theorem orientableCarrier_handle_b_neg {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 3)
          (unitInterval.symm t)) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (i : ℝ) + 4 - (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableHandlePosition_val, orientableBoundaryWord_length,
    unitInterval.coe_symm_eq]
  push_cast
  norm_num
  ring

/--
@isnad1 id=eq.0h4v.s9.8de4c1d50584 from=translated src=- shape=36810520 vocab=0f12213f
-/
theorem orientableCarrier_boundary_c_pos {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableBoundaryPosition_val, orientableBoundaryWord_length]
  push_cast
  norm_num
  ring

/--
@isnad1 id=eq.0h4v.s9.cb5a37e303ca from=translated src=- shape=966b710a vocab=0f12213f
-/
theorem orientableCarrier_boundary_h_pos {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 1) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + 1 + (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableBoundaryPosition_val, orientableBoundaryWord_length]
  push_cast
  norm_num
  ring

/--
@isnad1 id=eq.0h4v.s9.64f94e7c3258 from=translated src=- shape=77ed3ca3 vocab=b300cfbc
-/
theorem orientableCarrier_boundary_c_neg {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2)
          (unitInterval.symm t)) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableBoundaryPosition_val, orientableBoundaryWord_length,
    unitInterval.coe_symm_eq]
  push_cast
  norm_num
  ring

/-- Reversing a finite index converts its real value to `n - j - 1`.
@isnad1 id=eq.0h2v.s5.4109e29c12ee from=translated src=- shape=c056883c vocab=d6d87e1a
-/
theorem fin_rev_cast_real {n : ℕ} (j : Fin n) :
    ((Fin.rev j : Fin n) : ℝ) = n - (j : ℝ) - 1 := by
  rw [Fin.val_rev, Nat.cast_sub (Nat.succ_le_iff.mpr j.isLt)]
  push_cast
  ring

/-- Trusted boundary source `Fin.rev j` is the second canonical `cⱼ` side, modulo one turn.
@isnad1 id=eq.0h4v.s9.0d27c923b189 from=translated src=- shape=e3b0c902 vocab=be4547d9
-/
theorem orientableBoundary_trustedSource_eq_carrier_c_neg
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) / (4 * p + 3 * n)) =
      oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2)
          (unitInterval.symm t)) := by
  have hNnat : 0 < 4 * p + 3 * n := by
    have hj := j.isLt
    omega
  have hN : ((4 * p + 3 * n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hNnat.ne'
  have hN' : 4 * (p : ℝ) + 3 * (n : ℝ) ≠ 0 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hN
    exact hN
  have harg :
      (4 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) / (4 * p + 3 * n) =
        -(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) / (4 * p + 3 * n) + 1 := by
    rw [fin_rev_cast_real]
    field_simp [hN']
    ring
  calc
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) / (4 * p + 3 * n)) =
      ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) /
          (4 * p + 3 * n) + (1 : ℤ)) :=
      (ClosedUnitDisc.bdyPtOfReal_add_int _ 1).symm
    _ = ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) /
          (4 * p + 3 * n)) := by
      simpa using congrArg ClosedUnitDisc.bdyPtOfReal harg.symm
    _ = oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2)
          (unitInterval.symm t)) :=
      (orientableCarrier_boundary_c_neg j t).symm

/-- Trusted boundary target `Fin.rev j` is the first canonical `cⱼ` side, modulo one turn.
@isnad1 id=eq.0h4v.s9.db81e18fde75 from=translated src=- shape=5641610e vocab=615f4bf7
-/
theorem orientableBoundary_trustedTarget_eq_carrier_c_pos
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) / (4 * p + 3 * n)) =
      oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0) t) := by
  have hNnat : 0 < 4 * p + 3 * n := by
    have hj := j.isLt
    omega
  have hN : ((4 * p + 3 * n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hNnat.ne'
  have hN' : 4 * (p : ℝ) + 3 * (n : ℝ) ≠ 0 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hN
    exact hN
  have harg :
      (4 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) / (4 * p + 3 * n) =
        -(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
            (4 * p + 3 * n) + 1 := by
    rw [fin_rev_cast_real]
    field_simp [hN']
    ring
  calc
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
          (4 * p + 3 * n)) =
      ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
          (4 * p + 3 * n) + (1 : ℤ)) :=
      (ClosedUnitDisc.bdyPtOfReal_add_int _ 1).symm
    _ = ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) /
          (4 * p + 3 * n)) := by
      simpa using congrArg ClosedUnitDisc.bdyPtOfReal harg.symm
    _ = oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0) t) :=
      (orientableCarrier_boundary_c_pos j t).symm

/-- Every canonical `aᵢ` side pairing maps into the trusted orientable equivalence closure.
@isnad1 id=eqvgen.0h4v.s9.0c74a459c1fa from=translated src=- shape=45c3a8dd vocab=04aed37f
-/
theorem orientableCarrier_handle_a_eqvGen
    {p n : ℕ} (i : Fin p) (t : unitInterval) :
    Relation.EqvGen (OrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 0) t))
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 2)
          (unitInterval.symm t))) := by
  rw [orientableCarrier_handle_a_pos, orientableCarrier_handle_a_neg]
  exact Relation.EqvGen.rel _ _ (OrientableRel.a (n := n) t i)

/-- Every canonical `bᵢ` side pairing maps into the trusted orientable equivalence closure.
@isnad1 id=eqvgen.0h4v.s9.42503d6042ec from=translated src=- shape=45c3a8dd vocab=04aed37f
-/
theorem orientableCarrier_handle_b_eqvGen
    {p n : ℕ} (i : Fin p) (t : unitInterval) :
    Relation.EqvGen (OrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 1) t))
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 3)
          (unitInterval.symm t))) := by
  rw [orientableCarrier_handle_b_pos, orientableCarrier_handle_b_neg]
  exact Relation.EqvGen.rel _ _ (OrientableRel.b (n := n) t i)

/-- Every canonical `cⱼ` side pairing maps into the trusted orientable equivalence closure.
@isnad1 id=eqvgen.0h4v.s9.866b350bfaf8 from=translated src=- shape=10dbb980 vocab=8010ab71
-/
theorem orientableCarrier_boundary_c_eqvGen
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    Relation.EqvGen (OrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0) t))
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2)
          (unitInterval.symm t))) := by
  rw [← orientableBoundary_trustedTarget_eq_carrier_c_pos,
    ← orientableBoundary_trustedSource_eq_carrier_c_neg]
  exact Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _
      (OrientableRel.c (p := p) t (Fin.rev j)))

/-- The point on occurrence `i` of the canonical nonorientable one-face presentation. -/
noncomputable def nonOrientableOccurrencePoint (p n : ℕ)
    (i : Fin (nonOrientableBoundaryWord p n).length) (t : unitInterval) :
    (nonOrientableCellComplex p n).PolygonalPreRealization :=
  PolygonGluing.Side.point
    ((nonOrientableCellComplex p n).occurrenceSide
      ⟨PUnit.unit, i⟩) t

/-- The nonorientable carrier bridge sends occurrence `i` to `(i+t)/|word|`.
@isnad1 id=eq.0h4v.s8.d331f12b5c78 from=translated src=- shape=fe1bfd7f vocab=91ce1513
-/
theorem nonOrientableCarrier_occurrencePoint (p n : ℕ)
    (i : Fin (nonOrientableBoundaryWord p n).length) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n i t) =
      ClosedUnitDisc.bdyPtOfReal
        (((i.val : ℝ) + (t : ℝ)) / (nonOrientableBoundaryWord p n).length) := by
  simpa [nonOrientableCellComplex, nonOrientableOccurrencePoint] using
    oneFacePolygonalPreRealizationHomeomorph_sidePoint
      (nonOrientableBoundaryWord p n) i t

/--
@isnad1 id=eq.0h4v.s9.1cb8cc1d3fce from=translated src=- shape=32975658 vocab=183fd7d5
-/
theorem nonOrientableCarrier_crosscap_a_first
    {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableCrosscapPosition p n i 0) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (i : ℝ) + (t : ℝ)) / (2 * p + 3 * n)) := by
  rw [nonOrientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [nonOrientableCrosscapPosition_val, nonOrientableBoundaryWord_length]
  push_cast
  norm_num
  ring

/--
@isnad1 id=eq.0h4v.s9.d55184925b4b from=translated src=- shape=eb80ce19 vocab=183fd7d5
-/
theorem nonOrientableCarrier_crosscap_a_second
    {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableCrosscapPosition p n i 1) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (i : ℝ) + 1 + (t : ℝ)) / (2 * p + 3 * n)) := by
  rw [nonOrientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [nonOrientableCrosscapPosition_val, nonOrientableBoundaryWord_length]
  push_cast
  norm_num
  ring

/--
@isnad1 id=eq.0h4v.s9.4e534073ff02 from=translated src=- shape=36810520 vocab=1885e450
-/
theorem nonOrientableCarrier_boundary_c_pos
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 0) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) / (2 * p + 3 * n)) := by
  rw [nonOrientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [nonOrientableBoundaryPosition_val, nonOrientableBoundaryWord_length]
  push_cast
  norm_num
  ring

/--
@isnad1 id=eq.0h4v.s9.cbca48aec0cb from=translated src=- shape=966b710a vocab=1885e450
-/
theorem nonOrientableCarrier_boundary_h_pos
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 1) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + 1 + (t : ℝ)) / (2 * p + 3 * n)) := by
  rw [nonOrientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [nonOrientableBoundaryPosition_val, nonOrientableBoundaryWord_length]
  push_cast
  norm_num
  ring

/--
@isnad1 id=eq.0h4v.s9.d12e268db763 from=translated src=- shape=77ed3ca3 vocab=fde23e87
-/
theorem nonOrientableCarrier_boundary_c_neg
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 2) (unitInterval.symm t)) =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) /
          (2 * p + 3 * n)) := by
  rw [nonOrientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [nonOrientableBoundaryPosition_val, nonOrientableBoundaryWord_length,
    unitInterval.coe_symm_eq]
  push_cast
  norm_num
  ring

/-- Trusted boundary source `Fin.rev j` is the second nonorientable `cⱼ` side.
@isnad1 id=eq.0h4v.s9.d5d954e4f8c4 from=translated src=- shape=e3b0c902 vocab=510b9874
-/
theorem nonOrientableBoundary_trustedSource_eq_carrier_c_neg
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) / (2 * p + 3 * n)) =
      oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 2) (unitInterval.symm t)) := by
  have hNnat : 0 < 2 * p + 3 * n := by
    have hj := j.isLt
    omega
  have hN : ((2 * p + 3 * n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hNnat.ne'
  have hN' : 2 * (p : ℝ) + 3 * (n : ℝ) ≠ 0 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hN
    exact hN
  have harg :
      (2 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) / (2 * p + 3 * n) =
        -(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) /
            (2 * p + 3 * n) + 1 := by
    rw [fin_rev_cast_real]
    field_simp [hN']
    ring
  calc
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) / (2 * p + 3 * n)) =
      ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) /
          (2 * p + 3 * n) + (1 : ℤ)) :=
      (ClosedUnitDisc.bdyPtOfReal_add_int _ 1).symm
    _ = ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) /
          (2 * p + 3 * n)) := by
      simpa using congrArg ClosedUnitDisc.bdyPtOfReal harg.symm
    _ = oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 2) (unitInterval.symm t)) :=
      (nonOrientableCarrier_boundary_c_neg j t).symm

/-- Trusted boundary target `Fin.rev j` is the first nonorientable `cⱼ` side.
@isnad1 id=eq.0h4v.s9.ea88b0c62f12 from=translated src=- shape=5641610e vocab=f45e97e1
-/
theorem nonOrientableBoundary_trustedTarget_eq_carrier_c_pos
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
          (2 * p + 3 * n)) =
      oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 0) t) := by
  have hNnat : 0 < 2 * p + 3 * n := by
    have hj := j.isLt
    omega
  have hN : ((2 * p + 3 * n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hNnat.ne'
  have hN' : 2 * (p : ℝ) + 3 * (n : ℝ) ≠ 0 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hN
    exact hN
  have harg :
      (2 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) / (2 * p + 3 * n) =
        -(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
            (2 * p + 3 * n) + 1 := by
    rw [fin_rev_cast_real]
    field_simp [hN']
    ring
  calc
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
          (2 * p + 3 * n)) =
      ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
          (2 * p + 3 * n) + (1 : ℤ)) :=
      (ClosedUnitDisc.bdyPtOfReal_add_int _ 1).symm
    _ = ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) /
          (2 * p + 3 * n)) := by
      simpa using congrArg ClosedUnitDisc.bdyPtOfReal harg.symm
    _ = oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 0) t) :=
      (nonOrientableCarrier_boundary_c_pos j t).symm

/-- Every canonical crosscap pairing maps into the trusted nonorientable closure.
@isnad1 id=eqvgen.0h4v.s9.cdba587ae350 from=translated src=- shape=eb90bee2 vocab=e4b2fc94
-/
theorem nonOrientableCarrier_crosscap_a_eqvGen
    {p n : ℕ} (i : Fin p) (t : unitInterval) :
    Relation.EqvGen (NonOrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableCrosscapPosition p n i 0) t))
      (oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableCrosscapPosition p n i 1) t)) := by
  rw [nonOrientableCarrier_crosscap_a_first,
    nonOrientableCarrier_crosscap_a_second]
  exact Relation.EqvGen.rel _ _ (NonOrientableRel.a (n := n) t i)

/-- Every canonical boundary-seam pairing maps into the trusted nonorientable closure.
@isnad1 id=eqvgen.0h4v.s9.0086b5ceed5b from=translated src=- shape=10dbb980 vocab=b2e2e32a
-/
theorem nonOrientableCarrier_boundary_c_eqvGen
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    Relation.EqvGen (NonOrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 0) t))
      (oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 2) (unitInterval.symm t))) := by
  rw [← nonOrientableBoundary_trustedTarget_eq_carrier_c_pos,
    ← nonOrientableBoundary_trustedSource_eq_carrier_c_neg]
  exact Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _
      (NonOrientableRel.c (p := p) t (Fin.rev j)))

end LeanEval.Topology.ClassificationOfSurfaces.NormalForm
