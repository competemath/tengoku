module
public import Tengoku.Stafford38Formal.Stafford38.Geometry.PowerSeriesTangentLimit
public import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse
public import Tengoku.Seed.RingTheory.PowerSeries.Inverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms rowSelector_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms selectedMinorLeftInverse_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_leftInverse_of_selectedMinor_det_isUnit` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms powerSeries_selectedMinorLeftInverse_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms powerSeries_exists_leftInverse_of_selectedMinor_constantCoeff_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/

@[expose] public section

/-!
# Splitting a rectangular power-series matrix from a selected minor

Let `B` be a matrix whose columns are indexed by `κ`.  An embedding
`rows : κ ↪ ι` selects a square minor of `B`.  If the determinant of that
minor is a unit, its nonsingular inverse, followed by the row-selector matrix,
is an explicit left inverse of `B`.

For matrices over `k[[X]]`, it is enough to assume that the determinant of the
selected minor has nonzero constant coefficient.  This file does not assert
that a suitable minor exists for a geometric tangent family.
-/

namespace Stafford38.GeometrySplitTangentMatrix

noncomputable section

universe u v

variable {R : Type u} [CommRing R]

/-- The square submatrix obtained by retaining the explicitly selected rows.-/
def selectedMinor {ι κ : Type*} (B : Matrix ι κ R) (rows : κ ↪ ι) : Matrix κ κ R :=
  fun a b => B (rows a) b

/-- The matrix which restricts a column indexed by `ι` to the selected rows.-/
def rowSelector {ι κ : Type*} [DecidableEq ι] (rows : κ ↪ ι) : Matrix κ ι R :=
  fun a i => if rows a = i then 1 else 0

/--
@isnad1 id=eq.0h5v.s6.427f2b2f2386 from=translated src=- shape=5e1b6238 vocab=84def076
-/
theorem rowSelector_mul
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι κ R) (rows : κ ↪ ι) :
    rowSelector (R := R) rows * B = selectedMinor B rows := by
  ext a b
  simp [Matrix.mul_apply, rowSelector, selectedMinor]

/--
The constructive left inverse supplied by an invertible selected minor.

The nonsingular inverse is the adjugate divided by the determinant in
Mathlib's matrix API; no inverse of the rectangular matrix is used.-/
def selectedMinorLeftInverse
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ R) (rows : κ ↪ ι) : Matrix κ ι R :=
  (selectedMinor B rows)⁻¹ * rowSelector (R := R) rows

/-- A unit determinant of the selected square minor makes the construction a
left inverse of the original rectangular matrix.
@isnad1 id=eq.1h5v.s7.ed9e78891030 from=translated src=- shape=bb69f37a vocab=65c0a003
-/
theorem selectedMinorLeftInverse_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ R) (rows : κ ↪ ι)
    (hdet : IsUnit (selectedMinor B rows).det) :
    selectedMinorLeftInverse B rows * B = 1 := by
  rw [selectedMinorLeftInverse, Matrix.mul_assoc, rowSelector_mul]
  exact Matrix.nonsing_inv_mul _ hdet

/-- The selected-minor construction, packaged as an explicit split matrix.
@isnad1 id=ex.1h5v.s7.3e1c57234a9b from=translated src=- shape=151af627 vocab=d6af5fc5
-/
theorem exists_leftInverse_of_selectedMinor_det_isUnit
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ R) (rows : κ ↪ ι)
    (hdet : IsUnit (selectedMinor B rows).det) :
    ∃ C : Matrix κ ι R, C * B = 1 :=
  ⟨selectedMinorLeftInverse B rows,
    selectedMinorLeftInverse_mul B rows hdet⟩

/-! ## Power-series criterion -/

variable {k : Type v} [Field k]

/-- Over `k[[X]]`, a nonzero constant coefficient makes the selected
determinant a unit and hence gives the same explicit left inverse.
@isnad1 id=eq.1h5v.s7.8e40c0a894b6 from=translated src=- shape=b47a0b52 vocab=92821014
-/
theorem powerSeries_selectedMinorLeftInverse_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ (PowerSeries k)) (rows : κ ↪ ι)
    (hconst : PowerSeries.constantCoeff (selectedMinor B rows).det ≠ 0) :
    selectedMinorLeftInverse B rows * B = 1 := by
  apply selectedMinorLeftInverse_mul
  rw [PowerSeries.isUnit_iff_constantCoeff]
  exact isUnit_iff_ne_zero.mpr hconst

/-- Existence form used by the tangent-limit annihilator construction.
@isnad1 id=ex.1h5v.s7.ee326d834f4c from=translated src=- shape=235d9bd0 vocab=a9070972
-/
theorem powerSeries_exists_leftInverse_of_selectedMinor_constantCoeff_ne_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ (PowerSeries k)) (rows : κ ↪ ι)
    (hconst : PowerSeries.constantCoeff (selectedMinor B rows).det ≠ 0) :
    ∃ C : Matrix κ ι (PowerSeries k), C * B = 1 :=
  ⟨selectedMinorLeftInverse B rows,
    powerSeries_selectedMinorLeftInverse_mul B rows hconst⟩

end

end Stafford38.GeometrySplitTangentMatrix
