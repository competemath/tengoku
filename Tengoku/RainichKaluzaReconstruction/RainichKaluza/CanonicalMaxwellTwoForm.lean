import Tengoku.RainichKaluzaReconstruction.RainichKaluza.ComplexionCouplingSystem
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.LinearAlgebra.Matrix.Notation
import Tengoku.Seed.LinearAlgebra.Matrix.Trace
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical Lorentzian Maxwell two-form

This file realizes the Phase-III amplitude algebra as an actual antisymmetric
two-tensor in a four-dimensional orthonormal frame of signature `(-,+,+,+)`.
For

`F = E e⁰∧e¹ + B e²∧e³`,

the mixed Maxwell stress is computed directly from

`Tᵐₙ = Fᵐʳ Fₙᵣ - ¼ δᵐₙ F²`.

The calculation supplies a real canonical two-form square root for every
positive non-null stress magnitude.  Transport through smooth oriented
principal frames remains the geometric bundle-level step.
-/

namespace RainichKaluza

open scoped Matrix
open Matrix

/-- Minkowski signature signs in the selected orthonormal frame.-/
def minkowskiSign : Fin 4 → ℝ :=
  ![-1, 1, 1, 1]

/-- Canonical two-form with parallel electric and magnetic amplitudes.-/
def canonicalMaxwellTwoForm (E B : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ 0,  E,  0,  0;
     -E,  0,  0,  0;
      0,  0,  0,  B;
      0,  0, -B,  0]

/-- The canonical tensor is an actual two-form: it is antisymmetric.
@isnad1 id=eq.0h2v.s6.a31f84cdcd21 from=translated src=- shape=0dc5b459 vocab=7190802d
-/
theorem canonicalMaxwellTwoForm_transpose (E B : ℝ) :
    (canonicalMaxwellTwoForm E B)ᵀ = -canonicalMaxwellTwoForm E B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalMaxwellTwoForm, Matrix.transpose_apply]

/-- Raise both indices with the diagonal Minkowski metric.-/
def raiseBothIndices
    (F : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => minkowskiSign i * minkowskiSign j * F i j

/-- Lorentzian quadratic invariant `F_{mn}F^{mn}`.-/
def twoFormQuadraticInvariant
    (F : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∑ i, ∑ j, raiseBothIndices F i j * F i j

/-- Ordinary (unhalved) mixed Maxwell stress.  For the EMD Ricci residual in
`EMD_CONVENTION.md`, this is applied to the curvature-normalized form
`H = exp(a phi / 2) F / sqrt(2)`.-/
noncomputable def maxwellStressMixed
    (F : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j =>
    (∑ r, raiseBothIndices F i r * F j r) -
      (1 / 4 : ℝ) * (1 : Matrix (Fin 4) (Fin 4) ℝ) i j *
        twoFormQuadraticInvariant F

/-- Stress magnitude of the canonical two-form.-/
noncomputable def canonicalStressMagnitude (E B : ℝ) : ℝ :=
  (E ^ 2 + B ^ 2) / 2

/-- Canonical mixed Maxwell stress with negative eigenvalue on the Lorentzian
principal plane and positive eigenvalue on its spacelike complement.-/
noncomputable def canonicalMaxwellStress (E B : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let rho := canonicalStressMagnitude E B
  !![-rho,    0,   0,   0;
         0, -rho,   0,   0;
         0,    0, rho,   0;
         0,    0,   0, rho]

/-- Direct Lorentzian invariant calculation for the canonical two-form.
@isnad1 id=eq.0h2v.s6.cdeba1d9d1af from=translated src=- shape=4dcd1dcb vocab=f1efe714
-/
theorem canonicalMaxwellTwoForm_invariant (E B : ℝ) :
    twoFormQuadraticInvariant (canonicalMaxwellTwoForm E B) =
      2 * (B ^ 2 - E ^ 2) := by
  simp [twoFormQuadraticInvariant, raiseBothIndices, canonicalMaxwellTwoForm,
    minkowskiSign, Fin.sum_univ_succ]
  ring

/-- **Canonical Maxwell stress calculation.**
@isnad1 id=eq.0h2v.s4.c07b160e1d87 from=translated src=- shape=8fdbb122 vocab=ea218a1d
-/
theorem maxwellStressMixed_canonical (E B : ℝ) :
    maxwellStressMixed (canonicalMaxwellTwoForm E B) =
      canonicalMaxwellStress E B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [maxwellStressMixed, canonicalMaxwellStress,
      canonicalStressMagnitude, twoFormQuadraticInvariant, raiseBothIndices,
      canonicalMaxwellTwoForm, minkowskiSign, Fin.sum_univ_succ] <;> ring

/-- The canonical stress obeys the non-null algebraic Rainich square law.
@isnad1 id=eq.0h2v.s7.f7ec168b263b from=translated src=- shape=f74e877e vocab=3671839b
-/
theorem canonicalMaxwellStress_sq (E B : ℝ) :
    canonicalMaxwellStress E B * canonicalMaxwellStress E B =
      canonicalStressMagnitude E B ^ 2 •
        (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, canonicalMaxwellStress, canonicalStressMagnitude,
      Fin.sum_univ_succ] <;> ring

/-- The canonical mixed stress is tracefree.
@isnad1 id=eq.0h2v.s4.eba60a27b241 from=translated src=- shape=07e2c022 vocab=1b560b57
-/
theorem canonicalMaxwellStress_trace (E B : ℝ) :
    Matrix.trace (canonicalMaxwellStress E B) = 0 := by
  simp [Matrix.trace, canonicalMaxwellStress, canonicalStressMagnitude,
    Fin.sum_univ_succ]
  ring

/-- The canonical energy density is nonnegative.  In mixed components it is
`-T⁰₀=ρ` for the selected `(-,+,+,+)` signature.
@isnad1 id=le.0h2v.s5.fdb880fa3687 from=translated src=- shape=73d31fbf vocab=4739473d
-/
theorem canonicalMaxwellStress_energy_nonneg (E B : ℝ) :
    0 ≤ -canonicalMaxwellStress E B 0 0 := by
  simp [canonicalMaxwellStress, canonicalStressMagnitude]
  positivity

/-- Canonical residual with prescribed positive eigenvalue magnitude.-/
def canonicalMaxwellResidual (q : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-q,  0, 0, 0;
       0, -q, 0, 0;
       0,  0, q, 0;
       0,  0, 0, q]

/-- **Real canonical square-root existence.** Every positive non-null
canonical residual is the Maxwell stress of the explicit purely electric
two-form with amplitude `sqrt(2q)`.
@isnad1 id=eq.1h1v.s5.7d501e2c98d7 from=translated src=- shape=b2feb0fe vocab=98c25f2e
-/
theorem exists_canonicalMaxwellTwoForm_of_pos
    (q : ℝ) (hq : 0 < q) :
    maxwellStressMixed
      (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0) =
        canonicalMaxwellResidual q := by
  rw [maxwellStressMixed_canonical]
  have harg : 0 ≤ 2 * q := by positivity
  have hsqrt : (Real.sqrt (2 * q)) ^ 2 = 2 * q := Real.sq_sqrt harg
  have hrho : canonicalStressMagnitude (Real.sqrt (2 * q)) 0 = q := by
    unfold canonicalStressMagnitude
    rw [hsqrt]
    ring
  unfold canonicalMaxwellStress
  rw [hrho]
  rfl

/-- Canonical Hodge-star action on the amplitude pair for the selected
orientation; it squares to minus the identity.-/
def canonicalHodgeStar
    (E B : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  canonicalMaxwellTwoForm (-B) E

/-- The canonical Hodge star squares to `-1` on two-forms.
@isnad1 id=eq.0h2v.s5.dae6d9c80796 from=translated src=- shape=8da2c0ec vocab=a51438e1
-/
theorem canonicalHodgeStar_sq (E B : ℝ) :
    canonicalHodgeStar (-B) E = -canonicalMaxwellTwoForm E B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalHodgeStar, canonicalMaxwellTwoForm]

/-- A unit duality transformation is exactly the linear combination
`cF+s(*F)` in the canonical Hodge convention.
@isnad1 id=eq.0h3v.s7.003bf32f50cb from=translated src=- shape=eec4096e vocab=9bbd5c58
-/
theorem canonicalTwoForm_duality
    (p : DualityParameter) (E B : ℝ) :
    canonicalMaxwellTwoForm (dualityElectric p E B)
        (dualityMagnetic p E B) =
      p.c • canonicalMaxwellTwoForm E B +
        p.s • canonicalHodgeStar E B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dualityElectric, dualityMagnetic, canonicalHodgeStar,
      canonicalMaxwellTwoForm] <;> ring

/-- Canonical duality rotations leave the Maxwell stress unchanged.
@isnad1 id=eq.0h3v.s5.9b96cac9c93c from=translated src=- shape=aa5b388c vocab=209c8d3a
-/
theorem maxwellStressMixed_canonical_duality
    (p : DualityParameter) (E B : ℝ) :
    maxwellStressMixed
        (canonicalMaxwellTwoForm (dualityElectric p E B)
          (dualityMagnetic p E B)) =
      maxwellStressMixed (canonicalMaxwellTwoForm E B) := by
  rw [maxwellStressMixed_canonical, maxwellStressMixed_canonical]
  have hmag :
      canonicalStressMagnitude (dualityElectric p E B)
          (dualityMagnetic p E B) = canonicalStressMagnitude E B := by
    change canonicalMaxwellMagnitude (dualityElectric p E B)
        (dualityMagnetic p E B) / 2 = canonicalMaxwellMagnitude E B / 2
    rw [canonicalMaxwellMagnitude_duality]
  unfold canonicalMaxwellStress
  rw [hmag]

end RainichKaluza
