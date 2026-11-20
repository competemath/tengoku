import Tengoku.Seed.Analysis.Matrix.Order
import Tengoku.Seed.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Weighted geometric and Lim--Pálfia matrix means

This file starts at the matrix definitions.  Real powers are Mathlib's
continuous-functional-calculus powers in the matrix C⋆-algebra.
-/

namespace HiaiLimPowerMeans

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

variable {n m : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The Kubo--Ando weighted geometric mean
`A #ₜ B = A^(1/2) (A^(-1/2) B A^(-1/2))^t A^(1/2)`.

The definition makes sense for all matrices because CFC real powers are
total.  The results below use it only for positive-definite matrices.-/
noncomputable def weightedGeometricMean
    (A B : Matrix n n 𝕜) (t : ℝ) : Matrix n n 𝕜 :=
  A ^ (1 / 2 : ℝ) *
    (A ^ (-(1 / 2 : ℝ)) * B * A ^ (-(1 / 2 : ℝ))) ^ t *
      A ^ (1 / 2 : ℝ)

/-- Real CFC powers of a positive-definite matrix are positive definite.
@isnad1 id=posdef.1h4v.s7.fb1d39e18008 from=translated src=- shape=da25e74b vocab=ac933f99
-/
theorem Matrix.PosDef.rpow {A : Matrix n n 𝕜} (hA : A.PosDef) (t : ℝ) :
    (A ^ t).PosDef := by
  apply CFC.rpow_nonneg.posSemidef.posDef_iff_isUnit.mpr
  exact hA.isUnit.cfcRpow t hA.posSemidef.nonneg

/-- Taking a real power after matrix inversion negates the exponent.
@isnad1 id=eq.1h4v.s8.6c79be035f21 from=translated src=- shape=6c256ccc vocab=ee218b6c
-/
theorem Matrix.PosDef.inv_rpow {A : Matrix n n 𝕜} (hA : A.PosDef) (t : ℝ) :
    A⁻¹ ^ t = A ^ (-t) := by
  let u : (Matrix n n 𝕜)ˣ := hA.isUnit.unit
  have hu : (u : Matrix n n 𝕜) = A := hA.isUnit.unit_spec
  have h := CFC.rpow_neg u t hA.posSemidef.nonneg
  simpa [hu] using h.symm

/-- The matrix inverse of a positive-definite real power is the power with
negated exponent.
@isnad1 id=eq.1h4v.s8.b9539176131e from=translated src=- shape=99f717fe vocab=ee218b6c
-/
theorem Matrix.PosDef.rpow_inv {A : Matrix n n 𝕜} (hA : A.PosDef) (t : ℝ) :
    (A ^ t)⁻¹ = A ^ (-t) := by
  by_cases ht : t = 0
  · subst t
    simp [CFC.rpow_zero A hA.posSemidef.nonneg]
  · rw [Matrix.nonsing_inv_eq_ringInverse]
    exact CFC.inverse_rpow A t ht hA.isStrictlyPositive

/--
@isnad1 id=eq.1h3v.s8.eb6c0773646c from=translated src=- shape=4e7bff53 vocab=9f7a815c
-/
theorem Matrix.PosDef.invHalf_mul_half {A : Matrix n n 𝕜} (hA : A.PosDef) :
    A ^ (-(1 / 2 : ℝ)) * A ^ (1 / 2 : ℝ) = 1 := by
  exact CFC.rpow_neg_mul_rpow (1 / 2 : ℝ) hA.isStrictlyPositive

/--
@isnad1 id=eq.1h3v.s8.ed39bb980772 from=translated src=- shape=b3735b5b vocab=9f7a815c
-/
theorem Matrix.PosDef.half_mul_invHalf {A : Matrix n n 𝕜} (hA : A.PosDef) :
    A ^ (1 / 2 : ℝ) * A ^ (-(1 / 2 : ℝ)) = 1 := by
  exact CFC.rpow_mul_rpow_neg (1 / 2 : ℝ) hA.isStrictlyPositive

/--
@isnad1 id=eq.1h3v.s8.c2a78ee97f32 from=translated src=- shape=49f4ed4c vocab=9f7a815c
-/
theorem Matrix.PosDef.invHalf_conjugate_self {A : Matrix n n 𝕜}
    (hA : A.PosDef) :
    A ^ (-(1 / 2 : ℝ)) * A * A ^ (-(1 / 2 : ℝ)) = 1 := by
  let R : Matrix n n 𝕜 := A ^ (1 / 2 : ℝ)
  have hRR : R * R = A := by
    have h := CFC.rpow_add (a := A) (x := (1 / 2 : ℝ)) (y := (1 / 2 : ℝ)) hA.isUnit
    norm_num [CFC.rpow_one A hA.posSemidef.nonneg] at h ⊢
    exact h.symm
  calc
    A ^ (-(1 / 2 : ℝ)) * A * A ^ (-(1 / 2 : ℝ)) =
        A ^ (-(1 / 2 : ℝ)) * (R * R) * A ^ (-(1 / 2 : ℝ)) := by rw [hRR]
    _ =
        (A ^ (-(1 / 2 : ℝ)) * R) *
          (R * A ^ (-(1 / 2 : ℝ))) := by noncomm_ring
    _ = 1 := by
      rw [show A ^ (-(1 / 2 : ℝ)) * R = 1 from
          Matrix.PosDef.invHalf_mul_half hA,
        show R * A ^ (-(1 / 2 : ℝ)) = 1 from
          Matrix.PosDef.half_mul_invHalf hA, one_mul]

/-- The weighted geometric mean of two positive-definite matrices is positive
definite (for every real parameter for which the formula is considered).
@isnad1 id=posdef.2h5v.s6.0626da95f03e from=translated src=- shape=d47c0137 vocab=77c68b9f
-/
theorem weightedGeometricMean_posDef
    {A B : Matrix n n 𝕜} (hA : A.PosDef) (hB : B.PosDef) (t : ℝ) :
    (weightedGeometricMean A B t).PosDef := by
  let S : Matrix n n 𝕜 := A ^ (-(1 / 2 : ℝ))
  have hS : S.PosDef := Matrix.PosDef.rpow hA _
  have hinner : (S * B * S).PosDef := by
    have hSstar : Sᴴ = S := hS.isHermitian.eq
    simpa only [hSstar] using hB.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hS.isUnit)
  let R : Matrix n n 𝕜 := A ^ (1 / 2 : ℝ)
  have hR : R.PosDef := Matrix.PosDef.rpow hA _
  have hRstar : Rᴴ = R := hR.isHermitian.eq
  simpa only [weightedGeometricMean, show A ^ (-(1 / 2 : ℝ)) = S from rfl,
    show A ^ (1 / 2 : ℝ) = R from rfl, hRstar] using
      (Matrix.PosDef.rpow hinner t).conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_of_isUnit hR.isUnit)

/-- Self-duality of the weighted geometric mean.
@isnad1 id=eq.2h5v.s7.3adf7ccc6a28 from=translated src=- shape=e50e0358 vocab=5f56ef7b
-/
theorem weightedGeometricMean_inv
    {A B : Matrix n n 𝕜} (hA : A.PosDef) (hB : B.PosDef) (t : ℝ) :
    (weightedGeometricMean A B t)⁻¹ =
      weightedGeometricMean A⁻¹ B⁻¹ t := by
  let R : Matrix n n 𝕜 := A ^ (1 / 2 : ℝ)
  let S : Matrix n n 𝕜 := A ^ (-(1 / 2 : ℝ))
  let D : Matrix n n 𝕜 := S * B * S
  have hS : S.PosDef := Matrix.PosDef.rpow hA _
  have hD : D.PosDef := by
    have hSstar : S.conjTranspose = S := hS.isHermitian.eq
    simpa only [D, hSstar] using hB.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hS.isUnit)
  have hRinv : R⁻¹ = S := by
    simpa [R, S] using Matrix.PosDef.rpow_inv hA (1 / 2 : ℝ)
  have hSinv : S⁻¹ = R := by
    simpa [R, S] using Matrix.PosDef.rpow_inv hA (-(1 / 2 : ℝ))
  have hDtinv : (D ^ t)⁻¹ = D ^ (-t) :=
    Matrix.PosDef.rpow_inv hD t
  have hAinvHalf : A⁻¹ ^ (1 / 2 : ℝ) = S := by
    simpa [S] using Matrix.PosDef.inv_rpow hA (1 / 2 : ℝ)
  have hAinvInvHalf : A⁻¹ ^ (-(1 / 2 : ℝ)) = R := by
    simpa [R] using Matrix.PosDef.inv_rpow hA (-(1 / 2 : ℝ))
  have hDinv : D⁻¹ = R * B⁻¹ * R := by
    calc
      D⁻¹ = (S * B * S)⁻¹ := rfl
      _ = S⁻¹ * B⁻¹ * S⁻¹ := by
        rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mul_assoc]
      _ = R * B⁻¹ * R := by rw [hSinv]
  have hDinvPow : D⁻¹ ^ t = D ^ (-t) := Matrix.PosDef.inv_rpow hD t
  calc
    (weightedGeometricMean A B t)⁻¹ = (R * D ^ t * R)⁻¹ := rfl
    _ = R⁻¹ * (D ^ t)⁻¹ * R⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mul_assoc]
    _ = S * D ^ (-t) * S := by rw [hRinv, hDtinv]
    _ = weightedGeometricMean A⁻¹ B⁻¹ t := by
      simp only [weightedGeometricMean, hAinvHalf, hAinvInvHalf]
      rw [← hDinv, hDinvPow]

section FiniteFamily

variable [Fintype m]

/-- Strictly positive probability weights.-/
structure ProbabilityWeights (m : Type*) [Fintype m] where
  value : m → ℝ
  positive : ∀ j, 0 < value j
  sum_eq_one : ∑ j, value j = 1

/-- The nonlinear map whose positive-definite fixed point is the
Lim--Pálfia power mean.-/
noncomputable def positivePowerMeanMap
    (w : m → ℝ) (A : m → Matrix n n 𝕜) (t : ℝ)
    (X : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  ∑ j, w j • weightedGeometricMean X (A j) t

/-- A positive-definite solution of the Lim--Pálfia fixed-point equation.-/
def IsMean
    (w : m → ℝ) (A : m → Matrix n n 𝕜) (t : ℝ)
    (X : Matrix n n 𝕜) : Prop :=
  X.PosDef ∧ X = positivePowerMeanMap w A t X

/-- The exact finite-dimensional existence-and-uniqueness statement recorded
in Definition 1.1 of the paper.

This named proposition corresponds to Lim--Pálfia, Theorem 3.1 and
Definition 3.2.  A standalone module proves its complex finite-matrix
specialization from Mathlib.-/
def FixedPoint (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (n m : ℕ) [NeZero n] [NeZero m]
    (ω : ProbabilityWeights (Fin m))
    (A : Fin m → Matrix (Fin n) (Fin n) 𝕜) (t : ℝ),
      (∀ j, (A j).PosDef) → 0 < t → t ≤ 1 →
        ∃! X, IsMean ω.value A t X

/-- A positive-definite matrix satisfying the Lim--Pálfia fixed-point
equation.-/
structure Mean
    (ω : ProbabilityWeights m) (A : m → Matrix n n 𝕜) (t : ℝ) where
  value : Matrix n n 𝕜
  isMean : IsMean ω.value A t value

/-- Construct the named Lim--Pálfia mean from existence and uniqueness.-/
noncomputable def FixedPoint.mean
    (hLP : FixedPoint 𝕜)
    {n m : ℕ} [NeZero n] [NeZero m]
    (ω : ProbabilityWeights (Fin m))
    (A : Fin m → Matrix (Fin n) (Fin n) 𝕜) (t : ℝ)
    (hA : ∀ j, (A j).PosDef) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    Mean ω A t := by
  let hUnique := hLP n m ω A t hA ht0 ht1
  exact
    { value := Classical.choose hUnique.exists
      isMean := Classical.choose_spec hUnique.exists }

/-- The negative-order Lim--Pálfia power mean, defined by duality:
`P_r(ω; A) = P_{-r}(ω; A⁻¹)⁻¹` for `-1 ≤ r < 0`.-/
noncomputable def FixedPoint.negativePowerMean
    (hLP : FixedPoint 𝕜)
    {n m : ℕ} [NeZero n] [NeZero m]
    (ω : ProbabilityWeights (Fin m))
    (A : Fin m → Matrix (Fin n) (Fin n) 𝕜) (r : ℝ)
    (hA : ∀ j, (A j).PosDef) (hr1 : -1 ≤ r) (hr0 : r < 0) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  (hLP.mean ω (fun j ↦ (A j)⁻¹) (-r) (fun j ↦ (hA j).inv)
    (neg_pos.mpr hr0) (by linarith)).value⁻¹

/-- The negative-order mean defined by duality is positive definite.
@isnad1 id=posdef.4h6v.s7.a1005e0ec1bf from=translated src=- shape=452d6394 vocab=ead5f275
-/
theorem FixedPoint.negativePowerMean_posDef
    (hLP : FixedPoint 𝕜)
    {n m : ℕ} [NeZero n] [NeZero m]
    (ω : ProbabilityWeights (Fin m))
    (A : Fin m → Matrix (Fin n) (Fin n) 𝕜) (r : ℝ)
    (hA : ∀ j, (A j).PosDef) (hr1 : -1 ≤ r) (hr0 : r < 0) :
    (hLP.negativePowerMean ω A r hA hr1 hr0).PosDef := by
  unfold FixedPoint.negativePowerMean
  exact (hLP.mean ω (fun j ↦ (A j)⁻¹) (-r) (fun j ↦ (hA j).inv)
    (neg_pos.mpr hr0) (by linarith)).isMean.1.inv

/-- The mean selected from `FixedPoint` is the unique
positive-definite fixed point.-/
theorem FixedPoint.eq_mean
    (hLP : FixedPoint 𝕜)
    {n m : ℕ} [NeZero n] [NeZero m]
    (ω : ProbabilityWeights (Fin m))
    (A : Fin m → Matrix (Fin n) (Fin n) 𝕜) (t : ℝ)
    (hA : ∀ j, (A j).PosDef) (ht0 : 0 < t) (ht1 : t ≤ 1)
    {X : Matrix (Fin n) (Fin n) 𝕜}
    (hX : IsMean ω.value A t X) :
    X = (hLP.mean ω A t hA ht0 ht1).value := by
  exact (hLP n m ω A t hA ht0 ht1).unique hX
    (hLP.mean ω A t hA ht0 ht1).isMean

/--
@isnad1 id=posdef.0h7v.s6.efb22387f4fe from=translated src=- shape=d27ace9f vocab=03a2dca4
-/
theorem Mean.posDef
    {ω : ProbabilityWeights m} {A : m → Matrix n n 𝕜} {t : ℝ}
    (P : Mean ω A t) : P.value.PosDef := P.isMean.1

/--
@isnad1 id=eq.0h7v.s6.5ab30d58f156 from=translated src=- shape=cdd0486c vocab=55086d75
-/
theorem Mean.fixedPoint
    {ω : ProbabilityWeights m} {A : m → Matrix n n 𝕜} {t : ℝ}
    (P : Mean ω A t) :
    P.value = positivePowerMeanMap ω.value A t P.value := P.isMean.2

/--
@isnad1 id=posdef.1h7v.s6.ef8c5d71d850 from=translated src=- shape=9e7b2c0c vocab=0dc005f5
-/
theorem IsMean.posDef
    {w : m → ℝ} {A : m → Matrix n n 𝕜} {t : ℝ} {X : Matrix n n 𝕜}
    (hX : IsMean w A t X) : X.PosDef :=
  hX.1

/--
@isnad1 id=eq.1h7v.s6.1d2f8510da57 from=translated src=- shape=6e6d208a vocab=6f4c9251
-/
theorem IsMean.fixedPoint
    {w : m → ℝ} {A : m → Matrix n n 𝕜} {t : ℝ} {X : Matrix n n 𝕜}
    (hX : IsMean w A t X) :
    X = positivePowerMeanMap w A t X :=
  hX.2

/-- With positive weights and positive-definite inputs, the defining map
preserves the positive-definite cone.
@isnad1 id=posdef.3h7v.s7.2f30c775c7fe from=translated src=- shape=51f76795 vocab=4af6cbbd
-/
theorem positivePowerMeanMap_posDef [Nonempty m]
    {w : m → ℝ} {A : m → Matrix n n 𝕜} {t : ℝ} {X : Matrix n n 𝕜}
    (hw : ∀ j, 0 < w j) (hA : ∀ j, (A j).PosDef) (hX : X.PosDef) :
    (positivePowerMeanMap w A t X).PosDef := by
  rw [positivePowerMeanMap]
  simpa using
    (Matrix.posDef_sum (s := Finset.univ) Finset.univ_nonempty
      (fun j _ ↦ (weightedGeometricMean_posDef hX (hA j) t).smul (hw j)))

/-- Congruencing the defining map by `X⁻¹ᐟ²` removes both outer square
roots in every weighted geometric mean.
@isnad1 id=eq.1h7v.s10.54d438ecab83 from=translated src=- shape=59b31294 vocab=7507c929
-/
theorem normalize_positivePowerMeanMap
    (w : m → ℝ) (A : m → Matrix n n 𝕜) (t : ℝ)
    {X : Matrix n n 𝕜} (hX : X.PosDef) :
    X ^ (-(1 / 2 : ℝ)) * positivePowerMeanMap w A t X *
        X ^ (-(1 / 2 : ℝ)) =
      ∑ j, w j •
        (X ^ (-(1 / 2 : ℝ)) * A j * X ^ (-(1 / 2 : ℝ))) ^ t := by
  let S : Matrix n n 𝕜 := X ^ (-(1 / 2 : ℝ))
  let R : Matrix n n 𝕜 := X ^ (1 / 2 : ℝ)
  have hSR : S * R = 1 := Matrix.PosDef.invHalf_mul_half hX
  have hRS : R * S = 1 := Matrix.PosDef.half_mul_invHalf hX
  calc
    S * positivePowerMeanMap w A t X * S =
        ∑ j, w j • (S * weightedGeometricMean X (A j) t * S) := by
          simp only [positivePowerMeanMap, Finset.mul_sum, Finset.sum_mul,
            mul_smul_comm, smul_mul_assoc]
    _ = ∑ j, w j • (S * R * (S * A j * S) ^ t * R * S) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      simp only [weightedGeometricMean, S, R]
      noncomm_ring
    _ = ∑ j, w j • (S * A j * S) ^ t := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      calc
        S * R * (S * A j * S) ^ t * R * S =
            (S * R) * (S * A j * S) ^ t * (R * S) := by noncomm_ring
        _ = (S * A j * S) ^ t := by rw [hSR, hRS, one_mul, mul_one]
    _ = ∑ j, w j •
        (X ^ (-(1 / 2 : ℝ)) * A j * X ^ (-(1 / 2 : ℝ))) ^ t := rfl

end FiniteFamily

end HiaiLimPowerMeans
