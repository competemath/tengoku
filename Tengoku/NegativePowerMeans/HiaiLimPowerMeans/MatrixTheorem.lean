import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.MatrixMean
import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.MatrixDeterminant
import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.PowerCoordinate
import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.Majorization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Matrix-level determinant theorem for the Lim--Pálfia mean

This file derives the normalized supersolution inequality and the determinant
bound.  Its analytic premise is the multiplicative Lidskii majorization
inequality.
-/

namespace HiaiLimPowerMeans

open Finset Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-- A positive-definite matrix satisfying the power-mean supersolution
inequality.-/
def IsSuper
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    {𝕜 : Type*} [RCLike 𝕜]
    (w : m → ℝ) (A : m → Matrix n n 𝕜) (t : ℝ)
    (X : Matrix n n 𝕜) : Prop :=
  X.PosDef ∧ positivePowerMeanMap w A t X ≤ X

/--
@isnad1 id=issuper.1h7v.s5.5670141701e4 from=translated src=- shape=e6342e5a vocab=a255e8b3
-/
theorem IsMean.isSuper
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    {𝕜 : Type*} [RCLike 𝕜]
    {w : m → ℝ} {A : m → Matrix n n 𝕜} {t : ℝ} {X : Matrix n n 𝕜}
    (hX : IsMean w A t X) :
    IsSuper w A t X := by
  exact ⟨hX.posDef, hX.fixedPoint.ge⟩

/--
@isnad1 id=posdef.1h7v.s6.15fe2bdd4090 from=translated src=- shape=d374e2d3 vocab=ea00d5c1
-/
theorem IsSuper.posDef
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    {𝕜 : Type*} [RCLike 𝕜]
    {w : m → ℝ} {A : m → Matrix n n 𝕜} {t : ℝ} {X : Matrix n n 𝕜}
    (hX : IsSuper w A t X) : X.PosDef := hX.1

/-- Normalizing a power-mean supersolution gives both the matrix inequality
with identity on the right and its trace consequence.
@isnad1 id=and.1h7v.s10.91026ced5291 from=translated src=- shape=4e4f10ef vocab=50f90fbd
-/
theorem IsSuper.norm
    {n m : ℕ} [NeZero n] {𝕜 : Type*} [RCLike 𝕜]
    {w : Fin m → ℝ} {A : Fin m → Matrix (Fin n) (Fin n) 𝕜}
    {t : ℝ} {X : Matrix (Fin n) (Fin n) 𝕜}
    (hX : IsSuper w A t X) :
    ((∑ j, w j •
      (X ^ (-(1 / 2 : ℝ)) * A j * X ^ (-(1 / 2 : ℝ))) ^ t) ≤
        (1 : Matrix (Fin n) (Fin n) 𝕜)) ∧
      ((∑ j, w j * RCLike.re (Matrix.trace
        ((X ^ (-(1 / 2 : ℝ)) * A j * X ^ (-(1 / 2 : ℝ))) ^ t))) ≤
          (n : ℝ)) := by
  let S : Matrix (Fin n) (Fin n) 𝕜 := X ^ (-(1 / 2 : ℝ))
  have hS : S.PosDef := Matrix.PosDef.rpow hX.posDef _
  have hSstar : S.conjTranspose = S := hS.isHermitian.eq
  have hcongr :
      S * positivePowerMeanMap w A t X * S ≤ S * X * S := by
    change (S * X * S - S * positivePowerMeanMap w A t X * S).PosSemidef
    have hdiff : (X - positivePowerMeanMap w A t X).PosSemidef := hX.2
    simpa only [hSstar, mul_sub, sub_mul] using
      hdiff.conjTranspose_mul_mul_same S
  have hmatrix :
      (∑ j, w j •
        (X ^ (-(1 / 2 : ℝ)) * A j * X ^ (-(1 / 2 : ℝ))) ^ t) ≤
          (1 : Matrix (Fin n) (Fin n) 𝕜) := by
    calc
      (∑ j, w j •
        (X ^ (-(1 / 2 : ℝ)) * A j * X ^ (-(1 / 2 : ℝ))) ^ t) =
          S * positivePowerMeanMap w A t X * S :=
            (normalize_positivePowerMeanMap w A t hX.posDef).symm
      _ ≤ S * X * S := hcongr
      _ = 1 := Matrix.PosDef.invHalf_conjugate_self hX.posDef
  refine ⟨hmatrix, ?_⟩
  have htrace :=
    (Matrix.tracePositiveLinearMap (Fin n) ℝ 𝕜).monotone hmatrix
  have hre := RCLike.re_le_re htrace
  simpa [RCLike.smul_re] using hre

/-- The trace of a CFC real power is the sum of the corresponding real
powers of the eigenvalues.
@isnad1 id=eq.1h4v.s8.d11490378fea from=translated src=- shape=65c459d8 vocab=b9923514
-/
theorem Matrix.PosDef.re_trace_rpow_eq_sum_eigenvalues
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {D : Matrix (Fin n) (Fin n) 𝕜} (hD : D.PosDef) (t : ℝ) :
    RCLike.re (Matrix.trace (D ^ t)) =
      ∑ i, (decreasingEigenvalues hD.isHermitian i) ^ t := by
  calc
    RCLike.re (Matrix.trace (D ^ t)) =
        ∑ i, (hD.isHermitian.eigenvalues i) ^ t := by
      rw [CFC.rpow_eq_cfc_real hD.posSemidef.nonneg, hD.isHermitian.cfc_eq]
      simp [Matrix.IsHermitian.cfc, -Unitary.conjStarAlgAut_apply]
    _ = ∑ i, (decreasingEigenvalues hD.isHermitian i) ^ t :=
      (sum_comp_decreasingEigenvalues_eq_eigenvalues hD.isHermitian
        (fun x ↦ x ^ t)).symm

/-- The positive relative matrix occurring in multiplicative Lidskii.-/
noncomputable def relativeMatrix
    {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]
    (Y B : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  Y ^ (-(1 / 2 : ℝ)) * B * Y ^ (-(1 / 2 : ℝ))

/--
@isnad1 id=posdef.2h4v.s6.e8ae96af245b from=translated src=- shape=4e1ea137 vocab=23d718c1
-/
theorem relativeMatrix_posDef
    {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]
    {Y B : Matrix n n 𝕜} (hY : Y.PosDef) (hB : B.PosDef) :
    (relativeMatrix Y B).PosDef := by
  let S : Matrix n n 𝕜 := Y ^ (-(1 / 2 : ℝ))
  have hS : S.PosDef := Matrix.PosDef.rpow hY _
  have hSstar : S.conjTranspose = S := hS.isHermitian.eq
  simpa only [relativeMatrix, show Y ^ (-(1 / 2 : ℝ)) = S from rfl, hSstar] using
    hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hS.isUnit)

/-- Lower multiplicative Lidskii in the logarithmic majorization form stated
as equation (12) in the paper.  This is the named published input of the
conditional determinant argument and is verified in
`BoundaryProofs.LidskiiProof`.-/
def Lidskii (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (n : ℕ) [NeZero n]
    (B Y : Matrix (Fin n) (Fin n) 𝕜)
    (hB : B.PosDef) (hY : Y.PosDef),
      Majorized
        (fun i ↦ Real.log (decreasingEigenvalues hB.isHermitian i) -
          Real.log (decreasingEigenvalues hY.isHermitian i))
        (fun i ↦ Real.log (decreasingEigenvalues
          (relativeMatrix_posDef hY hB).isHermitian i))

/-- The trace consequence of multiplicative Lidskii used in the determinant
proof.-/
def LidskiiTrace (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (n : ℕ) [NeZero n]
    (B Y : Matrix (Fin n) (Fin n) 𝕜)
    (hB : B.PosDef) (hY : Y.PosDef) (t : ℝ), 0 < t →
      (∑ i, (decreasingEigenvalues hB.isHermitian i /
        decreasingEigenvalues hY.isHermitian i) ^ t) ≤
      RCLike.re (Matrix.trace
        ((Y ^ (-(1 / 2 : ℝ)) * B * Y ^ (-(1 / 2 : ℝ))) ^ t))

/-- The trace consequence of multiplicative Lidskii, proved by the finite
exponential case of Karamata's inequality.
@isnad1 id=lidskiit.1h1v.s3.858ec18562df from=translated src=- shape=c612a321 vocab=7db49cbd
-/
theorem Lidskii.trace
    {𝕜 : Type*} [RCLike 𝕜] (hL : Lidskii 𝕜) :
    LidskiiTrace 𝕜 := by
  intro n _ B Y hB hY t ht
  let D : Matrix (Fin n) (Fin n) 𝕜 := relativeMatrix Y B
  have hD : D.PosDef := relativeMatrix_posDef hY hB
  have hb : ∀ i, 0 < decreasingEigenvalues hB.isHermitian i :=
    Matrix.PosDef.decreasingEigenvalues_pos hB
  have hy : ∀ i, 0 < decreasingEigenvalues hY.isHermitian i :=
    Matrix.PosDef.decreasingEigenvalues_pos hY
  have hd : ∀ l, 0 < decreasingEigenvalues hD.isHermitian l :=
    Matrix.PosDef.decreasingEigenvalues_pos hD
  have hKaramata := (hL n B Y hB hY).sum_exp_le_sum_exp ht
  calc
    (∑ i, (decreasingEigenvalues hB.isHermitian i /
        decreasingEigenvalues hY.isHermitian i) ^ t) =
        ∑ i, Real.exp (t *
          (Real.log (decreasingEigenvalues hB.isHermitian i) -
            Real.log (decreasingEigenvalues hY.isHermitian i))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.rpow_def_of_pos (div_pos (hb i) (hy i)),
        Real.log_div (hb i).ne' (hy i).ne']
      congr 1
      ring
    _ ≤ ∑ i, Real.exp (t * Real.log
        (decreasingEigenvalues hD.isHermitian i)) := by
      simpa [D] using hKaramata
    _ = ∑ i, (decreasingEigenvalues hD.isHermitian i) ^ t := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.rpow_def_of_pos (hd i)]
      congr 1
      ring
    _ = RCLike.re (Matrix.trace (D ^ t)) :=
      (Matrix.PosDef.re_trace_rpow_eq_sum_eigenvalues hD t).symm
    _ = RCLike.re (Matrix.trace
        ((Y ^ (-(1 / 2 : ℝ)) * B * Y ^ (-(1 / 2 : ℝ))) ^ t)) := rfl

/-- The determinant bound for a positive-definite supersolution.
@isnad1 id=le.5h7v.s8.898bf06ea403 from=translated src=- shape=eb1ee1f7 vocab=024e192e
-/
theorem IsSuper.powerCoordinateProd_le_det
    {n m : ℕ} [NeZero n] [NeZero m]
    {𝕜 : Type*} [RCLike 𝕜]
    {w : Fin m → ℝ} {A : Fin m → Matrix (Fin n) (Fin n) 𝕜}
    {t : ℝ} {X : Matrix (Fin n) (Fin n) 𝕜}
    (hX : IsSuper w A t X)
    (hL : Lidskii 𝕜)
    (hw : ∀ j, 0 < w j) (hA : ∀ j, (A j).PosDef)
    (ht : 0 < t) :
    (∏ i, powerCoordinate w
      (fun j ↦ decreasingEigenvalues (hA j).isHermitian i) t) ≤ RCLike.re X.det := by
  let y : Fin n → ℝ := decreasingEigenvalues hX.posDef.isHermitian
  let b : Fin m → Fin n → ℝ :=
    fun j ↦ decreasingEigenvalues (hA j).isHermitian
  let q : Fin n → ℝ := fun i ↦ powerCoordinate w (fun j ↦ b j i) t
  have hy : ∀ i, 0 < y i :=
    Matrix.PosDef.decreasingEigenvalues_pos hX.posDef
  have hb : ∀ j i, 0 < b j i :=
    fun j ↦ Matrix.PosDef.decreasingEigenvalues_pos (hA j)
  have hq : ∀ i, 0 < q i := fun i ↦ powerCoordinate_pos hw (fun j ↦ hb j i)
  have hnorm :
      (∑ j, w j * RCLike.re (Matrix.trace
        ((X ^ (-(1 / 2 : ℝ)) * A j * X ^ (-(1 / 2 : ℝ))) ^ t))) ≤
          (n : ℝ) := hX.norm.2
  have hper : ∀ j,
      (∑ i, (b j i / y i) ^ t) ≤
        RCLike.re (Matrix.trace
          ((X ^ (-(1 / 2 : ℝ)) * A j * X ^ (-(1 / 2 : ℝ))) ^ t)) := by
    intro j
    simpa [b, y] using hL.trace n (A j) X (hA j) hX.posDef t ht
  have haggregate :
      (∑ i, ∑ j, w j * (b j i / y i) ^ t) ≤ (n : ℝ) := by
    calc
      (∑ i, ∑ j, w j * (b j i / y i) ^ t) =
          ∑ j, w j * ∑ i, (b j i / y i) ^ t := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
      _ ≤ ∑ j, w j * RCLike.re (Matrix.trace
          ((X ^ (-(1 / 2 : ℝ)) * A j * X ^ (-(1 / 2 : ℝ))) ^ t)) := by
            exact Finset.sum_le_sum fun j _ ↦
              mul_le_mul_of_nonneg_left (hper j) (hw j).le
      _ ≤ (n : ℝ) := hnorm
  have htrace : ∑ i, (q i / y i) ^ t ≤ (n : ℝ) := by
    calc
      ∑ i, (q i / y i) ^ t =
          ∑ i, ∑ j, w j * (b j i / y i) ^ t := by
            apply Finset.sum_congr rfl
            intro i _
            exact powerCoordinate_div_rpow hw (fun j ↦ hb j i) (hy i) ht
      _ ≤ (n : ℝ) := haggregate
  change (∏ i, q i) ≤ RCLike.re X.det
  exact det_ge_prod_of_normalized_trace_bound hX.posDef hq ht htrace

end HiaiLimPowerMeans
