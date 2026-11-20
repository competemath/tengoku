import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.Shorting
import Tengoku.NegativePowerMeans.BoundaryProofs.AndoInverse
import Tengoku.Seed.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Standalone verification of Ando's compression inequality

This file proves the published `Ando` ingredient for complex finite matrices.
The assembly module uses it in the unconditional paper-facing results.
-/

namespace HiaiLimPowerMeans

open Matrix MeasureTheory Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal

noncomputable section

/-- The scalar measure in the integral representation of `x ^ p` gives the
same representation in every finite complex matrix algebra.  This is the
matrix specialization of the lifting argument used in Mathlib's proof of
`CFC.exists_measure_nnrpow_eq_integral_cfc₁_rpowIntegrand₀₁`.-/
theorem matrix_nnrpow_integral_representation
    {n : Type*} [Fintype n] [DecidableEq n]
    {p : ℝ≥0} (hp : p ∈ Ioo 0 1)
    {mu : Measure ℝ}
    (hmu : ∀ x ∈ Ici (0 : ℝ),
      IntegrableOn (fun s ↦ Real.rpowIntegrand₀₁ p s x) (Ioi 0) mu ∧
        x ^ (p : ℝ) =
          ∫ s in Ioi 0, Real.rpowIntegrand₀₁ p s x ∂mu)
    (A : Matrix n n ℂ) (hA : 0 ≤ A) :
    IntegrableOn
        (fun s ↦ cfcₙ (Real.rpowIntegrand₀₁ p s) A) (Ioi 0) mu ∧
      A ^ p =
        ∫ s in Ioi 0, cfcₙ (Real.rpowIntegrand₀₁ p s) A ∂mu := by
  have p_pos : 0 < (p : ℝ) := by exact_mod_cast hp.1
  let f s := Real.rpowIntegrand₀₁ p s
  let maxr := sSup (quasispectrum ℝ A)
  have maxr_nonneg : 0 ≤ maxr :=
    le_csSup_of_le (b := 0) (IsCompact.bddAbove (by grind)) (by simp) (by simp)
  let bound (s : ℝ) := ‖f s maxr‖
  have hf : ContinuousOn (Function.uncurry f)
      (Ioi (0 : ℝ) ×ˢ quasispectrum ℝ A) := by
    refine Real.continuousOn_rpowIntegrand₀₁_uncurry hp (quasispectrum ℝ A) ?_
    grind
  have hbound : ∀ᵐ s ∂mu.restrict (Ioi 0),
      ∀ z ∈ quasispectrum ℝ A, ‖f s z‖ ≤ bound s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro z hz
    have hz' : 0 ≤ z := by grind
    unfold bound f
    rw [Real.norm_of_nonneg
          (Real.rpowIntegrand₀₁_nonneg p_pos (le_of_lt hs) hz'),
      Real.norm_of_nonneg
          (Real.rpowIntegrand₀₁_nonneg p_pos (le_of_lt hs) maxr_nonneg)]
    refine Real.rpowIntegrand₀₁_monotoneOn hp (le_of_lt hs)
      hz' maxr_nonneg ?_
    exact le_csSup (IsCompact.bddAbove (quasispectrum.isCompact _)) hz
  have hbound_finite_integral :
      HasFiniteIntegral bound (mu.restrict (Ioi 0)) := by
    rw [hasFiniteIntegral_norm_iff]
    exact (hmu maxr maxr_nonneg).1.2
  have hmapzero : ∀ᵐ (x : ℝ) ∂mu.restrict (Ioi 0),
      Real.rpowIntegrand₀₁ p x 0 = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
    simp
  refine ⟨?_, ?_⟩
  · exact integrableOn_cfcₙ measurableSet_Ioi _ bound A hf hmapzero
      hbound hbound_finite_integral
  · calc
      A ^ p = cfcₙ
          (fun r ↦ ∫ s in Ioi 0, Real.rpowIntegrand₀₁ p s r ∂mu) A := by
        rw [CFC.nnrpow_eq_cfcₙ_real _ _]
        exact cfcₙ_congr fun r _ ↦ (hmu r (by grind)).2
      _ = ∫ s in Ioi 0, cfcₙ (Real.rpowIntegrand₀₁ p s) A ∂mu :=
        cfcₙ_setIntegral measurableSet_Ioi _ bound A hf hmapzero hbound
          hbound_finite_integral hA.isSelfAdjoint

/-- Functional calculus evaluates the power-integral kernel by the expected
resolvent formula.-/
theorem cfcₙ_rpowIntegrand₀₁_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {p s : ℝ} (hp : p ∈ Ioo 0 1) (hs : 0 < s)
    (A : Matrix n n ℂ) (hA : 0 ≤ A) :
    cfcₙ (Real.rpowIntegrand₀₁ p s) A =
      algebraMap ℝ (Matrix n n ℂ) (s ^ (p - 1)) -
        s ^ p • Ring.inverse (algebraMap ℝ (Matrix n n ℂ) s + A) := by
  rw [cfcₙ_eq_cfc
    (hf := (Real.continuousOn_rpowIntegrand₀₁_Ici hp hs).mono (by grind))
    (hf0 := by simp)]
  rw [Real.rpowIntegrand₀₁_eq_sub hp.2.ne hs]
  have hg : ContinuousOn (fun z : ℝ ↦ (s + z)⁻¹) (spectrum ℝ A) := by
    fun_prop (disch := grind -abstractProof)
  have hspectrum : ∀ r ∈ spectrum ℝ A, s + r ≠ 0 := by grind
  have hsub := cfc_sub
    (fun _ : ℝ ↦ s ^ (p - 1)) (fun z : ℝ ↦ s ^ p * (s + z)⁻¹) A
  rw [hsub,
    cfc_const _ A hA.isSelfAdjoint,
    cfc_const_mul _ _ A hg,
    cfc_inv _ A hspectrum (hf := by fun_prop) (ha := hA.isSelfAdjoint),
    cfc_const_add s (fun z : ℝ ↦ z) A (by fun_prop) hA.isSelfAdjoint,
    cfc_id' ℝ A hA.isSelfAdjoint]

/-- Isometric compression fixes real scalar matrices.-/
theorem compress_algebraMap
    {n k : Type*} [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k]
    {V : Matrix n k ℂ} (hV : MatrixIsometry V) (s : ℝ) :
    compress V (algebraMap ℝ (Matrix n n ℂ) s) =
      algebraMap ℝ (Matrix k k ℂ) s := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  simp only [compress, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [hV]

/-- Compression preserves subtraction.-/
theorem compress_sub
    {n k : Type*} [Fintype n]
    (V : Matrix n k ℂ) (A B : Matrix n n ℂ) :
    compress V (A - B) = compress V A - compress V B := by
  simp [compress, Matrix.mul_sub, Matrix.sub_mul]

/-- Compression commutes with complex scalar multiplication.-/
theorem compress_smul
    {n k : Type*} [Fintype n]
    (V : Matrix n k ℂ) (c : ℂ) (A : Matrix n n ℂ) :
    compress V (c • A) = c • compress V A := by
  simp [compress, Matrix.mul_smul, Matrix.smul_mul]

/-- Compression commutes with real scalar multiplication.-/
theorem compress_smul_real
    {n k : Type*} [Fintype n]
    (V : Matrix n k ℂ) (c : ℝ) (A : Matrix n n ℂ) :
    compress V (c • A) = c • compress V A := by
  simp [compress, Matrix.mul_smul, Matrix.smul_mul]

open scoped Classical in
/-- Each resolvent kernel in the integral representation satisfies the
Hansen compression inequality.-/
theorem compress_cfcₙ_rpowIntegrand₀₁_le
    {n k : Type*} [Fintype n]
    [Fintype k] [DecidableEq k]
    {p s : ℝ} (hp : p ∈ Ioo 0 1) (hs : 0 < s)
    {V : Matrix n k ℂ} (hV : MatrixIsometry V)
    {A : Matrix n n ℂ} (hA : A.PosDef) :
    compress V (cfcₙ (Real.rpowIntegrand₀₁ p s) A) ≤
      cfcₙ (Real.rpowIntegrand₀₁ p s) (compress V A) := by
  let Y : Matrix n n ℂ := algebraMap ℝ (Matrix n n ℂ) s + A
  have hscalar :
      (algebraMap ℝ (Matrix n n ℂ) s).PosDef := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Matrix.PosDef.one.smul hs
  have hY : Y.PosDef := hscalar.add hA
  have hcompY : compress V Y =
      algebraMap ℝ (Matrix k k ℂ) s + compress V A := by
    simp only [Y, compress, Matrix.mul_add, Matrix.add_mul]
    rw [show V.conjTranspose * algebraMap ℝ (Matrix n n ℂ) s * V =
        algebraMap ℝ (Matrix k k ℂ) s from compress_algebraMap hV s]
  have hinv : (compress V Y)⁻¹ ≤ compress V Y⁻¹ :=
    inverse_compress_le hV hY
  letI : Invertible Y := hY.isUnit.invertible
  letI : Invertible (compress V Y) :=
    (compress_posDef hV hY).isUnit.invertible
  have hinvRing : Ring.inverse (compress V Y) ≤
      compress V (Ring.inverse Y) := by
    rw [Matrix.nonsing_inv_eq_ringInverse,
      Matrix.nonsing_inv_eq_ringInverse] at hinv
    exact hinv
  rw [cfcₙ_rpowIntegrand₀₁_eq hp hs A hA.posSemidef.nonneg]
  rw [cfcₙ_rpowIntegrand₀₁_eq hp hs (compress V A)
    (compress_posDef hV hA).posSemidef.nonneg]
  calc
    compress V
        (algebraMap ℝ (Matrix n n ℂ) (s ^ (p - 1)) -
          s ^ p • Ring.inverse Y) =
        algebraMap ℝ (Matrix k k ℂ) (s ^ (p - 1)) -
          s ^ p • compress V (Ring.inverse Y) := by
      rw [compress_sub, compress_algebraMap hV,
        compress_smul_real]
    _ ≤ algebraMap ℝ (Matrix k k ℂ) (s ^ (p - 1)) -
          s ^ p • Ring.inverse (compress V Y) := by
      gcongr
    _ = algebraMap ℝ (Matrix k k ℂ) (s ^ (p - 1)) -
          s ^ p • Ring.inverse
            (algebraMap ℝ (Matrix k k ℂ) s + compress V A) := by
      rw [hcompY]

/-- Compression as a continuous complex-linear map between finite matrix
spaces.-/
noncomputable def compressCLM
    {n k : Type*} [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k]
    (V : Matrix n k ℂ) :
    Matrix n n ℂ →L[ℂ] Matrix k k ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := compress V
      map_add' := by
        intro A B
        simp [compress, Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c A
        ext i j
        simp [compress, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul,
          mul_assoc] }

@[simp]
theorem compressCLM_apply
    {n k : Type*} [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k]
    (V : Matrix n k ℂ) (A : Matrix n n ℂ) :
    compressCLM V A = compress V A := rfl

/-- Isometric compression commutes with Bochner integration.-/
theorem compress_setIntegral
    {α n k : Type*} [MeasurableSpace α]
    [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (V : Matrix n k ℂ) {s : Set α} {mu : Measure α}
    {f : α → Matrix n n ℂ} (hf : IntegrableOn f s mu) :
    compress V (∫ x in s, f x ∂mu) =
      ∫ x in s, compress V (f x) ∂mu := by
  exact ((compressCLM V).integral_comp_comm hf).symm

section Hansen

variable {n k : Type*} [Fintype n] [DecidableEq n]
  [Fintype k] [DecidableEq k]

noncomputable local instance : CStarAlgebra (Matrix k k ℂ) where

/-- Hansen's inequality for real powers and rectangular isometric
compressions.-/
theorem compress_rpow_le
    {V : Matrix n k ℂ} (hV : MatrixIsometry V)
    {A : Matrix n n ℂ} (hA : A.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    compress V (A ^ t) ≤ (compress V A) ^ t := by
  rcases ht0.eq_or_lt with rfl | ht0
  · rw [CFC.rpow_zero A hA.posSemidef.nonneg,
      CFC.rpow_zero (compress V A)
        (compress_posDef hV hA).posSemidef.nonneg]
    simpa [compress] using le_of_eq hV
  rcases ht1.eq_or_lt with rfl | ht1
  · simp [CFC.rpow_one A hA.posSemidef.nonneg,
      CFC.rpow_one (compress V A) (compress_posDef hV hA).posSemidef.nonneg]
  let p : ℝ≥0 := ⟨t, ht0.le⟩
  have hp : p ∈ Ioo (0 : ℝ≥0) 1 := by
    constructor
    · exact_mod_cast ht0
    · exact_mod_cast ht1
  have hpReal : (p : ℝ) ∈ Ioo 0 1 := by
    exact_mod_cast hp
  obtain ⟨mu, hmu⟩ :=
    Real.exists_measure_rpow_eq_integral_rpowIntegrand₀₁ hpReal
  have hrepA := matrix_nnrpow_integral_representation hp hmu A
    hA.posSemidef.nonneg
  have hrepC := matrix_nnrpow_integral_representation hp hmu (compress V A)
    (compress_posDef hV hA).posSemidef.nonneg
  change compress V (A ^ (p : ℝ)) ≤ (compress V A) ^ (p : ℝ)
  rw [← CFC.nnrpow_eq_rpow hp.1, ← CFC.nnrpow_eq_rpow hp.1]
  rw [hrepA.2, hrepC.2, compress_setIntegral V hrepA.1]
  apply integral_mono_ae ((compressCLM V).integrable_comp hrepA.1) hrepC.1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact compress_cfcₙ_rpowIntegrand₀₁_le hpReal hs hV hA

end Hansen

/-- The square of the positive square root is the original matrix.-/
theorem Matrix.PosDef.sqrt_mul_sqrt
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) :
    A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) = A := by
  have h := CFC.rpow_add (a := A) (x := (1 / 2 : ℝ))
    (y := (1 / 2 : ℝ)) hA.isUnit
  norm_num [CFC.rpow_one A hA.posSemidef.nonneg] at h ⊢
  exact h.symm

/-- Ando's compression inequality for the weighted geometric mean, obtained
from Hansen's inequality by the standard normalization.-/
theorem weightedGeometricMean_compress_le
    {n k : Type*} [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k]
    {V : Matrix n k ℂ} (hV : MatrixIsometry V)
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    compress V (weightedGeometricMean A B t) ≤
      weightedGeometricMean (compress V A) (compress V B) t := by
  let C : Matrix k k ℂ := compress V A
  let R : Matrix n n ℂ := A ^ (1 / 2 : ℝ)
  let Q : Matrix n n ℂ := A ^ (-(1 / 2 : ℝ))
  let T : Matrix k k ℂ := C ^ (1 / 2 : ℝ)
  let S : Matrix k k ℂ := C ^ (-(1 / 2 : ℝ))
  let X : Matrix n n ℂ := Q * B * Q
  let W : Matrix n k ℂ := R * V * S
  have hC : C.PosDef := compress_posDef hV hA
  have hR : R.PosDef := Matrix.PosDef.rpow hA _
  have hQ : Q.PosDef := Matrix.PosDef.rpow hA _
  have hT : T.PosDef := Matrix.PosDef.rpow hC _
  have hS : S.PosDef := Matrix.PosDef.rpow hC _
  have hX : X.PosDef := by
    have hQstar : Q.conjTranspose = Q := hQ.isHermitian.eq
    simpa only [X, hQstar] using hB.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hQ.isUnit)
  have hRR : R * R = A := by
    simpa only [R] using Matrix.PosDef.sqrt_mul_sqrt hA
  have hW : MatrixIsometry W := by
    change W.conjTranspose * W = 1
    rw [show W.conjTranspose = S * V.conjTranspose * R by
      simp only [W, Matrix.conjTranspose_mul, hR.isHermitian.eq,
        hS.isHermitian.eq, Matrix.mul_assoc]]
    calc
      (S * V.conjTranspose * R) * W =
          S * (V.conjTranspose * ((R * R) * V)) * S := by
        simp only [W, Matrix.mul_assoc]
      _ = S * (V.conjTranspose * (A * V)) * S := by rw [hRR]
      _ = S * C * S := by simp only [C, compress, Matrix.mul_assoc]
      _ = 1 := Matrix.PosDef.invHalf_conjugate_self hC
  have hRXR : R * X * R = B := by
    calc
      R * X * R = (R * Q) * B * (Q * R) := by
        simp only [X]
        noncomm_ring
      _ = B := by
        rw [show R * Q = 1 from Matrix.PosDef.half_mul_invHalf hA,
          show Q * R = 1 from Matrix.PosDef.invHalf_mul_half hA,
          Matrix.one_mul, Matrix.mul_one]
  have hcompressWX : compress W X = S * compress V B * S := by
    calc
      compress W X =
          S * (V.conjTranspose * ((R * X * R) * V)) * S := by
        simp only [compress, W, Matrix.conjTranspose_mul,
          hR.isHermitian.eq, hS.isHermitian.eq, Matrix.mul_assoc]
      _ = S * (V.conjTranspose * (B * V)) * S := by rw [hRXR]
      _ = S * compress V B * S := by simp only [compress, Matrix.mul_assoc]
  have hcompressWt : compress W (X ^ t) =
      S * compress V (weightedGeometricMean A B t) * S := by
    calc
      compress W (X ^ t) =
          S * (V.conjTranspose * ((R * X ^ t * R) * V)) * S := by
        simp only [compress, W, Matrix.conjTranspose_mul,
          hR.isHermitian.eq, hS.isHermitian.eq, Matrix.mul_assoc]
      _ = S * compress V (weightedGeometricMean A B t) * S := by
        simp only [weightedGeometricMean, R, Q, X, compress,
          Matrix.mul_assoc]
  have hHansen := compress_rpow_le hW hX ht0 ht1
  rw [hcompressWt, hcompressWX] at hHansen
  have hconj := compress_mono T hHansen
  have hTS : T * S = 1 := Matrix.PosDef.half_mul_invHalf hC
  have hST : S * T = 1 := Matrix.PosDef.invHalf_mul_half hC
  have hcompressT (Z : Matrix k k ℂ) : compress T Z = T * Z * T := by
    rw [compress, hT.isHermitian.eq]
  have hundo (Z : Matrix k k ℂ) : compress T (S * Z * S) = Z := by
    rw [hcompressT]
    calc
      T * (S * Z * S) * T = (T * S) * Z * (S * T) := by
        noncomm_ring
      _ = Z := by rw [hTS, hST, Matrix.one_mul, Matrix.mul_one]
  calc
    compress V (weightedGeometricMean A B t) =
        compress T (S * compress V (weightedGeometricMean A B t) * S) := by
      exact (hundo _).symm
    _ ≤ compress T ((S * compress V B * S) ^ t) := hconj
    _ = weightedGeometricMean (compress V A) (compress V B) t := by
      rw [hcompressT]
      rfl

/-- Standalone verification of the exact published `Ando` statement.-/
theorem ando_from_mathlib
    (n k : Type*) [Fintype n] [DecidableEq n] [Nonempty n]
    [Fintype k] [DecidableEq k] [Nonempty k] :
    Ando ℂ n k := by
  intro V A B t hV hA hB ht0 ht1
  exact weightedGeometricMean_compress_le hV hA hB ht0 ht1

end

end HiaiLimPowerMeans
