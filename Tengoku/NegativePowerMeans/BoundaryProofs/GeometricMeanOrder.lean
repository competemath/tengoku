import Tengoku.NegativePowerMeans.BoundaryProofs.AndoProof

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Order properties of the weighted geometric mean

This file derives the congruence, symmetry, monotonicity, and scalar
homogeneity properties needed in the standalone proof of the Lim--Pálfia
fixed-point theorem.  It introduces no assumptions beyond Mathlib.
-/

namespace HiaiLimPowerMeans

open Matrix Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable local instance : CStarAlgebra (Matrix n n ℂ) where

/-- Real powers commute with multiplication by a positive real scalar.
@isnad1 id=eq.2h4v.s8.3e76c239c62e from=translated src=- shape=1d891aaa vocab=0e73a635
-/
theorem Matrix.PosDef.rpow_smul
    {A : Matrix n n ℂ} (hA : A.PosDef) {c t : ℝ} (hc : 0 < c) :
    (c • A) ^ t = c ^ t • A ^ t := by
  have hfun : ∀ x ∈ spectrum ℝ A, 0 < c * x := by
    intro x hx
    exact mul_pos hc (hA.isStrictlyPositive.spectrum_pos hx)
  have hrpow_cont : ContinuousOn (fun x : ℝ ↦ x ^ t) (spectrum ℝ A) :=
    ContinuousOn.rpow_const (by fun_prop) (by
      intro x hx
      exact Or.inl (ne_of_gt (hA.isStrictlyPositive.spectrum_pos hx)))
  calc
    (c • A) ^ t = (cfc (fun x : ℝ ↦ c * x) A) ^ t := by
      rw [cfc_const_mul_id c A hA.isHermitian.isSelfAdjoint]
    _ = cfc (fun x : ℝ ↦ (c * x) ^ t) A :=
      CFC.cfc_rpow hfun
    _ = cfc (fun x : ℝ ↦ c ^ t * x ^ t) A := by
      apply cfc_congr
      intro x hx
      change (c * x) ^ t = c ^ t * x ^ t
      rw [Real.mul_rpow (le_of_lt hc)
        (le_of_lt (hA.isStrictlyPositive.spectrum_pos hx))]
    _ = c ^ t • cfc (fun x : ℝ ↦ x ^ t) A := by
      exact cfc_const_mul (R := ℝ) (A := Matrix n n ℂ) (c ^ t)
        (fun x : ℝ ↦ x ^ t) A hrpow_cont
    _ = c ^ t • A ^ t := by
      rw [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]

/-- The weighted geometric mean is monotone in its second variable.
@isnad1 id=le.6h5v.s6.470775223144 from=translated src=- shape=85be4203 vocab=71723233
-/
theorem weightedGeometricMean_mono_right
    {A B C : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hBC : B ≤ C) :
    weightedGeometricMean A B t ≤ weightedGeometricMean A C t := by
  let S : Matrix n n ℂ := A ^ (-(1 / 2 : ℝ))
  let R : Matrix n n ℂ := A ^ (1 / 2 : ℝ)
  have hS : S.PosDef := Matrix.PosDef.rpow hA _
  have hR : R.PosDef := Matrix.PosDef.rpow hA _
  have hSB : (S * B * S).PosDef := by
    simpa only [hS.isHermitian.eq] using hB.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hS.isUnit)
  have hSC : (S * C * S).PosDef := by
    simpa only [hS.isHermitian.eq] using hC.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hS.isUnit)
  have hinner : S * B * S ≤ S * C * S := by
    simpa only [compress, hS.isHermitian.eq] using compress_mono S hBC
  have hpow : (S * B * S) ^ t ≤ (S * C * S) ^ t :=
    CFC.rpow_le_rpow ⟨ht0, ht1⟩ hinner
  have hout := compress_mono R hpow
  simpa only [weightedGeometricMean, S, R, compress, hR.isHermitian.eq]
    using hout

/-- The transformer inequality for an invertible square congruence.  The
normalizing matrix in Ando's argument is still an isometry; only positive
definiteness of the compressed first input uses invertibility here.
@isnad1 id=le.5h5v.s7.6f7d28222c6c from=translated src=- shape=ce710322 vocab=1386c290
-/
theorem weightedGeometricMean_compress_le_of_isUnit
    {V A B : Matrix n n ℂ} (hV : IsUnit V)
    (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    compress V (weightedGeometricMean A B t) ≤
      weightedGeometricMean (compress V A) (compress V B) t := by
  let C : Matrix n n ℂ := compress V A
  let R : Matrix n n ℂ := A ^ (1 / 2 : ℝ)
  let Q : Matrix n n ℂ := A ^ (-(1 / 2 : ℝ))
  let T : Matrix n n ℂ := C ^ (1 / 2 : ℝ)
  let S : Matrix n n ℂ := C ^ (-(1 / 2 : ℝ))
  let X : Matrix n n ℂ := Q * B * Q
  let W : Matrix n n ℂ := R * V * S
  have hC : C.PosDef := by
    exact hA.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hV)
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
  have hcompressT (Z : Matrix n n ℂ) : compress T Z = T * Z * T := by
    rw [compress, hT.isHermitian.eq]
  have hundo (Z : Matrix n n ℂ) : compress T (S * Z * S) = Z := by
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

/-- The weighted geometric mean is invariant under invertible congruence.
@isnad1 id=eq.4h5v.s7.7f237c5001fa from=translated src=- shape=7065e503 vocab=f7ac1ec7
-/
theorem weightedGeometricMean_compress_eq
    (V : (Matrix n n ℂ)ˣ) {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    compress (V : Matrix n n ℂ) (weightedGeometricMean A B t) =
      weightedGeometricMean (compress (V : Matrix n n ℂ) A)
        (compress (V : Matrix n n ℂ) B) t := by
  let C : Matrix n n ℂ := compress (V : Matrix n n ℂ) A
  let D : Matrix n n ℂ := compress (V : Matrix n n ℂ) B
  let W : (Matrix n n ℂ)ˣ := V⁻¹
  have hC : C.PosDef := hA.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit V.isUnit)
  have hD : D.PosDef := hB.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit V.isUnit)
  have hforward :
      compress (V : Matrix n n ℂ) (weightedGeometricMean A B t) ≤
        weightedGeometricMean C D t := by
    exact weightedGeometricMean_compress_le_of_isUnit V.isUnit hA hB ht0 ht1
  have hVW : (V : Matrix n n ℂ) * (W : Matrix n n ℂ) = 1 := by
    simp [W]
  have hWV : (W : Matrix n n ℂ) * (V : Matrix n n ℂ) = 1 := by
    simp [W]
  have hCA : compress (W : Matrix n n ℂ) C = A := by
    calc
      compress (W : Matrix n n ℂ) C =
          ((V : Matrix n n ℂ) * (W : Matrix n n ℂ)).conjTranspose *
            A * ((V : Matrix n n ℂ) * (W : Matrix n n ℂ)) := by
        simp only [C, compress, Matrix.conjTranspose_mul]
        noncomm_ring
      _ = A := by rw [hVW]; simp
  have hDB : compress (W : Matrix n n ℂ) D = B := by
    calc
      compress (W : Matrix n n ℂ) D =
          ((V : Matrix n n ℂ) * (W : Matrix n n ℂ)).conjTranspose *
            B * ((V : Matrix n n ℂ) * (W : Matrix n n ℂ)) := by
        simp only [D, compress, Matrix.conjTranspose_mul]
        noncomm_ring
      _ = B := by rw [hVW]; simp
  have hback :
      compress (W : Matrix n n ℂ) (weightedGeometricMean C D t) ≤
        weightedGeometricMean A B t := by
    simpa only [hCA, hDB] using
      weightedGeometricMean_compress_le_of_isUnit W.isUnit hC hD ht0 ht1
  have hback' := compress_mono (V : Matrix n n ℂ) hback
  have hundocomp (Z : Matrix n n ℂ) :
      compress (V : Matrix n n ℂ)
          (compress (W : Matrix n n ℂ) Z) = Z := by
    calc
      compress (V : Matrix n n ℂ) (compress (W : Matrix n n ℂ) Z) =
          ((W : Matrix n n ℂ) * (V : Matrix n n ℂ)).conjTranspose *
            Z * ((W : Matrix n n ℂ) * (V : Matrix n n ℂ)) := by
        simp only [compress, Matrix.conjTranspose_mul]
        noncomm_ring
      _ = Z := by rw [hWV]; simp
  apply le_antisymm hforward
  simpa only [hundocomp] using hback'

/--
@isnad1 id=eq.0h3v.s7.5471f9b4d36b from=translated src=- shape=7dbf6901 vocab=043a53cf
-/
@[simp]
theorem weightedGeometricMean_one_left (B : Matrix n n ℂ) (t : ℝ) :
    weightedGeometricMean 1 B t = B ^ t := by
  simp [weightedGeometricMean]

/-- The geometric mean with identity as its second argument.
@isnad1 id=eq.1h3v.s7.79970805ec16 from=translated src=- shape=933acf93 vocab=3e6c94bd
-/
theorem weightedGeometricMean_one_right
    {A : Matrix n n ℂ} (hA : A.PosDef) (t : ℝ) :
    weightedGeometricMean A 1 t = A ^ (1 - t) := by
  have hQsq :
      A ^ (-(1 / 2 : ℝ)) * A ^ (-(1 / 2 : ℝ)) = A ^ (-1 : ℝ) := by
    rw [← CFC.rpow_add hA.isUnit]
    congr 1
    norm_num
  have hpow : (A ^ (-1 : ℝ)) ^ t = A ^ (-t) := by
    rw [CFC.rpow_rpow A (-1 : ℝ) t (by norm_num) hA.isStrictlyPositive]
    congr 1
    ring
  rw [weightedGeometricMean]
  simp only [Matrix.mul_one, hQsq, hpow]
  calc
    A ^ (1 / 2 : ℝ) * A ^ (-t) * A ^ (1 / 2 : ℝ) =
        A ^ ((1 / 2 : ℝ) + (-t)) * A ^ (1 / 2 : ℝ) := by
      rw [CFC.rpow_add hA.isUnit]
    _ = A ^ (((1 / 2 : ℝ) + (-t)) + (1 / 2 : ℝ)) := by
      exact (CFC.rpow_add (a := A) (x := (1 / 2 : ℝ) + (-t))
        (y := (1 / 2 : ℝ)) hA.isUnit).symm
    _ = A ^ (1 - t) := by
      congr 1
      ring

/-- Symmetry with complementary weight.
@isnad1 id=eq.4h4v.s6.0122339ab418 from=translated src=- shape=48751312 vocab=22517cd2
-/
theorem weightedGeometricMean_symm
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    weightedGeometricMean A B t = weightedGeometricMean B A (1 - t) := by
  let R : Matrix n n ℂ := A ^ (1 / 2 : ℝ)
  let Q : Matrix n n ℂ := A ^ (-(1 / 2 : ℝ))
  let C : Matrix n n ℂ := Q * B * Q
  have hR : R.PosDef := Matrix.PosDef.rpow hA _
  have hQ : Q.PosDef := Matrix.PosDef.rpow hA _
  have hC : C.PosDef := by
    simpa only [C, hQ.isHermitian.eq] using hB.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hQ.isUnit)
  let U : (Matrix n n ℂ)ˣ := hR.isUnit.unit
  have hU : (U : Matrix n n ℂ) = R := hR.isUnit.unit_spec
  have hcompOne : compress (U : Matrix n n ℂ) 1 = A := by
    rw [hU, compress, hR.isHermitian.eq, Matrix.mul_one]
    exact Matrix.PosDef.sqrt_mul_sqrt hA
  have hcompC : compress (U : Matrix n n ℂ) C = B := by
    rw [hU, compress, hR.isHermitian.eq]
    calc
      R * C * R = (R * Q) * B * (Q * R) := by
        simp only [C]
        noncomm_ring
      _ = B := by
        rw [show R * Q = 1 from Matrix.PosDef.half_mul_invHalf hA,
          show Q * R = 1 from Matrix.PosDef.invHalf_mul_half hA,
          Matrix.one_mul, Matrix.mul_one]
  have ht'0 : 0 ≤ 1 - t := by linarith
  have ht'1 : 1 - t ≤ 1 := by linarith
  calc
    weightedGeometricMean A B t =
        compress (U : Matrix n n ℂ) (weightedGeometricMean 1 C t) := by
      rw [weightedGeometricMean_compress_eq U Matrix.PosDef.one hC ht0 ht1,
        hcompOne, hcompC]
    _ = compress (U : Matrix n n ℂ) (C ^ t) := by
      rw [weightedGeometricMean_one_left]
    _ = compress (U : Matrix n n ℂ)
        (weightedGeometricMean C 1 (1 - t)) := by
      rw [weightedGeometricMean_one_right hC]
      congr 2
      ring
    _ = weightedGeometricMean B A (1 - t) := by
      rw [weightedGeometricMean_compress_eq U hC Matrix.PosDef.one ht'0 ht'1,
        hcompC, hcompOne]

/-- The weighted geometric mean is monotone in its first variable.
@isnad1 id=le.6h5v.s6.0e8d4b71efd5 from=translated src=- shape=545cf90c vocab=71723233
-/
theorem weightedGeometricMean_mono_left
    {A B C : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hAB : A ≤ B) :
    weightedGeometricMean A C t ≤ weightedGeometricMean B C t := by
  have ht'0 : 0 ≤ 1 - t := by linarith
  have ht'1 : 1 - t ≤ 1 := by linarith
  rw [weightedGeometricMean_symm hA hC ht0 ht1,
    weightedGeometricMean_symm hB hC ht0 ht1]
  exact weightedGeometricMean_mono_right hC hA hB ht'0 ht'1 hAB

/-- Positive scalar homogeneity in the second variable.
@isnad1 id=eq.3h5v.s7.bd721435fdf2 from=translated src=- shape=0d1c18ea vocab=d856411b
-/
theorem weightedGeometricMean_smul_right
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {c t : ℝ} (hc : 0 < c) :
    weightedGeometricMean A (c • B) t =
      c ^ t • weightedGeometricMean A B t := by
  let S : Matrix n n ℂ := A ^ (-(1 / 2 : ℝ))
  have hS : S.PosDef := Matrix.PosDef.rpow hA _
  have hinner : (S * B * S).PosDef := by
    simpa only [hS.isHermitian.eq] using hB.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hS.isUnit)
  rw [weightedGeometricMean, weightedGeometricMean]
  have hscale : S * (c • B) * S = c • (S * B * S) := by
    simp
  rw [hscale, Matrix.PosDef.rpow_smul hinner hc]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rfl

/-- Positive scalar homogeneity in the first variable.
@isnad1 id=eq.5h5v.s7.60f62ac3fd16 from=translated src=- shape=5c0cd975 vocab=3055df66
-/
theorem weightedGeometricMean_smul_left
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {c t : ℝ} (hc : 0 < c) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    weightedGeometricMean (c • A) B t =
      c ^ (1 - t) • weightedGeometricMean A B t := by
  have hcA : (c • A).PosDef := hA.smul hc
  have ht'0 : 0 ≤ 1 - t := by linarith
  have ht'1 : 1 - t ≤ 1 := by linarith
  calc
    weightedGeometricMean (c • A) B t =
        weightedGeometricMean B (c • A) (1 - t) :=
      weightedGeometricMean_symm hcA hB ht0 ht1
    _ = c ^ (1 - t) • weightedGeometricMean B A (1 - t) :=
      weightedGeometricMean_smul_right hB hA hc
    _ = c ^ (1 - t) • weightedGeometricMean A B t := by
      rw [weightedGeometricMean_symm hA hB ht0 ht1]

end

end HiaiLimPowerMeans
