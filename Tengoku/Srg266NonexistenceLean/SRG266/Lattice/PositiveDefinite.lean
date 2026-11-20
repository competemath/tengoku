/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.RationalSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix

namespace SRG266

section GenericSOS

variable {R ι : Type*} [CommRing R] [Fintype ι]

/--
@isnad1 id=eq.0h3v.s6.2f04cf8024d5 from=translated src=- shape=9786ea1e vocab=60c28547
-/
theorem allOnes_mulVec (a : ι → R) :
    (allOnesMatrix : Matrix ι ι R) *ᵥ a = fun _ => ∑ i, a i := by
  funext i
  show (∑ j, (1 : R) * a j) = ∑ i, a i
  simp

/--
@isnad1 id=eq.0h3v.s6.7ad08cc867f4 from=translated src=- shape=e7345863 vocab=37dfed8a
-/
theorem dotProduct_allOnes_mulVec (a : ι → R) :
    a ⬝ᵥ ((allOnesMatrix : Matrix ι ι R) *ᵥ a) = (∑ i, a i) ^ 2 := by
  rw [allOnes_mulVec]
  show (∑ i, a i * ∑ j, a j) = (∑ i, a i) ^ 2
  rw [← Finset.sum_mul, sq]

/--
@isnad1 id=eq.3h5v.s8.6f2e0af219a3 from=translated src=- shape=cff7fa81 vocab=a46a17fd
-/
theorem dotProduct_mulVec_sos {L P : Matrix ι ι R}
    (hP : P = (11 : R) • L - (6 : R) • (allOnesMatrix : Matrix ι ι R))
    (hPP : P * P = (495 : R) • P) (hPsym : P.IsSymm) (a : ι → R) :
    5445 * (a ⬝ᵥ (L *ᵥ a)) =
      (P *ᵥ a) ⬝ᵥ (P *ᵥ a) + 2970 * (∑ i, a i) ^ 2 := by
  have hswap : P *ᵥ a = a ᵥ* P := (vecMul_eq_mulVec_of_isSymm hPsym a).symm
  have hsq : (P *ᵥ a) ⬝ᵥ (P *ᵥ a) = 495 * (a ⬝ᵥ (P *ᵥ a)) := by
    calc (P *ᵥ a) ⬝ᵥ (P *ᵥ a)
        = ((P *ᵥ a) ᵥ* P) ⬝ᵥ a := Matrix.dotProduct_mulVec _ _ _
      _ = ((a ᵥ* P) ᵥ* P) ⬝ᵥ a := by rw [← hswap]
      _ = (a ᵥ* (P * P)) ⬝ᵥ a := by rw [Matrix.vecMul_vecMul]
      _ = a ⬝ᵥ ((P * P) *ᵥ a) := (Matrix.dotProduct_mulVec _ _ _).symm
      _ = a ⬝ᵥ (((495 : R) • P) *ᵥ a) := by rw [hPP]
      _ = 495 * (a ⬝ᵥ (P *ᵥ a)) := by
          rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hlin : a ⬝ᵥ (P *ᵥ a) =
      11 * (a ⬝ᵥ (L *ᵥ a)) - 6 * (∑ i, a i) ^ 2 := by
    rw [hP, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.smul_mulVec,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      dotProduct_allOnes_mulVec]
  rw [hsq, hlin]
  ring

variable [LinearOrder R] [IsStrictOrderedRing R]

/--
@isnad1 id=le.3h5v.s8.d1199146baad from=translated src=- shape=b09266c0 vocab=1c2e18a8
-/
theorem dotProduct_mulVec_nonneg {L P : Matrix ι ι R}
    (hP : P = (11 : R) • L - (6 : R) • (allOnesMatrix : Matrix ι ι R))
    (hPP : P * P = (495 : R) • P) (hPsym : P.IsSymm) (a : ι → R) :
    0 ≤ a ⬝ᵥ (L *ᵥ a) := by
  have hsos := dotProduct_mulVec_sos hP hPP hPsym a
  have h1 : (0 : R) ≤ (P *ᵥ a) ⬝ᵥ (P *ᵥ a) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h2 : (0 : R) ≤ (∑ i, a i) ^ 2 := sq_nonneg _
  linarith

/--
@isnad1 id=eq.4h5v.s8.b9e80e56317b from=translated src=- shape=836b39a8 vocab=b157e156
-/
theorem dotProduct_mulVec_eq_zero {L P : Matrix ι ι R}
    (hP : P = (11 : R) • L - (6 : R) • (allOnesMatrix : Matrix ι ι R))
    (hPP : P * P = (495 : R) • P) (hPsym : P.IsSymm) (a : ι → R)
    (ha : a ⬝ᵥ (L *ᵥ a) = 0) : L *ᵥ a = 0 := by
  have hsos := dotProduct_mulVec_sos hP hPP hPsym a
  rw [ha, mul_zero] at hsos
  have h1 : (0 : R) ≤ (P *ᵥ a) ⬝ᵥ (P *ᵥ a) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h2 : (0 : R) ≤ (∑ i, a i) ^ 2 := sq_nonneg _
  have hsum : (∑ i, a i) = 0 := by
    have : (∑ i, a i) ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hzero : (P *ᵥ a) ⬝ᵥ (P *ᵥ a) = 0 := by linarith
  have hPa : P *ᵥ a = 0 := by
    funext i
    have hterm : ∀ j ∈ (Finset.univ : Finset ι), (P *ᵥ a) j * (P *ᵥ a) j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg _).mp hzero
    have := hterm i (Finset.mem_univ i)
    simpa using mul_self_eq_zero.mp this
  have hexp : P *ᵥ a = (11 : R) • (L *ᵥ a) - (6 : R) • (fun _ : ι => ∑ i, a i) := by
    rw [hP, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, allOnes_mulVec]
  rw [hexp] at hPa
  funext i
  have hi := congrFun hPa i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hsum,
    mul_zero, sub_zero] at hi
  show (L *ᵥ a) i = 0
  linarith

end GenericSOS

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/--
@isnad1 id=eq.0h3v.s8.b60843f2508b from=translated src=- shape=e07208ba vocab=eb60d6bb
-/
theorem localSupportNumerator_eq_zsmul (x : V) :
    localSupportNumerator G x =
      (11 : ℤ) • localGramMatrix G x -
        (6 : ℤ) • (allOnesMatrix :
          Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ) := by
  ext B C
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, allOnesMatrix_apply,
    mul_one]
  rfl

/--
@isnad1 id=eq.1h3v.s8.176e61bbdea9 from=translated src=- shape=74606e36 vocab=50a1ffda
-/
theorem localSupportNumerator_sq_zsmul (hG : IsHypothetical G) (x : V) :
    localSupportNumerator G x * localSupportNumerator G x =
      (495 : ℤ) • localSupportNumerator G x := by
  ext B C
  rw [localSupportNumerator_sq_apply G hG x B C, Matrix.smul_apply, smul_eq_mul]

/--
@isnad1 id=issymm.0h3v.s5.3bf26d9f50f7 from=translated src=- shape=9bbb9fae vocab=0114741e
-/
theorem localSupportNumerator_isSymm (x : V) : (localSupportNumerator G x).IsSymm :=
  Matrix.IsSymm.ext fun B C => by
    simp only [localSupportNumerator, localGramMatrix_comm G x C B]

def localSupportNumeratorRat (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℚ :=
  fun B C => (localSupportNumerator G x B C : ℚ)

/--
@isnad1 id=eq.0h3v.s8.8791d2d4a224 from=translated src=- shape=e07208ba vocab=4a5030d5
-/
theorem localSupportNumeratorRat_eq_smul (x : V) :
    localSupportNumeratorRat G x =
      (11 : ℚ) • localGramMatrixRat G x -
        (6 : ℚ) • (allOnesMatrix :
          Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℚ) := by
  ext B C
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, allOnesMatrix_apply,
    mul_one]
  show ((11 * localGramMatrix G x B C - 6 : ℤ) : ℚ) =
    11 * ((localGramMatrix G x B C : ℤ) : ℚ) - 6
  push_cast
  ring

/--
@isnad1 id=eq.1h3v.s7.19e1f181f80d from=translated src=- shape=74606e36 vocab=2d6c474b
-/
theorem localSupportNumeratorRat_sq (hG : IsHypothetical G) (x : V) :
    localSupportNumeratorRat G x * localSupportNumeratorRat G x =
      (495 : ℚ) • localSupportNumeratorRat G x := by
  ext B C
  have h := localSupportNumerator_sq_apply G hG x B C
  rw [Matrix.mul_apply] at h
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  show (∑ D, ((localSupportNumerator G x B D : ℤ) : ℚ) *
      ((localSupportNumerator G x D C : ℤ) : ℚ)) =
    495 * ((localSupportNumerator G x B C : ℤ) : ℚ)
  rw [show (∑ D, ((localSupportNumerator G x B D : ℤ) : ℚ) *
        ((localSupportNumerator G x D C : ℤ) : ℚ)) =
      ((∑ D, localSupportNumerator G x B D * localSupportNumerator G x D C : ℤ) : ℚ) by
    push_cast; rfl]
  rw [h]
  push_cast
  ring

/--
@isnad1 id=issymm.0h3v.s5.9f9185c34025 from=translated src=- shape=9bbb9fae vocab=31558bb0
-/
theorem localSupportNumeratorRat_isSymm (x : V) :
    (localSupportNumeratorRat G x).IsSymm :=
  Matrix.IsSymm.ext fun B C => by
    show ((localSupportNumerator G x C B : ℤ) : ℚ) =
      ((localSupportNumerator G x B C : ℤ) : ℚ)
    simp only [localSupportNumerator, localGramMatrix_comm G x C B]

/--
@isnad1 id=eq.1h4v.s8.1bb76bcef495 from=translated src=- shape=248c8723 vocab=24079826
-/
theorem localGram_sos (hG : IsHypothetical G) (x : V)
    (a : SecondSubconstituent G x → ℤ) :
    5445 * (a ⬝ᵥ (localGramMatrix G x *ᵥ a)) =
      (localSupportNumerator G x *ᵥ a) ⬝ᵥ (localSupportNumerator G x *ᵥ a) +
        2970 * (∑ B, a B) ^ 2 :=
  dotProduct_mulVec_sos (localSupportNumerator_eq_zsmul G x)
    (localSupportNumerator_sq_zsmul G hG x) (localSupportNumerator_isSymm G x) a

/--
@isnad1 id=eq.1h4v.s8.b11ceef7e5bc from=translated src=- shape=248c8723 vocab=fc3eb6bd
-/
theorem localGramRat_sos (hG : IsHypothetical G) (x : V)
    (a : SecondSubconstituent G x → ℚ) :
    5445 * (a ⬝ᵥ (localGramMatrixRat G x *ᵥ a)) =
      (localSupportNumeratorRat G x *ᵥ a) ⬝ᵥ (localSupportNumeratorRat G x *ᵥ a) +
        2970 * (∑ B, a B) ^ 2 :=
  dotProduct_mulVec_sos (localSupportNumeratorRat_eq_smul G x)
    (localSupportNumeratorRat_sq G hG x) (localSupportNumeratorRat_isSymm G x) a

/--
@isnad1 id=le.1h4v.s7.50f34b826893 from=translated src=- shape=bafcbd40 vocab=5ce49bdf
-/
theorem localGram_quadratic_nonneg (hG : IsHypothetical G) (x : V)
    (a : SecondSubconstituent G x → ℤ) :
    0 ≤ a ⬝ᵥ (localGramMatrix G x *ᵥ a) :=
  dotProduct_mulVec_nonneg (localSupportNumerator_eq_zsmul G x)
    (localSupportNumerator_sq_zsmul G hG x) (localSupportNumerator_isSymm G x) a

/--
@isnad1 id=iff.1h4v.s8.8fe504f26636 from=translated src=- shape=0de06fac vocab=dee23ecd
-/
theorem localGram_quadratic_eq_zero_iff (hG : IsHypothetical G) (x : V)
    (a : SecondSubconstituent G x → ℤ) :
    a ⬝ᵥ (localGramMatrix G x *ᵥ a) = 0 ↔ localGramMatrix G x *ᵥ a = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, dotProduct_zero]⟩
  exact dotProduct_mulVec_eq_zero (localSupportNumerator_eq_zsmul G x)
    (localSupportNumerator_sq_zsmul G hG x) (localSupportNumerator_isSymm G x) a h

/--
@isnad1 id=le.1h4v.s7.c949e1c161d4 from=translated src=- shape=bafcbd40 vocab=3227b759
-/
theorem localGramRat_quadratic_nonneg (hG : IsHypothetical G) (x : V)
    (a : SecondSubconstituent G x → ℚ) :
    0 ≤ a ⬝ᵥ (localGramMatrixRat G x *ᵥ a) :=
  dotProduct_mulVec_nonneg (localSupportNumeratorRat_eq_smul G x)
    (localSupportNumeratorRat_sq G hG x) (localSupportNumeratorRat_isSymm G x) a

/--
@isnad1 id=iff.1h4v.s8.052fd62e0fa6 from=translated src=- shape=0de06fac vocab=5463debd
-/
theorem localGramRat_quadratic_eq_zero_iff (hG : IsHypothetical G) (x : V)
    (a : SecondSubconstituent G x → ℚ) :
    a ⬝ᵥ (localGramMatrixRat G x *ᵥ a) = 0 ↔ localGramMatrixRat G x *ᵥ a = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, dotProduct_zero]⟩
  exact dotProduct_mulVec_eq_zero (localSupportNumeratorRat_eq_smul G x)
    (localSupportNumeratorRat_sq G hG x) (localSupportNumeratorRat_isSymm G x) a h

/--
@isnad1 id=eq.0h5v.s10.52e04c1ca333 from=translated src=- shape=ca04c9a7 vocab=9129e996
-/
theorem integralGramPairing_mk (x : V) (a b : SecondSubconstituent G x → ℤ) :
    integralGramPairing G x (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      a ⬝ᵥ (localGramMatrix G x *ᵥ b) :=
  Matrix.toBilin'_apply' _ _ _

/--
@isnad1 id=issymm.0h3v.s7.87ab153b6486 from=translated src=- shape=3c0fbbd4 vocab=8244fff2
-/
theorem integralGramPairing_isSymm (x : V) : (integralGramPairing G x).IsSymm := by
  constructor
  intro v w
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact (integralGramForm_isSymm G x).eq v w

/--
@isnad1 id=le.1h4v.s10.6b0f0605827d from=translated src=- shape=87e7c6c8 vocab=1dfcb0ff
-/
theorem integralGramPairing_nonneg (hG : IsHypothetical G) (x : V)
    (v : IntegralGramLattice G x) : 0 ≤ integralGramPairing G x v v := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [integralGramPairing_mk]
  exact localGram_quadratic_nonneg G hG x a

/--
@isnad1 id=lt.2h4v.s10.734d68fa4520 from=translated src=- shape=26313d67 vocab=d241a03e
-/
theorem integralGramPairing_posDef (hG : IsHypothetical G) (x : V)
    (v : IntegralGramLattice G x) (hv : v ≠ 0) :
    0 < integralGramPairing G x v v := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [integralGramPairing_mk]
  rcases lt_or_eq_of_le (localGram_quadratic_nonneg G hG x a) with h | h
  · exact h
  · refine absurd ?_ hv
    rw [Submodule.Quotient.mk_eq_zero, ← integralGramKernel_eq_relations]
    exact LinearMap.mem_ker.mpr
      ((localGram_quadratic_eq_zero_iff G hG x a).mp h.symm)

/--
@isnad1 id=nondegen.1h3v.s7.ddd256863191 from=translated src=- shape=cdd5e181 vocab=39747228
-/
theorem integralGramPairing_nondegenerate (hG : IsHypothetical G) (x : V) :
    (integralGramPairing G x).Nondegenerate :=
  (LinearMap.BilinForm.nondegenerate_iff' (integralGramPairing G x)
      (integralGramPairing_nonneg G hG x)
      (LinearMap.BilinForm.isSymm_iff.mp (integralGramPairing_isSymm G x))).mpr
    (integralGramPairing_posDef G hG x)

/--
@isnad1 id=eq.1h3v.s7.c8dc61e9e586 from=translated src=- shape=7a9b1ea6 vocab=86ed243c
-/
theorem finrank_integralGramLattice (hG : IsHypothetical G) (x : V) :
    Module.finrank ℤ (IntegralGramLattice G x) = 12 := by
  have h :
      Module.finrank ℤ (IntegralGramLattice G x) +
          Module.finrank ℤ (integralGramRelations G x) =
        Module.finrank ℤ (SecondSubconstituent G x → ℤ) :=
    (integralGramRelations G x).finrank_quotient_add_finrank
  have hker : Module.finrank ℤ (integralGramRelations G x) = 208 := by
    rw [← integralGramKernel_eq_relations]
    exact integralGramKernel_finrank G hG x
  rw [hker, Module.finrank_pi ℤ, secondSubconstituent_card G hG x] at h
  omega

/--
@isnad1 id=eq.0h4v.s9.ad40cd043d07 from=translated src=- shape=8eaf77e3 vocab=90885450
-/
theorem mk_eq_sum_smul_generator (x : V) (a : SecondSubconstituent G x → ℤ) :
    (Submodule.Quotient.mk a : IntegralGramLattice G x) =
      ∑ B, a B • integralGramGenerator G x B := by
  have hsum : (∑ B, a B • Pi.single B (1 : ℤ)) = a := by
    funext C
    simp [Pi.single_apply, Finset.sum_ite_eq]
  calc (Submodule.Quotient.mk a : IntegralGramLattice G x)
      = (integralGramRelations G x).mkQ (∑ B, a B • Pi.single B (1 : ℤ)) := by
        rw [hsum]; rfl
    _ = ∑ B, a B • integralGramGenerator G x B := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun B _ => by rw [map_smul]; rfl

/--
@isnad1 id=eq.0h5v.s11.6699a68c1e68 from=translated src=- shape=8ebae208 vocab=18f7707b
-/
theorem integralGramPairing_apply_mk_right (x : V)
    (v : IntegralGramLattice G x) (a : SecondSubconstituent G x → ℤ) :
    integralGramPairing G x v (Submodule.Quotient.mk a) =
      ∑ B, a B * integralGramPairing G x v (integralGramGenerator G x B) := by
  rw [mk_eq_sum_smul_generator G x a, map_sum]
  exact Finset.sum_congr rfl fun B _ => by rw [map_smul, smul_eq_mul]

theorem eq_zero_of_pairing_generators_eq_zero (hG : IsHypothetical G) (x : V)
    (v : IntegralGramLattice G x)
    (h : ∀ B, integralGramPairing G x v (integralGramGenerator G x B) = 0) :
    v = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have hzero :
      integralGramPairing G x (Submodule.Quotient.mk a)
        (Submodule.Quotient.mk a) = 0 := by
    rw [integralGramPairing_apply_mk_right]
    exact Finset.sum_eq_zero fun B _ => by rw [h B, mul_zero]
  by_contra hv
  exact (integralGramPairing_posDef G hG x _ hv).ne' hzero

/--
@isnad1 id=le.1h4v.s10.fdbe4b66b74e from=translated src=- shape=87e7c6c8 vocab=eebb18c3
-/
theorem ratGramForm_nonneg (hG : IsHypothetical G) (x : V) (v : ratGramSpace G x) :
    0 ≤ ratGramForm G x v v := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [ratGramForm_mk]
  exact localGramRat_quadratic_nonneg G hG x a

/--
@isnad1 id=lt.2h4v.s10.5beb49343d3e from=translated src=- shape=26313d67 vocab=66e06045
-/
theorem ratGramForm_posDef (hG : IsHypothetical G) (x : V)
    (v : ratGramSpace G x) (hv : v ≠ 0) : 0 < ratGramForm G x v v := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [ratGramForm_mk]
  rcases lt_or_eq_of_le (localGramRat_quadratic_nonneg G hG x a) with h | h
  · exact h
  · refine absurd ?_ hv
    rw [Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_ker.mpr
      ((localGramRat_quadratic_eq_zero_iff G hG x a).mp h.symm)

/--
@isnad1 id=nondegen.1h3v.s7.f27adcc4ecda from=translated src=- shape=cdd5e181 vocab=182edadd
-/
theorem ratGramForm_nondegenerate (hG : IsHypothetical G) (x : V) :
    (ratGramForm G x).Nondegenerate :=
  (LinearMap.BilinForm.nondegenerate_iff' (ratGramForm G x)
      (ratGramForm_nonneg G hG x)
      (LinearMap.BilinForm.isSymm_iff.mp (ratGramForm_isSymm G x))).mpr
    (ratGramForm_posDef G hG x)

end SRG266
