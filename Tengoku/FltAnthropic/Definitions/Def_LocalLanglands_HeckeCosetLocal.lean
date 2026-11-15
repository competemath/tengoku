import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_LocalHeckeInstance
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Tengoku.FltAnthropic.Definitions.Def_AbstractHeckeOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Matrix MulAction
open scoped Pointwise

namespace LocalGL2

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

def unipotentR (b : R) : GL (Fin 2) R :=
  ⟨!![1, b; 0, 1], !![1, -b; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def weylR : GL (Fin 2) R :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def unipotentInt (K : Type*) [Field K] [Algebra R K] (b : R) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.map (algebraMap R K) (unipotentR b)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/--
@isnad1 id=mem.0h3v.s8.687d5df9ad6f from=translated src=- shape=4478ff7c vocab=79b0debd
-/
lemma unipotentInt_mem (b : R) : unipotentInt K b ∈ integralSubgroup R K :=
  ⟨_, rfl⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/--
@isnad1 id=eq.0h3v.s8.bb0fcfd115d2 from=translated src=- shape=f8a42c51 vocab=eb344e1d
-/
@[simp] lemma coe_unipotentInt (b : R) :
    (unipotentInt K b : Matrix (Fin 2) (Fin 2) K) = !![1, algebraMap R K b; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentInt, unipotentR, Matrix.GeneralLinearGroup.map]

def weylInt (R K : Type*) [CommRing R] [Field K] [Algebra R K] : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.map (algebraMap R K) (weylR (R := R))

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/--
@isnad1 id=mem.0h2v.s8.af90fb06938f from=translated src=- shape=2902dce3 vocab=fea1eb74
-/
lemma weylInt_mem : weylInt R K ∈ integralSubgroup R K :=
  ⟨_, rfl⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/--
@isnad1 id=eq.0h2v.s8.4d81b7cb7c79 from=translated src=- shape=ad8c85f3 vocab=caecbad8
-/
@[simp] lemma coe_weylInt :
    (weylInt R K : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylInt, weylR, Matrix.GeneralLinearGroup.map]

variable (ϖ : R)

section Defs

variable (hϖ0 : algebraMap R K ϖ ≠ 0)

def diagPi : GL (Fin 2) K :=
  ⟨!![algebraMap R K ϖ, 0; 0, 1], !![(algebraMap R K ϖ)⁻¹, 0; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hϖ0], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hϖ0]⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/--
@isnad1 id=eq.1h3v.s9.d7006d991a39 from=translated src=- shape=0a662549 vocab=b734e8d4
-/
@[simp] lemma coe_diagPi :
    (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) = !![algebraMap R K ϖ, 0; 0, 1] := rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/--
@isnad1 id=eq.1h3v.s9.63e7c65ca39e from=translated src=- shape=4831739c vocab=b83b1bc5
-/
@[simp] lemma coe_diagPi_inv :
    ((diagPi ϖ hϖ0)⁻¹ : GL (Fin 2) K).val = !![(algebraMap R K ϖ)⁻¹, 0; 0, 1] := rfl

def localRepSome (b : R) : GL (Fin 2) K :=
  unipotentInt K b * diagPi ϖ hϖ0

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/--
@isnad1 id=eq.1h4v.s9.c88b011b6725 from=translated src=- shape=d51e6843 vocab=7d11fe7c
-/
@[simp] lemma coe_localRepSome (b : R) :
    (localRepSome ϖ hϖ0 b : Matrix (Fin 2) (Fin 2) K)
      = !![algebraMap R K ϖ, algebraMap R K b; 0, 1] := by
  show (unipotentInt K b : Matrix (Fin 2) (Fin 2) K) * (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
      = _
  rw [coe_unipotentInt, coe_diagPi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def localRepInf : GL (Fin 2) K :=
  weylInt R K * diagPi ϖ hϖ0 * weylInt R K

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/--
@isnad1 id=eq.1h3v.s9.b5589d63f8dd from=translated src=- shape=a1462c0a vocab=4e64441f
-/
@[simp] lemma coe_localRepInf :
    (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, algebraMap R K ϖ] := by
  show (weylInt R K : Matrix (Fin 2) (Fin 2) K) * (diagPi ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K)
      * (weylInt R K : Matrix (Fin 2) (Fin 2) K) = _
  rw [coe_weylInt, coe_diagPi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

/--
@isnad1 id=eq.0h3v.s7.ffebe8647aa5 from=translated src=- shape=1f3facdb vocab=257aad02
-/
lemma unipotentInt_inv (b : R) : (unipotentInt K b)⁻¹ = unipotentInt K (-b) := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, coe_unipotentInt, coe_unipotentInt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, map_neg]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

/--
@isnad1 id=eq.1h4v.s9.feb56e9a373f from=translated src=- shape=994c80bb vocab=f76d09c6
-/
@[simp] lemma coe_localRepSome_inv (b : R) :
    ((localRepSome ϖ hϖ0 b)⁻¹ : GL (Fin 2) K).val
      = !![(algebraMap R K ϖ)⁻¹, -(algebraMap R K b) * (algebraMap R K ϖ)⁻¹; 0, 1] := by
  rw [localRepSome, _root_.mul_inv_rev, Units.val_mul, coe_diagPi_inv, unipotentInt_inv,
    coe_unipotentInt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

def heckeMulSet : Set (GL (Fin 2) K) :=
  (integralSubgroup R K : Set (GL (Fin 2) K)) * ({diagPi ϖ hϖ0} : Set (GL (Fin 2) K))

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/--
@isnad1 id=iff.1h4v.s9.27e4ecdcbd2f from=translated src=- shape=cbf287ac vocab=efb3cc1a
-/
lemma mem_heckeMulSet_iff {x : GL (Fin 2) K} :
    x ∈ heckeMulSet ϖ hϖ0 ↔ ∃ u ∈ integralSubgroup R K, u * diagPi ϖ hϖ0 = x := by
  unfold heckeMulSet
  rw [Set.mem_mul]
  constructor
  · rintro ⟨u, hu, y, hy, rfl⟩
    exact ⟨u, hu, by rw [Set.mem_singleton_iff] at hy; rw [hy]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, diagPi ϖ hϖ0, rfl, rfl⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

/--
@isnad1 id=mem.1h4v.s10.ebd76efdbb3c from=translated src=- shape=3b945a74 vocab=26a2760f
-/
lemma mk_localRepSome_mem_image (b : R) :
    QuotientGroup.mk (localRepSome ϖ hϖ0 b)
      ∈ (QuotientGroup.mk '' (heckeMulSet ϖ hϖ0) :
          Set (GL (Fin 2) K ⧸ integralSubgroup R K)) :=
  Set.mem_image_of_mem _
    ((mem_heckeMulSet_iff ϖ hϖ0).mpr ⟨unipotentInt K b, unipotentInt_mem b, rfl⟩)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

/--
@isnad1 id=mem.1h3v.s10.ddb3c3fa89c8 from=translated src=- shape=fead4711 vocab=14f0bf9d
-/
lemma mk_localRepInf_mem_image :
    QuotientGroup.mk (localRepInf ϖ hϖ0)
      ∈ (QuotientGroup.mk '' (heckeMulSet ϖ hϖ0) :
          Set (GL (Fin 2) K ⧸ integralSubgroup R K)) := by
  refine (Set.mem_image _ _ _).mpr ⟨weylInt R K * diagPi ϖ hϖ0,
    (mem_heckeMulSet_iff ϖ hϖ0).mpr ⟨weylInt R K, weylInt_mem, rfl⟩, ?_⟩
  rw [QuotientGroup.eq]
  show (weylInt R K * diagPi ϖ hϖ0)⁻¹ * (weylInt R K * diagPi ϖ hϖ0 * weylInt R K)
      ∈ integralSubgroup R K
  rw [inv_mul_cancel_left]
  exact weylInt_mem

omit [IsDomain R] [IsDiscreteValuationRing R] in

/--
@isnad1 id=dvd.2h5v.s9.28d021a48aaa from=translated src=- shape=92597056 vocab=46e1e44a
-/
lemma dvd_sub_of_mk_localRepSome_eq {b b' : R}
    (h : (QuotientGroup.mk (localRepSome ϖ hϖ0 b) : _ ⧸ integralSubgroup R K)
        = QuotientGroup.mk (localRepSome ϖ hϖ0 b')) :
    ϖ ∣ b' - b := by
  rw [QuotientGroup.eq] at h
  obtain ⟨r, hr⟩ := exists_entry_eq_of_mem_integralSubgroup h 0 1

  rw [Units.val_mul, coe_localRepSome_inv, coe_localRepSome] at hr
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at hr
  norm_num at hr

  have hϖinj := IsFractionRing.injective R K
  refine ⟨r, hϖinj ?_⟩
  rw [map_sub, map_mul]
  field_simp at hr ⊢
  linear_combination -hr

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

/--
@isnad1 id=eq.2h5v.s9.68174cf6ec3d from=translated src=- shape=e2bb7e16 vocab=3cd0ddac
-/
lemma mk_localRepSome_eq_of_dvd_sub {b b' : R} (h : ϖ ∣ b' - b) :
    (QuotientGroup.mk (localRepSome ϖ hϖ0 b) : _ ⧸ integralSubgroup R K)
      = QuotientGroup.mk (localRepSome ϖ hϖ0 b') := by
  obtain ⟨r, hr⟩ := h
  rw [QuotientGroup.eq]
  refine ⟨unipotentR r, ?_⟩

  refine Units.ext ?_
  show (Matrix.GeneralLinearGroup.map (algebraMap R K) (unipotentR r)).val
      = (((localRepSome ϖ hϖ0 b)⁻¹ * localRepSome ϖ hϖ0 b' : GL (Fin 2) K)).val
  rw [Units.val_mul, coe_localRepSome_inv, coe_localRepSome]
  have hb' : algebraMap R K (b' - b) = algebraMap R K ϖ * algebraMap R K r := by
    rw [← map_mul, hr]
  rw [map_sub] at hb'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentR, Matrix.GeneralLinearGroup.map, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp
  linear_combination -hb'

omit [IsDomain R] [IsDiscreteValuationRing R] in

/--
@isnad1 id=ne.2h4v.s9.af299e88b054 from=translated src=- shape=a9a94526 vocab=564b037a
-/
lemma mk_localRepSome_ne_mk_localRepInf (hϖ : ¬ IsUnit ϖ) (b : R) :
    (QuotientGroup.mk (localRepSome ϖ hϖ0 b) : _ ⧸ integralSubgroup R K)
      ≠ QuotientGroup.mk (localRepInf ϖ hϖ0) := by
  intro h
  rw [QuotientGroup.eq] at h
  obtain ⟨r, hr⟩ := exists_entry_eq_of_mem_integralSubgroup h 0 0
  rw [Units.val_mul, coe_localRepSome_inv, coe_localRepInf] at hr
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at hr
  norm_num at hr

  apply hϖ
  have hϖinj := IsFractionRing.injective R K
  have hone : ϖ * r = 1 := by
    apply hϖinj
    rw [map_mul, map_one, hr, mul_inv_cancel₀ hϖ0]
  exact IsUnit.of_mul_eq_one r hone

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

/--
@isnad1 id=mem.2h4v.s10.309fa1c206fe from=translated src=- shape=9fd62927 vocab=e34207bd
-/
lemma conj_diagPi_mem_of_dvd (z : GL (Fin 2) R)
    (h : ϖ ∣ (z : Matrix (Fin 2) (Fin 2) R) 0 1) :
    (diagPi ϖ hϖ0)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K) z * diagPi ϖ hϖ0
      ∈ integralSubgroup R K := by
  obtain ⟨e, he⟩ := h
  set M : Matrix (Fin 2) (Fin 2) R :=
    !![(z : Matrix (Fin 2) (Fin 2) R) 0 0, e;
       (z : Matrix (Fin 2) (Fin 2) R) 1 0 * ϖ, (z : Matrix (Fin 2) (Fin 2) R) 1 1] with hM
  have hdet : M.det = ((z : Matrix (Fin 2) (Fin 2) R)).det := by
    rw [hM, Matrix.det_fin_two_of, Matrix.det_fin_two, he]
    ring
  have hMunit : IsUnit M.det := by
    rw [hdet, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det z).isUnit
  refine ⟨Matrix.GeneralLinearGroup.mk'' M hMunit, ?_⟩
  have hz01 : (algebraMap R K) ((z : Matrix (Fin 2) (Fin 2) R) 0 1)
      = algebraMap R K ϖ * algebraMap R K e := by rw [← map_mul, he]

  have hcomm : diagPi ϖ hϖ0 * Matrix.GeneralLinearGroup.map (algebraMap R K)
        (Matrix.GeneralLinearGroup.mk'' M hMunit)
      = Matrix.GeneralLinearGroup.map (algebraMap R K) z * diagPi ϖ hϖ0 := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_diagPi]
    rw [show ((Matrix.GeneralLinearGroup.map (algebraMap R K) z) : Matrix (Fin 2) (Fin 2) K)
        = (algebraMap R K).mapMatrix (z : Matrix (Fin 2) (Fin 2) R) from rfl]
    rw [show ((Matrix.GeneralLinearGroup.map (algebraMap R K)
          (Matrix.GeneralLinearGroup.mk'' M hMunit)) : Matrix (Fin 2) (Fin 2) K)
        = (algebraMap R K).mapMatrix M from rfl]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hM, Matrix.mul_apply, Fin.sum_univ_two, RingHom.mapMatrix_apply, map_mul,
        hz01]
    ring

  symm
  calc (diagPi ϖ hϖ0)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K) z * diagPi ϖ hϖ0
      = (diagPi ϖ hϖ0)⁻¹ * (Matrix.GeneralLinearGroup.map (algebraMap R K) z
          * diagPi ϖ hϖ0) := by rw [mul_assoc]
    _ = (diagPi ϖ hϖ0)⁻¹ * (diagPi ϖ hϖ0 * Matrix.GeneralLinearGroup.map (algebraMap R K)
          (Matrix.GeneralLinearGroup.mk'' M hMunit)) := by rw [hcomm]
    _ = Matrix.GeneralLinearGroup.map (algebraMap R K)
          (Matrix.GeneralLinearGroup.mk'' M hMunit) := by rw [inv_mul_cancel_left]

omit [IsFractionRing R K] in

/--
@isnad1 id=or.3h4v.s10.eddc7fd1d710 from=translated src=- shape=b36e2fb3 vocab=5522ee83
-/
theorem exists_rep_of_mem_heckeMulSet (hϖirr : Irreducible ϖ) {x : GL (Fin 2) K}
    (hx : x ∈ heckeMulSet ϖ hϖ0) :
    (∃ b, (QuotientGroup.mk (localRepSome ϖ hϖ0 b) : _ ⧸ integralSubgroup R K)
        = QuotientGroup.mk x)
      ∨ (QuotientGroup.mk (localRepInf ϖ hϖ0) : _ ⧸ integralSubgroup R K)
          = QuotientGroup.mk x := by
  obtain ⟨u, hu, rfl⟩ := (mem_heckeMulSet_iff ϖ hϖ0).mp hx
  obtain ⟨y, rfl⟩ := hu
  by_cases hd : IsUnit ((y : Matrix (Fin 2) (Fin 2) R) 1 1)
  ·
    left
    obtain ⟨d, hd⟩ := hd
    refine ⟨(y : Matrix (Fin 2) (Fin 2) R) 0 1 * (↑d⁻¹ : R), ?_⟩
    rw [QuotientGroup.eq]
    have key : (localRepSome ϖ hϖ0 ((y : Matrix (Fin 2) (Fin 2) R) 0 1 * (↑d⁻¹ : R)))⁻¹
        * (Matrix.GeneralLinearGroup.map (algebraMap R K) y * diagPi ϖ hϖ0)
        = (diagPi ϖ hϖ0)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K)
            (unipotentR (-((y : Matrix (Fin 2) (Fin 2) R) 0 1 * (↑d⁻¹ : R))) * y)
          * diagPi ϖ hϖ0 := by
      rw [localRepSome, _root_.mul_inv_rev, unipotentInt_inv, map_mul, unipotentInt]
      group
    rw [key]
    refine conj_diagPi_mem_of_dvd ϖ hϖ0 _ ?_

    have : ((unipotentR (-((y : Matrix (Fin 2) (Fin 2) R) 0 1 * (↑d⁻¹ : R))) * y :
        GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := by
      rw [Units.val_mul]
      show ((!![1, -((y : Matrix (Fin 2) (Fin 2) R) 0 1 * (↑d⁻¹ : R)); 0, 1] :
          Matrix (Fin 2) (Fin 2) R) * (y : Matrix (Fin 2) (Fin 2) R)) 0 1 = 0
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp only [← hd]
      simp [mul_assoc, Units.inv_mul]
    rw [this]
    exact dvd_zero ϖ
  ·
    right
    have hdvd : ϖ ∣ (y : Matrix (Fin 2) (Fin 2) R) 1 1 := by
      rw [← Ideal.mem_span_singleton, ← hϖirr.maximalIdeal_eq]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hd)
    rw [QuotientGroup.eq]
    have key : (localRepInf ϖ hϖ0)⁻¹
        * (Matrix.GeneralLinearGroup.map (algebraMap R K) y * diagPi ϖ hϖ0)
        = (weylInt R K)⁻¹ * ((diagPi ϖ hϖ0)⁻¹
            * Matrix.GeneralLinearGroup.map (algebraMap R K) (weylR⁻¹ * y)
          * diagPi ϖ hϖ0) := by
      rw [localRepInf, weylInt, map_mul, map_inv]
      group
    rw [key]
    rw [mul_mem_cancel_left (inv_mem (weylInt_mem (R := R) (K := K)))]
    refine conj_diagPi_mem_of_dvd ϖ hϖ0 _ ?_

    have : ((weylR⁻¹ * y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1
        = (y : Matrix (Fin 2) (Fin 2) R) 1 1 := by
      rw [Units.val_mul]
      show ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R) * (y : Matrix (Fin 2) (Fin 2) R)) 0 1
          = _
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp
    rw [this]
    exact hdvd

omit [IsFractionRing R K] in

/--
@isnad1 id=finite.2h3v.s9.47758b85d2c0 from=translated src=- shape=fd4c8617 vocab=a6e9eb0c
-/
theorem finite_image_mul_diagPi (hϖirr : Irreducible ϖ)
    [Finite (R ⧸ Ideal.span {ϖ})] :
    (QuotientGroup.mk '' (heckeMulSet ϖ hϖ0) :
      Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite := by
  classical
  refine Set.Finite.subset (Set.finite_range
    (fun c : Option (R ⧸ Ideal.span {ϖ}) =>
      (Option.elim c (QuotientGroup.mk (localRepInf ϖ hϖ0))
        (fun cc => QuotientGroup.mk (localRepSome ϖ hϖ0 (Quotient.out cc)))
        : GL (Fin 2) K ⧸ integralSubgroup R K))) ?_
  rintro _ ⟨x, hx, rfl⟩
  rcases exists_rep_of_mem_heckeMulSet ϖ hϖ0 hϖirr hx with ⟨b, hb⟩ | hinf
  · refine ⟨some (Ideal.Quotient.mk _ b), ?_⟩
    show QuotientGroup.mk (localRepSome ϖ hϖ0 (Quotient.out (Ideal.Quotient.mk _ b))) = _
    rw [← hb]
    refine mk_localRepSome_eq_of_dvd_sub ϖ hϖ0 ?_
    rw [← Ideal.mem_span_singleton]
    rw [← Ideal.Quotient.eq]
    exact (Ideal.Quotient.mk_out _).symm
  · exact ⟨none, hinf⟩

noncomputable def localHeckeOperator (hϖirr : Irreducible ϖ)
    [Finite (R ⧸ Ideal.span {ϖ})]
    {A : Type*} [AddCommMonoid A] [DistribMulAction (GL (Fin 2) K) A]
    (S : Type*) [Ring S] [Module S A] [SMulCommClass (GL (Fin 2) K) S A] :
    MulAction.fixedPoints (integralSubgroup R K) A
      →ₗ[S] MulAction.fixedPoints (integralSubgroup R K) A :=
  AbstractHeckeOperator.HeckeOperator (R := S) (diagPi ϖ hϖ0) (integralSubgroup R K)
    (integralSubgroup R K) (finite_image_mul_diagPi ϖ hϖ0 hϖirr)

omit [IsDomain R] [IsDiscreteValuationRing R] in

/--
@isnad1 id=and.2h3v.s10.e42f5df1d6f0 from=translated src=- shape=4facc6b4 vocab=b416ac36
-/
theorem three_distinct_cosets (hϖirr : Irreducible ϖ) :
    (QuotientGroup.mk (localRepSome ϖ hϖ0 0) : _ ⧸ integralSubgroup R K)
        ≠ QuotientGroup.mk (localRepSome ϖ hϖ0 1)
      ∧ (QuotientGroup.mk (localRepSome ϖ hϖ0 0) : _ ⧸ integralSubgroup R K)
          ≠ QuotientGroup.mk (localRepInf ϖ hϖ0)
      ∧ (QuotientGroup.mk (localRepSome ϖ hϖ0 1) : _ ⧸ integralSubgroup R K)
          ≠ QuotientGroup.mk (localRepInf ϖ hϖ0) := by
  refine ⟨fun h => ?_, mk_localRepSome_ne_mk_localRepInf ϖ hϖ0 hϖirr.not_isUnit 0,
    mk_localRepSome_ne_mk_localRepInf ϖ hϖ0 hϖirr.not_isUnit 1⟩
  have := dvd_sub_of_mk_localRepSome_eq ϖ hϖ0 h
  rw [sub_zero] at this
  exact hϖirr.not_isUnit (isUnit_of_dvd_one this)

omit [IsDomain R] [IsDiscreteValuationRing R] in

/--
@isnad1 id=ne.2h4v.s9.78e0fcc49cde from=translated src=- shape=0a4fc905 vocab=b416ac36
-/
theorem localRepInf_not_covered_by_finite (hϖirr : Irreducible ϖ) :
    ∀ b : R, (QuotientGroup.mk (localRepInf ϖ hϖ0) : _ ⧸ integralSubgroup R K)
      ≠ QuotientGroup.mk (localRepSome ϖ hϖ0 b) :=
  fun b h => mk_localRepSome_ne_mk_localRepInf ϖ hϖ0 hϖirr.not_isUnit b h.symm

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

/--
@isnad1 id=eq.2h4v.s9.cd62ac02237c from=translated src=- shape=0804767a vocab=1a4a2d73
-/
theorem localRepSome_collapse_of_isUnit (hϖu : IsUnit ϖ) (b : R) :
    (QuotientGroup.mk (localRepSome ϖ hϖ0 b) : _ ⧸ integralSubgroup R K)
      = QuotientGroup.mk (localRepSome ϖ hϖ0 0) :=
  mk_localRepSome_eq_of_dvd_sub ϖ hϖ0 hϖu.dvd

end Defs

end LocalGL2
