/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku.LeanPool.LeanPool.Monlib4.LinearAlgebra.Ips.Pos
public import Tengoku
import Tengoku.LeanPool.LeanPool.Monlib4.LinearAlgebra.Matrix.Basic
import Tengoku.LeanPool.LeanPool.Monlib4.Preq.RCLikeLe

/-!
# Positivity of matrices and linear maps

Compatibility wrappers for the part of Monlib's matrix-positive API now covered by Mathlib.
-/

@[expose] public section

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

open scoped ComplexConjugate

/-- The adjoint of the linear map associated to a matrix is the map associated to its conjugate
transpose.
@isnad1 id=eq.0h4v.s14.1cacc6d7f61d from=translated src=- shape=c0d4fe79 vocab=a50d804c
-/
theorem conjTranspose_eq_adjoint (A : Matrix m n 𝕜) :
    A.conjTranspose.toEuclideanLin = LinearMap.adjoint A.toEuclideanLin :=
  Matrix.toEuclideanLin_conjTranspose_eq_adjoint A

end Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜]

open Matrix
open scoped Matrix ComplexOrder

/--
@isnad1 id=possemid.0h4v.s6.ebd225f46337 from=translated src=- shape=727d5e16 vocab=958e3256
-/
alias Matrix.posSemidef_star_mul_self := Matrix.posSemidef_conjTranspose_mul_self
/--
@isnad1 id=possemid.0h4v.s6.48efcdac5026 from=translated src=- shape=b999c67b vocab=958e3256
-/
alias Matrix.posSemidef_mul_star_self := Matrix.posSemidef_self_mul_conjTranspose

/--
@isnad1 id=eq.0h2v.s10.1950b6f07a4c from=translated src=- shape=ca6078b2 vocab=f2dfa3e8
-/
theorem Matrix.toEuclideanLin_eq_piLp_linearEquiv [Fintype n] [DecidableEq n] :
    Matrix.toEuclideanLin (𝕜 := 𝕜) (m := n) (n := n) =
      Matrix.toLin (PiLp.basisFun 2 𝕜 n) (PiLp.basisFun 2 𝕜 n) := by
  simpa [Matrix.toEuclideanLin] using
    Matrix.toLpLin_eq_toLin (R := 𝕜) (m := n) (n := n) 2 2

open scoped InnerProductSpace

/--
@isnad1 id=iff.0h3v.s12.c28a8152ee4d from=translated src=- shape=d4177cb7 vocab=092dc22b
-/
theorem Matrix.posSemidef_eq_linearMap_positive' [Fintype n] [DecidableEq n]
    (x : Matrix n n 𝕜) :
    x.PosSemidef ↔ x.toEuclideanLin.IsPositive' := by
  rw [LinearMap.isPositive'_iff_isPositive]
  exact Matrix.isPositive_toEuclideanLin_iff.symm

open scoped MatrixOrder

/--
@isnad1 id=iff.0h3v.s7.c684746a50b1 from=translated src=- shape=4f1d6a23 vocab=186c8883
-/
theorem Matrix.posSemidef_iff [Fintype n] (x : Matrix n n 𝕜) :
    x.PosSemidef ↔ ∃ y : Matrix n n 𝕜, x = yᴴ * y := by
  classical
  rw [← Matrix.nonneg_iff_posSemidef]
  simpa [Matrix.star_eq_conjTranspose] using
    (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := x))

local notation "⟪" x "," y "⟫_𝕜" => @inner 𝕜 _ _ x y

open scoped BigOperators

/--
@isnad1 id=eq.0h4v.s7.651c4709a7b1 from=translated src=- shape=f00eddbe vocab=20be1b52
-/
theorem Matrix.dotProduct_eq_inner {n : Type*} [Fintype n] (x y : n → 𝕜) :
    dotProduct (star x) y = ∑ i : n, ⟪x i, y i⟫_𝕜 := by
  simp [dotProduct, RCLike.inner_apply, mul_comm]

/--
@isnad1 id=ishermit.0h4v.s7.3c877c9fddb3 from=translated src=- shape=035f8099 vocab=6bed3c19
-/
theorem Matrix.isHermitian_self_hMul_conjTranspose {m n : Type*} [Fintype m]
    (A : Matrix m n 𝕜) :
    (Aᴴ * A).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_self A

/--
@isnad1 id=eq.0h3v.s7.0369f9e85a22 from=translated src=- shape=fb232201 vocab=9905a38f
-/
theorem Matrix.trace_star [Fintype n] {A : Matrix n n 𝕜} : star A.trace = Aᴴ.trace := by
  rw [Matrix.trace_conjTranspose]

/--
@isnad1 id=le.2h4v.s12.46b1e109e268 from=translated src=- shape=6e649026 vocab=ce113b91
-/
theorem Matrix.nonneg_eigenvalues_of_posSemidef [Fintype n] [DecidableEq n]
    {μ : ℝ} {A : Matrix n n 𝕜}
    (hμ : Module.End.HasEigenvalue (toEuclideanLin A) ↑μ) (H : A.PosSemidef) :
    0 ≤ μ := by
  have hpos := Matrix.isPositive_toEuclideanLin_iff.mpr H
  exact eigenvalue_nonneg_of_nonneg hμ fun v => by
    rw [← hpos.1 v v]
    exact hpos.2 v

/--
@isnad1 id=le.1h4v.s5.4aacf2522489 from=translated src=- shape=6f9b3e81 vocab=17c55808
-/
theorem Matrix.IsHermitian.nonneg_eigenvalues_of_posSemidef [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (i : n) :
    0 ≤ hA.1.eigenvalues i :=
  hA.eigenvalues_nonneg i

/-- A matrix is invertible when its associated linear map is bijective. -/
@[reducible]
noncomputable def Matrix.invertibleOfBijToLin' [Fintype n] [DecidableEq n]
    {Q : Matrix n n 𝕜} (h : Function.Bijective (toLin' Q)) :
    Invertible Q := by
  have h : Invertible (toLin' Q) := by
    refine IsUnit.invertible ?_
    rw [LinearMap.isUnit_iff_ker_eq_bot]
    exact LinearMap.ker_eq_bot_of_injective h.1
  refine IsUnit.invertible ?_
  rw [Matrix.isUnit_iff_isUnit_det, ← LinearMap.det_toLin']
  apply LinearMap.isUnit_det
  rw [← nonempty_invertible_iff_isUnit]
  exact Nonempty.intro h

/--
@isnad1 id=bijectiv.0h4v.s11.b5a87f441047 from=translated src=- shape=8817872f vocab=50166c65
-/
lemma Matrix.bij_toLin'_of_invertible [Fintype n] [DecidableEq n]
    {Q : Matrix n n 𝕜} (h : Invertible Q) :
    Function.Bijective (toLin' Q) := by
  simp_rw [Function.bijective_iff_has_inverse]
  use (toLin' ⅟ Q)
  simp only [Function.LeftInverse, Function.RightInverse, ← toLin'_mul_apply,
    Invertible.invOf_mul_self, mul_invOf_self, toLin'_one, and_self,
    LinearMap.id_apply, forall_true_iff]

/--
@isnad1 id=iff.1h3v.s11.d3c80448ceb1 from=translated src=- shape=d4e51ff6 vocab=87107555
-/
theorem Matrix.PosSemidef.invertibleIff_posDef {n : Type*} [Fintype n]
    [DecidableEq n] {x : Matrix n n 𝕜} (hx : x.PosSemidef) :
    Function.Bijective (toLin' x) ↔ x.PosDef := by
  have hbij_isUnit : Function.Bijective (toLin' x) ↔ IsUnit x := by
    constructor
    · intro h
      exact (nonempty_invertible_iff_isUnit x).mp ⟨Matrix.invertibleOfBijToLin' h⟩
    · intro h
      rcases (nonempty_invertible_iff_isUnit x).mpr h with ⟨hInv⟩
      exact Matrix.bij_toLin'_of_invertible hInv
  rw [hbij_isUnit, hx.posDef_iff_isUnit]

/-- A positive definite matrix is invertible. -/
@[reducible]
noncomputable def Matrix.PosDef.invertible [Fintype n] [DecidableEq n] {Q : Matrix n n 𝕜}
    (hQ : Q.PosDef) :
    Invertible Q :=
  hQ.isUnit.invertible

/--
@isnad1 id=iff.0h3v.s7.025861368fb8 from=translated src=- shape=30855e87 vocab=2341b069
-/
theorem Matrix.posSemidef_iff_vecMulVec [Finite n] {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : ℕ) (v : Fin m → EuclideanSpace 𝕜 n),
        x = ∑ i : Fin m, vecMulVec (v i : n → 𝕜) (star (v i : n → 𝕜)) := by
  constructor
  · intro h
    rcases (Matrix.posSemidef_iff_eq_sum_vecMulVec (𝕜 := 𝕜) (M := x)).mp h with
      ⟨m, v, hv⟩
    exact ⟨m, fun i => WithLp.toLp 2 (v i), by simpa using hv⟩
  · rintro ⟨m, v, hv⟩
    apply (Matrix.posSemidef_iff_eq_sum_vecMulVec (𝕜 := 𝕜) (M := x)).mpr
    exact ⟨m, fun i => (v i : n → 𝕜), by simpa using hv⟩

/--
@isnad1 id=possemid.0h3v.s6.2130ca9f4584 from=translated src=- shape=38e5b86c vocab=0f53e38f
-/
theorem vecMulVec_posSemidef [Finite n] (x : n → 𝕜) :
    (vecMulVec x (star x)).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star x

/-- The identity is a positive definite matrix.
@isnad1 id=posdef.0h2v.s6.9ad8c214f937 from=translated src=- shape=b5354bce vocab=cf95288c
-/
theorem Matrix.posDefOne [DecidableEq n] : (1 : Matrix n n 𝕜).PosDef :=
  Matrix.PosDef.one

/--
@isnad1 id=lt.1h4v.s5.dda1b45a8e85 from=translated src=- shape=355bfb74 vocab=762bd5fc
-/
alias Matrix.PosDef.pos_eigenvalues := Matrix.PosDef.eigenvalues_pos

/--
@isnad1 id=ne.1h3v.s6.e0eca45e3c5d from=translated src=- shape=5a5b326e vocab=2d0cc1e5
-/
theorem Matrix.PosDef.trace_ne_zero [Fintype n] [Nonempty n]
    {x : Matrix n n 𝕜} (hx : x.PosDef) :
    x.trace ≠ 0 :=
  ne_of_gt hx.trace_pos

/-- The Euclidean linear map associated to a matrix acts by matrix-vector multiplication.
@isnad1 id=eq.0h4v.s12.219f3200af73 from=translated src=- shape=f0bde2a9 vocab=5efceb03
-/
lemma Matrix.toEuclideanLin_apply' [Fintype n] [DecidableEq n]
    (x : Matrix n n 𝕜) (v : EuclideanSpace 𝕜 n) :
    x.toEuclideanLin v = x.mulVec v :=
  rfl

namespace rankOne

theorem _root_.rankOne.EuclideanSpace.toEuclideanLin_symm {𝕜 : Type*} [RCLike 𝕜] {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq m]
    (x : EuclideanSpace 𝕜 n) (y : EuclideanSpace 𝕜 m) :
    Matrix.toEuclideanLin.symm (rankOne 𝕜 x y).toLinearMap =
      Matrix.replicateCol (Fin 1) (x : n → 𝕜) *
        (Matrix.replicateCol (Fin 1) (y : m → 𝕜))ᴴ := by
  have hrank : (rankOne 𝕜 x y).toLinearMap =
      (InnerProductSpace.rankOne 𝕜 x y).toLinearMap := by
    ext z i
    rfl
  rw [hrank, InnerProductSpace.symm_toEuclideanLin_rankOne, Matrix.vecMulVec_eq (Fin 1),
    Matrix.conjTranspose_replicateCol]
  rfl

theorem _root_.rankOne.EuclideanSpace.toMatrix' {𝕜 : Type*} [RCLike 𝕜] {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq m]
    (x : EuclideanSpace 𝕜 n) (y : EuclideanSpace 𝕜 m) :
    Matrix.toEuclideanLin.symm (rankOne 𝕜 x y).toLinearMap =
      Matrix.replicateCol (Fin 1) (x : n → 𝕜) *
        (Matrix.replicateCol (Fin 1) (y : m → 𝕜))ᴴ :=
  rankOne.EuclideanSpace.toEuclideanLin_symm x y

end rankOne

/--
@isnad1 id=eq.0h3v.s7.2f723d31d184 from=translated src=- shape=7a3f2969 vocab=14bd0d27
-/
theorem Matrix.vecMulVec_eq_replicateCol_conjTranspose (v : n → 𝕜) :
    vecMulVec v (star v) = replicateCol (Fin 1) v * (replicateCol (Fin 1) v)ᴴ := by
  rw [Matrix.conjTranspose_replicateCol, Matrix.vecMulVec_eq (Fin 1)]
  rfl

/--
@isnad1 id=iff.0h3v.s8.ad08c619a7ae from=translated src=- shape=92e9b094 vocab=b23493d3
-/
theorem Matrix.posSemidef_iff_replicateCol_mul_conjTranspose_replicateCol [Finite n]
    {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : ℕ) (v : Fin m → EuclideanSpace 𝕜 n),
        x =
          ∑ i : Fin m,
            replicateCol (Fin 1) (v i : n → 𝕜) *
              (replicateCol (Fin 1) (v i : n → 𝕜))ᴴ := by
  rw [Matrix.posSemidef_iff_vecMulVec]
  constructor <;> rintro ⟨m, v, hv⟩ <;>
    exact ⟨m, v, by simpa only [Matrix.vecMulVec_eq_replicateCol_conjTranspose] using hv⟩

/--
@isnad1 id=iff.0h3v.s7.494e62637d42 from=translated src=- shape=ed505be4 vocab=324e56c6
-/
theorem Matrix.posSemidef_iff_vecMulVec' [Finite n]
    {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : Type) (_hm : Fintype m) (v : m → EuclideanSpace 𝕜 n),
        x = ∑ i : m, vecMulVec (v i : n → 𝕜) (star (v i : n → 𝕜)) := by
  constructor
  · intro hx
    rcases (Matrix.posSemidef_iff_vecMulVec.mp hx) with ⟨m, v, hv⟩
    exact ⟨Fin m, inferInstance, v, hv⟩
  · rintro ⟨m, hm, v, hv⟩
    let := hm
    rw [Matrix.posSemidef_iff_vecMulVec]
    let v' : Fin (Fintype.card m) → EuclideanSpace 𝕜 n :=
      fun i => v ((Fintype.equivFin m).symm i)
    refine ⟨Fintype.card m, v', ?_⟩
    rw [hv]
    exact Fintype.sum_equiv (Fintype.equivFin m)
      (fun i => vecMulVec (v i : n → 𝕜) (star (v i : n → 𝕜)))
      (fun i => vecMulVec (v' i : n → 𝕜) (star (v' i : n → 𝕜)))
      (by intro i; simp [v'])

/--
@isnad1 id=iff.0h3v.s8.a52050efb08b from=translated src=- shape=6b5a40cd vocab=24b12de3
-/
theorem Matrix.posSemidef_iff_replicateCol_mul_conjTranspose_replicateCol' [Finite n]
    {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : Type) (_hm : Fintype m) (v : m → EuclideanSpace 𝕜 n),
        x =
          ∑ i : m,
            replicateCol (Fin 1) (v i : n → 𝕜) *
              (replicateCol (Fin 1) (v i : n → 𝕜))ᴴ := by
  rw [Matrix.posSemidef_iff_vecMulVec']
  constructor <;> rintro ⟨m, hm, v, hv⟩ <;>
    exact ⟨m, hm, v, by simpa only [Matrix.vecMulVec_eq_replicateCol_conjTranspose] using hv⟩

/-- For complex matrices, positive semidefiniteness is equivalent to nonnegative quadratic
forms.
@isnad1 id=iff.0h2v.s6.87f096a50111 from=translated src=- shape=6b981d9d vocab=df8650b9
-/
theorem Matrix.PosSemidef.complex [Fintype n] (x : Matrix n n ℂ) :
    x.PosSemidef ↔ ∀ y : n → ℂ, 0 ≤ star y ⬝ᵥ x.mulVec y := by
  classical
  rw [Matrix.posSemidef_eq_linearMap_positive' x, LinearMap.complex_isPositive']
  constructor
  · intro h y
    specialize h (WithLp.toLp 2 y)
    simpa [Matrix.toLpLin_toLp, PiLp.inner_apply, Matrix.dotProduct_eq_inner,
      RCLike.inner_apply, Matrix.mulVec] using h
  · intro h v
    simpa [Matrix.toLpLin_toLp, PiLp.inner_apply, Matrix.dotProduct_eq_inner,
      RCLike.inner_apply, Matrix.mulVec] using h v

/--
@isnad1 id=iff.0h2v.s6.87f096a50111 from=translated src=- shape=6b981d9d vocab=df8650b9
-/
theorem PosSemidef.complex [Fintype n] (x : Matrix n n ℂ) :
    x.PosSemidef ↔ ∀ y : n → ℂ, 0 ≤ star y ⬝ᵥ x.mulVec y :=
  Matrix.PosSemidef.complex x

/--
@isnad1 id=eq.0h3v.s7.b394ebd48794 from=translated src=- shape=8fbf4ee3 vocab=9d424a25
-/
theorem single.sum_eq_one [Fintype n] [DecidableEq n] (a : 𝕜) :
    ∑ k : n, single k k a = a • 1 := by
  rw [Matrix.one_eq_sum_std_matrix]
  simp_rw [Finset.smul_sum, Matrix.smul_single, smul_eq_mul, mul_one]

/--
@isnad1 id=eq.0h8v.s8.85f1d4fe58d2 from=translated src=- shape=2a689279 vocab=f77786c6
-/
theorem single_hMul [Fintype n] [DecidableEq n] (i j k l : n) (a b : 𝕜) :
    single i j a * single k l b =
      ite (j = k) (1 : 𝕜) (0 : 𝕜) • single i l (a * b) := by
  ext p q
  rw [Matrix.single.hMul_stdBasisMatrix i p j k l q a b]
  by_cases hip : i = p <;> by_cases hjk : j = k <;> by_cases hlq : l = q <;>
    simp [Matrix.smul_apply, Matrix.single, smul_eq_mul, hip, hjk, hlq]

/--
@isnad1 id=eq.0h5v.s6.987393971769 from=translated src=- shape=d045b2c5 vocab=d2832ea5
-/
theorem Matrix.smul_single' {n R : Type*} [CommSemiring R] [DecidableEq n] (i j : n)
    (c : R) :
    single i j c = c • single i j 1 := by
  rw [smul_single, smul_eq_mul, mul_one]

/--
@isnad1 id=eq.0h3v.s6.8c82d372a243 from=translated src=- shape=28f9ad44 vocab=c064eee2
-/
theorem Matrix.trace_iff' [Fintype n] (x : Matrix n n 𝕜) : x.trace = ∑ i : n, x i i :=
  rfl

/--
@isnad1 id=existsun.0h2v.s10.c907fea347a7 from=translated src=- shape=fde1f019 vocab=bdcd939e
-/
theorem existsUnique_trace [Fintype n] [DecidableEq n] [Nontrivial n] :
    ∃! φ : Matrix n n 𝕜 →ₗ[𝕜] 𝕜,
      (∀ a b : Matrix n n 𝕜, φ (a * b) = φ (b * a)) ∧ φ 1 = 1 := by
  use (1 / Fintype.card n : 𝕜) • traceLinearMap n 𝕜 𝕜
  have trace_functional_iff :
      ∀ φ : Matrix n n 𝕜 →ₗ[𝕜] 𝕜,
        (∀ a b : Matrix n n 𝕜, φ (a * b) = φ (b * a)) ∧ φ 1 = 1 ↔
          φ = (1 / Fintype.card n : 𝕜) • traceLinearMap n 𝕜 𝕜 := by
    intro φ
    have hcard_inv : (↑(Fintype.card n) : 𝕜)⁻¹ * ↑(@Finset.univ n _).card = 1 := by
      simp_all
    constructor
    · intro h
      rw [LinearMap.ext_iff]
      intro x
      have hsingle :
          ∀ i j : n,
            φ (single i j (1 : 𝕜)) =
              (1 / (Fintype.card n : 𝕜)) • ite (j = i) (1 : 𝕜) (0 : 𝕜) := by
        intro i j
        calc
          φ (single i j (1 : 𝕜)) =
              (1 / (Fintype.card n : 𝕜)) •
                ∑ k, φ (single i k 1 * (single k j 1 : Matrix n n 𝕜)) := ?_
          _ =
              (1 / (Fintype.card n : 𝕜)) •
                ∑ k, φ (single k j 1 * single i k 1) := ?_
          _ = (1 / (Fintype.card n : 𝕜)) •
              ite (j = i) (φ (∑ k, single k k 1)) 0 := ?_
          _ = (1 / (Fintype.card n : 𝕜)) • ite (j = i) (φ 1) 0 := ?_
          _ = (1 / (Fintype.card n : 𝕜)) • ite (j = i) 1 0 := ?_
        · simp_all
        · simp_rw [h.1]
        · simp_rw [single_hMul, one_mul, _root_.map_smul, smul_eq_mul, boole_mul,
            Finset.sum_ite_irrel, Finset.sum_const_zero, map_sum]
        · simp_rw [single.sum_eq_one, one_smul]
        · simp_rw [h.2]
      rw [LinearMap.smul_apply, Matrix.traceLinearMap_apply]
      nth_rw 1 [matrix_eq_sum_single x]
      simp_rw [Matrix.smul_single' _ _ (x _ _), map_sum, _root_.map_smul]
      calc
        ∑ x_1, ∑ x_2, x x_1 x_2 • φ (single x_1 x_2 1) =
            ∑ x_1, ∑ x_2,
              x x_1 x_2 • (1 / (Fintype.card n : 𝕜)) •
                ite (x_2 = x_1) (1 : 𝕜) 0 := ?_
        _ = ∑ x_1, x x_1 x_1 • (1 / Fintype.card n : 𝕜) := ?_
        _ = (1 / Fintype.card n : 𝕜) • x.trace := ?_
      · simp_rw [← hsingle]
      · simp_all
      · simp_rw [← Finset.sum_smul, Matrix.trace_iff' x, smul_eq_mul, mul_comm]
    · rintro rfl
      simp_rw [LinearMap.smul_apply, traceLinearMap_apply, Matrix.trace_iff' 1, one_apply_eq,
        Finset.sum_const, one_div, nsmul_eq_mul, mul_one]
      refine ⟨fun x y => ?_, hcard_inv⟩
      rw [trace_mul_comm]
  simp only [trace_functional_iff, imp_self, forall_true_iff, and_true]

/--
@isnad1 id=eq.0h5v.s6.a792899382a5 from=translated src=- shape=e82bc557 vocab=08bececb
-/
theorem Matrix.single.trace [Fintype n] [DecidableEq n] (i j : n) (a : 𝕜) :
    (single i j a).trace = ite (i = j) a 0 := by
  by_cases h : i = j
  · simp_all
  · simp [Matrix.trace_single_eq_of_ne i j a h, h]

/--
@isnad1 id=eq.0h6v.s6.1ecc4f9d9681 from=translated src=- shape=948f779f vocab=f33fe80f
-/
theorem Matrix.single_eq {R n m : Type*} [Semiring R] [DecidableEq n] [DecidableEq m]
    (i : n) (j : m) (a : R) :
    single i j a = fun i' j' => ite (i = i' ∧ j = j') a 0 :=
  rfl

/--
@isnad1 id=iff.0h3v.s7.28b1a260ebde from=translated src=- shape=d4f97978 vocab=c3ce0d0b
-/
theorem vecMulVec_eq_zero_iff (x : n → 𝕜) : vecMulVec x (star x) = 0 ↔ x = 0 := by
  simp_all

/--
@isnad1 id=eq.0h4v.s5.69cd1d6ab187 from=translated src=- shape=19ec118d vocab=17947a3f
-/
lemma norm_ite {α : Type*} [Norm α] (P : Prop) [Decidable P] (a b : α) :
    ‖(ite P a b : α)‖ = (ite P ‖a‖ ‖b‖) := by
  split_ifs <;> rfl

/--
@isnad1 id=iff.0h3v.s6.a00052f5da61 from=translated src=- shape=e581ea12 vocab=da0b6d2c
-/
theorem Matrix.PosSemidef.diagonal_iff [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).PosSemidef ↔ ∀ i, 0 ≤ x i :=
  Matrix.posSemidef_diagonal_iff

/--
@isnad1 id=iff.0h3v.s6.3d66b10927bc from=translated src=- shape=e581ea12 vocab=1a9915ea
-/
theorem Matrix.PosDef.diagonal_iff [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).PosDef ↔ ∀ i, 0 < x i :=
  Matrix.posDef_diagonal_iff

/--
@isnad1 id=eq.0h2v.s10.a9552df2e719 from=translated src=- shape=0bb876f9 vocab=a5af0831
-/
theorem Matrix.toLin_piLp_eq_toLin' {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix.toLpLin (R := 𝕜) (m := n) (n := n) 2 2 =
      Matrix.toLin (PiLp.basisFun 2 𝕜 n) (PiLp.basisFun 2 𝕜 n) :=
  Matrix.toLpLin_eq_toLin (R := 𝕜) (m := n) (n := n) 2 2

/--
@isnad1 id=iff.2h4v.s7.b8172a3c74e1 from=translated src=- shape=a17dd1a0 vocab=59c054e1
-/
alias Matrix.commute_iff := Matrix.IsHermitian.commute_iff

namespace Matrix

theorem _root_.Matrix.Finset.sum_abs_eq_zero_iff' {s : Type*} [Fintype s] {x : s → 𝕜} :
    ∑ i, ‖x i‖ ^ 2 = 0 ↔ ∀ i : s, ‖x i‖ ^ 2 = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _]
  simp only [Finset.mem_univ, forall_true_left]

/-- The trace of `xᴴ * x` is nonnegative.
@isnad1 id=le.0h4v.s7.3df3c7a00c60 from=translated src=- shape=d15c3118 vocab=0d03c594
-/
theorem trace_conjTranspose_hMul_self_nonneg {m : Type*} [Fintype m] [Fintype n]
    (x : Matrix m n 𝕜) :
    0 ≤ (xᴴ * x).trace :=
  (Matrix.posSemidef_conjTranspose_mul_self x).trace_nonneg

/-- A positive semidefinite matrix gives a nonnegative weighted `xᴴ * x` trace. -/
theorem _root_.Matrix.PosSemidef.trace_conjTranspose_hMul_self_nonneg {m : Type*}
    [Fintype m] [Fintype n] {Q : Matrix m m 𝕜}
    (hQ : Q.PosSemidef) (x : Matrix n m 𝕜) :
    0 ≤ (Q * xᴴ * x).trace := by
  classical
  rcases (Matrix.posSemidef_iff Q).mp hQ with ⟨y, rfl⟩
  rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc]
  nth_rw 1 [← conjTranspose_conjTranspose x]
  rw [← Matrix.conjTranspose_mul]
  simp_rw [Matrix.mul_assoc]
  exact Matrix.trace_conjTranspose_hMul_self_nonneg _

/-- The trace of `xᴴ * x` vanishes exactly when `x` is zero.
@isnad1 id=iff.0h4v.s7.d58ca2467b13 from=translated src=- shape=0ecabe5f vocab=99a23e45
-/
theorem trace_conjTranspose_hMul_self_eq_zero {m : Type*} [Fintype n] [Fintype m]
    (x : Matrix n m 𝕜) :
    (xᴴ * x).trace = 0 ↔ x = 0 :=
  Matrix.trace_conjTranspose_mul_self_eq_zero_iff

/-- A positive definite matrix gives a faithful weighted `xᴴ * x` trace. -/
theorem _root_.Matrix.PosDef.trace_conjTranspose_hMul_self_eq_zero {m : Type*}
    [Fintype m] [Fintype n] {Q : Matrix m m 𝕜}
    (hQ : Q.PosDef) {x : Matrix n m 𝕜} :
    (Q * xᴴ * x).trace = 0 ↔ x = 0 := by
  classical
  rcases (Matrix.posSemidef_iff Q).mp hQ.posSemidef with ⟨y, hy⟩
  rw [hy, trace_mul_cycle, ← Matrix.mul_assoc]
  nth_rw 1 [← conjTranspose_conjTranspose x]
  rw [← conjTranspose_mul]
  simp_rw [Matrix.mul_assoc]
  rw [Matrix.trace_conjTranspose_hMul_self_eq_zero _]
  constructor
  · intro h
    have hQx : Q * xᴴ = 0 := by
      rw [hy, Matrix.mul_assoc, h, Matrix.mul_zero]
    let := hQ.invertible
    have hxT : xᴴ = 0 :=
      (Matrix.mul_right_injective_of_invertible (A := Q)) (by simpa using hQx)
    rwa [← Matrix.conjTranspose_eq_zero]
  · simp_all

alias _root_.Matrix.Nontracial.trace_conjTranspose_hMul_self_eq_zero :=
  _root_.Matrix.PosDef.trace_conjTranspose_hMul_self_eq_zero

/-- Hermitian weighted traces are conjugate symmetric. -/
theorem _root_.Matrix.IsHermitian.trace_conj_symm_star_hMul {m : Type*} [Fintype m] [Fintype n]
    {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (x y : Matrix n m 𝕜) :
    (starRingEnd 𝕜) (Q * yᴴ * x).trace = (Q * xᴴ * y).trace := by
  simp_rw [starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose, hQ.eq, Matrix.mul_assoc]
  rw [trace_mul_cycle']

/-- `xᴴ * x` vanishes exactly when `x` is zero.
@isnad1 id=iff.0h4v.s7.abcba844b4ab from=translated src=- shape=fd2d51f0 vocab=87b3128b
-/
theorem conjTranspose_hMul_self_eq_zero {m : Type*} [Fintype n]
    (x : Matrix n m 𝕜) :
    xᴴ * x = 0 ↔ x = 0 :=
  Matrix.conjTranspose_mul_self_eq_zero

theorem _root_.Matrix.PosSemidef.replicateColMulConjTransposereplicateCol [Finite n]
    (x : n → 𝕜) :
    (replicateCol (Fin 1) x * (replicateCol (Fin 1) x)ᴴ : Matrix n n 𝕜).PosSemidef := by
  rw [← Matrix.vecMulVec_eq_replicateCol_conjTranspose]
  exact Matrix.posSemidef_vecMulVec_self_star x

end Matrix
