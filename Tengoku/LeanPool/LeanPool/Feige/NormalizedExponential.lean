/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.SimplexGeometry
public import Tengoku

/-!
# Normalized exponentials and simplex coordinates

This file begins the change of variables behind the identification of
normalized independent exponentials with the uniform simplex law.  We use
the product model `ℝ × (Fin n → ℝ)`: the first target coordinate is `E₀`,
and the remaining coordinates are `Eᵢ`.

The forward map is

`(t,x) ↦ (t(1-∑xᵢ), fun i ↦ t xᵢ)`,

and its inverse divides all nonzero-total vectors by their total mass.
-/

@[expose] public section

open scoped BigOperators ENNReal
open Set
open MeasureTheory

namespace Feige

variable {n : ℕ}

/-- Total mass of an `E₀,E₁,...,Eₙ` vector in product coordinates. -/
def exponentialTotal (e : ℝ × (Fin n → ℝ)) : ℝ :=
  e.1 + ∑ i, e.2 i

/-- Polar/simplex coordinate map used for normalized exponentials. -/
def exponentialSimplexForward
    (z : ℝ × (Fin n → ℝ)) : ℝ × (Fin n → ℝ) :=
  (z.1 * (1 - ∑ i, z.2 i), fun i ↦ z.1 * z.2 i)

/-- Inverse normalized-coordinate map.  It is used only on the domain where
the total is positive. -/
noncomputable def exponentialSimplexInverse
    (e : ℝ × (Fin n → ℝ)) : ℝ × (Fin n → ℝ) :=
  (exponentialTotal e, fun i ↦ e.2 i / exponentialTotal e)

/-- Natural source domain for the change of variables. -/
def exponentialSimplexSource : Set (ℝ × (Fin n → ℝ)) :=
  {z | 0 < z.1 ∧ z.2 ∈ fullSimplex (Fin n)}

/-- Nonnegative exponential vectors with nonzero total mass. -/
def positiveExponentialOrthant : Set (ℝ × (Fin n → ℝ)) :=
  {e | 0 ≤ e.1 ∧ (∀ i, 0 ≤ e.2 i) ∧ 0 < exponentialTotal e}

/--
@isnad1 id=continuo.0h1v.s5.e5dfd7cfd7df from=translated src=- shape=3d04320b vocab=d0851151
-/
theorem continuous_exponentialTotal :
    Continuous (exponentialTotal : (ℝ × (Fin n → ℝ)) → ℝ) := by
  unfold exponentialTotal
  fun_prop

/--
@isnad1 id=continuo.0h1v.s6.97204fc554cb from=translated src=- shape=58efe012 vocab=f97988ca
-/
theorem continuous_exponentialSimplexForward :
    Continuous (exponentialSimplexForward :
      (ℝ × (Fin n → ℝ)) → ℝ × (Fin n → ℝ)) := by
  unfold exponentialSimplexForward
  fun_prop

/--
@isnad1 id=measurab.0h1v.s5.b5086c8305de from=translated src=- shape=58efe012 vocab=ff66e28c
-/
theorem measurable_exponentialSimplexForward :
    Measurable (exponentialSimplexForward :
      (ℝ × (Fin n → ℝ)) → ℝ × (Fin n → ℝ)) :=
  continuous_exponentialSimplexForward.measurable

/--
@isnad1 id=measurab.0h1v.s5.46aa3c629136 from=translated src=- shape=58efe012 vocab=9075d2c0
-/
theorem measurable_exponentialSimplexInverse :
    Measurable (exponentialSimplexInverse :
      (ℝ × (Fin n → ℝ)) → ℝ × (Fin n → ℝ)) := by
  unfold exponentialSimplexInverse exponentialTotal
  fun_prop

/--
@isnad1 id=measurab.0h1v.s4.6a480666250a from=translated src=- shape=86c19a80 vocab=4d59b183
-/
theorem isMeasurableSet_exponentialSimplexSource :
    MeasurableSet (exponentialSimplexSource :
      Set (ℝ × (Fin n → ℝ))) := by
  exact (isOpen_lt continuous_const continuous_fst).measurableSet.inter
    (measurableSet_fullSimplex.preimage measurable_snd)

/--
@isnad1 id=measurab.0h1v.s4.fa17a2058c6e from=translated src=- shape=86c19a80 vocab=e905bb13
-/
theorem isMeasurableSet_positiveExponentialOrthant :
    MeasurableSet (positiveExponentialOrthant :
      Set (ℝ × (Fin n → ℝ))) := by
  have hfirst : MeasurableSet {e : ℝ × (Fin n → ℝ) | 0 ≤ e.1} :=
    measurableSet_le measurable_const measurable_fst
  have hcoords : MeasurableSet {e : ℝ × (Fin n → ℝ) | ∀ i, 0 ≤ e.2 i} := by
    simp only [← Set.mem_Ici]
    exact isClosed_Ici.measurableSet.preimage measurable_snd
  have htotal : MeasurableSet
      {e : ℝ × (Fin n → ℝ) | 0 < exponentialTotal e} :=
    measurableSet_lt measurable_const continuous_exponentialTotal.measurable
  exact hfirst.inter (hcoords.inter htotal)

/--
@isnad1 id=eq.0h2v.s4.07524e2375e3 from=translated src=- shape=70ced4a3 vocab=0202d76c
-/
theorem exponentialTotal_forward (z : ℝ × (Fin n → ℝ)) :
    exponentialTotal (exponentialSimplexForward z) = z.1 := by
  simp only [exponentialTotal, exponentialSimplexForward]
  rw [← Finset.mul_sum]
  ring

/--
@isnad1 id=mem.1h2v.s5.70a07b852629 from=translated src=- shape=2a8ebe69 vocab=eed65ea3
-/
theorem exponentialSimplexForward_mem
    {z : ℝ × (Fin n → ℝ)} (hz : z ∈ exponentialSimplexSource) :
    exponentialSimplexForward z ∈ positiveExponentialOrthant := by
  rcases hz with ⟨ht, hx0, hxsum⟩
  refine ⟨mul_nonneg ht.le (sub_nonneg.mpr hxsum), ?_, ?_⟩
  · intro i
    exact mul_nonneg ht.le (hx0 i)
  · rw [exponentialTotal_forward]
    exact ht

/--
@isnad1 id=mem.1h2v.s5.f710f1a07f4d from=translated src=- shape=2a8ebe69 vocab=9d6e959a
-/
theorem exponentialSimplexInverse_mem
    {e : ℝ × (Fin n → ℝ)} (he : e ∈ positiveExponentialOrthant) :
    exponentialSimplexInverse e ∈ exponentialSimplexSource := by
  rcases he with ⟨he0, hei, ht⟩
  refine ⟨ht, ?_⟩
  rw [mem_fullSimplex_iff]
  constructor
  · intro i
    exact div_nonneg (hei i) ht.le
  · simp only [exponentialSimplexInverse]
    rw [← Finset.sum_div]
    rw [div_le_one ht]
    unfold exponentialTotal
    linarith

/--
@isnad1 id=eq.1h2v.s5.12a7490fc2e9 from=translated src=- shape=452826cd vocab=f925ed7b
-/
theorem exponentialSimplexInverse_forward
    {z : ℝ × (Fin n → ℝ)} (hz : z ∈ exponentialSimplexSource) :
    exponentialSimplexInverse (exponentialSimplexForward z) = z := by
  rcases hz with ⟨ht, hx⟩
  apply Prod.ext
  · exact exponentialTotal_forward z
  · funext i
    change
      (exponentialSimplexForward z).2 i /
          exponentialTotal (exponentialSimplexForward z) = z.2 i
    rw [exponentialTotal_forward]
    simp only [exponentialSimplexForward]
    exact mul_div_cancel_left₀ (z.2 i) ht.ne'

/--
@isnad1 id=eq.1h2v.s5.eb05aef5ce0e from=translated src=- shape=452826cd vocab=a93dfcfb
-/
theorem exponentialSimplexForward_inverse
    {e : ℝ × (Fin n → ℝ)} (he : e ∈ positiveExponentialOrthant) :
    exponentialSimplexForward (exponentialSimplexInverse e) = e := by
  rcases he with ⟨he0, hei, ht⟩
  apply Prod.ext
  · change exponentialTotal e *
        (1 - ∑ i, e.2 i / exponentialTotal e) = e.1
    rw [← Finset.sum_div]
    field_simp [ht.ne']
    unfold exponentialTotal
    ring
  · funext i
    simp only [exponentialSimplexForward, exponentialSimplexInverse]
    exact mul_div_cancel₀ (e.2 i) ht.ne'

/-- The coordinate change is a bijection between its natural source and
target domains.
@isnad1 id=bijon.0h1v.s4.e3deccd0a564 from=translated src=- shape=9fe868ba vocab=5cbd65e3
-/
theorem exponentialSimplex_bijOn :
    Set.BijOn (exponentialSimplexForward (n := n))
      (exponentialSimplexSource (n := n))
      (positiveExponentialOrthant (n := n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact exponentialSimplexForward_mem hz
  · intro z hz w hw hzw
    rw [← exponentialSimplexInverse_forward hz,
      ← exponentialSimplexInverse_forward hw, hzw]
  · intro e he
    exact ⟨exponentialSimplexInverse e,
      exponentialSimplexInverse_mem he, exponentialSimplexForward_inverse he⟩

/-! ## Fréchet derivative of the coordinate change -/

/-- Differential of the total simplex-coordinate sum. -/
noncomputable def simplexCoordinateSumDerivative :
    (ℝ × (Fin n → ℝ)) →L[ℝ] ℝ :=
  ∑ i : Fin n,
    (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ))

/-- The explicit Fréchet derivative of `exponentialSimplexForward`.

Applied to an increment `(dt,dx)`, it is

`(dt(1-∑x)-t∑dx, fun i ↦ dt*xᵢ+t*dxᵢ)`.
-/
noncomputable def exponentialSimplexForwardDerivative
    (z : ℝ × (Fin n → ℝ)) :
    (ℝ × (Fin n → ℝ)) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
  let dt := ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)
  let dx : Fin n → (ℝ × (Fin n → ℝ)) →L[ℝ] ℝ :=
    fun i ↦ (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ))
  ((z.1 • (-simplexCoordinateSumDerivative) +
      (1 - ∑ i, z.2 i) • dt).prod
    (ContinuousLinearMap.pi fun i ↦ z.1 • dx i + z.2 i • dt))

/--
@isnad1 id=eq.0h2v.s8.8adbd67a6935 from=translated src=- shape=e3a7e065 vocab=cc6aa293
-/
@[simp]
theorem simplexCoordinateSumDerivative_apply
    (h : ℝ × (Fin n → ℝ)) :
    simplexCoordinateSumDerivative h = ∑ i, h.2 i := by
  simp [simplexCoordinateSumDerivative]

/--
@isnad1 id=eq.0h3v.s9.8966f98a11e3 from=translated src=- shape=71f61d35 vocab=f6cc9548
-/
theorem exponentialSimplexForwardDerivative_apply
    (z h : ℝ × (Fin n → ℝ)) :
    exponentialSimplexForwardDerivative z h =
      (h.1 * (1 - ∑ i, z.2 i) - z.1 * ∑ i, h.2 i,
        fun i ↦ h.1 * z.2 i + z.1 * h.2 i) := by
  ext <;> simp [exponentialSimplexForwardDerivative,
    simplexCoordinateSumDerivative_apply] <;> ring

/--
@isnad1 id=hasfderi.0h2v.s7.beb2c53e18d1 from=translated src=- shape=4c684c6b vocab=7fae6814
-/
theorem hasFDerivAt_exponentialSimplexForward
    (z : ℝ × (Fin n → ℝ)) :
    HasFDerivAt exponentialSimplexForward
      (exponentialSimplexForwardDerivative z) z := by
  have h :
      HasFDerivAt exponentialSimplexForward
        (exponentialSimplexForwardDerivative z) z := by
    unfold exponentialSimplexForward
    dsimp [exponentialSimplexForwardDerivative,
      simplexCoordinateSumDerivative]
    fun_prop
  exact h

/--
@isnad1 id=eq.0h2v.s9.18ef49c9e5dd from=translated src=- shape=8d981a83 vocab=8a432a18
-/
theorem fderiv_exponentialSimplexForward
    (z : ℝ × (Fin n → ℝ)) :
    fderiv ℝ exponentialSimplexForward z =
      exponentialSimplexForwardDerivative z :=
  (hasFDerivAt_exponentialSimplexForward z).fderiv

/-! ## Matrix of the derivative -/

/-- Identify an `Option (Fin n)` coordinate vector with radial/product
coordinates. -/
def optionVectorToProduct (v : Option (Fin n) → ℝ) :
    ℝ × (Fin n → ℝ) :=
  (v none, fun i ↦ v (some i))

/-- The optional-coordinate identification is measurable.
@isnad1 id=measurab.0h1v.s5.68693aa302ee from=translated src=- shape=94d3e796 vocab=5b41dd68
-/
theorem measurable_optionVectorToProduct :
    Measurable (optionVectorToProduct (n := n)) := by
  unfold optionVectorToProduct
  fun_prop

/-- The inverse coordinate identification. -/
def productToOptionVector (z : ℝ × (Fin n → ℝ)) :
    Option (Fin n) → ℝ
  | none => z.1
  | some i => z.2 i

/--
@isnad1 id=eq.0h2v.s4.c35488a0dc5f from=translated src=- shape=3e31b8f8 vocab=5818a3c9
-/
@[simp]
theorem productToOptionVector_optionVectorToProduct
    (v : Option (Fin n) → ℝ) :
    productToOptionVector (optionVectorToProduct v) = v := by
  funext i
  cases i <;> rfl

/--
@isnad1 id=eq.0h2v.s4.7a77581e7284 from=translated src=- shape=79d2a4dc vocab=d199b5c7
-/
@[simp]
theorem optionVectorToProduct_productToOptionVector
    (z : ℝ × (Fin n → ℝ)) :
    optionVectorToProduct (productToOptionVector z) = z := by
  ext <;> rfl

/-- Jacobian matrix of `exponentialSimplexForward` in the basis indexed by
`none, some 0, ..., some (n-1)`. -/
noncomputable def exponentialSimplexJacobianMatrix
    (z : ℝ × (Fin n → ℝ)) :
    Matrix (Option (Fin n)) (Option (Fin n)) ℝ
  | none, none => 1 - ∑ i, z.2 i
  | none, some _ => -z.1
  | some i, none => z.2 i
  | some i, some j => if i = j then z.1 else 0

/--
@isnad1 id=eq.0h2v.s5.6b8a497797ab from=translated src=- shape=d35ef2e7 vocab=e0808993
-/
@[simp]
theorem exponentialSimplexJacobianMatrix_none_none
    (z : ℝ × (Fin n → ℝ)) :
    exponentialSimplexJacobianMatrix z none none =
      1 - ∑ i, z.2 i :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.f4897b4b2fea from=translated src=- shape=a3e0c364 vocab=46f478cb
-/
@[simp]
theorem exponentialSimplexJacobianMatrix_none_some
    (z : ℝ × (Fin n → ℝ)) (j : Fin n) :
    exponentialSimplexJacobianMatrix z none (some j) = -z.1 :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.65bc30242674 from=translated src=- shape=7ed828cd vocab=97a63623
-/
@[simp]
theorem exponentialSimplexJacobianMatrix_some_none
    (z : ℝ × (Fin n → ℝ)) (i : Fin n) :
    exponentialSimplexJacobianMatrix z (some i) none = z.2 i :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.a92e9c6e9412 from=translated src=- shape=bc761064 vocab=54583d4e
-/
@[simp]
theorem exponentialSimplexJacobianMatrix_some_some
    (z : ℝ × (Fin n → ℝ)) (i j : Fin n) :
    exponentialSimplexJacobianMatrix z (some i) (some j) =
      if i = j then z.1 else 0 :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.19c6f87a7bf2 from=translated src=- shape=2ec6cc7c vocab=936ddd9d
-/
theorem exponentialSimplexJacobianMatrix_mulVec_none
    (z : ℝ × (Fin n → ℝ)) (v : Option (Fin n) → ℝ) :
    (exponentialSimplexJacobianMatrix z).mulVec v none =
      v none * (1 - ∑ i, z.2 i) - z.1 * ∑ i, v (some i) := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_option, mul_comm,
    Finset.mul_sum]
  ring

/--
@isnad1 id=eq.0h4v.s6.a3cd1576c672 from=translated src=- shape=03480159 vocab=c558bfa9
-/
theorem exponentialSimplexJacobianMatrix_mulVec_some
    (z : ℝ × (Fin n → ℝ)) (v : Option (Fin n) → ℝ) (i : Fin n) :
    (exponentialSimplexJacobianMatrix z).mulVec v (some i) =
      v none * z.2 i + z.1 * v (some i) := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_option, mul_comm]

/-- The explicit Jacobian matrix represents the Fréchet derivative proved
above.
@isnad1 id=eq.0h3v.s8.3d8e5ad6d577 from=translated src=- shape=42db0c72 vocab=7835ed1b
-/
theorem productToOptionVector_derivative_eq_mulVec
    (z : ℝ × (Fin n → ℝ)) (v : Option (Fin n) → ℝ) :
    productToOptionVector
        (exponentialSimplexForwardDerivative z (optionVectorToProduct v)) =
      (exponentialSimplexJacobianMatrix z).mulVec v := by
  funext i
  cases i with
  | none =>
      rw [exponentialSimplexJacobianMatrix_mulVec_none]
      simp [productToOptionVector, optionVectorToProduct,
        exponentialSimplexForwardDerivative_apply]
  | some i =>
      rw [exponentialSimplexJacobianMatrix_mulVec_some]
      simp [productToOptionVector, optionVectorToProduct,
        exponentialSimplexForwardDerivative_apply]

/-! ## Determinant of the Jacobian -/

/-- Add all rows of the Jacobian to its `none` row.  This elementary row
operation leaves the determinant unchanged and makes the matrix triangular.
-/
noncomputable def reducedExponentialSimplexJacobianMatrix
    (z : ℝ × (Fin n → ℝ)) :
    Matrix (Option (Fin n)) (Option (Fin n)) ℝ :=
  (exponentialSimplexJacobianMatrix z).updateRow none
    (∑ k, (1 : ℝ) • (exponentialSimplexJacobianMatrix z) k)

/--
@isnad1 id=eq.0h2v.s6.7f93e3c71e14 from=translated src=- shape=f0f31480 vocab=5c929234
-/
theorem det_reducedExponentialSimplexJacobianMatrix
    (z : ℝ × (Fin n → ℝ)) :
    (reducedExponentialSimplexJacobianMatrix z).det =
      (exponentialSimplexJacobianMatrix z).det := by
  unfold reducedExponentialSimplexJacobianMatrix
  simpa using Matrix.det_updateRow_sum
    (exponentialSimplexJacobianMatrix z) none (fun _ ↦ (1 : ℝ))

/--
@isnad1 id=eq.0h2v.s4.fe683998d4db from=translated src=- shape=ca1f742a vocab=8b248553
-/
@[simp]
theorem reducedExponentialSimplexJacobianMatrix_none_none
    (z : ℝ × (Fin n → ℝ)) :
    reducedExponentialSimplexJacobianMatrix z none none = 1 := by
  classical
  rw [reducedExponentialSimplexJacobianMatrix, Matrix.updateRow_self]
  rw [Fintype.sum_apply]
  simp only [Pi.smul_apply, one_smul]
  rw [Fintype.sum_option]
  simp

/--
@isnad1 id=eq.0h3v.s4.a9c8d53743c1 from=translated src=- shape=54f26cec vocab=9603f2b8
-/
@[simp]
theorem reducedExponentialSimplexJacobianMatrix_none_some
    (z : ℝ × (Fin n → ℝ)) (j : Fin n) :
    reducedExponentialSimplexJacobianMatrix z none (some j) = 0 := by
  classical
  rw [reducedExponentialSimplexJacobianMatrix, Matrix.updateRow_self]
  rw [Fintype.sum_apply]
  simp only [Pi.smul_apply, one_smul]
  rw [Fintype.sum_option]
  simp

/--
@isnad1 id=eq.0h3v.s5.1cc844323ca9 from=translated src=- shape=7ed828cd vocab=e732e3c0
-/
@[simp]
theorem reducedExponentialSimplexJacobianMatrix_some_none
    (z : ℝ × (Fin n → ℝ)) (i : Fin n) :
    reducedExponentialSimplexJacobianMatrix z (some i) none = z.2 i := by
  rw [reducedExponentialSimplexJacobianMatrix, Matrix.updateRow_ne (by simp)]
  rfl

/--
@isnad1 id=eq.0h4v.s5.4b742cc0bfaa from=translated src=- shape=bc761064 vocab=8d3321d2
-/
@[simp]
theorem reducedExponentialSimplexJacobianMatrix_some_some
    (z : ℝ × (Fin n → ℝ)) (i j : Fin n) :
    reducedExponentialSimplexJacobianMatrix z (some i) (some j) =
      if i = j then z.1 else 0 := by
  rw [reducedExponentialSimplexJacobianMatrix, Matrix.updateRow_ne (by simp)]
  rfl

/--
@isnad1 id=eq.0h2v.s5.425942b00b3c from=translated src=- shape=e1c5bace vocab=c06965c9
-/
theorem det_reducedExponentialSimplexJacobianMatrix_eq_pow
    (z : ℝ × (Fin n → ℝ)) :
    (reducedExponentialSimplexJacobianMatrix z).det = z.1 ^ n := by
  let : LinearOrder (Option (Fin n)) :=
    LinearOrder.lift' (finSuccEquiv' (0 : Fin (n + 1))).symm
      (finSuccEquiv' (0 : Fin (n + 1))).symm.injective
  rw [Matrix.det_of_isLowerTriangular _ (by
    intro i j hij
    cases i with
    | none =>
        cases j with
        | none => simp at hij
        | some j => exact reducedExponentialSimplexJacobianMatrix_none_some z j
    | some i =>
        cases j with
        | none =>
            exfalso
            change
              (finSuccEquiv' (0 : Fin (n + 1))).symm (some i) <
                (finSuccEquiv' (0 : Fin (n + 1))).symm none at hij
            simp at hij
        | some j =>
            simp only [reducedExponentialSimplexJacobianMatrix_some_some]
            rw [ite_eq_right]
            intro h
            subst j
            simp at hij)]
  simp [Fintype.prod_option]

/-- The Jacobian determinant of the radial--simplex coordinate map is
`t ^ n`.
@isnad1 id=eq.0h2v.s5.73e7440278dc from=translated src=- shape=e1c5bace vocab=56442a8b
-/
theorem det_exponentialSimplexJacobianMatrix
    (z : ℝ × (Fin n → ℝ)) :
    (exponentialSimplexJacobianMatrix z).det = z.1 ^ n := by
  rw [← det_reducedExponentialSimplexJacobianMatrix z,
    det_reducedExponentialSimplexJacobianMatrix_eq_pow]

/-! ## Change of variables -/

/-- The coordinate basis whose `none` coordinate is the radial coordinate
and whose `some i` coordinates are the simplex coordinates. -/
noncomputable def exponentialCoordinateBasis :
    Module.Basis (Option (Fin n)) ℝ (ℝ × (Fin n → ℝ)) :=
  (Pi.basisFun ℝ (Option (Fin n))).map
    (LinearEquiv.piOptionEquivProd ℝ)

/-- The determinant of the Fréchet derivative, in the intrinsic
finite-dimensional determinant used by Mathlib's change-of-variables
theorem.
@isnad1 id=eq.0h2v.s6.659241604388 from=translated src=- shape=1420fe94 vocab=2f6dd8ae
-/
theorem det_exponentialSimplexForwardDerivative
    (z : ℝ × (Fin n → ℝ)) :
    (exponentialSimplexForwardDerivative z).det = z.1 ^ n := by
  classical
  change LinearMap.det
    (exponentialSimplexForwardDerivative z).toLinearMap = _
  rw [← LinearMap.det_toMatrix (exponentialCoordinateBasis (n := n))]
  rw [← det_exponentialSimplexJacobianMatrix z]
  congr 1
  ext i j
  simp only [LinearMap.toMatrix_apply]
  cases i <;> cases j <;>
    simp [exponentialCoordinateBasis,
      exponentialSimplexForwardDerivative_apply,
      exponentialSimplexJacobianMatrix, LinearEquiv.piOptionEquivProd,
      Equiv.piOptionEquivProd, Pi.single_apply]

/-- The coordinate Haar measure is exactly the default product Lebesgue
measure, not merely a nonzero scalar multiple of it.
@isnad1 id=eq.0h1v.s7.e8bd51fed59a from=translated src=- shape=a19fcc85 vocab=2aaf9a7b
-/
theorem exponentialCoordinateBasis_addHaar_eq_volume :
    (exponentialCoordinateBasis (n := n)).addHaar =
      (volume : Measure (ℝ × (Fin n → ℝ))) := by
  classical
  let e : (Option (Fin n) → ℝ) ≃L[ℝ] (ℝ × (Fin n → ℝ)) :=
    (LinearEquiv.piOptionEquivProd ℝ).toContinuousLinearEquiv
  unfold exponentialCoordinateBasis
  change ((Pi.basisFun ℝ (Option (Fin n))).map e.toLinearEquiv).addHaar = _
  rw [← Module.Basis.map_addHaar (Pi.basisFun ℝ (Option (Fin n))) e]
  have hpi : (Pi.basisFun ℝ (Option (Fin n))).addHaar =
      (volume : Measure (Option (Fin n) → ℝ)) := by
    rw [Module.Basis.addHaar_def, Module.Basis.parallelepiped_basisFun,
      addHaarMeasure_eq_volume_pi]
  rw [hpi]
  have hg : Measure.map (MeasurableEquiv.piOptionEquivProd
        (fun _ : Option (Fin n) ↦ ℝ))
      (volume : Measure (Option (Fin n) → ℝ)) =
      (volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ) := by
    rw [(MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (Fin n) ↦ ℝ)).map_apply_eq_iff_map_symm_apply_eq]
    simpa only [volume_pi] using
      (Measure.pi_map_piOptionEquivProd
        (fun _ : Option (Fin n) ↦ (volume : Measure ℝ))).symm
  rw [show (e : (Option (Fin n) → ℝ) → (ℝ × (Fin n → ℝ))) =
      Prod.swap ∘ (MeasurableEquiv.piOptionEquivProd
        (fun _ : Option (Fin n) ↦ ℝ)) by rfl]
  rw [← Measure.map_map measurable_swap (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option (Fin n) ↦ ℝ)).measurable]
  rw [hg, Measure.prod_swap]
  exact (Measure.volume_eq_prod ℝ (Fin n → ℝ)).symm

/-- Restricted change of variables from radial--simplex coordinates to the
positive exponential orthant.  This is the nonnegative integral formula
directly supplied by Mathlib's finite-dimensional Jacobian theorem, with
all geometric and differentiability hypotheses discharged here.
@isnad1 id=eq.0h2v.s8.8ceff222f1a4 from=translated src=- shape=61f13970 vocab=ff5de4b6
-/
theorem lintegral_positiveExponentialOrthant_eq
    (g : (ℝ × (Fin n → ℝ)) → ℝ≥0∞) :
    ∫⁻ e in positiveExponentialOrthant (n := n), g e ∂volume =
      ∫⁻ z in exponentialSimplexSource (n := n),
        ENNReal.ofReal (z.1 ^ n) * g (exponentialSimplexForward z)
          ∂volume := by
  rw [← exponentialCoordinateBasis_addHaar_eq_volume (n := n)]
  rw [← exponentialSimplex_bijOn.image_eq]
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (exponentialCoordinateBasis (n := n)).addHaar
    isMeasurableSet_exponentialSimplexSource
    (fun z _ ↦ (hasFDerivAt_exponentialSimplexForward z).hasFDerivWithinAt)
    exponentialSimplex_bijOn.injOn g]
  apply MeasureTheory.lintegral_congr_ae
  filter_upwards [
    MeasureTheory.ae_restrict_mem
      isMeasurableSet_exponentialSimplexSource] with z hz
  rw [det_exponentialSimplexForwardDerivative]
  rw [abs_of_nonneg (pow_nonneg hz.1.le n)]

/-! ## The radial Gamma integral -/

/-- The elementary radial integral appearing after the normalized
exponential change of variables.
@isnad1 id=eq.0h1v.s6.3a9b87d62cfd from=translated src=- shape=baac4ac7 vocab=db1a0472
-/
theorem integral_exp_neg_mul_pow_Ioi (n : ℕ) :
    ∫ t : ℝ in Ioi 0, Real.exp (-t) * t ^ n =
      (n.factorial : ℝ) := by
  rw [show (fun t : ℝ => Real.exp (-t) * t ^ n) =
      fun t => t ^ ((n : ℝ) + 1 - 1) * Real.exp (-(1 * t)) by
    funext t
    rw [add_sub_cancel_right, Real.rpow_natCast]
    simp [mul_comm]]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) zero_lt_one]
  simp [Real.Gamma_nat_eq_factorial]

/-- `ENNReal`/Tonelli form of the radial Gamma integral.
@isnad1 id=eq.0h1v.s6.021f1c0528d9 from=translated src=- shape=87115298 vocab=64e0486d
-/
theorem lintegral_ofReal_exp_neg_mul_pow_Ioi (n : ℕ) :
    ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (Real.exp (-t) * t ^ n) =
      (n.factorial : ℝ≥0∞) := by
  have hint : IntegrableOn
      (fun t : ℝ => Real.exp (-t) * t ^ n) (Ioi 0) := by
    convert Real.GammaIntegral_convergent
      (s := (n : ℝ) + 1) (by positivity) using 1
    funext t
    rw [add_sub_cancel_right, Real.rpow_natCast]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht =>
      mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.le n))]
  rw [integral_exp_neg_mul_pow_Ioi]
  simp

/-! ## Normalized exponential coordinates -/

/--
@isnad1 id=eq.0h1v.s5.041a82cca6d7 from=translated src=- shape=027451b8 vocab=51a448bb
-/
theorem exponentialSimplexSource_eq_prod :
    exponentialSimplexSource (n := n) =
      Ioi (0 : ℝ) ×ˢ fullSimplex (Fin n) := by
  ext z
  simp [exponentialSimplexSource]

/-- Tonelli separation of the radial factor from an arbitrary measurable
nonnegative test function on the simplex.
@isnad1 id=eq.1h2v.s8.2560f6beca5f from=translated src=- shape=4ab39233 vocab=4d42c282
-/
theorem lintegral_exponentialRadial_mul_test
    (h : (Fin n → ℝ) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ z in exponentialSimplexSource (n := n),
        ENNReal.ofReal (Real.exp (-z.1) * z.1 ^ n) * h z.2 ∂volume =
      (n.factorial : ℝ≥0∞) *
        ∫⁻ x in fullSimplex (Fin n), h x ∂volume := by
  rw [exponentialSimplexSource_eq_prod]
  rw [Measure.volume_eq_prod]
  rw [setLIntegral_prod]
  · simp_rw [lintegral_const_mul _ hh]
    rw [lintegral_mul_const]
    · rw [lintegral_ofReal_exp_neg_mul_pow_Ioi]
    · fun_prop
  · fun_prop

/-- The measure on simplex coordinates obtained from independent unit-rate
exponentials: factorial times Lebesgue measure restricted to the full
simplex. -/
noncomputable def normalizedExponentialSimplexMeasure :
    Measure (Fin n → ℝ) :=
  (n.factorial : ℝ≥0∞) •
    (volume.restrict (fullSimplex (Fin n)))

/-- Identification of normalized independent exponentials with the
factorial-density uniform simplex measure, formulated against arbitrary
measurable nonnegative test functions.
@isnad1 id=eq.1h2v.s7.7f0ab95de6b4 from=translated src=- shape=b310bd44 vocab=870614fe
-/
theorem lintegral_normalizedExponential_eq_simplex
    (h : (Fin n → ℝ) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ e in positiveExponentialOrthant (n := n),
        ENNReal.ofReal (Real.exp (-exponentialTotal e)) *
          h (exponentialSimplexInverse e).2 ∂volume =
      ∫⁻ x, h x ∂(normalizedExponentialSimplexMeasure (n := n)) := by
  rw [lintegral_positiveExponentialOrthant_eq]
  calc
    _ = ∫⁻ z in exponentialSimplexSource (n := n),
        ENNReal.ofReal (Real.exp (-z.1) * z.1 ^ n) * h z.2
          ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [
        ae_restrict_mem isMeasurableSet_exponentialSimplexSource] with z hz
      rw [exponentialTotal_forward, exponentialSimplexInverse_forward hz]
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      ac_rfl
    _ = (n.factorial : ℝ≥0∞) *
        ∫⁻ x in fullSimplex (Fin n), h x ∂volume :=
      lintegral_exponentialRadial_mul_test h hh
    _ = _ := by
      rw [normalizedExponentialSimplexMeasure, lintegral_smul_measure]
      rfl

/-- The unit-rate exponential density, extended by zero to the negative
half-line. -/
noncomputable def unitExponentialDensity (t : ℝ) : ℝ :=
  (Ici (0 : ℝ)).indicator (fun t ↦ Real.exp (-t)) t

/--
@isnad1 id=eq.0h0v.s5.649a53636936 from=translated src=- shape=f0e61117 vocab=e19f3a44
-/
theorem integral_unitExponentialDensity :
    ∫ t : ℝ, unitExponentialDensity t = 1 := by
  change ∫ t : ℝ, (Ici (0 : ℝ)).indicator
    (fun t ↦ Real.exp (-t)) t = 1
  rw [integral_indicator measurableSet_Ici]
  rw [integral_Ici_eq_integral_Ioi]
  simpa using integral_exp_neg_mul_pow_Ioi 0

/-- A finite product of unit exponential densities has total mass one.
@isnad1 id=eq.0h1v.s6.c7486ebed51a from=translated src=- shape=c670091d vocab=97a3de89
-/
theorem integral_pi_unitExponentialDensity :
    ∫ x : Fin n → ℝ, ∏ i, unitExponentialDensity (x i) = 1 := by
  rw [integral_fintype_prod_volume_eq_prod]
  simp [integral_unitExponentialDensity]

end Feige
