import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.DiskCalculus

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_81 u_82 u_83 u_84 u_85 u_86 u_87 u_88 u_89 u_90

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section
open Filter Topology MeasureTheory Set Metric
open scoped ENNReal NNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_81} [Fintype n] [DecidableEq n]

lemma fourier_nat_pow (t : AddCircle (1:ℝ)) (k : ℕ) :
    fourier 1 t ^ k = fourier (k:ℤ) t := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [pow_succ, hk, ← fourier_add]
    congr 2

end

section
open Filter Topology MeasureTheory Set Metric
open scoped ENNReal NNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_82} [Fintype n] [DecidableEq n]

end

section
open Filter Topology MeasureTheory Set Metric
open scoped ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder Kronecker
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_83} {m : Type u_84} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

def completeAnalyticEval (D : Matrix n n ℂ) (F : ℂ → Matrix m m ℂ) :
    Matrix (n×m) (n×m) ℂ :=
  fun i j => matrixAnalyticEval D (fun z => F z i.2 j.2) i.1 j.1

lemma continuous_analytic_circle
    {m : Type u_84} [Fintype m] [DecidableEq m] {F : ℂ → Matrix m m ℂ}
    (hF : ∀ i j, AnalyticOnNhd ℂ (fun z => F z i j) (closedBall 0 1)) :
    Continuous (fun t : AddCircle (1:ℝ) => F (fourier 1 t)) := by
  apply continuous_matrix
  intro i j
  exact (hF i j).continuousOn.comp_continuous (fourier 1).continuous fun point => by
    simp only [mem_closedBall, dist_zero_right, fourier_norm_value, le_refl]

end

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker

lemma primaryEval_add {V : Type u_85} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ T, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ T, AnalyticAt ℂ g z) :
    primaryEval T (fun z => f z + g z) = primaryEval T f + primaryEval T g := by
  apply primary_end_ext_spectrum (T := T)
  intro β hβ x
  simp only [LinearMap.add_apply, primaryEval_coe]
  rw [scalarJetEval_add (hf β hβ) (hg β hβ)]
  simp

variable {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma matrixAnalyticEval_const (D : Matrix n n ℂ) (c : ℂ) :
    matrixAnalyticEval D (fun _ => c) = algebraMap ℂ (Matrix n n ℂ) c := by
  apply Matrix.toLinAlgEquiv'.injective
  simp [matrixAnalyticEval, primaryEval_const]

lemma matrixAnalyticEval_id (D : Matrix n n ℂ) :
    matrixAnalyticEval D (fun z => z) = D := by
  simpa using matrixAnalyticEval_polynomial D (Polynomial.X : ℂ[X])

lemma matrixAnalyticEval_add (D : Matrix n n ℂ) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ g z) :
    matrixAnalyticEval D (fun z => f z + g z) = matrixAnalyticEval D f + matrixAnalyticEval D g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, map_add, AlgEquiv.apply_symm_apply]
  exact primaryEval_add _ (fun z hz => hf z (by simpa using hz))
    (fun z hz => hg z (by simpa using hz))

lemma matrixAnalyticEval_mul (D : Matrix n n ℂ) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ g z) :
    matrixAnalyticEval D (fun z => f z * g z) = matrixAnalyticEval D f * matrixAnalyticEval D g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, map_mul, AlgEquiv.apply_symm_apply]
  exact primaryEval_mul _ (fun z hz => hf z (by simpa using hz))
    (fun z hz => hg z (by simpa using hz))

lemma matrixAnalyticEval_sum {ι : Type u_88} (s : Finset ι) (D : Matrix n n ℂ) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (f i) z) :
    matrixAnalyticEval D (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, matrixAnalyticEval D (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [matrixAnalyticEval_const]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [matrixAnalyticEval_add D (hf i (Finset.mem_insert_self _ _))
      (fun z hz => Finset.analyticAt_fun_sum _ fun j hj => hf j (Finset.mem_insert_of_mem hj) z hz)]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma completeAnalyticEval_const
    {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) (C : Matrix m m ℂ) :
    completeAnalyticEval D (fun _ => C) = (1 : Matrix n n ℂ) ⊗ₖ C := by
  ext i j
  simp only [completeAnalyticEval, matrixAnalyticEval_const, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply]
  ring

lemma completeAnalyticEval_add
    {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) {F G : ℂ → Matrix m m ℂ}
    (hF : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => F z i j) z)
    (hG : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => G z i j) z) :
    completeAnalyticEval D (fun z => F z + G z) =
      completeAnalyticEval D F + completeAnalyticEval D G := by
  ext i j
  simp only [completeAnalyticEval, Matrix.add_apply]
  rw [matrixAnalyticEval_add D (hF _ _) (hG _ _)]
  rfl

lemma completeAnalyticEval_mul
    {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) {F G : ℂ → Matrix m m ℂ}
    (hF : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => F z i j) z)
    (hG : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => G z i j) z) :
    completeAnalyticEval D (fun z => F z * G z) =
      completeAnalyticEval D F * completeAnalyticEval D G := by
  ext i j
  simp only [completeAnalyticEval, Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [matrixAnalyticEval_sum Finset.univ D (f := fun k z => F z i.2 k * G z k j.2)
    (fun k _ z hz => (hF i.2 k z hz).mul (hG k j.2 z hz))]
  simp only [Matrix.sum_apply]
  simp_rw [matrixAnalyticEval_mul D (hF _ _) (hG _ _), Matrix.mul_apply]
  rw [Finset.sum_comm]

lemma completeAnalyticEval_zsmul
    {n : Type u_86} {m : Type u_87} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) (C : Matrix m m ℂ) :
    completeAnalyticEval D (fun z => z • C) = D ⊗ₖ C := by
  ext i j
  simp only [completeAnalyticEval, Matrix.smul_apply, smul_eq_mul]
  simp only [matrixAnalyticEval_mul D (f := fun z => z) (g := fun _ => C i.2 j.2)
    (fun _ _ => analyticAt_id) (fun _ _ => analyticAt_const),
    matrixAnalyticEval_id, matrixAnalyticEval_const, Algebra.algebraMap_eq_smul_one]
  simp [Matrix.kroneckerMap_apply, mul_comm]

end

open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma matrixAnalyticEval_eventuallyEq (D : Matrix n n ℂ) {f g : ℂ → ℂ}
    (h : ∀ z ∈ spectrum ℂ D, f =ᶠ[nhds z] g) :
    matrixAnalyticEval D f = matrixAnalyticEval D g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply]
  exact primaryEval_eventuallyEq _ (fun z hz => h z (by simpa using hz))

lemma completeAnalyticEval_eqOn
    {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) {F G : ℂ → Matrix m m ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hDU : spectrum ℂ D ⊆ U) (he : EqOn F G U) :
    completeAnalyticEval D F = completeAnalyticEval D G := by
  ext i j
  unfold completeAnalyticEval
  apply congrArg (fun M : Matrix n n ℂ => M i.1 j.1)
  apply matrixAnalyticEval_eventuallyEq
  intro z hz
  filter_upwards [hU.mem_nhds (hDU hz)] with w hw
  rw [he hw]

lemma matrixAnalyticEval_sub (D : Matrix n n ℂ) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ g z) :
    matrixAnalyticEval D (fun z => f z - g z) = matrixAnalyticEval D f - matrixAnalyticEval D g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, map_sub, AlgEquiv.apply_symm_apply]
  exact primaryEval_sub _ (fun z hz => hf z (by simpa using hz))
    (fun z hz => hg z (by simpa using hz))

lemma completeAnalyticEval_sub
    {n : Type u_89} {m : Type u_90} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (D : Matrix n n ℂ) {F G : ℂ → Matrix m m ℂ}
    (hF : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => F z i j) z)
    (hG : ∀ i j, ∀ z ∈ spectrum ℂ D, AnalyticAt ℂ (fun z => G z i j) z) :
    completeAnalyticEval D (fun z => F z - G z) =
      completeAnalyticEval D F - completeAnalyticEval D G := by
  ext i j
  simp only [completeAnalyticEval, Matrix.sub_apply]
  rw [matrixAnalyticEval_sub D (hF _ _) (hG _ _)]
  rfl

lemma matrix_entry_analytic {f : ℂ → Matrix m m ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (i j : m) : AnalyticAt ℂ (fun w => f w i j) z := by
  let L : Matrix m m ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i j, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  exact (L.toContinuousLinearMap.analyticAt (f z)).comp hf

lemma scalar_matrix_inverse_analytic {a : Matrix m m ℂ} {z : ℂ}
    (hunit : IsUnit (1-z • a)) :
    AnalyticAt ℂ (fun w : ℂ => (1-w • a)⁻¹) z := by
  have ha : AnalyticAt ℂ (fun w : ℂ => (1-w • a : Matrix m m ℂ)) z := by fun_prop
  simpa only [Function.comp_def, ← Matrix.nonsing_inv_eq_ringInverse] using
    (show AnalyticAt ℂ Ring.inverse (1-z • a) from by
      simpa only [hunit.unit_spec] using (analyticAt_inverse (𝕜 := ℂ) hunit.unit)).comp
        (f := fun w : ℂ => (1-w • a : Matrix m m ℂ)) ha

lemma resolvent_disk_analytic {a : Matrix m m ℂ} (ha : ‖a‖ ≤ 1) :
    AnalyticOnNhd ℂ (fun z : ℂ => (1-z • a)⁻¹) (ball 0 1) := by
  intro z hz
  apply scalar_matrix_inverse_analytic
  apply isUnit_one_sub_of_norm_lt_one
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left ha (norm_nonneg z)).trans_lt
    (by simpa only [mul_one] using mem_ball_zero_iff.mp hz)

end CompleteCrouzeix

end

end OAI
