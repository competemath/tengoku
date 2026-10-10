import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.UnitaryRealization

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_177 u_178 u_179 u_180 u_181 u_182 u_183

section
section
section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology
open Set Filter Metric Topology

section
open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology
variable {n : Type u_177} [Fintype n] [DecidableEq n]

lemma transfer_meromorphic (a b c d : Matrix n n ℂ) (i j : n) :
    MeromorphicOn (fun z => transfer a b c d z i j) Set.univ := by
  intro z _
  have hM (i j : n) : MeromorphicAt (fun w : ℂ => (1-w • a : Matrix n n ℂ) i j) z := by
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    fun_prop
  simp only [transfer,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply]
  apply (MeromorphicAt.const _ z).add
  apply (MeromorphicAt.id z).mul
  apply MeromorphicAt.fun_sum
  intro k _
  apply MeromorphicAt.mul _ (MeromorphicAt.const _ z)
  apply MeromorphicAt.fun_sum
  intro l _
  exact (MeromorphicAt.const _ z).mul (meromorphic_matrix_inverse hM l k)

lemma transfer_analytic {a b c d : Matrix n n ℂ} (ha : ‖a‖ ≤ 1) :
    AnalyticOnNhd ℂ (transfer a b c d) (ball 0 1) := by
  intro z hz
  have hza : ‖z • a‖ < 1 := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left ha (norm_nonneg z)).trans_lt
      (by simpa only [mul_one] using mem_ball_zero_iff.mp hz)
  have hi := scalar_matrix_inverse_analytic (isUnit_one_sub_of_norm_lt_one hza)
  unfold transfer
  fun_prop

theorem exists_transfer_extension {a b c d : Matrix n n ℂ}
    (hU : (Matrix.fromBlocks a b c d)ᴴ * Matrix.fromBlocks a b c d = 1) :
    ∃ R : ℂ → Matrix n n ℂ,
      AnalyticOnNhd ℂ R (closedBall 0 1) ∧ EqOn R (transfer a b c d) (ball 0 1) ∧
      ∀ z ∈ closedBall 0 1, ‖R z‖ ≤ 1 := by
  classical
  have ha := transfer_analytic (b := b) (c := c) (d := d) (block_unitary_contractions hU).1
  have hentries : ∀ i j : n, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 1) ∧
      EqOn g (fun z => transfer a b c d z i j) (ball 0 1) := by
    intro i j
    let L : Matrix n n ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun M => M i j, map_add' := by intros; rfl, map_smul' := by intros; rfl }
    apply bounded_meromorphic_disk_extension (C := ‖L.toContinuousLinearMap‖)
      (transfer_meromorphic a b c d i j) (fun z hz => matrix_entry_analytic (ha z hz) i j)
    intro z hz
    exact (L.toContinuousLinearMap.le_opNorm (transfer a b c d z)).trans
      (mul_le_of_le_one_right (norm_nonneg _) (transfer_contraction hU (mem_ball_zero_iff.mp hz)))
  choose g hga hge using hentries
  let R : ℂ → Matrix n n ℂ := fun z i j => g i j z
  have hRa : AnalyticOnNhd ℂ R (closedBall 0 1) := by
    intro z hz
    have he : R = fun w => ∑ i : n, ∑ j : n, g i j w • Matrix.single i j (1:ℂ) := by
      funext w
      ext i j
      simp [R,Matrix.sum_apply,Matrix.single_apply, ite_and]
    rw [he]
    apply Finset.analyticAt_fun_sum
    intro i _
    apply Finset.analyticAt_fun_sum
    intro j _
    exact (hga i j z hz).smul analyticAt_const
  have hRe : EqOn R (transfer a b c d) (ball 0 1) := by
    intro z hz
    ext i j
    exact hge i j hz
  refine ⟨R,hRa,hRe,?_⟩
  intro z hz
  have hcl : closure (ball (0:ℂ) 1) = closedBall 0 1 := closure_ball 0 (by norm_num)
  apply le_on_closure (fun w hw => ?_) (hRa.continuousOn.norm.mono (by rw [hcl]))
    continuousOn_const (by rwa [hcl])
  rw [hRe hw]
  exact transfer_contraction hU (mem_ball_zero_iff.mp hw)

end

section
open Filter Topology Set Metric
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_178} [Fintype n] [DecidableEq n]

end

section
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder Pointwise
section

section Stability
variable {A : Type u_179} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

end Stability

section Metric
variable {n : Type u_180} [Fintype n] [DecidableEq n]

def steinTerm (T : Matrix n n ℂ) (j : ℕ) : Matrix n n ℂ :=
  (T ^ j)ᴴ * T ^ j

def steinMetric (T : Matrix n n ℂ) : Matrix n n ℂ := ∑' j : ℕ, steinTerm T j

lemma steinMetric_nonneg (T : Matrix n n ℂ) : 0 ≤ steinMetric T := by
  apply tsum_nonneg
  intro j
  exact (Matrix.posSemidef_conjTranspose_mul_self (T ^ j)).nonneg

end Metric

section Minimum
variable {n : Type u_181} [Fintype n] [DecidableEq n] [Nonempty n]

def MetricFeasible (T : Matrix n n ℂ) (τ : ℝ) (H : Matrix n n ℂ) : Prop :=
  1 ≤ H ∧ H ≤ algebraMap ℝ (Matrix n n ℂ) τ ∧ Tᴴ * H * T ≤ H

lemma scalarMatrix_le_iff (a b : ℝ) :
    algebraMap ℝ (Matrix n n ℂ) a ≤ algebraMap ℝ (Matrix n n ℂ) b ↔ a ≤ b := by
  constructor
  · intro h
    have hd := (h : ((algebraMap ℝ (Matrix n n ℂ)) b -
      (algebraMap ℝ (Matrix n n ℂ)) a).PosSemidef).diag_nonneg (i := Classical.arbitrary n)
    simpa [Matrix.sub_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply,
      Matrix.one_apply] using hd
  · intro h
    rw [Matrix.le_iff, ← map_sub]
    rw [Algebra.algebraMap_eq_smul_one]
    exact Matrix.nonneg_iff_posSemidef.mp
      (smul_nonneg (sub_nonneg.mpr h) (zero_le_one : 0 ≤ (1 : Matrix n n ℂ)))

lemma MetricFeasible.one_le {T H : Matrix n n ℂ} {τ : ℝ}
    (h : MetricFeasible T τ H) : 1 ≤ τ := by
  apply (scalarMatrix_le_iff (n := n) 1 τ).mp
  simpa using h.1.trans h.2.1

lemma MetricFeasible.norm_le {T H : Matrix n n ℂ} {τ : ℝ}
    (h : MetricFeasible T τ H) : ‖H‖ ≤ τ :=
  (CStarAlgebra.norm_le_iff_le_algebraMap H (zero_le_one.trans h.one_le)
    (zero_le_one.trans h.1)).mpr h.2.1

lemma isClosed_metricFeasible {n : Type u_181} [Fintype n] [DecidableEq n] [Nonempty n]
    (T : Matrix n n ℂ) :
    IsClosed {x : ℝ × Matrix n n ℂ | MetricFeasible T x.1 x.2} := by
  unfold MetricFeasible
  exact (isClosed_le continuous_const continuous_snd).inter
    ((isClosed_le continuous_snd ((continuous_algebraMap ℝ _).comp continuous_fst)).inter
      (isClosed_le ((continuous_const.mul continuous_snd).mul continuous_const) continuous_snd))

end Minimum

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : Type u_182} [Fintype n] [DecidableEq n]
abbrev HermitianMatrix (n : Type u_183) [Fintype n] [DecidableEq n] :=
  selfAdjoint (Matrix n n ℂ)
def fromHSL : HSMatrix n →ₗ[ℝ] Matrix n n ℂ where
  toFun := fromHS
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def hermTrace (B A : HermitianMatrix n) : ℝ :=
  (Matrix.trace ((B : Matrix n n ℂ) * (A : Matrix n n ℂ))).re

lemma hermTrace_realPart (B : Matrix n n ℂ) (A : HermitianMatrix n) :
    hermTrace (realPart B) A =
      (Matrix.trace (Bᴴ * (A : Matrix n n ℂ))).re := by
  have hA : (A : Matrix n n ℂ)ᴴ = A := A.property
  have hconj : (Matrix.trace (B * (A : Matrix n n ℂ))).re =
      (Matrix.trace (Bᴴ * (A : Matrix n n ℂ))).re := by
    have hc := congrArg Complex.re (Matrix.trace_conjTranspose (B * (A : Matrix n n ℂ)))
    rw [Matrix.conjTranspose_mul, hA, Matrix.trace_mul_comm] at hc
    simpa using hc.symm
  simp only [hermTrace, realPart_apply_coe, Matrix.star_eq_conjTranspose,
    Matrix.add_mul, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_add,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_re]
  rw [hconj]
  ring

theorem exists_hermitian_trace_representative
    (φ : HermitianMatrix n →ₗ[ℝ] ℝ) :
    ∃ B : HermitianMatrix n, ∀ A, φ A = hermTrace B A := by
  let f : HSMatrix n →ₗ[ℝ] ℝ := φ.comp (realPart.comp fromHSL)
  let fc : HSMatrix n →L[ℝ] ℝ := f.toContinuousLinearMap
  obtain ⟨v, hv⟩ := (InnerProductSpace.toDual ℝ (HSMatrix n)).surjective fc
  refine ⟨realPart (fromHS v), ?_⟩
  intro A
  have h := congrArg (fun g : HSMatrix n →L[ℝ] ℝ => g (toHS (A : Matrix n n ℂ))) hv
  change inner ℝ v (toHS (A : Matrix n n ℂ)) = _ at h
  have hr : realPart (A : Matrix n n ℂ) = A := by
    exact Subtype.ext A.property.coe_realPart
  have hval : fc (toHS (A : Matrix n n ℂ)) = φ A := by
    change φ (realPart (fromHS (toHS (A : Matrix n n ℂ)))) = φ A
    rw [fromHS_toHS, hr]
  rw [hval] at h
  rw [hermTrace_realPart, ← hs_inner, toHS_fromHS]
  have hir (u w : HSMatrix n) : inner ℝ u w = (inner ℂ u w).re := by
    simp only [PiLp.inner_apply, Complex.re_sum]
    rfl
  simpa only [hir] using h.symm

lemma hermTrace_symm (A B : HermitianMatrix n) : hermTrace A B = hermTrace B A := by
  exact congrArg Complex.re (Matrix.trace_mul_comm _ _)

lemma hermTrace_nonneg_iff (B : HermitianMatrix n) :
    (0 ≤ (B : Matrix n n ℂ)) ↔
      ∀ A : HermitianMatrix n, 0 ≤ (A : Matrix n n ℂ) → 0 ≤ hermTrace B A := by
  constructor
  · intro hB A hA
    obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
    have h := (Matrix.nonneg_iff_posSemidef.mp hB).mul_mul_conjTranspose_same C
    have hr := (Complex.nonneg_iff.mp h.trace_nonneg).1
    rw [Matrix.trace_mul_cycle] at hr
    rw [Matrix.trace_mul_comm] at hr
    simpa only [hermTrace, hC, Matrix.star_eq_conjTranspose] using hr
  · intro h
    apply Matrix.PosSemidef.nonneg
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg B.property
    intro x
    let A : HermitianMatrix n :=
      ⟨Matrix.vecMulVec x (star x), (Matrix.posSemidef_vecMulVec_self_star x).isHermitian⟩
    have hx := h A (Matrix.posSemidef_vecMulVec_self_star x).nonneg
    change 0 ≤ (Matrix.trace ((B : Matrix n n ℂ) * Matrix.vecMulVec x (star x))).re at hx
    rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] at hx
    apply Complex.nonneg_iff.mpr
    refine ⟨hx, ?_⟩
    exact (Matrix.IsHermitian.im_star_dotProduct_mulVec_self B.property x).symm

end
end
end
end
end

end CompleteCrouzeix

end

end OAI
