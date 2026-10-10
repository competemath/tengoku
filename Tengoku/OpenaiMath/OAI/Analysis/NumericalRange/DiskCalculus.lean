import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.HolomorphicEvaluation

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_65 u_66 u_67 u_68 u_69 u_70 u_71 u_72 u_73 u_74 u_75 u_76 u_77 u_78 u_79 u_80

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset

section
open Filter Topology Set Module
variable {V : Type u_65} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]

lemma primaryEval_tendsto_apply {ι : Type u_66} {l : Filter ι}
    (T : Module.End ℂ V) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (h : ∀ β ∈ spectrum ℂ T, ∀ k < finrank ℂ V,
      Tendsto (fun i => iteratedDeriv k (F i) β) l (nhds (iteratedDeriv k f β))) (x : V) :
    Tendsto (fun i => primaryEval T (F i) x) l (nhds (primaryEval T f x)) := by
  have hx : x ∈ ⨆ β, T.maxGenEigenspace β := by rw [T.iSup_maxGenEigenspace_eq_top]; trivial
  refine Submodule.iSup_induction _
    (motive := fun x => Tendsto (fun i => primaryEval T (F i) x) l (nhds (primaryEval T f x))) hx
    ?_ (by simpa using tendsto_const_nhds) ?_
  · intro β x hx
    by_cases hβ : β ∈ spectrum ℂ T
    · have he (g : ℂ → ℂ) : primaryEval T g x =
          ∑ k ∈ Finset.range (finrank ℂ V),
          (iteratedDeriv k g β / (k.factorial : ℂ)) •
            (((primaryNilpotent T β)^k) ⟨x,hx⟩ : V) := by
        rw [primaryEval_coe T g β ⟨x,hx⟩]
        simp only [scalarJetEval, LinearMap.sum_apply, LinearMap.smul_apply,
          Submodule.coe_sum, Submodule.coe_smul]
      simp only [he]
      apply tendsto_finsetSum
      intro k hk
      exact ((h β hβ k (Finset.mem_range.mp hk)).div_const _).smul tendsto_const_nhds
    · have hspace : T.maxGenEigenspace β = ⊥ := by
        by_contra hn
        have he : T.HasGenEigenvalue β (finrank ℂ V) := by
          rwa [T.maxGenEigenspace_eq_genEigenspace_finrank β] at hn
        exact hβ (Module.End.hasEigenvalue_of_hasGenEigenvalue he).mem_spectrum
      have he : x = 0 := by simpa [hspace] using hx
      simpa only [he, map_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : V)) l (nhds 0))
  · intro x y hx hy
    simpa only [map_add] using hx.add hy

end

section
open Filter Topology Set Module
variable {n : Type u_67} [Fintype n] [DecidableEq n]

noncomputable def matrixAnalyticEval (A : Matrix n n ℂ) (f : ℂ → ℂ) : Matrix n n ℂ :=
  Matrix.toLinAlgEquiv'.symm (primaryEval (Matrix.toLinAlgEquiv' A) f)

lemma matrixAnalyticEval_polynomial (A : Matrix n n ℂ) (p : ℂ[X]) :
    matrixAnalyticEval A (fun z => p.eval z) = Polynomial.aeval A p := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply, primaryEval_polynomial,
    Polynomial.aeval_algHom_apply]

lemma matrixAnalyticEval_tendsto {ι : Type u_68} {l : Filter ι}
    (A : Matrix n n ℂ) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (h : ∀ β ∈ spectrum ℂ A, ∀ k < Fintype.card n,
      Tendsto (fun i => iteratedDeriv k (F i) β) l (nhds (iteratedDeriv k f β))) :
    Tendsto (fun i => matrixAnalyticEval A (F i)) l (nhds (matrixAnalyticEval A f)) := by
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  have he := primaryEval_tendsto_apply (Matrix.toLinAlgEquiv' A)
    (F := F) (f := f) (fun β hβ k hk => h β (by
      simpa only [AlgEquiv.spectrum_eq] using hβ) k (by simpa using hk)) (Pi.single b 1)
  exact (tendsto_pi_nhds.mp he) a

end

section
open Filter Topology Set Module

lemma locallyUniform_iteratedDeriv {ι : Type u_69} {l : Filter ι}
    {U : Set ℂ} (hU : IsOpen U) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) U)
    (ht : TendstoLocallyUniformlyOn F f l U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv k (F i)) (iteratedDeriv k f) l U := by
  induction k with
  | zero => simpa using ht
  | succ k ih =>
    simp only [iteratedDeriv_succ]
    apply ih.deriv _ hU
    exact Eventually.of_forall fun i => by
      simpa only [iteratedDeriv_eq_iterate] using
        ((hF i).iterated_deriv k).differentiableOn

lemma matrixAnalyticEval_tendsto_locallyUniform
    {n : Type u_70} [Fintype n] [DecidableEq n] {ι : Type u_71} {l : Filter ι}
    (A : Matrix n n ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hAU : spectrum ℂ A ⊆ U) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) U)
    (ht : TendstoLocallyUniformlyOn F f l U) :
    Tendsto (fun i => matrixAnalyticEval A (F i)) l (nhds (matrixAnalyticEval A f)) := by
  apply matrixAnalyticEval_tendsto
  intro β hβ k _
  exact (locallyUniform_iteratedDeriv hU hF ht k).tendsto_at (hAU hβ)

end

section
open Filter Topology Set Metric
open scoped NNReal ENNReal

noncomputable def seriesPolynomial (p : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range N, Polynomial.monomial k (p.coeff k)

lemma seriesPolynomial_eval (p : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) (z : ℂ) :
    (seriesPolynomial p N).eval z = p.partialSum N z := by
  simp only [seriesPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    FormalMultilinearSeries.partialSum, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    smul_eq_mul, mul_comm]

lemma analytic_closed_disk_polynomial_approximation {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 1)) :
    ∃ r : ℝ, 1 < r ∧ ∃ p : ℕ → ℂ[X],
      TendstoUniformlyOn (fun N z => (p N).eval z) f atTop (ball 0 r) := by
  obtain ⟨δ, hδ, hinc⟩ := (isCompact_closedBall (0:ℂ) 1).exists_cthickening_subset_open
    (isOpen_analyticAt ℂ f) hf
  rw [cthickening_closedBall hδ.le (by norm_num : (0:ℝ) ≤ 1)] at hinc
  let R : ℝ≥0 := ⟨δ+1, by linarith⟩
  have hR : 0 < R := by change (0:ℝ) < δ+1; linarith
  have hd : DifferentiableOn ℂ f (closedBall 0 R) := by
    intro z hz
    exact (hinc hz).differentiableAt.differentiableWithinAt
  have hs := hd.hasFPowerSeriesOnBall hR
  let r : ℝ≥0 := ⟨δ/2+1, by linarith⟩
  refine ⟨(r : ℝ), by change 1 < δ/2+1; linarith, seriesPolynomial (cauchyPowerSeries f 0 R), ?_⟩
  have hr : (r : ℝ≥0∞) < (R : ℝ≥0∞) := by
    rw [ENNReal.coe_lt_coe]
    change δ/2+1 < δ+1
    linarith
  have ht := hs.tendstoUniformlyOn hr
  simpa only [seriesPolynomial_eval, zero_add] using ht

end

open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section Stability
variable {A : Type u_72} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

end Stability

open MeasureTheory
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
abbrev circleMeasure := @AddCircle.haarAddCircle 1 inferInstance
variable {n : Type u_73} [instFintypeN : Fintype n] [instDecidableEqN : DecidableEq n]

def diskResolventSeries (D : Matrix n n ℂ) (t : AddCircle (1:ℝ)) : Matrix n n ℂ :=
  ∑' j : ℕ, fourier (-(j:ℤ)) t • D^j

lemma fourier_norm_value (k : ℤ) (t : AddCircle (1:ℝ)) : ‖fourier k t‖ = 1 :=
  Circle.norm_coe _

lemma fourier_neg_nat_pow (t : AddCircle (1:ℝ)) (j : ℕ) :
    fourier (-1) t ^ j = fourier (-(j:ℤ)) t := by
  induction j with
  | zero => simp
  | succ j hj =>
    rw [pow_succ,hj,← fourier_add]
    congr 2
    push_cast
    ring

def diskDensity (D : Matrix n n ℂ) (t : AddCircle (1:ℝ)) : Matrix n n ℂ :=
  diskResolventSeries D t + (diskResolventSeries D t)ᴴ - 1

lemma integral_fourier (k : ℤ) :
    (∫ t : AddCircle (1:ℝ), fourier k t ∂circleMeasure) = if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1:ℝ)) k) 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, Pi.single_apply,
    ite_eq_left_iff, eq_comm] using h

lemma integral_fourier_smul (k : ℤ) (A : Matrix n n ℂ) :
    (∫ t : AddCircle (1:ℝ), fourier k t • A ∂circleMeasure) = if k = 0 then A else 0 := by
  rw [integral_smul_const,integral_fourier]
  split_ifs <;> simp

lemma integral_matrix_fourier_series (A : ℕ → Matrix n n ℂ)
    (hA : Summable (fun j => ‖A j‖)) (l : ℕ → ℤ) (k : ℤ) :
    (∫ t : AddCircle (1:ℝ), fourier k t • (∑' j : ℕ, fourier (l j) t • A j) ∂circleMeasure) =
      ∑' j : ℕ, if k + l j = 0 then A j else 0 := by
  have he (t : AddCircle (1:ℝ)) :
      fourier k t • (∑' j : ℕ, fourier (l j) t • A j) =
        ∑' j : ℕ, fourier (k+l j) t • A j := by
    rw [← tsum_const_smul'']
    apply tsum_congr
    intro j
    rw [smul_smul,← fourier_add]
  simp_rw [he]
  rw [← integral_tsum_of_summable_integral_norm]
  · apply tsum_congr
    intro j
    exact integral_fourier_smul _ _
  · intro j
    exact ((fourier (k+l j)).continuous.smul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · simpa only [norm_smul,fourier_norm_value,one_mul,integral_const,measure_univ,
      Measure.real,measure_univ, ENNReal.toReal_one,one_smul] using hA

open scoped Kronecker

variable {m : Type u_74} [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

lemma contraction_block_iff (C : Matrix m m ℂ) :
    (Matrix.fromBlocks 1 C Cᴴ 1).PosSemidef ↔ ‖C‖ ≤ 1 := by
  let : Invertible (1 : Matrix m m ℂ) := invertibleOne
  rw [Matrix.PosDef.fromBlocks₁₁ C (1 : Matrix m m ℂ) Matrix.PosDef.one]
  simp only [inv_one, Matrix.mul_one]
  change Cᴴ*C ≤ 1 ↔ ‖C‖ ≤ 1
  rw [← CStarAlgebra.norm_le_one_iff_of_nonneg (Cᴴ*C)
    (Matrix.posSemidef_conjTranspose_mul_self C).nonneg,
    Matrix.l2_opNorm_conjTranspose_mul_self]
  constructor <;> intro h <;> nlinarith [norm_nonneg C]

lemma positive_density_block
    {n : Type u_73} [Fintype n] [DecidableEq n] {m : Type u_74} [Fintype m] [DecidableEq m]
    {L : Matrix n n ℂ} (hL : L.PosSemidef)
    {F : Matrix m m ℂ} (hF : ‖F‖ ≤ 1) :
    (Matrix.fromBlocks (L ⊗ₖ 1) (L ⊗ₖ F) (L ⊗ₖ F)ᴴ (L ⊗ₖ 1)).PosSemidef := by
  have h := (hL.kronecker ((contraction_block_iff F).mpr hF)).submatrix
    (Equiv.prodSumDistrib n m m).symm
  have he : Matrix.fromBlocks (L ⊗ₖ 1) (L ⊗ₖ F) (L ⊗ₖ F)ᴴ (L ⊗ₖ 1) =
      (L ⊗ₖ Matrix.fromBlocks 1 F Fᴴ 1).submatrix
        (Equiv.prodSumDistrib n m m).symm (Equiv.prodSumDistrib n m m).symm := by
    rw [Matrix.conjTranspose_kronecker, hL.isHermitian.eq]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  rwa [he]

def entryCLM (i j : n) : Matrix n n ℂ →L[ℂ] ℂ :=
  (show Matrix n n ℂ →ₗ[ℂ] ℂ from
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap

lemma matrix_integral_entry {X : Type u_75} [MeasurableSpace X] {μ : Measure X}
    {L : X → Matrix n n ℂ} (hL : Integrable L μ) (i j : n) :
    (∫ t, L t ∂μ) i j = ∫ t, L t i j ∂μ :=
  ((entryCLM i j).integral_comp_comm hL).symm

def kronCLM (B : Matrix m m ℂ) : Matrix n n ℂ →L[ℂ] Matrix (n×m) (n×m) ℂ :=
  (show Matrix n n ℂ →ₗ[ℂ] Matrix (n×m) (n×m) ℂ from
    { toFun := fun A => A ⊗ₖ B
      map_add' := fun A C => Matrix.add_kronecker A C B
      map_smul' := fun c A => Matrix.smul_kronecker c A B }).toContinuousLinearMap

lemma integral_kron_const {X : Type u_76} [MeasurableSpace X] {μ : Measure X}
    {L : X → Matrix n n ℂ} (hL : Integrable L μ) (B : Matrix m m ℂ) :
    (∫ t, L t ⊗ₖ B ∂μ) = (∫ t, L t ∂μ) ⊗ₖ B :=
  (kronCLM B).integral_comp_comm hL

lemma integral_fromBlocks {X : Type u_77} [MeasurableSpace X] {μ : Measure X}
    {A B C D : X → Matrix n n ℂ}
    (hA : Integrable A μ) (hB : Integrable B μ) (hC : Integrable C μ) (hD : Integrable D μ) :
    (∫ t, Matrix.fromBlocks (A t) (B t) (C t) (D t) ∂μ) =
      Matrix.fromBlocks (∫ t, A t ∂μ) (∫ t, B t ∂μ) (∫ t, C t ∂μ) (∫ t, D t ∂μ) := by
  let e : (Matrix n n ℂ × Matrix n n ℂ × Matrix n n ℂ × Matrix n n ℂ) →L[ℂ]
      Matrix (n⊕n) (n⊕n) ℂ :=
    (show (Matrix n n ℂ × Matrix n n ℂ × Matrix n n ℂ × Matrix n n ℂ) →ₗ[ℂ]
      Matrix (n⊕n) (n⊕n) ℂ from
      { toFun := fun X => Matrix.fromBlocks X.1 X.2.1 X.2.2.1 X.2.2.2
        map_add' := fun X Y => by ext i j; rcases i with i | i <;> rcases j with j | j <;> rfl
        map_smul' := fun c X => by ext i j; rcases i with i | i <;> rcases j with j | j <;> rfl
      }).toContinuousLinearMap
  have h := e.integral_comp_comm (hA.prodMk (hB.prodMk (hC.prodMk hD)))
  change (∫ t, Matrix.fromBlocks (A t) (B t) (C t) (D t) ∂μ) =
    Matrix.fromBlocks (∫ t, (A t, B t, C t, D t) ∂μ).1
      (∫ t, (A t, B t, C t, D t) ∂μ).2.1
      (∫ t, (A t, B t, C t, D t) ∂μ).2.2.1
      (∫ t, (A t, B t, C t, D t) ∂μ).2.2.2 at h
  simpa only [integral_pair hA (hB.prodMk (hC.prodMk hD)),
    integral_pair hB (hC.prodMk hD), integral_pair hC hD] using h

def conjTransposeRCLM : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  (show Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ from
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := fun c A => by simp }).toContinuousLinearMap

lemma integral_conjTranspose {X : Type u_78} [MeasurableSpace X] {μ : Measure X}
    {L : X → Matrix n n ℂ} (hL : Integrable L μ) :
    (∫ t, (L t)ᴴ ∂μ) = (∫ t, L t ∂μ)ᴴ :=
  conjTransposeRCLM.integral_comp_comm hL

theorem norm_integral_density_kron {X : Type u_79} [MeasurableSpace X] {μ : Measure X}
    {L : X → Matrix n n ℂ} {F : X → Matrix m m ℂ}
    (hL : Integrable L μ) (hLF : Integrable (fun t => L t ⊗ₖ F t) μ)
    (hpos : ∀ t, (L t).PosSemidef) (hmass : ∫ t, L t ∂μ = 1)
    (hF : ∀ t, ‖F t‖ ≤ 1) : ‖∫ t, L t ⊗ₖ F t ∂μ‖ ≤ 1 := by
  have hd (t : X) := positive_density_block (hpos t) (hF t)
  have hnonneg : 0 ≤ ∫ t, Matrix.fromBlocks (L t ⊗ₖ 1) (L t ⊗ₖ F t)
      (L t ⊗ₖ F t)ᴴ (L t ⊗ₖ 1) ∂μ :=
    integral_nonneg (fun t => (hd t).nonneg)
  have hdiag : Integrable (fun t => L t ⊗ₖ (1 : Matrix m m ℂ)) μ :=
    (kronCLM (1 : Matrix m m ℂ)).integrable_comp hL
  have hstar : Integrable (fun t => (L t ⊗ₖ F t)ᴴ) μ :=
    conjTransposeRCLM.integrable_comp hLF
  rw [integral_fromBlocks hdiag hLF hstar hdiag, integral_kron_const hL,
    hmass, Matrix.one_kronecker_one, integral_conjTranspose hLF] at hnonneg
  exact (contraction_block_iff _).mp (Matrix.nonneg_iff_posSemidef.mp hnonneg)

lemma continuous_kron
    {n : Type u_73} [Fintype n] [DecidableEq n] {m : Type u_74} [Fintype m] [DecidableEq m]
    {X : Type u_80} [TopologicalSpace X]
    {L : X → Matrix n n ℂ} {F : X → Matrix m m ℂ}
    (hL : Continuous L) (hF : Continuous F) : Continuous (fun t => L t ⊗ₖ F t) := by
  apply continuous_matrix
  intro i j
  exact ((entryCLM i.1 j.1).continuous.comp hL).mul
    ((entryCLM i.2 j.2).continuous.comp hF)

def circlePolynomial {d : ℕ} (B : Fin (d+1) → Matrix m m ℂ)
    (t : AddCircle (1:ℝ)) : Matrix m m ℂ := ∑ k, fourier (k.val:ℤ) t • B k

lemma continuous_circlePolynomial
    {m : Type u_74} [Fintype m] [DecidableEq m] {d : ℕ} (B : Fin (d+1) → Matrix m m ℂ) :
    Continuous (circlePolynomial B) := by
  exact continuous_finsetSum _ (fun k _ => (fourier (k.val:ℤ)).continuous.smul continuous_const)

lemma kron_circlePolynomial
    {n : Type u_73} [Fintype n] [DecidableEq n] {m : Type u_74} [Fintype m] [DecidableEq m] {d : ℕ}
    (L : Matrix n n ℂ)
    (B : Fin (d+1) → Matrix m m ℂ) (t : AddCircle (1:ℝ)) :
    L ⊗ₖ circlePolynomial B t = ∑ k, (fourier (k.val:ℤ) t • L) ⊗ₖ B k := by
  ext i j
  simp only [circlePolynomial, Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end CompleteCrouzeix

end

end OAI
