import Tengoku.OpenaiMath.OAI.MathematicalPhysics.CriticalSK.SmallBall

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

open Set MeasureTheory

lemma euclideanMatrix_norm_le_frobenius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖A.toEuclideanLin.toContinuousLinearMap‖ ≤ Real.sqrt (∑ i, ∑ j, A i j^2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  have hi (i : Fin n) : (∑ j, A i j*x j)^2 ≤ (∑ j, A i j^2)*(∑ j, (x j)^2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [← Finset.sum_mul,← EuclideanSpace.real_norm_sq_eq x] at hs
  have hy : ‖A.toEuclideanLin.toContinuousLinearMap x‖^2 = ∑ i, (∑ j, A i j*x j)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [← hy] at hs
  have hF : 0 ≤ ∑ i, ∑ j, A i j^2 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hr := Real.sq_sqrt hF
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp ?_
  rw [mul_pow,hr]
  exact hs

lemma covariance_continuous (n : ℕ) : Continuous (covariance (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [covariance_eq,mean]
  apply continuous_finsetSum
  intro x _
  exact (gibbs_continuous x).mul continuous_const

lemma covarianceNorm_continuous (n : ℕ) : Continuous (covarianceNorm (n := n)) := by
  unfold covarianceNorm
  have h : Continuous (fun W : Disorder n => (covariance W).toEuclideanLin.toContinuousLinearMap) := by
    exact (LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap).comp (covariance_continuous n)
  exact h.norm

lemma variance_linear_quadratic {n : ℕ} (W : Disorder n) (a : EuclideanSpace ℝ (Fin n)) :
    variance W (linearObservable a) = inner ℝ a ((covariance W).toEuclideanLin a) := by
  rw [variance,mean_linearObservable]
  simp only [sub_zero,mean,linearObservable,
    EuclideanSpace.inner_eq_star_dotProduct,star_trivial,Matrix.toLpLin_apply,Matrix.mulVec,dotProduct,covariance_eq,mean]
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma variance_linear_le_norm {n : ℕ} (W : Disorder n) (a : EuclideanSpace ℝ (Fin n)) :
    variance W (linearObservable a) ≤ covarianceNorm W*‖a‖^2 := by
  rw [variance_linear_quadratic]
  have hh := real_inner_le_norm a ((covariance W).toEuclideanLin a)
  have hn := (covariance W).toEuclideanLin.toContinuousLinearMap.le_opNorm a
  calc
    inner ℝ a ((covariance W).toEuclideanLin a) ≤ ‖a‖*‖(covariance W).toEuclideanLin a‖ := hh
    _ ≤ ‖a‖*(covarianceNorm W*‖a‖) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = covarianceNorm W*‖a‖^2 := by ring

lemma variance_linear_smallBall {n : ℕ} (W : Disorder n) (a : Fin n → ℝ) {b : ℝ} (hb : 0 ≤ b) :
    b^2*(1-linearSmallBall W a b) ≤ variance W (linearObservable a) := by
  rw [variance,mean_linearObservable]
  simp only [sub_zero,mean]
  rw [← gibbs_sum W,linearSmallBall,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : |linearObservable a x| ≤ b
  · simp only [ite_eq_left hx,sub_self,mul_zero]
    exact mul_nonneg (gibbs_nonneg W x) (sq_nonneg _)
  · simp only [ite_eq_right hx,sub_zero]
    have hs : b^2 ≤ linearObservable a x^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hb (le_of_lt (lt_of_not_ge hx)) 2
    nlinarith [mul_le_mul_of_nonneg_left hs (gibbs_nonneg W x)]

lemma sum_four_exchange {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (f : ι → κ → α → β → ℝ) :
    (∑ i, ∑ j, ∑ x, ∑ y, f i j x y) = ∑ x, ∑ y, ∑ i, ∑ j, f i j x y := by
  calc
    _ = ∑ i, ∑ x, ∑ j, ∑ y, f i j x y := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ i, ∑ y, ∑ j, f i j x y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]

lemma gibbsOverlap_nonneg {n : ℕ} (W : Disorder n) : 0 ≤ gibbsOverlap W := by
  unfold gibbsOverlap
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by
    exact mul_nonneg (mul_nonneg (gibbs_nonneg W x) (gibbs_nonneg W y)) (sq_nonneg _)

lemma gibbsOverlap_continuous (n : ℕ) : Continuous (gibbsOverlap (n := n)) := by
  unfold gibbsOverlap
  apply continuous_finsetSum
  intro x _
  apply continuous_finsetSum
  intro y _
  exact ((gibbs_continuous x).mul (gibbs_continuous y)).mul continuous_const

lemma finite_gram_frobenius {ι X : Type*} [Fintype ι] [Fintype X]
    (w : X → ℝ) (v : X → ι → ℝ) :
    (∑ i, ∑ j, (∑ x, w x*(v x i*v x j))^2) =
      ∑ x, ∑ y, w x*w y*(∑ i, v x i*v y i)^2 := by
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
  rw [sum_four_exchange]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma covariance_frobenius_overlap {n : ℕ} (hn : 0 < n) (W : Disorder n) :
    (∑ i, ∑ j, covariance W i j^2) = (n:ℝ)^2*gibbsOverlap W := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hR : (n:ℝ)^2*gibbsOverlap W =
      ∑ x, ∑ y, gibbs W x*gibbs W y*(∑ i, spinValue (x i)*spinValue (y i))^2 := by
    unfold gibbsOverlap
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    have hi : inner ℝ (cubeVector x) (cubeVector y) = ∑ i, spinValue (x i)*spinValue (y i) := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,cubeVector]
      apply Finset.sum_congr rfl
      intro i _
      change spinValue (y i)*spinValue (x i) = spinValue (x i)*spinValue (y i)
      ring
    rw [cubeOverlap,hi]
    field_simp
  rw [hR]
  simp only [covariance_eq,mean]
  exact finite_gram_frobenius (gibbs W) (fun x i => spinValue (x i))

lemma covarianceNorm_sq_le_overlap {n : ℕ} (hn : 0 < n) (W : Disorder n) :
    covarianceNorm W^2 ≤ (n:ℝ)^2*gibbsOverlap W := by
  have h := euclideanMatrix_norm_le_frobenius (covariance W)
  have hs : 0 ≤ ∑ i, ∑ j, covariance W i j^2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [Real.sq_sqrt hs,covariance_frobenius_overlap hn W] at hb
  exact hb

lemma rotatedCubeOverlap_eq {n : ℕ} {W : Disorder n} (lam : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (c : ℝ)
    (h : ∀ x, hamiltonian W x = (1/2:ℝ)*diagonalEnergy lam (orthogonalIsometry U (cubeVector x))+c) :
    rotatedCubeOverlap lam U = gibbsOverlap W := by
  have hg := gibbs_exp_shift _ c h
  unfold rotatedCubeOverlap rotatedCubePair rotatedCubePartition gibbsOverlap
  rw [mul_pow,mul_div_mul_left _ _ (pow_ne_zero _ (inv_ne_zero (by positivity : (Fintype.card (Spin n):ℝ) ≠ 0)))]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  rw [hg,hg,show (diagonalEnergy lam (orthogonalIsometry U (cubeVector x))+
    diagonalEnergy lam (orthogonalIsometry U (cubeVector y)))/2 =
    (1/2:ℝ)*diagonalEnergy lam (orthogonalIsometry U (cubeVector x))+
      (1/2:ℝ)*diagonalEnergy lam (orthogonalIsometry U (cubeVector y)) by ring,Real.exp_add]
  ring

open Set MeasureTheory Filter

lemma haar_gibbsOverlap_bound {n : ℕ} (hn : 0 < n)
    (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i) {K : ℝ} (hK : 0 < K) :
    (orthogonalHaar (Fin n)).real {U | K ≤ gibbsOverlap (gaussianDisorder (haarConjugate U A))} ≤
      4*(∫ U, (rotatedCubePartition (matrixOrderedEigenvalues A) 1 U /
          spherePartition (matrixOrderedEigenvalues A) 1 (Real.sqrt n)-1)^2 ∂orthogonalHaar (Fin n))+
        4*((∫ U, rotatedCubePair (matrixOrderedEigenvalues A) (fun q => q^2) U ∂orthogonalHaar (Fin n))/
          spherePartition (matrixOrderedEigenvalues A) 1 (Real.sqrt n)^2)/K := by
  obtain ⟨V,hV⟩ := gaussian_matrix_energy_eigenbasis A hA
  let lam := matrixOrderedEigenvalues A
  let R := matrixOfIsometry V
  have he (U : Matrix.orthogonalGroup (Fin n) ℝ) : gibbsOverlap (gaussianDisorder (haarConjugate U A)) =
      rotatedCubeOverlap lam (R*U) := by
    symm
    apply rotatedCubeOverlap_eq lam (R*U) (-(1/2:ℝ)*∑ j, haarConjugate U A j j)
    intro x
    simpa only [gaussianDisorder,lam,R,sub_eq_add_neg,neg_mul] using haarConjugate_hamiltonian A hA V hV U x
  simp_rw [he]
  change ((orthogonalHaar (Fin n)) ((fun U => R*U) ⁻¹' {U | K ≤ rotatedCubeOverlap lam U})).toReal ≤ _
  rw [measure_preimage_mul]
  exact rotatedCubeOverlap_probability hn lam hK

lemma naturalOverlapConstant_pos {L : ℝ} (hL : 0 < L) : 0 < naturalOverlapConstant L := by
  unfold naturalOverlapConstant
  positivity

lemma two_thirds_cube {x : ℝ} (hx : 0 ≤ x) : (x^(2/3:ℝ))^3 = x^2 := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

lemma tight_interval_limit {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (f : ∀ n, X n → ℝ) (hf : ∀ n, Measurable (f n))
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n)
    (hlower : ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (μ n).real {x | f n x ≤ c*s n} < α)
    (hupper : ∀ α : ℝ, 0 < α → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (μ n).real {x | C*s n ≤ f n x} < α)
    (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop) :
    Tendsto (fun n => (μ n).real {x | s n/M n ≤ f n x ∧ f n x ≤ M n*s n}) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨c,hc,hl⟩ := hlower ((1-a)/2) (by linarith)
    obtain ⟨C,hC,hu⟩ := hupper ((1-a)/2) (by linarith)
    filter_upwards [hl,hu,(tendsto_atTop.mp hM (1/c)),(tendsto_atTop.mp hM C)] with n hnlo hnup hnM hnC
    let E : Set (X n) := {x | s n/M n ≤ f n x ∧ f n x ≤ M n*s n}
    have hE : MeasurableSet E := (measurableSet_le measurable_const (hf n)).inter
      (measurableSet_le (hf n) measurable_const)
    have hlow : s n/M n ≤ c*s n := by
      apply (div_le_iff₀ (hMpos n)).mpr
      have hh : 1 ≤ M n*c := (div_le_iff₀ hc).mp hnM
      nlinarith [mul_le_mul_of_nonneg_right hh (hs n).le]
    have hset : Eᶜ ⊆ {x | f n x ≤ c*s n} ∪ {x | C*s n ≤ f n x} := by
      intro x hx
      by_cases hxl : s n/M n ≤ f n x
      · right
        have hxu : M n*s n < f n x := by
          apply lt_of_not_ge
          intro hh
          exact hx ⟨hxl,hh⟩
        exact (mul_le_mul_of_nonneg_right hnC (hs n).le).trans hxu.le
      · left
        exact (lt_of_not_ge hxl).le.trans hlow
    have hbad := (measureReal_mono (μ := μ n) hset).trans (measureReal_union_le _ _)
    have hadd := measureReal_add_measureReal_compl (μ := μ n) hE
    rw [probReal_univ] at hadd
    change a < (μ n).real E
    linarith
  · intro a ha
    exact Filter.Eventually.of_forall (fun _ => lt_of_le_of_lt measureReal_le_one ha)

end CriticalSK

end

end OAI
