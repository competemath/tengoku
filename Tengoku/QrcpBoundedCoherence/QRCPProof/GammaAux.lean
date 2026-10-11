import Tengoku

/-! # Auxiliary lemmas for `gamma_eq_inv_sqrt_min_eigenvalue` -/

open Matrix Real
open scoped Matrix.Norms.L2Operator

private lemma unitary_norm_conj {k : ℕ} [DecidableEq (Fin k)] [Nonempty (Fin k)]
    (U : unitaryGroup (Fin k) ℝ) (A : Matrix (Fin k) (Fin k) ℝ) :
    ‖(Unitary.conjStarAlgAut ℝ (Matrix (Fin k) (Fin k) ℝ) U) A‖ = ‖A‖ := by
  simp only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  have hUU : (U : Matrix (Fin k) (Fin k) ℝ) * (U : Matrix (Fin k) (Fin k) ℝ)ᴴ = 1 := by
    have := U.2; rw [Matrix.mem_unitaryGroup_iff] at this; rwa [star_eq_conjTranspose] at this
  have hUHU : (U : Matrix (Fin k) (Fin k) ℝ)ᴴ * U = 1 := by
    have hdet : IsUnit (U : Matrix (Fin k) (Fin k) ℝ).det :=
      IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, hUU, Matrix.det_one])
    rw [← Matrix.inv_eq_right_inv hUU]; exact Matrix.nonsing_inv_mul _ hdet
  have hU1 : ‖(U : Matrix (Fin k) (Fin k) ℝ)‖ = 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self (U : Matrix (Fin k) (Fin k) ℝ)ᴴ
    rw [Matrix.conjTranspose_conjTranspose, hUU, Matrix.l2_opNorm_conjTranspose] at h
    have h1 : ‖(1 : Matrix (Fin k) (Fin k) ℝ)‖ = 1 := by
      rw [← Matrix.l2_opNorm_toEuclideanCLM, map_one]; exact ContinuousLinearMap.norm_id
    rw [h1] at h; nlinarith [norm_nonneg (U : Matrix (Fin k) (Fin k) ℝ)]
  have hUH1 : ‖(U : Matrix (Fin k) (Fin k) ℝ)ᴴ‖ = 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]; exact hU1
  apply le_antisymm
  · calc ‖(U : Matrix (Fin k) (Fin k) ℝ) * A * (U : Matrix (Fin k) (Fin k) ℝ)ᴴ‖
        ≤ ‖(U : Matrix (Fin k) (Fin k) ℝ)‖ * ‖A‖ * ‖(U : Matrix (Fin k) (Fin k) ℝ)ᴴ‖ :=
            le_trans (Matrix.l2_opNorm_mul _ _)
              (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ = ‖A‖ := by rw [hU1, hUH1]; ring
  · have key : A = (U : Matrix (Fin k) (Fin k) ℝ)ᴴ *
        ((U : Matrix (Fin k) (Fin k) ℝ) * A * (U : Matrix (Fin k) (Fin k) ℝ)ᴴ) *
        (U : Matrix (Fin k) (Fin k) ℝ) := by
      have : (U : Matrix (Fin k) (Fin k) ℝ)ᴴ *
          ((U : Matrix (Fin k) (Fin k) ℝ) * A * (U : Matrix (Fin k) (Fin k) ℝ)ᴴ) *
          (U : Matrix (Fin k) (Fin k) ℝ) =
          ((U : Matrix (Fin k) (Fin k) ℝ)ᴴ * U) * A *
          ((U : Matrix (Fin k) (Fin k) ℝ)ᴴ * U) := by simp only [← Matrix.mul_assoc]
      rw [this, hUHU, Matrix.one_mul, Matrix.mul_one]
    conv_lhs => rw [key]
    calc ‖(U : Matrix (Fin k) (Fin k) ℝ)ᴴ *
          ((U : Matrix (Fin k) (Fin k) ℝ) * A * (U : Matrix (Fin k) (Fin k) ℝ)ᴴ) *
          (U : Matrix (Fin k) (Fin k) ℝ)‖
        ≤ ‖(U : Matrix (Fin k) (Fin k) ℝ)ᴴ‖ *
          ‖(U : Matrix (Fin k) (Fin k) ℝ) * A * (U : Matrix (Fin k) (Fin k) ℝ)ᴴ‖ *
          ‖(U : Matrix (Fin k) (Fin k) ℝ)‖ :=
            le_trans (Matrix.l2_opNorm_mul _ _)
              (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ = ‖(U : Matrix (Fin k) (Fin k) ℝ) * A * (U : Matrix (Fin k) (Fin k) ℝ)ᴴ‖ := by
            rw [hU1, hUH1]; ring

private lemma iSup_inv_eq_inv_iInf {k : ℕ} [Nonempty (Fin k)] (f : Fin k → ℝ)
    (hf : ∀ i, 0 < f i) : ⨆ i, (f i)⁻¹ = (⨅ i, f i)⁻¹ := by
  have bddB : BddBelow (Set.range f) := (Set.finite_range f).bddBelow
  have bddA : BddAbove (Set.range (fun i => (f i)⁻¹)) := (Set.finite_range _).bddAbove
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_min_image Finset.univ f
    ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  have heq : ⨅ i, f i = f i₀ :=
    le_antisymm (ciInf_le bddB i₀) (le_ciInf (fun i => hi₀ i (Finset.mem_univ _)))
  have hfpos : 0 < ⨅ i, f i := heq ▸ hf i₀
  apply le_antisymm
  · apply ciSup_le; intro i; exact inv_anti₀ hfpos (ciInf_le bddB i)
  · rw [heq]; exact le_ciSup bddA i₀

/-- For an invertible real square matrix M, the L2 operator norm satisfies
  ‖(toEuclideanCLM M)⁻¹‖ = 1 / √(⨅ i, (MᴴM).eigenvalues i) -/
lemma norm_inv_eq_inv_sqrt_min_eigenvalue {k : ℕ} [DecidableEq (Fin k)] [Nonempty (Fin k)]
    (M : Matrix (Fin k) (Fin k) ℝ) [Invertible M] :
    ‖(Matrix.toEuclideanCLM.toFun M⁻¹)‖ =
      1 / Real.sqrt (⨅ (i : Fin k),
        (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i) := by
  -- Reduce to ‖M⁻¹‖ via l2_opNorm_toEuclideanCLM
  have hM : IsUnit M.det := isUnit_det_of_invertible M
  have hCLM : (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹ :
      EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) =
      ContinuousLinearMap.inverse (Matrix.toEuclideanCLM (𝕜 := ℝ) M) := by
    symm; apply ContinuousLinearMap.inverse_eq
    · rw [← ContinuousLinearMap.mul_def, ← map_mul, mul_nonsing_inv M hM, map_one,
          ContinuousLinearMap.one_def]
    · rw [← ContinuousLinearMap.mul_def, ← map_mul, nonsing_inv_mul M hM, map_one,
          ContinuousLinearMap.one_def]
  rw [show Matrix.toEuclideanCLM.toFun M⁻¹ =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹ :
        EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) from rfl,
    Matrix.l2_opNorm_toEuclideanCLM]
  -- Set up hH and positivity of eigenvalues
  set hH := Matrix.isHermitian_conjTranspose_mul_self M
  have hMHM_pd : (Mᴴ * M).PosDef := by
    apply Matrix.PosDef.conjTranspose_mul_self; intro x y h
    have := congr_arg (M⁻¹.mulVec ·) h
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec] at this
    exact this
  have hpos : ∀ i, 0 < hH.eigenvalues i :=
    (Matrix.IsHermitian.posDef_iff_eigenvalues_pos hH).mp hMHM_pd
  -- (MᴴM)⁻¹ = hH.cfc (·⁻¹) via spectral theorem
  have hMHM_inv : (Mᴴ * M)⁻¹ = hH.cfc (·⁻¹) := by
    rw [Matrix.IsHermitian.cfc]; apply Matrix.inv_eq_right_inv
    calc Mᴴ * M * ((Unitary.conjStarAlgAut ℝ (Matrix (Fin k) (Fin k) ℝ) hH.eigenvectorUnitary)
          (Matrix.diagonal (RCLike.ofReal ∘ (·⁻¹) ∘ hH.eigenvalues)))
        = ((Unitary.conjStarAlgAut ℝ (Matrix (Fin k) (Fin k) ℝ) hH.eigenvectorUnitary)
            (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues))) *
          ((Unitary.conjStarAlgAut ℝ (Matrix (Fin k) (Fin k) ℝ) hH.eigenvectorUnitary)
            (Matrix.diagonal (RCLike.ofReal ∘ (·⁻¹) ∘ hH.eigenvalues))) := by
              rw [← hH.spectral_theorem]
      _ = (Unitary.conjStarAlgAut ℝ (Matrix (Fin k) (Fin k) ℝ) hH.eigenvectorUnitary)
            (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
             Matrix.diagonal (RCLike.ofReal ∘ (·⁻¹) ∘ hH.eigenvalues)) := by rw [← map_mul]
      _ = 1 := by
            rw [Matrix.diagonal_mul_diagonal]; simp only [Function.comp]
            have : (fun i => (RCLike.ofReal (hH.eigenvalues i) : ℝ) *
                RCLike.ofReal ((hH.eigenvalues i)⁻¹)) = fun _ => (1 : ℝ) := by
              ext i; rw [← RCLike.ofReal_mul, mul_inv_cancel₀ (ne_of_gt (hpos i)),
                         RCLike.ofReal_one]
            rw [this, Matrix.diagonal_one, map_one]
  -- ‖(MᴴM)⁻¹‖ = 1/(⨅ i, hH.eigenvalues i)
  have hMHM_inv_norm : ‖(Mᴴ * M)⁻¹‖ = 1 / ⨅ i, hH.eigenvalues i := by
    rw [hMHM_inv, Matrix.IsHermitian.cfc, unitary_norm_conj, Matrix.l2_opNorm_diagonal]
    simp only [Pi.norm_def, Finset.sup_univ_eq_ciSup, Function.comp]
    rw [show (⨆ b, ‖(RCLike.ofReal (hH.eigenvalues b)⁻¹ : ℝ)‖₊ : NNReal).toReal =
        ⨆ i, (hH.eigenvalues i)⁻¹ from by
      simp only [NNReal.coe_iSup]
      congr 1; funext i
      rw [show (RCLike.ofReal (hH.eigenvalues i)⁻¹ : ℝ) = (hH.eigenvalues i)⁻¹ from rfl,
          Real.nnnorm_of_nonneg (inv_nonneg.mpr (hpos i).le), NNReal.coe_mk]]
    rw [iSup_inv_eq_inv_iInf _ hpos, one_div]
  -- ‖M⁻¹‖² = ‖(MᴴM)⁻¹‖ via C*-identity
  have hM_inv_sq : ‖M⁻¹‖ ^ 2 = ‖(Mᴴ * M)⁻¹‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose M⁻¹, sq,
        ← Matrix.l2_opNorm_conjTranspose_mul_self (M⁻¹)ᴴ,
        Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv, Matrix.mul_inv_rev]
  -- Combine: ‖M⁻¹‖ = 1/√(⨅ i, hH.eigenvalues i)
  have hpos_iInf : 0 < ⨅ i, hH.eigenvalues i := by
    obtain ⟨i₀, _, hi₀⟩ := Finset.exists_min_image Finset.univ hH.eigenvalues
      ⟨Classical.arbitrary _, Finset.mem_univ _⟩
    rw [le_antisymm (ciInf_le (Set.finite_range _).bddBelow i₀)
        (le_ciInf (fun i => hi₀ i (Finset.mem_univ _)))]
    exact hpos i₀
  rw [one_div, ← Real.sqrt_inv, ← Real.sqrt_sq (norm_nonneg _), hM_inv_sq, hMHM_inv_norm,
      one_div, Real.sqrt_inv]
