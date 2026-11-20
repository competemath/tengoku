import Tengoku.Hellingerrepolean4.Hellinger.ProductStateProperties
import Tengoku.Hellingerrepolean4.Hellinger.Complexification
import Tengoku.Hellingerrepolean4.Hellinger.ComplexEigenvalueOrder
import Tengoku.Hellingerrepolean4.Hellinger.PosteriorGram
import Tengoku.Hellingerrepolean4.Hellinger.CutNorm
import Tengoku.Hellingerrepolean4.Hellinger.PaperSpecs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Manuscript-facing spectral contracts. Each theorem repeats the full
mathematical assertion at its concrete objects; the proofs supply every
intermediate ensemble, spectrum, and matrix-norm fact. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace Hellinger.SpectralContracts
open ProductState ParityBlocks

/--
@isnad1 id=le.2h3v.s10.2a12c0c97b21 from=translated src=- shape=7b27398a vocab=62180899
-/
theorem square_root_lifting (n : ℕ) (f : Cube n → ℝ) (hf : PaperSpecs.IsBoolean f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    ComplexSpectral.traceNorm
      (Complexification.complexify (state n (root ρ)) -
        Complexification.complexify (Matrix.diagonal f) *
        Complexification.complexify (state n (root ρ)) *
        Complexification.complexify (Matrix.diagonal f)) / 2 ≤
      PaperSpecs.posteriorRootMean f ρ hρ := by
  rw [Complexification.traceNorm_reflection_difference]
  exact PosteriorState.bsc_lifting n f hf ρ hρ

/--
@isnad1 id=and.0h2v.s8.041af956750c from=translated src=- shape=5f203971 vocab=f214e350
-/
theorem product_state_formula (n : ℕ) (c : ℝ) :
    state n c = ((2 : ℝ) ^ n)⁻¹ • (List.ofFn (fun i : Fin n =>
      1 + c • SpinState.spin n i)).prod ∧
    (∀ x z, state n c x z = c ^ hammingDistance n x z / (2 : ℝ) ^ n) := by
  exact ⟨SpinState.state_ordered_product n c, state_entry n c⟩

/--
@isnad1 id=and.4h3v.s13.09866809fd2e from=translated src=- shape=ea49a0c1 vocab=f09f8d7e
-/
theorem anticommuting_witnesses (d : ℕ) (K F : Matrix (Fin d) (Fin d) ℂ)
    (hK : K.PosSemidef) (_htrace : K.trace = 1)
    (hF : F.IsHermitian) (hF2 : F * F = 1) :
    IsGreatest {t : ℝ | ∃ Q : Matrix (Fin d) (Fin d) ℂ,
      Q.IsHermitian ∧ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) Q‖ ≤ 1 ∧
      F * Q * F = -Q ∧ t = (K * Q).trace.re}
      (ComplexSpectral.traceNorm (K - F * K * F) / 2) ∧
    (∀ Q : Matrix (Fin d) (Fin d) ℂ, Q.IsHermitian →
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) Q‖ ≤ 1 → F * Q * F = -Q →
      ∀ ψ : Fin d → ℂ, ‖WithLp.toLp 2 ψ‖ = 1 →
        (star ψ ⬝ᵥ F *ᵥ ψ).re ^ 2 + (star ψ ⬝ᵥ Q *ᵥ ψ).re ^ 2 ≤ 1) := by
  exact ⟨ComplexSpectral.anticommuting_trace_maximum hK.isHermitian hF hF2,
    fun Q hQ hnorm ha ψ hψ =>
      ComplexSpectral.anticommuting_uncertainty hF hF2 hQ hnorm ha ψ hψ⟩

def evenRestriction (n : ℕ) (c : ℝ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ :=
  (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary (n + 1)) (state (n + 1) c)).submatrix
    (fun i => (evenEquiv n i).val) (fun i => (evenEquiv n i).val)

def oddRestriction (n : ℕ) (c : ℝ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ :=
  (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary (n + 1)) (state (n + 1) c)).submatrix
    (fun i => (oddEquiv n i).val) (fun i => (oddEquiv n i).val)

/--
@isnad1 id=eq.0h2v.s6.942414b48b09 from=translated src=- shape=68df6c85 vocab=7a0acecc
-/
theorem evenRestriction_diagonal (n : ℕ) (c : ℝ) :
    evenRestriction n c = Matrix.diagonal (evenEigenvalue n c) := by
  ext i j
  have h := congrArg (fun M : Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n))
      (Fin (2 ^ n) ⊕ Fin (2 ^ n)) ℝ => M (Sum.inl i) (Sum.inl j))
    (state_diagonal_blocks n c)
  simpa only [evenRestriction, transformed_state, Matrix.submatrix_apply,
    blockEquiv_inl, Matrix.fromBlocks_apply₁₁] using h

/--
@isnad1 id=eq.0h2v.s6.ba5eb5317f7f from=translated src=- shape=68df6c85 vocab=e059b963
-/
theorem oddRestriction_diagonal (n : ℕ) (c : ℝ) :
    oddRestriction n c = Matrix.diagonal (oddEigenvalue n c) := by
  ext i j
  have h := congrArg (fun M : Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n))
      (Fin (2 ^ n) ⊕ Fin (2 ^ n)) ℝ => M (Sum.inr i) (Sum.inr j))
    (state_diagonal_blocks n c)
  simpa only [oddRestriction, transformed_state, Matrix.submatrix_apply,
    blockEquiv_inr, Matrix.fromBlocks_apply₂₂] using h

/-- The decreasing eigenvalues of the actual two parity restrictions.
@isnad1 id=ex.1h2v.s9.b84354832e8d from=translated src=- shape=507775d6 vocab=fbee3ada
-/
theorem exact_parity_spectrum_distance (n : ℕ) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    ∃ hA : (evenRestriction n c).IsHermitian,
    ∃ hB : (oddRestriction n c).IsHermitian,
      (∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j|) = c := by
  rw [evenRestriction_diagonal, oddRestriction_diagonal]
  refine ⟨Matrix.isHermitian_diagonal _, Matrix.isHermitian_diagonal _, ?_⟩
  rw [TraceNorm.eigenvalues₀_diagonal_of_antitone _ (evenEigenvalue_antitone n c hc),
    TraceNorm.eigenvalues₀_diagonal_of_antitone _ (oddEigenvalue_antitone n c hc)]
  calc
    _ = ∑ j : Fin (2 ^ n), |evenEigenvalue n c j - oddEigenvalue n c j| :=
      (finCongr (Fintype.card_fin (2 ^ n))).sum_comp _
    _ = c := actual_parity_spectra_l1 n c hc

/--
@isnad1 id=eq.6h5v.s8.f5dbc0379965 from=translated src=- shape=6ea9477d vocab=1abb6829
-/
theorem trace_equality (n : ℕ) (f : Cube n → ℝ) (hf : PaperSpecs.IsBoolean f)
    (hnonconstant : ∃ x z, f x ≠ f z) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (_hρpos : 0 < ρ) (hρlt : ρ < 1)
    (heq : PaperSpecs.posteriorRootMean f ρ hρ =
      TraceNorm.traceNorm (state n (root ρ) -
        Matrix.diagonal f * state n (root ρ) * Matrix.diagonal f) / 2) :
    ∀ y z, |(cubeBSC n ρ hρ).apply f y| = |(cubeBSC n ρ hρ).apply f z| := by
  exact PosteriorGram.bsc_posterior_abs_constant_of_lifting_equality
    f hf hnonconstant ρ hρ hρlt heq.symm

/--
@isnad1 id=le.2h3v.s7.1773b85d869e from=translated src=- shape=ce1506b6 vocab=67c7b5fa
-/
theorem ordered_matrix_comparison (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j|) ≤
      ComplexSpectral.traceNorm (A - B) :=
  ComplexSpectral.ordered_eigenvalue_distance_le_traceNorm hA hB

/--
@isnad1 id=ex.1h2v.s7.bc1f910a77f1 from=translated src=- shape=032832fa vocab=441bb28f
-/
theorem gibbs_representation (n : ℕ) (c : ℝ) (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ β : ℝ, 0 < β ∧ c = Real.tanh β ∧
      state n c = ((2 * Real.cosh β) ^ n)⁻¹ •
        NormedSpace.exp (β • ∑ i : Fin n, SpinState.spin n i) :=
  SpinState.exists_positive_gibbs_parameter n c hc

/--
@isnad1 id=ex.1h1v.s11.b151a53778e4 from=translated src=- shape=c871ac90 vocab=a79c29b2
-/
theorem three_qubit_counterexample (c : ℝ) (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ P : Matrix (Cube 3) (Cube 3) ℂ,
      P.IsHermitian ∧ P * P = 1 ∧
      (∀ s, (Complexification.complexify (hadamard 3) * P *
        Complexification.complexify (hadamard 3)) s s = 0) ∧
      ComplexSpectral.traceNorm (Complexification.complexify (state 3 c) -
        P * Complexification.complexify (state 3 c) * P) / 2 = c * (1 + c ^ 2) / 2 ∧
      c * (1 + c ^ 2) / 2 < c ∧
      (∀ f : Cube 3 → ℝ, P ≠ Complexification.complexify (Matrix.diagonal f)) := by
  obtain ⟨P, hP, hP2, hdiag, hnorm, hlt, hnot⟩ :=
    ReflectionCounterexample.reflection_counterexample c hc
  refine ⟨Complexification.complexify P, Complexification.complexify_isHermitian hP,
    ?_, ?_, ?_, hlt, ?_⟩
  · rw [← map_mul, hP2, map_one]
  · intro s
    rw [← map_mul, ← map_mul]
    have h := hdiag s
    simp only [Unitary.conjStarAlgAut_apply, hadamardUnitary_coe,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      hadamard_transpose] at h
    simp only [Complexification.complexify_apply, h, Complex.ofReal_zero]
  · rw [Complexification.traceNorm_reflection_difference, hnorm]
  · intro f h
    apply hnot f
    ext x z
    have he := congrArg (fun M : Matrix (Cube 3) (Cube 3) ℂ => M x z) h
    exact Complex.ofReal_injective he

end Hellinger.SpectralContracts
