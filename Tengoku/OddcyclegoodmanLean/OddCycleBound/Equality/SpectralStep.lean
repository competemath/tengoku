import Tengoku.OddcyclegoodmanLean.OddCycleBound.Equality.RegularKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The spectral step of Proposition 6.2, without eigenvalues

Let `U` be an a.e. `q`-regular graphon with `q > 0` and `t(C_m, U) = q^{m-1}` for an odd `m ≥ 3`.
Writing `T n = trace (compPow U n) = t(C_{n+1}, U)`, the Hilbert–Schmidt pairings of kernel
powers are `⟨U^{a+1}, U^{b+1}⟩ = T (a + b + 1)`. The operator bound gives
`T (2j+3) ≤ q² T (2j+1)`, Cauchy–Schwarz gives `T(2a)² ≤ T(2a-1) T(2a+1)`, and `T 1 = ∫∫ U² ≤ q`.
With `m = 2a + 1` this is the chain `q^{m-1} = t(C_m, U) ≤ q^{m-2} ∫∫ U² ≤ q^{m-1}` of the paper.
Its equality cases give `∫∫ U² = ∫∫ U`, hence `U ∈ {0,1}` a.e., and
`‖U ∘ U - q U‖²_HS = 0`, which is `T_U² = q T_U` at the level of kernels.
-/

open MeasureTheory

namespace OddCycleBound.Equality

/-! ### A numerical lemma -/

section Numerical

variable {q : ℝ} (T : ℕ → ℝ)

end Numerical

/-! ### The kernel-level statement -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

lemma edgeDensity_of_regular {q : ℝ}
    (hdeg : ∀ᵐ x ∂μ, degree U μ x = q) : edgeDensity U μ = q := by
  rw [edgeDensity, mean, integral_congr_ae hdeg]
  simp

lemma integral_prod_eq_edgeDensity (hU : IsGraphon U μ) :
    ∫ p, U p.1 p.2 ∂(μ.prod μ) = edgeDensity U μ := by
  have hint : Integrable (fun p : Ω × Ω => U p.1 p.2) (μ.prod μ) :=
    (goodK_of_isGraphon hU).integrable_prod
  rw [integral_prod _ hint]
  rfl

lemma hsInner_self_le_edgeDensity (hU : IsGraphon U μ) :
    hsInner μ U U ≤ edgeDensity U μ := by
  have hGU := goodK_of_isGraphon hU
  rw [← integral_prod_eq_edgeDensity hU]
  refine integral_mono (hGU.integrable_mul hGU) hGU.integrable_prod fun p => ?_
  have h0 := hU.nonneg p.1 p.2
  have h1 := hU.le_one p.1 p.2
  show U p.1 p.2 * U p.1 p.2 ≤ U p.1 p.2
  nlinarith

lemma zero_or_one_of_hsInner_self_eq (hU : IsGraphon U μ)
    (h : hsInner μ U U = edgeDensity U μ) :
    ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = 0 ∨ U p.1 p.2 = 1 := by
  have hGU := goodK_of_isGraphon hU
  rw [← integral_prod_eq_edgeDensity hU, hsInner] at h
  have hI1 : Integrable (fun p : Ω × Ω => U p.1 p.2) (μ.prod μ) := hGU.integrable_prod
  have hI2 : Integrable (fun p : Ω × Ω => U p.1 p.2 * U p.1 p.2) (μ.prod μ) :=
    hGU.integrable_mul hGU
  have hI : Integrable (fun p : Ω × Ω => U p.1 p.2 - U p.1 p.2 * U p.1 p.2) (μ.prod μ) :=
    hI1.sub hI2
  have hdiff : ∫ p, (U p.1 p.2 - U p.1 p.2 * U p.1 p.2) ∂(μ.prod μ) = 0 := by
    rw [integral_sub hI1 hI2]
    linarith
  rw [integral_eq_zero_iff_of_nonneg (fun p => by
      have h0 := hU.nonneg p.1 p.2
      have h1 := hU.le_one p.1 p.2
      show 0 ≤ U p.1 p.2 - U p.1 p.2 * U p.1 p.2
      nlinarith) hI] at hdiff
  filter_upwards [hdiff] with p hp
  have hp' : U p.1 p.2 * (1 - U p.1 p.2) = 0 := by
    have : U p.1 p.2 - U p.1 p.2 * U p.1 p.2 = 0 := hp
    linarith
  rcases mul_eq_zero.mp hp' with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

end OddCycleBound.Equality
