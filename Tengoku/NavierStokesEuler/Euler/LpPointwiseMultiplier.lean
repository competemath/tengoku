import Tengoku.NavierStokesEuler.Euler.LpDominatedConvergence

/-! Bounded pointwise operator fields act on actual L² classes. Joint
continuity of the coefficients, with a uniform bound, gives strong
continuity even when uniform convergence of coefficients is unavailable. -/

noncomputable section

namespace EulerLpPointwiseMultiplier

open MeasureTheory Filter
open scoped Topology

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure X) (A : X → E →L[ℝ] F)
  (hA : AEStronglyMeasurable A μ) (C : ℝ) (hC : ∀ x, ‖A x‖ ≤ C)

include hA hC in
/--
@isnad1 id=memlp.2h7v.s9.182a5405688d from=translated src=- shape=01bd7da9 vocab=2e612354
-/
theorem apply_memLp (u : Lp E 2 μ) : MemLp (fun x => A x (u x)) 2 μ := by
  apply (Lp.memLp u).of_le_mul (c := C)
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk (Lp.aestronglyMeasurable u))
  · exact Eventually.of_forall (fun x => ((A x).le_opNorm (u x)).trans
      (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg (u x))))

def applyLp (u : Lp E 2 μ) : Lp F 2 μ :=
  (apply_memLp μ A hA C hC u).toLp (fun x => A x (u x))

/--
@isnad1 id=eventual.2h7v.s10.778720fab2b7 from=translated src=- shape=caf2e850 vocab=f1c85f08
-/
theorem applyLp_ae (u : Lp E 2 μ) :
    (applyLp μ A hA C hC u : X → F) =ᵐ[μ] fun x => A x (u x) :=
  (apply_memLp μ A hA C hC u).coeFn_toLp

/--
@isnad1 id=le.2h7v.s9.7318cb32d36c from=translated src=- shape=f6be9cef vocab=a6721527
-/
theorem applyLp_norm_le (u : Lp E 2 μ) :
    ‖applyLp μ A hA C hC u‖ ≤ C*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [applyLp_ae μ A hA C hC u] with x hx
  rw [hx]
  exact ((A x).le_opNorm (u x)).trans
    (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg (u x)))

def linear : Lp E 2 μ →ₗ[ℝ] Lp F 2 μ where
  toFun := applyLp μ A hA C hC
  map_add' u v := by
    apply Lp.ext
    filter_upwards [applyLp_ae μ A hA C hC (u+v), applyLp_ae μ A hA C hC u,
      applyLp_ae μ A hA C hC v, Lp.coeFn_add u v,
      Lp.coeFn_add (applyLp μ A hA C hC u) (applyLp μ A hA C hC v)]
      with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h4 h5
    rw [h1,h5,h4,h2,h3,map_add]
  map_smul' r u := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [applyLp_ae μ A hA C hC (r • u), applyLp_ae μ A hA C hC u,
      Lp.coeFn_smul r u,Lp.coeFn_smul r (applyLp μ A hA C hC u)] with x h1 h2 h3 h4
    simp only [Pi.smul_apply] at h3 h4
    rw [h1,h4,h3,h2,map_smul]

def operator : Lp E 2 μ →L[ℝ] Lp F 2 μ :=
  (linear μ A hA C hC).mkContinuous C (applyLp_norm_le μ A hA C hC)

/--
@isnad1 id=eventual.2h7v.s12.a3183c85172e from=translated src=- shape=de55c07e vocab=01977dfe
-/
theorem operator_ae (u : Lp E 2 μ) :
    (operator μ A hA C hC u : X → F) =ᵐ[μ] fun x => A x (u x) :=
  applyLp_ae μ A hA C hC u

/--
@isnad1 id=le.2h7v.s12.a8e5dea36572 from=translated src=- shape=4e004d52 vocab=0561461b
-/
theorem operator_bound (u : Lp E 2 μ) : ‖operator μ A hA C hC u‖ ≤ C*‖u‖ :=
  applyLp_norm_le μ A hA C hC u

variable {K : Type*} [TopologicalSpace K] [FirstCountableTopology K]
  (B : K → X → E →L[ℝ] F) (hB : ∀ t, AEStronglyMeasurable (B t) μ)
  (hBt : ∀ x, Continuous (fun t => B t x)) (hBC : ∀ t x, ‖B t x‖ ≤ C)

include hBt in
/--
@isnad1 id=continuo.3h8v.s12.496725d3a7cd from=translated src=- shape=200cdb4d vocab=eb4fd54e
-/
theorem operator_strongly_continuous (u : Lp E 2 μ) :
    Continuous (fun t => operator μ (B t) (hB t) C (hBC t) u) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply EulerLpConvergence.tendsto_of_dominated μ
    (fun t => operator μ (B t) (hB t) C (hBC t) u)
    (operator μ (B t₀) (hB t₀) C (hBC t₀) u)
    (fun t x => B t x (u x)) (fun x => B t₀ x (u x))
    (fun t => operator_ae μ (B t) (hB t) C (hBC t) u)
    (operator_ae μ (B t₀) (hB t₀) C (hBC t₀) u)
    (fun x => (2*C)*‖u x‖) ((Lp.memLp u).norm.const_mul (2*C))
  · apply Eventually.of_forall
    intro t
    apply Eventually.of_forall
    intro x
    calc
      _ ≤ ‖B t x (u x)‖ + ‖B t₀ x (u x)‖ := norm_sub_le _ _
      _ ≤ C*‖u x‖ + C*‖u x‖ := add_le_add
        (((B t x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hBC t x) (norm_nonneg _)))
        (((B t₀ x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hBC t₀ x) (norm_nonneg _)))
      _ = _ := by ring
  · exact Eventually.of_forall (fun x => ((hBt x).clm_apply continuous_const).tendsto t₀)

include hBt in
/--
@isnad1 id=continuo.4h8v.s12.06faddf3213e from=translated src=- shape=a0ea9db9 vocab=eb4fd54e
-/
theorem operator_path_continuous (u : K → Lp E 2 μ) (hu : Continuous u) :
    Continuous (fun t => operator μ (B t) (hB t) C (hBC t) (u t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h₁ : Tendsto (fun t => C*‖u t-u t₀‖) (𝓝 t₀) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,norm_zero,mul_zero] using ((hu.tendsto t₀).sub_const (u t₀)).norm.const_mul C
  have h₂ : Tendsto (fun t => ‖operator μ (B t) (hB t) C (hBC t) (u t₀) -
      operator μ (B t₀) (hB t₀) C (hBC t₀) (u t₀)‖) (𝓝 t₀) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,norm_zero] using
      (((operator_strongly_continuous μ C B hB hBt hBC (u t₀)).tendsto t₀).sub_const
        (operator μ (B t₀) (hB t₀) C (hBC t₀) (u t₀))).norm
  apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa only [add_zero] using h₁.add h₂)
  intro t
  calc
    _ ≤ ‖operator μ (B t) (hB t) C (hBC t) (u t) -
        operator μ (B t) (hB t) C (hBC t) (u t₀)‖ +
      ‖operator μ (B t) (hB t) C (hBC t) (u t₀) -
        operator μ (B t₀) (hB t₀) C (hBC t₀) (u t₀)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C*‖u t-u t₀‖ +
      ‖operator μ (B t) (hB t) C (hBC t) (u t₀) -
        operator μ (B t₀) (hB t₀) C (hBC t₀) (u t₀)‖ := add_le_add (by
      rw [← map_sub]
      exact operator_bound μ (B t) (hB t) C (hBC t) (u t-u t₀)) le_rfl

end EulerLpPointwiseMultiplier
