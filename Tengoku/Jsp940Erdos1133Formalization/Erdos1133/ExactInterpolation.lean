import Tengoku.Jsp940Erdos1133Formalization.Erdos1152.V5.NormalizeTrig
import Tengoku.Seed.Analysis.SpecificLimits.Normed
import Tengoku.Seed.Analysis.Normed.Group.InfiniteSum
import Tengoku.Seed.Topology.Algebra.Module.FiniteDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Uniform approximate interpolation implies exact interpolation, by a
convergent residual-correction series inside a closed Fourier band. -/

noncomputable section
open scoped BigOperators Topology Real
open Set Finset Filter
open Erdos1152.V5

namespace Erdos1133

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- A quantitative residual-correction theorem. The approximate preimages may
be chosen nonlinearly; no linear right inverse is assumed or constructed.
@isnad1 id=ex.5h7v.s9.c3416a9dc2e7 from=translated src=- shape=8040fed0 vocab=77c80b54
-/
theorem exists_exact_preimage_of_approx
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (happrox : ∀ y : F, ∃ x ∈ S,
      ‖x‖ ≤ K * ‖y‖ ∧ ‖y - T x‖ ≤ q * ‖y‖)
    (y : F) :
    ∃ x ∈ S, T x = y ∧ ‖x‖ ≤ K / (1 - q) * ‖y‖ := by
  classical
  choose A hAS hAnorm hAerr using happrox
  let r : ℕ → F := Nat.rec y (fun _ v => v - T (A v))
  let u : ℕ → E := fun n => A (r n)
  have hrzero : r 0 = y := rfl
  have hrsucc (n : ℕ) : r (n + 1) = r n - T (u n) := rfl
  have hrnorm (n : ℕ) : ‖r n‖ ≤ q ^ n * ‖y‖ := by
    induction n with
    | zero => simp [hrzero]
    | succ n ih =>
      calc
        ‖r (n + 1)‖ ≤ q * ‖r n‖ := hAerr (r n)
        _ ≤ q * (q ^ n * ‖y‖) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (n + 1) * ‖y‖ := by rw [pow_succ]; ring
  have hunorm (n : ℕ) : ‖u n‖ ≤ (K * ‖y‖) * q ^ n := by
    exact (hAnorm (r n)).trans (by
      calc
        K * ‖r n‖ ≤ K * (q ^ n * ‖y‖) := mul_le_mul_of_nonneg_left (hrnorm n) hK
        _ = (K * ‖y‖) * q ^ n := by ring)
  have hgeo : Summable (fun n : ℕ => (K * ‖y‖) * q ^ n) :=
    (hasSum_geometric_of_lt_one hq hq1).summable.mul_left _
  have hunormsum : Summable (fun n => ‖u n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hunorm hgeo
  have husum : Summable u := hunormsum.of_norm
  have hmem : (∑' n, u n) ∈ S :=
    hS.mem_of_tendsto husum.hasSum.tendsto_sum_nat
      (Eventually.of_forall fun n => S.sum_mem fun i hi => hAS (r i))
  have hpartial (n : ℕ) : T (∑ i ∈ Finset.range n, u i) = y - r n := by
    induction n with
    | zero => simp [hrzero]
    | succ n ih =>
      rw [Finset.sum_range_succ, map_add, ih, hrsucc]
      abel
  have hrlim : Tendsto r atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => hrnorm n)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const ‖y‖
  have hTlim : Tendsto (fun n => T (∑ i ∈ Finset.range n, u i)) atTop
      (𝓝 (T (∑' n, u n))) := T.continuous.tendsto _ |>.comp husum.hasSum.tendsto_sum_nat
  have hylim : Tendsto (fun n => T (∑ i ∈ Finset.range n, u i)) atTop (𝓝 y) := by
    simpa only [hpartial, sub_zero] using tendsto_const_nhds.sub hrlim
  refine ⟨∑' n, u n, hmem, tendsto_nhds_unique hTlim hylim, ?_⟩
  calc
    ‖∑' n, u n‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm hunormsum
    _ ≤ ∑' n : ℕ, (K * ‖y‖) * q ^ n := Summable.tsum_le_tsum hunorm hunormsum hgeo
    _ = K / (1 - q) * ‖y‖ := by
      rw [tsum_mul_left, (hasSum_geometric_of_lt_one hq hq1).tsum_eq]
      ring

/-- Unit-data approximate solvability already suffices; all other residuals
are reduced to it by scalar normalization.
@isnad1 id=ex.5h7v.s9.eb504f847b90 from=translated src=- shape=1d56a051 vocab=77c80b54
-/
theorem exists_exact_preimage_of_unit_approx
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (happrox : ∀ y : F, ‖y‖ ≤ 1 → ∃ x ∈ S,
      ‖x‖ ≤ K ∧ ‖y - T x‖ ≤ q)
    (y : F) :
    ∃ x ∈ S, T x = y ∧ ‖x‖ ≤ K / (1 - q) * ‖y‖ := by
  apply exists_exact_preimage_of_approx T S hS K q hK hq hq1 ?_ y
  intro z
  by_cases hz : z = 0
  · exact ⟨0, S.zero_mem, by simp [hz], by simp [hz]⟩
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  obtain ⟨x, hx, hxn, hxe⟩ := happrox (‖z‖⁻¹ • z) (by
    simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn, le_refl])
  refine ⟨‖z‖ • x, S.smul_mem _ hx, ?_, ?_⟩
  · rw [norm_smul, norm_norm]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hxn (norm_nonneg z)
  · have he : z - T (‖z‖ • x) = ‖z‖ • (‖z‖⁻¹ • z - T x) := by
      rw [map_smul, smul_sub, smul_smul, mul_inv_cancel₀ hn, one_smul]
    rw [he, norm_smul, norm_norm]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hxe (norm_nonneg z)

/-- The actual real-valued part of the finite complex Fourier band.-/
def realFourierBand (m : ℕ) : Submodule ℝ CircleFunction where
  carrier := {f | f ∈ bandSpace m ∧ ∀ x, (f x).im = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact ⟨(bandSpace m).add_mem hf.1 hg.1, by intro x; simp [hf.2, hg.2]⟩
  smul_mem' := by
    intro c f hf
    refine ⟨((bandSpace m).restrictScalars ℝ).smul_mem c hf.1, ?_⟩
    intro x
    change ((c : ℂ) * f x).im = 0
    simp [hf.2]

/--
@isnad1 id=iff.0h2v.s9.7954dacd66c9 from=translated src=- shape=d1499a0e vocab=b1d8e579
-/
@[simp] theorem mem_realFourierBand (m : ℕ) (f : CircleFunction) :
    f ∈ realFourierBand m ↔ f ∈ bandSpace m ∧ ∀ x, (f x).im = 0 := Iff.rfl

/-- Closure is proved from the finite spanning family of characters, rather
than postulated as part of the interpolation hypothesis.
@isnad1 id=isclosed.0h1v.s8.d60d47cc02be from=translated src=- shape=9e325049 vocab=42f9abaa
-/
theorem realFourierBand_isClosed (m : ℕ) : IsClosed (realFourierBand m : Set CircleFunction) := by
  have : FiniteDimensional ℂ (bandSpace m) :=
    FiniteDimensional.span_of_finite ℂ
      ((Set.finite_Icc (-(m : ℤ)) m).image character)
  have hband := (bandSpace m).closed_of_finiteDimensional
  have hreal : IsClosed {f : CircleFunction | ∀ x, (f x).im = 0} := by
    have h : IsClosed (⋂ x : FourierCircle, {f : CircleFunction | (f x).im = 0}) :=
      isClosed_iInter (fun x : FourierCircle =>
      isClosed_eq (show Continuous (fun f : CircleFunction => (f x).im) by fun_prop)
        continuous_const)
    simpa only [Set.ofPred_forall] using h
  exact hband.inter hreal

/-- The true finite-dimensional real sample vector of a continuous function.-/
def circleSampleMap {ι : Type*} [Fintype ι] (node : ι → FourierCircle) :
    CircleFunction →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i => Complex.reCLM.comp (ContinuousMap.evalCLM ℝ (node i))

/--
@isnad1 id=eq.0h4v.s9.676fd0512c25 from=translated src=- shape=f8f07d01 vocab=3c8b1a24
-/
@[simp] theorem circleSampleMap_apply {ι : Type*} [Fintype ι]
    (node : ι → FourierCircle) (f : CircleFunction) (i : ι) :
    circleSampleMap node f i = (f (node i)).re := rfl

/-- Relative-error approximate real trigonometric interpolation yields exact
interpolation of every data vector with the geometric-series norm bound.
@isnad1 id=ex.4h6v.s10.d7bde050f24d from=translated src=- shape=fd0c00f2 vocab=30736bd5
-/
theorem exact_real_trig_interpolation_of_approx
    {ι : Type*} [Fintype ι] (node : ι → FourierCircle) (m : ℕ)
    (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (happrox : ∀ d : ι → ℝ, ∃ f : CircleFunction,
      f ∈ bandSpace m ∧ (∀ x, (f x).im = 0) ∧
      ‖f‖ ≤ K * ‖d‖ ∧ ∀ i, |(f (node i)).re - d i| ≤ q * ‖d‖)
    (d : ι → ℝ) :
    ∃ f : CircleFunction, f ∈ bandSpace m ∧ (∀ x, (f x).im = 0) ∧
      (∀ i, f (node i) = (d i : ℂ)) ∧ ‖f‖ ≤ K / (1 - q) * ‖d‖ := by
  have ha : ∀ y : ι → ℝ, ∃ f ∈ realFourierBand m,
      ‖f‖ ≤ K * ‖y‖ ∧ ‖y - circleSampleMap node f‖ ≤ q * ‖y‖ := by
    intro y
    obtain ⟨f, hfb, hfr, hfn, hfe⟩ := happrox y
    refine ⟨f, ⟨hfb, hfr⟩, hfn, ?_⟩
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hq (norm_nonneg y))).mpr
    intro i
    simpa only [Pi.sub_apply, circleSampleMap_apply, Real.norm_eq_abs, abs_sub_comm]
      using hfe i
  obtain ⟨f, hf, he, hn⟩ := exists_exact_preimage_of_approx
    (circleSampleMap node) (realFourierBand m) (realFourierBand_isClosed m)
    K q hK hq hq1 ha d
  refine ⟨f, hf.1, hf.2, ?_, hn⟩
  intro i
  apply Complex.ext
  · exact congrFun he i
  · exact hf.2 (node i)

/-- The unit-data form needed after windowing and periodization. Its conclusion
applies to all data vectors, so it also supplies every residual correction.
@isnad1 id=ex.4h6v.s10.a8bd9002ad8c from=translated src=- shape=da8a6254 vocab=30736bd5
-/
theorem exact_real_trig_interpolation_of_unit_approx
    {ι : Type*} [Fintype ι] (node : ι → FourierCircle) (m : ℕ)
    (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (happrox : ∀ d : ι → ℝ, ‖d‖ ≤ 1 → ∃ f : CircleFunction,
      f ∈ bandSpace m ∧ (∀ x, (f x).im = 0) ∧
      ‖f‖ ≤ K ∧ ∀ i, |(f (node i)).re - d i| ≤ q)
    (d : ι → ℝ) :
    ∃ f : CircleFunction, f ∈ bandSpace m ∧ (∀ x, (f x).im = 0) ∧
      (∀ i, f (node i) = (d i : ℂ)) ∧ ‖f‖ ≤ K / (1 - q) * ‖d‖ := by
  have ha : ∀ y : ι → ℝ, ‖y‖ ≤ 1 → ∃ f ∈ realFourierBand m,
      ‖f‖ ≤ K ∧ ‖y - circleSampleMap node f‖ ≤ q := by
    intro y hy
    obtain ⟨f, hfb, hfr, hfn, hfe⟩ := happrox y hy
    refine ⟨f, ⟨hfb, hfr⟩, hfn, ?_⟩
    apply (pi_norm_le_iff_of_nonneg hq).mpr
    intro i
    simpa only [Pi.sub_apply, circleSampleMap_apply, Real.norm_eq_abs, abs_sub_comm]
      using hfe i
  obtain ⟨f, hf, he, hn⟩ := exists_exact_preimage_of_unit_approx
    (circleSampleMap node) (realFourierBand m) (realFourierBand_isClosed m)
    K q hK hq hq1 ha d
  refine ⟨f, hf.1, hf.2, ?_, hn⟩
  intro i
  apply Complex.ext
  · exact congrFun he i
  · exact hf.2 (node i)

/-- In particular, unit data admit an exact interpolant of norm at most
K/(1-q), the form used to contradict the finite obstruction.
@isnad1 id=ex.5h6v.s10.eb584d0684d3 from=translated src=- shape=cd3624f2 vocab=30736bd5
-/
theorem exact_unit_real_trig_interpolation
    {ι : Type*} [Fintype ι] (node : ι → FourierCircle) (m : ℕ)
    (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (happrox : ∀ d : ι → ℝ, ‖d‖ ≤ 1 → ∃ f : CircleFunction,
      f ∈ bandSpace m ∧ (∀ x, (f x).im = 0) ∧
      ‖f‖ ≤ K ∧ ∀ i, |(f (node i)).re - d i| ≤ q)
    (d : ι → ℝ) (hd : ‖d‖ ≤ 1) :
    ∃ f : CircleFunction, f ∈ bandSpace m ∧ (∀ x, (f x).im = 0) ∧
      (∀ i, f (node i) = (d i : ℂ)) ∧ ‖f‖ ≤ K / (1 - q) := by
  obtain ⟨f, hfb, hfr, hfe, hfn⟩ := exact_real_trig_interpolation_of_unit_approx
    node m K q hK hq hq1 happrox d
  refine ⟨f, hfb, hfr, hfe, hfn.trans ?_⟩
  have hconst : 0 ≤ K / (1 - q) := div_nonneg hK (sub_pos.mpr hq1).le
  simpa using mul_le_mul_of_nonneg_left hd hconst

end Erdos1133
