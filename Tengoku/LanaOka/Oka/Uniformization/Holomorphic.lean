/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Analysis.Analytic.IsolatedZeros
import Tengoku.Seed.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Tengoku.Seed.Analysis.Complex.AbsMax
import Tengoku.Seed.Analysis.Complex.LocallyUniformLimit
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.LogDeriv
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Analytic
import Tengoku.Seed.RingTheory.RootsOfUnity.Complex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Three facts about holomorphic functions of one variable

* `Uniformization.deriv_ne_zero_of_injOn`: a holomorphic function which is injective on a
  neighbourhood of `z` has nonzero derivative at `z`. Near a critical point `f` is
  `f z + φ ^ n` with `n ≥ 2` and `φ` a local coordinate, and `φ` takes both values `ε` and `ε ζ`
  for a primitive `n`-th root of unity `ζ`.
* `Uniformization.differentiableAt_of_comp_eq`: a continuous lift `σ` of a holomorphic map `g`
  through a holomorphic `f` with `f′ ≠ 0` (that is, `f ∘ σ = g`) is holomorphic.
* `Uniformization.eventually_eq_of_tendstoLocallyUniformlyOn` (**Hurwitz**): if holomorphic `Fₙ`
  omit the value `β` near `z` and converge locally uniformly to `f` with `f z = β`, then `f = β`
  near `z`.
-/

open Filter Metric Set Topology

namespace Uniformization

/-- A function holomorphic on a neighbourhood of `z` is analytic at `z`. -/
theorem analyticAt_of_differentiableOn {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ} (hf : DifferentiableOn ℂ f U)
    (hU : U ∈ 𝓝 z) : AnalyticAt ℂ f z := by
  obtain ⟨V, hVU, hV, hzV⟩ := _root_.mem_nhds_iff.mp hU
  exact (hf.mono hVU).analyticAt (hV.mem_nhds hzV)

/-- A holomorphic function which is injective on a neighbourhood of `z` has nonzero derivative at
`z`. -/
theorem deriv_ne_zero_of_injOn {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ} (hf : DifferentiableOn ℂ f U)
    (hU : U ∈ 𝓝 z) (hinj : InjOn f U) : deriv f z ≠ 0 := by
  intro hd
  have han : AnalyticAt ℂ f z := analyticAt_of_differentiableOn hf hU
  have han' : AnalyticAt ℂ (fun w ↦ f w - f z) z := han.sub analyticAt_const
  -- `f` is not locally constant, being injective on a neighbourhood of `z`.
  have hnc : ¬ ∀ᶠ w in 𝓝 z, f w - f z = 0 := by
    intro h
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h.and (eventually_mem_nhds_iff.mpr
      hU |>.mono fun _ h ↦ mem_of_mem_nhds h))
    have h1 : z + (ε / 2 : ℝ) ∈ ball z ε := by
      rw [mem_ball, dist_eq_norm]; simp [abs_of_pos hε]; linarith
    have := hinj (hball _ h1).2 (hball z (mem_ball_self hε)).2
      (sub_eq_zero.mp (hball _ h1).1)
    have : ((ε / 2 : ℝ) : ℂ) = 0 := by simpa using this
    exact (by positivity : (ε / 2 : ℝ) ≠ 0) (by exact_mod_cast this)
  obtain ⟨n, g, hg, hgz, hfg⟩ := han'.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnc
  simp only [smul_eq_mul] at hfg
  -- the order `n` is at least `2`
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := hfg.self_of_nhds
    simp only [sub_self, pow_zero, one_mul] at this
    exact hgz this.symm
  have hn1 : n ≠ 1 := by
    rintro rfl
    have hd' : HasDerivAt (fun w ↦ f w - f z) (g z) z := by
      have h1 : HasDerivAt (fun w ↦ (w - z) ^ 1) 1 z := by
        simpa using (hasDerivAt_id z).sub_const z
      have := (h1.mul hg.differentiableAt.hasDerivAt).congr_of_eventuallyEq hfg
      simpa using this
    have : deriv (fun w ↦ f w - f z) z = deriv f z := by simp
    rw [← this, hd'.deriv] at hd
    exact hgz hd
  have hn2 : 2 ≤ n := by omega
  -- an `n`-th root `h` of `g` near `z`
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c ^ n = g z := ⟨g z ^ (n⁻¹ : ℂ), Complex.cpow_nat_inv_pow _ hn0⟩
  have hc0 : c ≠ 0 := by rintro rfl; simp [zero_pow hn0] at hc; exact hgz hc.symm
  set h : ℂ → ℂ := fun w ↦ c * Complex.exp (Complex.log (g w / g z) / n) with hh
  have hgw : ∀ᶠ w in 𝓝 z, g w / g z ∈ Complex.slitPlane := by
    have : Tendsto (fun w ↦ g w / g z) (𝓝 z) (𝓝 1) := by
      simpa [div_self hgz] using (hg.continuousAt.div_const (g z)).tendsto
    exact this.eventually (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
  have hhpow : ∀ᶠ w in 𝓝 z, h w ^ n = g w := by
    refine hgw.mono fun w hw ↦ ?_
    have hw0 : g w / g z ≠ 0 := Complex.slitPlane_ne_zero hw
    rw [hh, mul_pow, hc, ← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn0),
      Complex.exp_log hw0]
    field_simp
  have hhan : AnalyticAt ℂ h z := by
    have hsl : g z / g z ∈ Complex.slitPlane := by
      simp [div_self hgz]
    have h1 : AnalyticAt ℂ (fun w ↦ g w / g z) z := hg.div_const
    have h2 : AnalyticAt ℂ (fun w ↦ Complex.log (g w / g z) / n) z := (h1.clog hsl).div_const
    exact analyticAt_const.mul h2.cexp'
  have hhz : h z = c := by simp [hh, div_self hgz]
  set φ : ℂ → ℂ := fun w ↦ (w - z) * h w with hφ
  have hφd : HasStrictDerivAt φ c z := by
    have h1 : HasStrictDerivAt (fun w : ℂ ↦ w - z) 1 z := (hasStrictDerivAt_id z).sub_const z
    have := HasStrictDerivAt.mul h1 hhan.hasStrictDerivAt
    simp only [one_mul, sub_self, zero_mul, add_zero, hhz] at this
    exact this
  have hfφ : ∀ᶠ w in 𝓝 z, f w = f z + φ w ^ n := by
    filter_upwards [hfg, hhpow] with w h1 h2
    rw [hφ, mul_pow, h2, ← h1]; ring
  -- `φ` maps every neighbourhood of `z` onto a neighbourhood of `0`
  have hmap := hφd.map_nhds_eq hc0
  have hφz : φ z = 0 := by simp [hφ]
  rw [hφz] at hmap
  have hV : {w | f w = f z + φ w ^ n} ∩ U ∈ 𝓝 z := inter_mem hfφ hU
  have hW : φ '' ({w | f w = f z + φ w ^ n} ∩ U) ∈ 𝓝 (0 : ℂ) := by
    rw [← hmap]; exact image_mem_map hV
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have hζn : ζ ^ n = 1 := hprim.pow_eq_one
  have hζ1 : ζ ≠ 1 := hprim.ne_one (by omega)
  have hζnorm : ‖ζ‖ = 1 := by
    rw [Complex.norm_exp]; simp
  set δ : ℂ := ((ε / 2 : ℝ) : ℂ)
  have hδ : δ ∈ ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff]; simp [δ, abs_of_pos hε]; linarith
  have hδζ : δ * ζ ∈ ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff, norm_mul, hζnorm, mul_one]; simpa using hδ
  obtain ⟨w₁, ⟨hw₁f, hw₁U⟩, hw₁⟩ := hεW hδ
  obtain ⟨w₂, ⟨hw₂f, hw₂U⟩, hw₂⟩ := hεW hδζ
  have heq : f w₁ = f w₂ := by
    rw [hw₁f, hw₂f, hw₁, hw₂, mul_pow, hζn, mul_one]
  have hw : w₁ = w₂ := hinj hw₁U hw₂U heq
  have hδ0 : δ ≠ 0 := by simp [δ, hε.ne']
  apply hζ1
  have : φ w₁ = φ w₂ := by rw [hw]
  rw [hw₁, hw₂] at this
  exact (mul_eq_left₀ hδ0).mp this.symm

/-- A continuous lift of a holomorphic map through a holomorphic map with nonzero derivative is
holomorphic: if `f ∘ σ = g` near `u`, `σ` is continuous at `u`, `f` has nonzero strict derivative
at `σ u` and `g` is differentiable at `u`, then `σ` is differentiable at `u`. -/
theorem differentiableAt_of_comp_eq {f g σ : ℂ → ℂ} {u f' : ℂ}
    (hf : HasStrictDerivAt f f' (σ u)) (hf' : f' ≠ 0) (hσ : ContinuousAt σ u)
    (hfg : ∀ᶠ v in 𝓝 u, f (σ v) = g v) (hg : DifferentiableAt ℂ g u) :
    DifferentiableAt ℂ σ u := by
  have hinv := hf.to_localInverse hf'
  have hleft := hf.eventually_left_inverse hf'
  have hσ' : ∀ᶠ v in 𝓝 u, hf.localInverse f f' (σ u) hf' (f (σ v)) = σ v :=
    hσ.eventually hleft
  have heq : σ =ᶠ[𝓝 u] fun v ↦ hf.localInverse f f' (σ u) hf' (g v) := by
    filter_upwards [hσ', hfg] with v h1 h2
    rw [← h2, h1]
  have hgu : g u = f (σ u) := hfg.self_of_nhds.symm
  have : DifferentiableAt ℂ (fun v ↦ hf.localInverse f f' (σ u) hf' (g v)) u := by
    have h2 : DifferentiableAt ℂ (hf.localInverse f f' (σ u) hf') (g u) := by
      rw [hgu]; exact hinv.hasDerivAt.differentiableAt
    exact h2.comp u hg
  exact this.congr_of_eventuallyEq heq

/-- **Hurwitz's theorem**, in the form used here: if holomorphic functions `F n` on `ball z r` all
omit the value `β` (for large `n`) and converge locally uniformly on `ball z r` to `f` with
`f z = β`, then `f = β` on a neighbourhood of `z`. -/
theorem eventually_eq_of_tendstoLocallyUniformlyOn {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {z β : ℂ}
    {r : ℝ} (hr : 0 < r) (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (ball z r))
    (hlim : TendstoLocallyUniformlyOn F f atTop (ball z r))
    (hne : ∀ᶠ n in atTop, ∀ w ∈ ball z r, F n w ≠ β) (hfz : f z = β) :
    ∀ᶠ w in 𝓝 z, f w = β := by
  have hfd : DifferentiableOn ℂ f (ball z r) := hlim.differentiableOn hF isOpen_ball
  have han : AnalyticAt ℂ (fun w ↦ f w - β) z :=
    (analyticAt_of_differentiableOn hfd (ball_mem_nhds z hr)).sub analyticAt_const
  rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact h.mono fun w hw ↦ sub_eq_zero.mp hw
  exfalso
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp h)
  set ρ := min ε r / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρε : ρ < ε := by rw [hρ]; linarith [min_le_left ε r]
  have hρr : ρ < r := by rw [hρ]; linarith [min_le_right ε r]
  have hsph : (sphere z ρ).Nonempty := NormedSpace.sphere_nonempty.mpr hρ0.le
  have hcont : ContinuousOn (fun w ↦ ‖f w - β‖) (sphere z ρ) :=
    ((hfd.continuousOn.mono (sphere_subset_ball hρr)).sub continuousOn_const).norm
  obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_sphere z ρ).exists_isMinOn hsph hcont
  set m := ‖f w₀ - β‖ with hm
  have hm0 : 0 < m := by
    refine norm_pos_iff.mpr (hεball w₀ ?_ ?_)
    · rw [mem_sphere] at hw₀; rw [mem_ball, hw₀]; exact hρε
    · intro hwz; rw [mem_sphere, hwz, dist_self] at hw₀; exact hρ0.ne' hw₀.symm
  -- uniform convergence on the closed ball
  have hunif : TendstoUniformlyOn F f atTop (closedBall z ρ) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hlim _
      (closedBall_subset_ball hρr) (isCompact_closedBall z ρ)
  have hclose : ∀ᶠ n in atTop, ∀ w ∈ closedBall z ρ, dist (f w) (F n w) < m / 2 :=
    Metric.tendstoUniformlyOn_iff.mp hunif _ (by positivity)
  obtain ⟨n, hn1, hn2, hn3⟩ := (hF.and (hne.and hclose)).exists
  -- max modulus for `1 / (F n - β)`
  have hdiff : DifferentiableOn ℂ (fun w ↦ (F n w - β)⁻¹) (ball z r) :=
    (hn1.sub_const β).inv fun w hw ↦ sub_ne_zero.mpr (hn2 w hw)
  have hbound : ‖(F n z - β)⁻¹‖ ≤ (m / 2)⁻¹ := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (f := fun w ↦ (F n w - β)⁻¹)
      (U := ball z ρ) (z := z) isBounded_ball (hdiff.diffContOnCl_ball (closedBall_subset_ball hρr))
      ?_ (subset_closure (mem_ball_self hρ0))
    · intro w hw
      rw [frontier_ball z hρ0.ne'] at hw
      have h1 : m ≤ ‖f w - β‖ := hmin hw
      have h2 : dist (f w) (F n w) < m / 2 := hn3 w (sphere_subset_closedBall hw)
      rw [dist_eq_norm] at h2
      have h3 : m / 2 ≤ ‖F n w - β‖ := by
        have := norm_add_le (F n w - β) (f w - F n w)
        have e : F n w - β + (f w - F n w) = f w - β := by ring
        rw [e] at this; linarith
      rw [norm_inv]
      exact inv_anti₀ (by positivity) h3
  have h4 : dist (f z) (F n z) < m / 2 := hn3 z (mem_closedBall_self hρ0.le)
  rw [hfz, dist_eq_norm, norm_sub_rev] at h4
  have hne0 : F n z - β ≠ 0 := sub_ne_zero.mpr (hn2 z (mem_ball_self hr))
  rw [norm_inv] at hbound
  have := (inv_le_inv₀ (norm_pos_iff.mpr hne0) (by positivity)).mp hbound
  linarith

/-- **Inverse function theorem, section form.** If `f` has a nonzero strict derivative at `a`,
then `f` has a continuous section over a disc about `f a` taking the value `a` at `f a`. -/
theorem exists_localSection {f : ℂ → ℂ} {f' a : ℂ} (hf : HasStrictDerivAt f f' a) (hf' : f' ≠ 0) :
    ∃ ε > 0, ∃ s : ℂ → ℂ, ContinuousOn s (ball (f a) ε) ∧ (∀ y ∈ ball (f a) ε, f (s y) = y) ∧
      s (f a) = a := by
  set e := (hf.hasStrictFDerivAt_equiv hf').toOpenPartialHomeomorph f
  have hsrc : a ∈ e.source := (hf.hasStrictFDerivAt_equiv hf').mem_toOpenPartialHomeomorph_source
  have htgt : f a ∈ e.target :=
    (hf.hasStrictFDerivAt_equiv hf').image_mem_toOpenPartialHomeomorph_target
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target _ htgt
  refine ⟨ε, hε, e.symm, e.continuousOn_symm.mono hball, fun y hy ↦ e.right_inv (hball hy), ?_⟩
  exact e.left_inv hsrc

end Uniformization
