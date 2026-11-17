import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`, 4 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero

set_option autoImplicit false

open MeasureTheory Set Function Filter Topology

noncomputable section

namespace AutomorphicForm
namespace GL2Real
namespace ScalarTermVanishing
open _root_.AutomorphicForm.GL2Real open _root_.AutomorphicForm

def gI {P : Type*} (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P) : (Fin 2 → Fin 2 → ℝ) → ℂ :=
  fun M => fderiv ℝ (fun M => Φ (M, p)) M (Matrix.of.symm !![1, 0; 0, 1])

/--
@isnad1 id=hascompa.1h3v.s7.decd99feebea from=translated src=- shape=101d36bc vocab=0b99d3ae
-/
lemma slice_hasCompactSupport {P : Type*} [TopologicalSpace P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦc : HasCompactSupport Φ) (p : P) :
    HasCompactSupport (fun M : Fin 2 → Fin 2 → ℝ => Φ (M, p)) := by
  refine HasCompactSupport.intro (hΦc.isCompact.image continuous_fst) ?_
  intro M hM
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact hM ⟨(M, p), h, rfl⟩

section Slice

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/--
@isnad1 id=contdiff.1h3v.s9.df97b2aebac0 from=translated src=- shape=c9b71d5b vocab=4a827265
-/
lemma slice_contDiff (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (p : P) :
    ContDiff ℝ (⊤ : ℕ∞) (fun M : Fin 2 → Fin 2 → ℝ => Φ (M, p)) :=
  hΦs.comp (contDiff_id.prodMk contDiff_const)

/--
@isnad1 id=ex.2h3v.s9.50acd6c80a75 from=translated src=- shape=e7a572ef vocab=4a73b68e
-/
lemma exists_bound_and_radius (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (p : P) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧ (∀ M, ‖gI Φ p M‖ ≤ C) ∧
      (∀ M, gI Φ p M ≠ 0 → ∀ i j, |M i j| ≤ R) := by
  have hψs := slice_contDiff Φ hΦs p
  have hψc := slice_hasCompactSupport Φ hΦc p
  have hgc : HasCompactSupport (gI Φ p) :=
    HasCompactSupport.fderiv_apply ℝ hψc (Matrix.of.symm !![1, 0; 0, 1])
  have hgcont : Continuous (gI Φ p) :=
    (hψs.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨C₀, hC₀⟩ := hgcont.bounded_above_of_compact_support hgc
  obtain ⟨R₀, hR₀⟩ := hgc.isCompact.isBounded.exists_norm_le
  refine ⟨max C₀ 0, max R₀ 1, le_max_right _ _, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun M => (hC₀ M).trans (le_max_left _ _), ?_⟩
  intro M hM i j
  have hmem : M ∈ tsupport (gI Φ p) := subset_tsupport _ hM
  have h1 : ‖M i j‖ ≤ ‖M i‖ := norm_le_pi_norm (M i) j
  have h2 : ‖M i‖ ≤ ‖M‖ := norm_le_pi_norm M i
  rw [Real.norm_eq_abs] at h1
  exact (h1.trans (h2.trans (hR₀ M hmem))).trans (le_max_left _ _)

end Slice

def Mplus (r θ u v : ℝ) : Fin 2 → Fin 2 → ℝ :=
  Matrix.of.symm !![r * (Real.cos θ - v), r * ((Real.sin θ ^ 2 + v ^ 2) / u);
    -(r * u), r * (Real.cos θ + v)]

def Mminus (r θ u v : ℝ) : Fin 2 → Fin 2 → ℝ :=
  Matrix.of.symm !![r * (Real.cos θ + v), -(r * ((Real.sin θ ^ 2 + v ^ 2) / u));
    r * u, r * (Real.cos θ - v)]

/--
@isnad1 id=eq.0h4v.s5.eb6bfdcabc99 from=translated src=- shape=ccb1a0d0 vocab=5c573128
-/
@[scoped simp] lemma Mplus_10 (r θ u v : ℝ) : Mplus r θ u v 1 0 = -(r * u) := rfl
/--
@isnad1 id=eq.0h4v.s6.0c63fa412c4f from=translated src=- shape=c6ffdbd1 vocab=9dedebdf
-/
@[scoped simp] lemma Mplus_01 (r θ u v : ℝ) :
    Mplus r θ u v 0 1 = r * ((Real.sin θ ^ 2 + v ^ 2) / u) := rfl
/--
@isnad1 id=eq.0h4v.s5.10d106651365 from=translated src=- shape=d69758ba vocab=ceebe3f4
-/
@[scoped simp] lemma Mminus_10 (r θ u v : ℝ) : Mminus r θ u v 1 0 = r * u := rfl
/--
@isnad1 id=eq.0h4v.s6.d967ca337897 from=translated src=- shape=5248ab4c vocab=bb26dc1c
-/
@[scoped simp] lemma Mminus_01 (r θ u v : ℝ) :
    Mminus r θ u v 0 1 = -(r * ((Real.sin θ ^ 2 + v ^ 2) / u)) := rfl

/--
@isnad1 id=and.4h5v.s7.7a0f236f2e29 from=translated src=- shape=59dae1d0 vocab=05bde34c
-/
lemma constraints_of_entries {r θ u v R : ℝ} (hr : 0 < r) (hu : 0 < u)
    (h10 : r * u ≤ R) (h01 : r * ((Real.sin θ ^ 2 + v ^ 2) / u) ≤ R) :
    u ≤ R / r ∧ v ^ 2 ≤ R / r * u := by
  constructor
  · rw [le_div_iff₀ hr]
    linarith
  · have h1 : (Real.sin θ ^ 2 + v ^ 2) / u ≤ R / r := by
      rw [le_div_iff₀ hr]
      linarith
    rw [div_le_iff₀ hu] at h1
    nlinarith [sq_nonneg (Real.sin θ)]

section Pointwise

variable {P : Type*}

/--
@isnad1 id=and.4h8v.s7.ba43849c2a1c from=translated src=- shape=8b79adc5 vocab=a29e70f1
-/
lemma constraints_plus {Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {p : P} {R : ℝ}
    (hR : ∀ M, gI Φ p M ≠ 0 → ∀ i j, |M i j| ≤ R) {r θ u v : ℝ} (hr : 0 < r) (hu : 0 < u)
    (h : gI Φ p (Mplus r θ u v) ≠ 0) : u ≤ R / r ∧ v ^ 2 ≤ R / r * u := by
  have h10 := hR _ h 1 0
  have h01 := hR _ h 0 1
  simp only [Mplus_10, Mplus_01] at h10 h01
  rw [abs_neg, abs_of_pos (mul_pos hr hu)] at h10
  rw [abs_of_nonneg (by positivity)] at h01
  exact constraints_of_entries hr hu h10 h01

/--
@isnad1 id=and.4h8v.s7.a3e9a32fd046 from=translated src=- shape=8b79adc5 vocab=5e991b5d
-/
lemma constraints_minus {Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {p : P} {R : ℝ}
    (hR : ∀ M, gI Φ p M ≠ 0 → ∀ i j, |M i j| ≤ R) {r θ u v : ℝ} (hr : 0 < r) (hu : 0 < u)
    (h : gI Φ p (Mminus r θ u v) ≠ 0) : u ≤ R / r ∧ v ^ 2 ≤ R / r * u := by
  have h10 := hR _ h 1 0
  have h01 := hR _ h 0 1
  simp only [Mminus_10, Mminus_01] at h10 h01
  rw [abs_of_pos (mul_pos hr hu)] at h10
  rw [abs_neg, abs_of_nonneg (by positivity)] at h01
  exact constraints_of_entries hr hu h10 h01

end Pointwise

def dom (C K : ℝ) (q : ℝ × ℝ) : ℝ :=
  if 0 < q.1 ∧ q.1 ≤ K ∧ q.2 ^ 2 ≤ K * q.1 then 2 * C / q.1 else 0

/--
@isnad1 id=le.1h3v.s5.312efc5d58af from=translated src=- shape=0029bda3 vocab=99bb23d2
-/
lemma dom_nonneg {C K : ℝ} (hC : 0 ≤ C) (q : ℝ × ℝ) : 0 ≤ dom C K q := by
  unfold dom
  split_ifs with h
  · exact div_nonneg (by positivity) h.1.le
  · exact le_rfl

/--
@isnad1 id=measurab.0h2v.s4.cc29ae10520f from=translated src=- shape=74ae2556 vocab=500ae43c
-/
lemma measurable_dom (C K : ℝ) : Measurable (dom C K) := by
  unfold dom
  refine Measurable.ite ?_ (by fun_prop) measurable_const
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le (measurable_snd.pow_const 2) (measurable_fst.const_mul K)))

/--
@isnad1 id=eq.1h3v.s7.db5d9e5b9cf7 from=translated src=- shape=99a7eb46 vocab=6d30d54f
-/
lemma dom_slice_eq (C K u : ℝ) (hK : 0 ≤ K) :
    (fun v => dom C K (u, v)) =
      if 0 < u ∧ u ≤ K then
        (Icc (-Real.sqrt (K * u)) (Real.sqrt (K * u))).indicator (fun _ => 2 * C / u)
      else 0 := by
  ext v
  by_cases h : 0 < u ∧ u ≤ K
  · rw [ite_eq_left h]
    have hKu : 0 ≤ K * u := mul_nonneg hK h.1.le
    simp only [dom, indicator, mem_Icc]
    by_cases hv : v ^ 2 ≤ K * u
    · rw [ite_eq_left ⟨h.1, h.2, hv⟩, ite_eq_left ((Real.sq_le hKu).1 hv)]
    · rw [ite_eq_right (fun h' => hv h'.2.2), ite_eq_right (fun h' => hv ((Real.sq_le hKu).2 h'))]
  · rw [ite_eq_right h]
    simp only [dom, Pi.zero_apply]
    rw [ite_eq_right (fun h' => h ⟨h'.1, h'.2.1⟩)]

/--
@isnad1 id=integrab.1h3v.s5.265c85d9e235 from=translated src=- shape=2dbbe487 vocab=dc5164af
-/
lemma dom_slice_integrable (C K u : ℝ) (hK : 0 ≤ K) :
    Integrable (fun v => dom C K (u, v)) := by
  rw [dom_slice_eq C K u hK]
  split_ifs with h
  · exact (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Icc
  · exact integrable_zero _ _ _

/--
@isnad1 id=eq.2h3v.s7.36bdb0d40d52 from=translated src=- shape=0faff985 vocab=7bb5737d
-/
lemma dom_norm_slice_integral (C K u : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) :
    ∫ v, ‖dom C K (u, v)‖ =
      (Ioc 0 K).indicator (fun u => 4 * C * Real.sqrt K * u ^ (-(1 / 2 : ℝ))) u := by
  by_cases h : 0 < u ∧ u ≤ K
  · have hKu : 0 ≤ K * u := mul_nonneg hK h.1.le
    have hslice : (fun v => ‖dom C K (u, v)‖) =
        (Icc (-Real.sqrt (K * u)) (Real.sqrt (K * u))).indicator (fun _ => 2 * C / u) := by
      funext v
      have := congrFun (dom_slice_eq C K u hK) v
      simp only [ite_eq_left h] at this
      rw [this, norm_indicator_eq_indicator_norm]
      simp only [Real.norm_of_nonneg (div_nonneg (by positivity : (0 : ℝ) ≤ 2 * C) h.1.le)]
    rw [hslice, integral_indicator_const _ measurableSet_Icc, smul_eq_mul,
      Real.volume_real_Icc_of_le (by linarith [Real.sqrt_nonneg (K * u)]),
      indicator_of_mem (mem_Ioc.2 h), Real.sqrt_mul hK, Real.rpow_neg h.1.le,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_div_self]
    ring
  · have hslice : (fun v => ‖dom C K (u, v)‖) = fun _ => 0 := by
      funext v
      have := congrFun (dom_slice_eq C K u hK) v
      simp only [ite_eq_right h, Pi.zero_apply] at this
      rw [this, norm_zero]
    have hu : u ∉ Ioc 0 K := fun h' => h ⟨h'.1, h'.2⟩
    rw [hslice, integral_zero, indicator_of_notMem hu]

/--
@isnad1 id=integrab.2h2v.s6.f35881ade99a from=translated src=- shape=0b35128a vocab=bc28e450
-/
lemma integrable_dom (C K : ℝ) (hC : 0 ≤ C) (hK : 0 < K) :
    Integrable (dom C K) (volume : Measure (ℝ × ℝ)) := by
  have hmeas : Measurable (dom C K) := measurable_dom C K
  rw [Measure.volume_eq_prod]
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).2
    ⟨ae_of_all _ (fun u => dom_slice_integrable C K u hK.le), ?_⟩
  have heq : (fun u => ∫ v, ‖dom C K (u, v)‖) =
      (Ioc 0 K).indicator (fun u => 4 * C * Real.sqrt K * u ^ (-(1 / 2 : ℝ))) := by
    funext u
    exact dom_norm_slice_integral C K u hC hK.le
  rw [heq, integrable_indicator_iff measurableSet_Ioc]
  have h1 : IntegrableOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) (Ioo 0 K) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hK).2 (by norm_num)
  have h2 : IntegrableOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) (Ioc 0 K) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).2 h1
  exact h2.const_mul _

section Domination

variable {P : Type*}

/--
@isnad1 id=le.5h9v.s7.124297409cff from=translated src=- shape=dfb8a82b vocab=00a12f19
-/
lemma norm_integrand_le {Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ} {p : P} {C R : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ M, ‖gI Φ p M‖ ≤ C) (hR : ∀ M, gI Φ p M ≠ 0 → ∀ i j, |M i j| ≤ R)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) (u v : ℝ) (hu : 0 < u) :
    ‖(gI Φ p (Mplus r θ u v) + gI Φ p (Mminus r θ u v)) / (u : ℂ)‖ ≤ dom C (R / r) (u, v) := by
  by_cases hreg : 0 < u ∧ u ≤ R / r ∧ v ^ 2 ≤ R / r * u
  · have hdom : dom C (R / r) (u, v) = 2 * C / u := by
      simp only [dom]
      rw [ite_eq_left hreg]
    rw [hdom, norm_div, Complex.norm_real, Real.norm_of_nonneg hu.le, div_le_div_iff_of_pos_right hu]
    calc ‖gI Φ p (Mplus r θ u v) + gI Φ p (Mminus r θ u v)‖
        ≤ ‖gI Φ p (Mplus r θ u v)‖ + ‖gI Φ p (Mminus r θ u v)‖ := norm_add_le _ _
      _ ≤ C + C := add_le_add (hC _) (hC _)
      _ = 2 * C := by ring
  · have hA : gI Φ p (Mplus r θ u v) = 0 := by
      by_contra hA
      exact hreg ⟨hu, constraints_plus hR hr hu hA⟩
    have hB : gI Φ p (Mminus r θ u v) = 0 := by
      by_contra hB
      exact hreg ⟨hu, constraints_minus hR hr hu hB⟩
    rw [hA, hB, add_zero, zero_div, norm_zero]
    exact dom_nonneg hC0 _

end Domination

section Main

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/--
@isnad1 id=tendsto.3h4v.s9.98d0b2bedf5f from=translated src=- shape=4fd38df2 vocab=afdbad44
-/
theorem tendsto_sin_mul_integral (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (p : P) (r : ℝ) (hr : 0 < r) :
    Tendsto (fun θ : ℝ => (Real.sin θ : ℂ) * ∫ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
        (gI Φ p (Mplus r θ q.1 q.2) + gI Φ p (Mminus r θ q.1 q.2)) / (q.1 : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, R, hC0, hR0, hC, hR⟩ := exists_bound_and_radius Φ hΦs hΦc p
  have hK : 0 < R / r := div_pos hR0 hr
  have hInt : Integrable (dom C (R / r)) (volume : Measure (ℝ × ℝ)) :=
    integrable_dom C (R / r) hC0 hK
  set B : ℝ := ∫ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), dom C (R / r) q with hB
  have hbound : ∀ θ : ℝ, ‖(Real.sin θ : ℂ) * ∫ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
      (gI Φ p (Mplus r θ q.1 q.2) + gI Φ p (Mminus r θ q.1 q.2)) / (q.1 : ℂ)‖ ≤
        |Real.sin θ| * B := by
    intro θ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine norm_integral_le_of_norm_le hInt.integrableOn ?_
    rw [ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)]
    refine ae_of_all _ (fun q hq => ?_)
    exact norm_integrand_le hC0 hC hR hr θ q.1 q.2 hq.1
  refine squeeze_zero_norm hbound ?_
  have h : Tendsto (fun θ : ℝ => |Real.sin θ| * B) (𝓝 0) (𝓝 (|Real.sin 0| * B)) :=
    ((Real.continuous_sin.tendsto 0).abs).mul_const B
  rw [Real.sin_zero, abs_zero, zero_mul] at h
  exact h.mono_left nhdsWithin_le_nhds

end Main

end AutomorphicForm.GL2Real.ScalarTermVanishing
open scoped _root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.AutomorphicForm _root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.AutomorphicForm.GL2Real _root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.AutomorphicForm.GL2Real.ScalarTermVanishing
open scoped _root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.AutomorphicForm _root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.AutomorphicForm.GL2Real
open scoped _root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.AutomorphicForm

end
open scoped _root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.AutomorphicForm _root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.AutomorphicForm.GL2Real _root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.AutomorphicForm.GL2Real.ScalarTermVanishing

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.AutomorphicForm _root_.AutomorphicForm.GL2Real _root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.AutomorphicForm.GL2Real AutomorphicForm.GL2Real.ScalarTermVanishing in
/--
@isnad1 id=tendsto.3h4v.s12.9561f18f96d8 from=translated src=- shape=2cdcbe5b vocab=8e2a572b
-/
theorem solution
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (p : P) (r : ℝ) (hr : 0 < r) :
    Filter.Tendsto (fun θ : ℝ => (Real.sin θ : ℂ) * ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.univ,
        (fderiv ℝ (fun M => Φ (M, p))
            (Matrix.of.symm !![r * (Real.cos θ - q.2), r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1);
              -(r * q.1), r * (Real.cos θ + q.2)])
            (Matrix.of.symm !![1, 0; 0, 1]) +
          fderiv ℝ (fun M => Φ (M, p))
            (Matrix.of.symm !![r * (Real.cos θ + q.2), -(r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1));
              r * q.1, r * (Real.cos θ - q.2)])
            (Matrix.of.symm !![1, 0; 0, 1])) / (q.1 : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  tendsto_sin_mul_integral Φ hΦs hΦc p r hr
