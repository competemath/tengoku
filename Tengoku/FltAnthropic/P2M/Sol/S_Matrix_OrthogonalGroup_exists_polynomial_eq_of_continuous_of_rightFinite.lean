import Tengoku.Seed.Analysis.Matrix.Normed
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 4 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite

set_option autoImplicit false

noncomputable section

namespace M4aP3C
namespace TensorSplit

variable {G : Type*}

/--
@isnad1 id=ex.0h3v.s9.06c9e09ff5db from=translated src=- shape=6a7febe6 vocab=e71144ac
-/
theorem exists_eval_combination (W : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ W]
    (φ : Module.Dual ℂ W) :
    ∃ (m : ℕ) (e : Fin m → ℂ) (x : Fin m → G), ∀ w : W, φ w = ∑ l, e l * (w : G → ℂ) (x l) := by
  classical
  let ev : G → Module.Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hev : ∀ x (w : W), ev x w = (w : G → ℂ) x := fun x w => rfl
  let Φ : Submodule ℂ (Module.Dual ℂ W) := Submodule.span ℂ (Set.range ev)
  have hco : Φ.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext x
    have := hw (ev x) (Submodule.subset_span ⟨x, rfl⟩)
    rw [hev] at this
    simpa using this
  have hΦ : Φ = ⊤ := by
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Φ)
    rw [hco, Submodule.dualAnnihilator_bot] at h
    exact h.symm
  have hφ : φ ∈ Φ := by rw [hΦ]; exact Submodule.mem_top
  rw [Submodule.mem_span_set'] at hφ
  obtain ⟨m, e, g, hg⟩ := hφ
  have hg' : ∀ l, ∃ x, ev x = ((g l : Set.range ev) : Module.Dual ℂ W) := fun l => (g l).2
  choose x hx using hg'
  refine ⟨m, e, x, fun w => ?_⟩
  rw [← hg]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [LinearMap.smul_apply, ← hx l, hev, smul_eq_mul]

end M4aP3C.TensorSplit

end

noncomputable section

open MeasureTheory

namespace M4aP3C
namespace O2Finite

abbrev O2 : Type := ↥(Matrix.orthogonalGroup (Fin 2) ℝ)

def polyFun : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℝ → ℂ) :=
  Submodule.span ℂ
    {F | ∃ l : List (Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod}

/--
@isnad1 id=iscompac.0h0v.s7.2f07cf073b06 from=translated src=- shape=a8f2997c vocab=87ceee55
-/
theorem isCompact_orthogonalGroup :
    IsCompact ((Matrix.orthogonalGroup (Fin 2) ℝ : Set (Matrix (Fin 2) (Fin 2) ℝ))) := by
  have hclosed : IsClosed ((Matrix.orthogonalGroup (Fin 2) ℝ : Set (Matrix (Fin 2) (Fin 2) ℝ))) :=
    isClosed_unitary
  letI : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℝ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℝ) := Matrix.normedSpace
  haveI : ProperSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    FiniteDimensional.proper ℝ (Matrix (Fin 2) (Fin 2) ℝ)
  have hsub : (Matrix.orthogonalGroup (Fin 2) ℝ : Set (Matrix (Fin 2) (Fin 2) ℝ))
      ⊆ Metric.closedBall 0 1 := by
    intro m hm
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (Matrix.norm_le_iff zero_le_one).2 fun i j => entry_norm_bound_of_unitary hm i j
  exact Metric.isCompact_of_isClosed_isBounded hclosed
    (Metric.isBounded_closedBall.subset hsub)

scoped instance : CompactSpace O2 := isCompact_iff_compactSpace.mp isCompact_orthogonalGroup

scoped instance : MeasurableSpace O2 := borel O2

scoped instance : BorelSpace O2 := ⟨rfl⟩

scoped instance : MeasurableMul O2 :=
  ⟨fun g => (continuous_const_mul g).measurable, fun g => (continuous_mul_const g).measurable⟩

def K0 : TopologicalSpace.PositiveCompacts O2 :=
  ⟨⟨Set.univ, isCompact_univ⟩, by rw [interior_univ]; exact Set.univ_nonempty⟩

def haarO2 : Measure O2 := Measure.haarMeasure K0

scoped instance : Measure.IsHaarMeasure haarO2 := Measure.isHaarMeasure_haarMeasure K0

/--
@isnad1 id=eq.0h0v.s4.8de7644ca2d2 from=translated src=- shape=7c7ab9f0 vocab=5aad9324
-/
theorem haarO2_univ : haarO2 Set.univ = 1 := Measure.haarMeasure_self

scoped instance : IsProbabilityMeasure haarO2 := ⟨haarO2_univ⟩

/--
@isnad1 id=eq.0h2v.s7.a08e5f036d4c from=translated src=- shape=d54bc837 vocab=0fb77767
-/
theorem integral_translate (g : O2) (f : O2 → ℂ) :
    ∫ h, f (g * h) ∂haarO2 = ∫ h, f h ∂haarO2 :=
  integral_mul_left_eq_self f g

/--
@isnad1 id=integrab.1h2v.s8.da751ad86f38 from=translated src=- shape=4183922c vocab=91f7557b
-/
theorem integrable_of_continuous {E : Type} [NormedAddCommGroup E] {f : O2 → E}
    (hf : Continuous f) : Integrable f haarO2 :=
  hf.integrable_of_hasCompactSupport (isClosed_tsupport f).isCompact

/--
@isnad1 id=lt.3h1v.s8.c5415f01295f from=translated src=- shape=756f92c6 vocab=12f28b7b
-/
theorem integral_pos_of_continuous {χ : O2 → ℝ} (hc : Continuous χ) (h0 : 0 ≤ χ)
    (h1 : 0 < χ 1) : 0 < ∫ h, χ h ∂haarO2 := by
  rw [integral_pos_iff_support_of_nonneg h0 (integrable_of_continuous hc)]
  have hopen : IsOpen (Function.support χ) := by
    rw [Function.support_eq_preimage]
    exact isClosed_singleton.isOpen_compl.preimage hc
  exact hopen.measure_pos haarO2 ⟨1, Function.mem_support.mpr (ne_of_gt h1)⟩

def qker (k : O2) : ℝ := (2 + Matrix.trace (k : Matrix (Fin 2) (Fin 2) ℝ)) / 4

/--
@isnad1 id=continuo.0h0v.s8.2967d6940597 from=translated src=- shape=54c8eceb vocab=c865ea61
-/
theorem continuous_qker : Continuous qker := by
  have htr : Continuous fun k : O2 => Matrix.trace (k : Matrix (Fin 2) (Fin 2) ℝ) :=
    Continuous.matrix_trace continuous_subtype_val
  exact (continuous_const.add htr).div_const 4

/--
@isnad1 id=le.0h3v.s8.b8ea4ff0c3ff from=translated src=- shape=e10b9f7a vocab=3a9902ad
-/
theorem entry_abs_le (k : O2) (i j : Fin 2) : |(k : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
  have h := entry_norm_bound_of_unitary k.2 i j
  rwa [Real.norm_eq_abs] at h

/--
@isnad1 id=le.0h3v.s8.44240be22e57 from=translated src=- shape=8c0767e8 vocab=15d91336
-/
theorem entry_le (k : O2) (i j : Fin 2) : (k : Matrix (Fin 2) (Fin 2) ℝ) i j ≤ 1 :=
  le_trans (le_abs_self _) (entry_abs_le k i j)

/--
@isnad1 id=le.0h1v.s3.6803fcdbe1b8 from=translated src=- shape=b9369acb vocab=6bc05c7b
-/
theorem qker_nonneg (k : O2) : 0 ≤ qker k := by
  have h0 := abs_le.mp (entry_abs_le k 0 0)
  have h1 := abs_le.mp (entry_abs_le k 1 1)
  unfold qker
  rw [Matrix.trace_fin_two]
  linarith [h0.1, h1.1]

/--
@isnad1 id=le.0h1v.s3.c9c39ecac8cc from=translated src=- shape=a311c14d vocab=6bc05c7b
-/
theorem qker_le_one (k : O2) : qker k ≤ 1 := by
  have h0 := entry_le k 0 0
  have h1 := entry_le k 1 1
  unfold qker
  rw [Matrix.trace_fin_two]
  linarith

/--
@isnad1 id=eq.0h0v.s6.a89bed6dc9fa from=translated src=- shape=1ac31801 vocab=91c8e39e
-/
theorem qker_one : qker 1 = 1 := by
  have h : ((1 : O2) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := rfl
  unfold qker
  rw [h, Matrix.trace_one]
  norm_num

/--
@isnad1 id=iff.0h1v.s6.a2519dd125b5 from=translated src=- shape=3a75f94e vocab=91c8e39e
-/
theorem qker_eq_one_iff {k : O2} : qker k = 1 ↔ k = 1 := by
  constructor
  · intro hq
    have e0 := entry_le k 0 0
    have e1 := entry_le k 1 1
    have htr : (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 2 := by
      unfold qker at hq
      rw [Matrix.trace_fin_two] at hq
      linarith
    have h00 : (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := by linarith
    have h11 : (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by linarith
    have hu : (k : Matrix (Fin 2) (Fin 2) ℝ) * star (k : Matrix (Fin 2) (Fin 2) ℝ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp k.2
    have row : ∀ i : Fin 2, (k : Matrix (Fin 2) (Fin 2) ℝ) i 0 * (k : Matrix (Fin 2) (Fin 2) ℝ) i 0 +
        (k : Matrix (Fin 2) (Fin 2) ℝ) i 1 * (k : Matrix (Fin 2) (Fin 2) ℝ) i 1 = 1 := by
      intro i
      have r := congrArg (fun M => M i i) hu
      simp only [Matrix.mul_apply, Matrix.one_apply_eq] at r
      rw [Fin.sum_univ_two] at r
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.conjTranspose_apply] at r
      simpa only [star_trivial] using r
    have h01 : (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by
      have h := row 0
      rw [h00] at h
      exact mul_self_eq_zero.mp (by linarith)
    have h10 : (k : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
      have h := row 1
      rw [h11] at h
      exact mul_self_eq_zero.mp (by linarith)
    have hAone : (k : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
      rw [Matrix.eta_fin_two (k : Matrix (Fin 2) (Fin 2) ℝ), h00, h01, h10, h11,
        Matrix.one_fin_two]
    exact Subtype.ext hAone
  · rintro rfl
    exact qker_one

/--
@isnad1 id=ex.1h1v.s8.957afc290758 from=translated src=- shape=798c0331 vocab=fe8bb194
-/
theorem exists_lt_one_bound {U : Set O2} (hU : U ∈ nhds (1 : O2)) :
    ∃ δ : ℝ, δ < 1 ∧ ∀ k : O2, k ∉ U → qker k ≤ δ := by
  rcases Set.eq_empty_or_nonempty ((interior U)ᶜ : Set O2) with hS | hS
  · refine ⟨0, by norm_num, fun k hk => ?_⟩
    exfalso
    have hkS : k ∈ ((interior U)ᶜ : Set O2) := fun hin => hk (interior_subset hin)
    rw [hS] at hkS
    simp at hkS
  · obtain ⟨m₀, hm₀, hmax⟩ :=
      (isOpen_interior.isClosed_compl.isCompact).exists_isMaxOn hS continuous_qker.continuousOn
    refine ⟨qker m₀, ?_, fun k hk => hmax (fun hin => hk (interior_subset hin))⟩
    rcases lt_or_eq_of_le (qker_le_one m₀) with h | h
    · exact h
    · exfalso
      have h1 : m₀ = 1 := qker_eq_one_iff.mp h
      rw [h1] at hm₀
      exact hm₀ (mem_interior_iff_mem_nhds.mpr hU)

def fejerNorm (n : ℕ) : ℝ := ∫ h, qker h ^ n ∂haarO2

/--
@isnad1 id=lt.0h1v.s3.9801b9938713 from=translated src=- shape=b9369acb vocab=d4364272
-/
theorem fejerNorm_pos (n : ℕ) : 0 < fejerNorm n := by
  refine integral_pos_of_continuous (continuous_qker.pow n)
    (fun h => pow_nonneg (qker_nonneg h) n) ?_
  rw [qker_one, one_pow]
  norm_num

def fejerConv (n : ℕ) (Φ : O2 → ℂ) (k : O2) : ℂ :=
  (fejerNorm n)⁻¹ • ∫ h, Φ (k * h) * ((qker h ^ n : ℝ) : ℂ) ∂haarO2

/--
@isnad1 id=integrab.1h3v.s8.24962e3fd80e from=translated src=- shape=fb29918a vocab=9e0df89b
-/
theorem integrable_conv_kernel {Φ : O2 → ℂ} (hc : Continuous Φ) (n : ℕ) (k : O2) :
    Integrable (fun h => Φ (k * h) * ((qker h ^ n : ℝ) : ℂ)) haarO2 :=
  integrable_of_continuous ((hc.comp (continuous_const_mul k)).mul
    (Complex.continuous_ofReal.comp (continuous_qker.pow n)))

/--
@isnad1 id=eq.1h3v.s9.0183c38a440c from=translated src=- shape=c38c60c8 vocab=acea8f3c
-/
theorem fejerConv_sub {Φ : O2 → ℂ} (hc : Continuous Φ) (n : ℕ) (k : O2) :
    fejerConv n Φ k - Φ k
      = (fejerNorm n)⁻¹ • ∫ h, (Φ (k * h) - Φ k) * ((qker h ^ n : ℝ) : ℂ) ∂haarO2 := by
  have hint1 := integrable_conv_kernel hc n k
  have hint2 : Integrable (fun h : O2 => Φ k * ((qker h ^ n : ℝ) : ℂ)) haarO2 :=
    integrable_of_continuous (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_qker.pow n)))
  have hq2c : (∫ h, ((qker h ^ n : ℝ) : ℂ) ∂haarO2) = ((fejerNorm n : ℝ) : ℂ) := by
    unfold fejerNorm
    exact integral_ofReal
  have hpt : ∀ h : O2, (Φ (k * h) - Φ k) * ((qker h ^ n : ℝ) : ℂ)
      = Φ (k * h) * ((qker h ^ n : ℝ) : ℂ) - Φ k * ((qker h ^ n : ℝ) : ℂ) := by
    intro h; ring
  have hsplit : ∫ h, (Φ (k * h) - Φ k) * ((qker h ^ n : ℝ) : ℂ) ∂haarO2
      = (∫ h, Φ (k * h) * ((qker h ^ n : ℝ) : ℂ) ∂haarO2)
        - Φ k * ((fejerNorm n : ℝ) : ℂ) := by
    simp only [hpt]
    rw [integral_sub hint1 hint2, integral_const_mul, hq2c]
  unfold fejerConv
  rw [hsplit, smul_sub]
  congr 1
  have hne : ((fejerNorm n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (fejerNorm_pos n))
  rw [Complex.real_smul, Complex.ofReal_inv]
  field_simp

private theorem aux_ratio (x d e b : ℝ) (n : ℕ) (he : e ≠ 0) (hb : b ≠ 0) :
    (e^n * b)⁻¹ * (2*x*d^n) = (2*x/b) * (d/e)^n := by
  rw [div_pow]
  field_simp

/--
@isnad1 id=tendsto.1h2v.s8.0161a1eb5459 from=translated src=- shape=ff0c4433 vocab=a26e4dda
-/
theorem fejerConv_tendsto {Φ : O2 → ℂ} (hc : Continuous Φ) (k : O2) :
    Filter.Tendsto (fun n => fejerConv n Φ k) Filter.atTop (nhds (Φ k)) := by

  obtain ⟨xm, -, hxm⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.norm.continuousOn
  have hCb : ∀ x : O2, ‖Φ x‖ ≤ ‖Φ xm‖ := fun x => hxm (Set.mem_univ x)
  set C : ℝ := ‖Φ xm‖ with hCdef
  have hC0 : 0 ≤ C := norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε/4 := by linarith

  have hg : Continuous fun h : O2 => Φ (k * h) := hc.comp (continuous_const_mul k)
  set U : Set O2 := (fun h : O2 => Φ (k * h)) ⁻¹' Metric.ball (Φ k) (ε/4) with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball.preimage hg
  have hU1 : (1 : O2) ∈ U := by
    simp only [hUdef, Set.mem_preimage, Metric.mem_ball, mul_one, dist_self]
    exact hε4

  obtain ⟨δ₀, hδ₀1, hδ₀b⟩ := exists_lt_one_bound (hUopen.mem_nhds hU1)
  set δ : ℝ := max δ₀ 0 with hδdef
  have hδ1 : δ < 1 := max_lt hδ₀1 one_pos
  have hδ0 : 0 ≤ δ := le_max_right _ _
  have hδb : ∀ h : O2, h ∉ U → qker h ≤ δ := fun h hh => (hδ₀b h hh).trans (le_max_left _ _)
  set η : ℝ := (1 + δ)/2 with hηdef
  have hδη : δ < η := by rw [hηdef]; linarith
  have hη1 : η < 1 := by rw [hηdef]; linarith
  have hη0 : 0 < η := by rw [hηdef]; linarith
  set V : Set O2 := {h : O2 | η < qker h} with hVdef
  have hVopen : IsOpen V := isOpen_lt continuous_const continuous_qker
  have hV1 : (1 : O2) ∈ V := by
    simp only [hVdef, Set.mem_ofPred_eq, qker_one]
    exact hη1
  have hβpos : 0 < haarO2.real V := by
    rw [Measure.real]
    exact ENNReal.toReal_pos (ne_of_gt (hVopen.measure_pos haarO2 ⟨1, hV1⟩)) (measure_ne_top _ _)
  set β : ℝ := haarO2.real V with hβdef
  have hβne : β ≠ 0 := ne_of_gt hβpos

  have hlow : ∀ n : ℕ, η ^ n * β ≤ fejerNorm n := by
    intro n
    have hqn : Integrable (fun h : O2 => qker h ^ n) haarO2 :=
      integrable_of_continuous (continuous_qker.pow n)
    have h1 : ∫ _ in V, (η ^ n : ℝ) ∂haarO2 ≤ ∫ h in V, qker h ^ n ∂haarO2 := by
      refine setIntegral_mono_on integrableOn_const hqn.integrableOn
        hVopen.measurableSet fun h hh => ?_
      exact pow_le_pow_left₀ (le_of_lt hη0) (le_of_lt hh) n
    have h2 : ∫ h in V, qker h ^ n ∂haarO2 ≤ fejerNorm n := by
      unfold fejerNorm
      exact setIntegral_le_integral hqn
        (Filter.Eventually.of_forall fun h => pow_nonneg (qker_nonneg h) n)
    rw [setIntegral_const, smul_eq_mul] at h1
    calc η ^ n * β = β * η ^ n := mul_comm _ _
      _ ≤ ∫ h in V, qker h ^ n ∂haarO2 := h1
      _ ≤ fejerNorm n := h2

  have hkey : ∀ n : ℕ, dist (fejerConv n Φ k) (Φ k) ≤ ε/4 + (2*C/β) * (δ/η) ^ n := by
    intro n
    have hnpos := fejerNorm_pos n
    have hDint : Integrable (fun h : O2 => ‖Φ (k * h) - Φ k‖ * qker h ^ n) haarO2 :=
      integrable_of_continuous ((hg.sub continuous_const).norm.mul (continuous_qker.pow n))
    rw [dist_eq_norm, fejerConv_sub hc n k, norm_smul]
    have hinv0 : (0:ℝ) ≤ (fejerNorm n)⁻¹ := le_of_lt (inv_pos.mpr hnpos)
    have hnn : ‖(fejerNorm n)⁻¹‖ = (fejerNorm n)⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hinv0]
    rw [hnn]
    have hstep1 : ‖∫ h, (Φ (k * h) - Φ k) * ((qker h ^ n : ℝ) : ℂ) ∂haarO2‖
        ≤ ∫ h, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarO2 := by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
      show ‖(Φ (k * h) - Φ k) * ((qker h ^ n : ℝ) : ℂ)‖ = ‖Φ (k * h) - Φ k‖ * qker h ^ n
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (qker_nonneg h) n)]
    have hsplit : ∫ h, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarO2
        = (∫ h in U, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarO2)
          + ∫ h in Uᶜ, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarO2 :=
      (integral_add_compl hUopen.measurableSet hDint).symm
    have hqn : Integrable (fun h : O2 => qker h ^ n) haarO2 :=
      integrable_of_continuous (continuous_qker.pow n)
    have hUb : ∫ h in U, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarO2 ≤ (ε/4) * fejerNorm n := by
      have hmono : ∫ h in U, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarO2
          ≤ ∫ h in U, (ε/4) * qker h ^ n ∂haarO2 := by
        refine setIntegral_mono_on hDint.integrableOn
          (integrable_of_continuous (continuous_const.mul (continuous_qker.pow n))).integrableOn
          hUopen.measurableSet fun h hh => ?_
        have hdist : dist (Φ (k * h)) (Φ k) < ε/4 := by
          simpa [hUdef, Metric.mem_ball] using hh
        rw [dist_eq_norm] at hdist
        exact mul_le_mul_of_nonneg_right (le_of_lt hdist) (pow_nonneg (qker_nonneg h) n)
      refine hmono.trans ?_
      rw [MeasureTheory.integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hε4)
      exact setIntegral_le_integral hqn
        (Filter.Eventually.of_forall fun h => pow_nonneg (qker_nonneg h) n)
    have hUcb : ∫ h in Uᶜ, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarO2 ≤ 2*C*δ^n := by
      have hmono : ∫ h in Uᶜ, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarO2
          ≤ ∫ _ in Uᶜ, (2*C*δ^n : ℝ) ∂haarO2 := by
        refine setIntegral_mono_on hDint.integrableOn integrableOn_const
          hUopen.measurableSet.compl fun h hh => ?_
        have h1 : ‖Φ (k * h) - Φ k‖ ≤ 2*C := by
          have hx := hCb (k*h)
          have hy := hCb k
          calc ‖Φ (k * h) - Φ k‖ ≤ ‖Φ (k * h)‖ + ‖Φ k‖ := norm_sub_le _ _
            _ ≤ 2*C := by rw [hCdef] at hx hy ⊢; linarith
        have h2 : qker h ^ n ≤ δ ^ n := pow_le_pow_left₀ (qker_nonneg h) (hδb h hh) n
        exact mul_le_mul h1 h2 (pow_nonneg (qker_nonneg h) n) (by positivity)
      refine hmono.trans ?_
      rw [setIntegral_const, smul_eq_mul]
      have hle1 : haarO2.real Uᶜ ≤ 1 := by
        have h1 : haarO2 Uᶜ ≤ 1 := by
          rw [← haarO2_univ]
          exact measure_mono (Set.subset_univ _)
        rw [Measure.real]
        calc (haarO2 Uᶜ).toReal ≤ (1 : ENNReal).toReal :=
          ENNReal.toReal_mono ENNReal.one_ne_top h1
          _ = 1 := ENNReal.toReal_one
      exact mul_le_of_le_one_left (by positivity) hle1
    have htotal : ∫ h, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarO2
        ≤ (ε/4) * fejerNorm n + 2*C*δ^n := by
      rw [hsplit]
      exact add_le_add hUb hUcb
    have hmain : (fejerNorm n)⁻¹ * ‖∫ h, (Φ (k*h) - Φ k) * ((qker h ^ n : ℝ):ℂ) ∂haarO2‖
        ≤ (fejerNorm n)⁻¹ * ((ε/4) * fejerNorm n + 2*C*δ^n) :=
      mul_le_mul_of_nonneg_left (hstep1.trans htotal) hinv0
    refine hmain.trans ?_
    rw [mul_add]
    have e1 : (fejerNorm n)⁻¹ * ((ε/4) * fejerNorm n) = ε/4 := by
      field_simp
    have hinvle : (fejerNorm n)⁻¹ ≤ ((η:ℝ)^n*β)⁻¹ :=
      inv_anti₀ (mul_pos (pow_pos hη0 n) hβpos) (hlow n)
    have e2 : (fejerNorm n)⁻¹ * (2*C*δ^n) ≤ ((η:ℝ)^n*β)⁻¹ * (2*C*δ^n) :=
      mul_le_mul_of_nonneg_right hinvle
        (mul_nonneg (mul_nonneg (by norm_num) hC0) (pow_nonneg hδ0 n))
    have e3 : ((η:ℝ)^n*β)⁻¹ * (2*C*δ^n) = (2*C/β) * (δ/η)^n :=
      aux_ratio C δ η β n (ne_of_gt hη0) hβne
    rw [e1]
    have := e2.trans_eq e3
    linarith

  have htail : Filter.Tendsto (fun n => (2*C/β) * (δ/η)^n) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n => ((δ/η) : ℝ)^n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hδ0 (le_of_lt hη0))
        ((div_lt_one hη0).mpr hδη)
    simpa using h1.const_mul (2*C/β)
  have hev : ∀ᶠ n in Filter.atTop, (2*C/β) * (δ/η)^n < ε/4 := htail.eventually (gt_mem_nhds hε4)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  calc dist (fejerConv n Φ k) (Φ k) ≤ ε/4 + (2*C/β)*(δ/η)^n := hkey n
    _ < ε/4 + ε/4 := by linarith [hN n hn]
    _ < ε := by linarith

/--
@isnad1 id=mem.2h3v.s9.726e3a03cf63 from=translated src=- shape=d82498ff vocab=32948b4e
-/
theorem fejerConv_mem_span {Φ : O2 → ℂ} (hc : Continuous Φ) {s : Finset (O2 → ℂ)}
    (hfin : ∀ k : O2, (fun x => Φ (x * k)) ∈ Submodule.span ℂ (s : Set (O2 → ℂ)))
    (n : ℕ) : fejerConv n Φ ∈ Submodule.span ℂ (s : Set (O2 → ℂ)) := by
  classical
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (s : Set (O2 → ℂ))) :=
    FiniteDimensional.span_of_finite ℂ s.finite_toSet
  set V : Submodule ℂ (O2 → ℂ) := Submodule.span ℂ (s : Set (O2 → ℂ)) with hVdef
  set T : O2 → V := fun h => ⟨fun x => Φ (x * h), hfin h⟩ with hTdef
  set b := Module.finBasis ℂ V with hbdef
  have hev : ∀ j, ∃ (m : ℕ) (e : Fin m → ℂ) (x : Fin m → O2),
      ∀ w : V, b.coord j w = ∑ l, e l * (w : O2 → ℂ) (x l) := fun j =>
    M4aP3C.TensorSplit.exists_eval_combination V (b.coord j)
  choose m e xs hev using hev
  have hcont : ∀ j, Continuous fun h : O2 => (b.coord j) (T h) := by
    intro j
    have heq : (fun h : O2 => (b.coord j) (T h))
        = fun h : O2 => ∑ l, e j l * Φ (xs j l * h) := by
      funext h
      rw [hev j (T h)]
    rw [heq]
    exact continuous_finsetSum _ fun l _ =>
      continuous_const.mul (hc.comp (continuous_const_mul (xs j l)))
  have hexp : ∀ k h : O2, Φ (k * h) = ∑ j, (b.coord j) (T h) * ((b j : O2 → ℂ) k) := by
    intro k h
    have h0 : Φ (k * h) = (T h : O2 → ℂ) k := rfl
    have h1 : ((T h : O2 → ℂ)) k = ((∑ j, (b.repr (T h)) j • b j : V) : O2 → ℂ) k := by
      rw [b.sum_repr (T h)]
    rw [h0, h1, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
  have hrepr : fejerConv n Φ = ∑ j,
      (((fejerNorm n)⁻¹ • ∫ h, (b.coord j) (T h) * ((qker h ^ n : ℝ) : ℂ) ∂haarO2 : ℂ)) •
        ((b j : O2 → ℂ)) := by
    funext k
    rw [Finset.sum_apply]
    unfold fejerConv
    have h1 : (fun h : O2 => Φ (k * h) * ((qker h ^ n : ℝ) : ℂ))
        = fun h : O2 => ∑ j, ((b j : O2 → ℂ) k) *
            ((b.coord j) (T h) * ((qker h ^ n : ℝ) : ℂ)) := by
      funext h
      rw [hexp k h, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1]
    have hswap := integral_finsetSum (μ := haarO2) Finset.univ
      (f := fun j (h : O2) => ((b j : O2 → ℂ) k) *
        ((b.coord j) (T h) * ((qker h ^ n : ℝ) : ℂ)))
      (fun j _ => integrable_of_continuous (continuous_const.mul ((hcont j).mul
        (Complex.continuous_ofReal.comp (continuous_qker.pow n)))))
    rw [hswap]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    ring
  rw [hrepr]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2

def entryCLM (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp
    ((ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)))

def coordFns : Fin 4 → (Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℂ) :=
  ![entryCLM 0 0, entryCLM 0 1, entryCLM 1 0, entryCLM 1 1]

def monom (β : Fin 4 → ℕ) : Matrix (Fin 2) (Fin 2) ℝ → ℂ :=
  fun M => ∏ α, (coordFns α M) ^ (β α)

def Pdeg (n : ℕ) : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℝ → ℂ) :=
  Submodule.span ℂ (Set.range fun β : {β : Fin 4 → ℕ // ∀ α, β α ≤ n} => monom ↑β)

/--
@isnad1 id=finite.0h1v.s5.7f8800f68095 from=translated src=- shape=fd3bc570 vocab=0244ee19
-/
scoped instance finite_expIndex (n : ℕ) : Finite {β : Fin 4 → ℕ // ∀ α, β α ≤ n} := by
  refine Finite.of_injective
    (fun β => (fun α => (⟨β.1 α, Nat.lt_succ_of_le (β.2 α)⟩ : Fin (n+1)))) ?_
  intro β γ hβγ
  apply Subtype.ext
  funext α
  exact congrArg Fin.val (congrFun hβγ α)

/--
@isnad1 id=finitedi.0h1v.s9.bb5fe1fe8fcc from=translated src=- shape=348bd117 vocab=48bf61d1
-/
theorem finiteDimensional_Pdeg (n : ℕ) : FiniteDimensional ℂ (Pdeg n) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

/--
@isnad1 id=mem.0h0v.s8.32aaa08da62a from=translated src=- shape=344fe896 vocab=269269cd
-/
theorem one_mem_polyFun : (fun _ : Matrix (Fin 2) (Fin 2) ℝ => (1 : ℂ)) ∈ polyFun := by
  refine Submodule.subset_span ⟨[], ?_⟩
  funext m
  simp

/--
@isnad1 id=mem.2h2v.s10.5f2bebb67c10 from=translated src=- shape=3dd06770 vocab=4ee36f07
-/
theorem polyFun_mul_mem {f g : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hf : f ∈ polyFun) (hg : g ∈ polyFun) : f * g ∈ polyFun := by
  have hSS : polyFun * polyFun ≤ polyFun := by
    unfold polyFun
    rw [Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro F ⟨F₁, ⟨l₁, rfl⟩, F₂, ⟨l₂, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨l₁ ++ l₂, ?_⟩
    funext M
    simp [List.map_append, List.prod_append]
  exact hSS (Submodule.mul_mem_mul hf hg)

/--
@isnad1 id=le.0h1v.s8.b6abd5e7d752 from=translated src=- shape=64689294 vocab=f8d78273
-/
theorem Pdeg_le_polyFun (n : ℕ) : Pdeg n ≤ polyFun := by
  refine Submodule.span_le.mpr ?_
  rintro F ⟨β, rfl⟩
  have hpow : ∀ (α : Fin 4) (m : ℕ), (fun M => (coordFns α M) ^ m) ∈ polyFun := by
    intro α m
    refine Submodule.subset_span ⟨List.replicate m (coordFns α), ?_⟩
    funext M
    simp [List.map_replicate, List.prod_replicate]
  have hmono : monom ↑β = ∏ α, (fun M => (coordFns α M) ^ ((β : Fin 4 → ℕ) α)) := by
    funext M
    rw [Finset.prod_apply]
    rfl
  show monom ↑β ∈ polyFun
  rw [hmono]
  refine Finset.prod_induction _ (· ∈ polyFun) (fun a b ha hb => polyFun_mul_mem ha hb)
    one_mem_polyFun (fun α _ => hpow α _)

/--
@isnad1 id=mem.2h4v.s10.6fd4ea7bbfae from=translated src=- shape=62786826 vocab=a8228b69
-/
theorem Pdeg_mul_mem {a b : ℕ} {f g : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hf : f ∈ Pdeg a) (hg : g ∈ Pdeg b) : f * g ∈ Pdeg (a + b) := by
  have hle : Pdeg a * Pdeg b ≤ Pdeg (a + b) := by
    unfold Pdeg
    rw [Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro F ⟨F₁, ⟨β₁, rfl⟩, F₂, ⟨β₂, rfl⟩, rfl⟩
    refine Submodule.subset_span
      ⟨⟨(β₁ : Fin 4 → ℕ) + (β₂ : Fin 4 → ℕ), fun α => add_le_add (β₁.2 α) (β₂.2 α)⟩, ?_⟩
    funext M
    simp [monom, Pi.mul_apply, ← Finset.prod_mul_distrib, pow_add]
  exact hle (Submodule.mul_mem_mul hf hg)

/--
@isnad1 id=mem.1h2v.s9.0ddd7d99091a from=translated src=- shape=361a1248 vocab=b127e846
-/
theorem pow_mem_Pdeg {f : Matrix (Fin 2) (Fin 2) ℝ → ℂ} (hf : f ∈ Pdeg 1) :
    ∀ n : ℕ, f ^ n ∈ Pdeg n
  | 0 => by
    rw [pow_zero]
    refine Submodule.subset_span ⟨⟨0, fun α => le_refl 0⟩, ?_⟩
    funext M
    simp [monom]
  | n + 1 => by
    rw [pow_succ]
    exact Pdeg_mul_mem (pow_mem_Pdeg hf n) hf

/--
@isnad1 id=mem.0h1v.s9.709985b19c1c from=translated src=- shape=b172cf67 vocab=ddc6502c
-/
theorem coordFn_mem_Pdeg_one (α : Fin 4) : (fun M => coordFns α M) ∈ Pdeg 1 := by
  refine Submodule.subset_span
    ⟨⟨Pi.single α 1, fun γ => ?_⟩, ?_⟩
  · by_cases hγ : γ = α
    · subst hγ; simp
    · simp [Pi.single_eq_of_ne hγ]
  · funext M
    show monom (Pi.single α 1) M = coordFns α M
    unfold monom
    rw [Fintype.prod_eq_single α (fun γ hγ => by simp [Pi.single_eq_of_ne hγ])]
    simp

/--
@isnad1 id=mem.0h1v.s8.1d33b41cc12c from=translated src=- shape=6e387bf6 vocab=fba03919
-/
theorem const_mem_Pdeg_one (c : ℂ) :
    (fun _ : Matrix (Fin 2) (Fin 2) ℝ => c) ∈ Pdeg 1 := by
  have h1 : (fun _ : Matrix (Fin 2) (Fin 2) ℝ => (1 : ℂ)) ∈ Pdeg 1 := by
    refine Submodule.subset_span ⟨⟨0, fun α => Nat.zero_le 1⟩, ?_⟩
    funext M
    simp [monom]
  have heq : (fun _ : Matrix (Fin 2) (Fin 2) ℝ => c)
      = c • (fun _ : Matrix (Fin 2) (Fin 2) ℝ => (1 : ℂ)) := by
    funext M
    simp
  rw [heq]
  exact Submodule.smul_mem (Pdeg 1) c h1

def aker (h : O2) : Matrix (Fin 2) (Fin 2) ℝ → ℝ :=
  fun M => (2 + Matrix.trace (star M * (h : Matrix (Fin 2) (Fin 2) ℝ))) / 4

/--
@isnad1 id=eq.0h2v.s9.53577cf65cee from=translated src=- shape=12b0ed0b vocab=2c52a312
-/
theorem aker_coe (h k : O2) : aker h (k : Matrix (Fin 2) (Fin 2) ℝ) = qker (k⁻¹ * h) := by
  unfold aker qker
  congr 2

/--
@isnad1 id=continuo.0h1v.s8.74c153a01587 from=translated src=- shape=8dbc80ff vocab=c141ae45
-/
theorem continuous_aker (x : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous fun h : O2 => aker h x := by
  have hmul : Continuous fun h : O2 => star x * (h : Matrix (Fin 2) (Fin 2) ℝ) :=
    Continuous.matrix_mul continuous_const continuous_subtype_val
  have htr : Continuous fun h : O2 =>
      Matrix.trace (star x * (h : Matrix (Fin 2) (Fin 2) ℝ)) :=
    Continuous.matrix_trace hmul
  exact (continuous_const.add htr).div_const 4

/--
@isnad1 id=mem.0h1v.s8.a5b37916e7d0 from=translated src=- shape=d9c11ef6 vocab=5e59996c
-/
theorem akerC_mem_Pdeg_one (h : O2) :
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => ((aker h M : ℝ) : ℂ)) ∈ Pdeg 1 := by
  set H : Matrix (Fin 2) (Fin 2) ℝ := (h : Matrix (Fin 2) (Fin 2) ℝ) with hH
  have hexp : (fun M : Matrix (Fin 2) (Fin 2) ℝ => ((aker h M : ℝ) : ℂ))
      = (fun _ => (1/2 : ℂ))
        + ((((H 0 0 : ℝ) : ℂ) / 4) • fun M : Matrix (Fin 2) (Fin 2) ℝ => ((M 0 0 : ℝ) : ℂ))
        + ((((H 0 1 : ℝ) : ℂ) / 4) • fun M : Matrix (Fin 2) (Fin 2) ℝ => ((M 0 1 : ℝ) : ℂ))
        + ((((H 1 0 : ℝ) : ℂ) / 4) • fun M : Matrix (Fin 2) (Fin 2) ℝ => ((M 1 0 : ℝ) : ℂ))
        + ((((H 1 1 : ℝ) : ℂ) / 4) • fun M : Matrix (Fin 2) (Fin 2) ℝ => ((M 1 1 : ℝ) : ℂ)) := by
    funext M
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    unfold aker
    rw [← hH, Matrix.trace_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, star_trivial]
    push_cast
    ring
  rw [hexp]
  have m00 : (fun M : Matrix (Fin 2) (Fin 2) ℝ => ((M 0 0 : ℝ) : ℂ)) ∈ Pdeg 1 := coordFn_mem_Pdeg_one 0
  have m01 : (fun M : Matrix (Fin 2) (Fin 2) ℝ => ((M 0 1 : ℝ) : ℂ)) ∈ Pdeg 1 := coordFn_mem_Pdeg_one 1
  have m10 : (fun M : Matrix (Fin 2) (Fin 2) ℝ => ((M 1 0 : ℝ) : ℂ)) ∈ Pdeg 1 := coordFn_mem_Pdeg_one 2
  have m11 : (fun M : Matrix (Fin 2) (Fin 2) ℝ => ((M 1 1 : ℝ) : ℂ)) ∈ Pdeg 1 := coordFn_mem_Pdeg_one 3
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (const_mem_Pdeg_one _) (Submodule.smul_mem _ _ m00)) (Submodule.smul_mem _ _ m01))
    (Submodule.smul_mem _ _ m10)) (Submodule.smul_mem _ _ m11)

def restrictO2 : (Matrix (Fin 2) (Fin 2) ℝ → ℂ) →ₗ[ℂ] (O2 → ℂ) where
  toFun F := fun k => F (k : Matrix (Fin 2) (Fin 2) ℝ)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/--
@isnad1 id=ex.1h2v.s9.9386ee56e4ad from=translated src=- shape=3021c3fd vocab=686c8252
-/
theorem exists_polyFun_fejerConv {Φ : O2 → ℂ} (hc : Continuous Φ) (n : ℕ) :
    ∃ F ∈ polyFun, ∀ k : O2, fejerConv n Φ k = F (k : Matrix (Fin 2) (Fin 2) ℝ) := by
  classical

  have hsub : ∀ k : O2, (∫ h, Φ (k * h) * ((qker h ^ n : ℝ) : ℂ) ∂haarO2)
      = ∫ h, Φ h * ((aker h (k : Matrix (Fin 2) (Fin 2) ℝ) ^ n : ℝ) : ℂ) ∂haarO2 := by
    intro k
    calc ∫ h, Φ (k * h) * ((qker h ^ n : ℝ) : ℂ) ∂haarO2
        = ∫ h, Φ (k * h) * ((qker (k⁻¹ * (k * h)) ^ n : ℝ) : ℂ) ∂haarO2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
          show Φ (k * h) * ((qker h ^ n : ℝ) : ℂ)
            = Φ (k * h) * ((qker (k⁻¹ * (k * h)) ^ n : ℝ) : ℂ)
          rw [inv_mul_cancel_left]
      _ = ∫ h, Φ h * ((qker (k⁻¹ * h) ^ n : ℝ) : ℂ) ∂haarO2 :=
          integral_translate k (fun h => Φ h * ((qker (k⁻¹ * h) ^ n : ℝ) : ℂ))
      _ = ∫ h, Φ h * ((aker h (k : Matrix (Fin 2) (Fin 2) ℝ) ^ n : ℝ) : ℂ) ∂haarO2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
          show Φ h * ((qker (k⁻¹ * h) ^ n : ℝ) : ℂ)
            = Φ h * ((aker h (k : Matrix (Fin 2) (Fin 2) ℝ) ^ n : ℝ) : ℂ)
          rw [aker_coe]
  haveI : FiniteDimensional ℂ (Pdeg n) := finiteDimensional_Pdeg n

  have hmemW : ∀ h : O2,
      (fun M : Matrix (Fin 2) (Fin 2) ℝ => ((aker h M ^ n : ℝ) : ℂ)) ∈ Pdeg n := by
    intro h
    have h1 : (fun M : Matrix (Fin 2) (Fin 2) ℝ => ((aker h M : ℝ) : ℂ)) ^ n ∈ Pdeg n :=
      pow_mem_Pdeg (akerC_mem_Pdeg_one h) n
    have heq : (fun M : Matrix (Fin 2) (Fin 2) ℝ => ((aker h M ^ n : ℝ) : ℂ))
        = (fun M : Matrix (Fin 2) (Fin 2) ℝ => ((aker h M : ℝ) : ℂ)) ^ n := by
      funext M
      simp only [Pi.pow_apply]
      push_cast
      ring
    rw [heq]
    exact h1
  set T : O2 → (Pdeg n) :=
    fun h => ⟨fun M => ((aker h M ^ n : ℝ) : ℂ), hmemW h⟩ with hTdef
  set b := Module.finBasis ℂ (Pdeg n) with hbdef
  have hev : ∀ j, ∃ (m : ℕ) (e : Fin m → ℂ) (x : Fin m → Matrix (Fin 2) (Fin 2) ℝ),
      ∀ w : (Pdeg n), b.coord j w = ∑ l, e l * (w : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (x l) :=
    fun j => M4aP3C.TensorSplit.exists_eval_combination (Pdeg n) (b.coord j)
  choose m e xs hev using hev
  have hcont : ∀ j, Continuous fun h : O2 => (b.coord j) (T h) := by
    intro j
    have heq : (fun h : O2 => (b.coord j) (T h))
        = fun h : O2 => ∑ l, e j l * ((aker h (xs j l) ^ n : ℝ) : ℂ) := by
      funext h
      rw [hev j (T h)]
    rw [heq]
    exact continuous_finsetSum _ fun l _ => continuous_const.mul
      (Complex.continuous_ofReal.comp ((continuous_aker (xs j l)).pow n))
  refine ⟨∑ j, (((fejerNorm n)⁻¹ • ∫ h, Φ h * (b.coord j) (T h) ∂haarO2 : ℂ)) •
    ((b j : Matrix (Fin 2) (Fin 2) ℝ → ℂ)), ?_, ?_⟩
  · exact Pdeg_le_polyFun n (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2)
  · intro k
    unfold fejerConv
    rw [hsub k]
    have hexp : ∀ h : O2, Φ h * ((aker h (k : Matrix (Fin 2) (Fin 2) ℝ) ^ n : ℝ) : ℂ)
        = ∑ j, ((b j : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (k : Matrix (Fin 2) (Fin 2) ℝ)) *
            (Φ h * (b.coord j) (T h)) := by
      intro h
      have h0 : ((aker h ((k : Matrix (Fin 2) (Fin 2) ℝ)) ^ n : ℝ) : ℂ)
          = (T h : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (k : Matrix (Fin 2) (Fin 2) ℝ) := rfl
      have h1 : ((T h : Matrix (Fin 2) (Fin 2) ℝ → ℂ)) (k : Matrix (Fin 2) (Fin 2) ℝ)
          = ((∑ j, (b.repr (T h)) j • b j : (Pdeg n)) :
              Matrix (Fin 2) (Fin 2) ℝ → ℂ) (k : Matrix (Fin 2) (Fin 2) ℝ) := by
        rw [b.sum_repr (T h)]
      rw [h0, h1, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
    have hswap := integral_finsetSum (μ := haarO2) Finset.univ
      (f := fun j (h : O2) =>
        ((b j : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (k : Matrix (Fin 2) (Fin 2) ℝ)) *
          (Φ h * (b.coord j) (T h)))
      (fun j _ => integrable_of_continuous (continuous_const.mul (hc.mul (hcont j))))
    rw [hswap, Finset.smul_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    ring

/--
@isnad1 id=ex.2h1v.s10.b5e87a94f50f from=translated src=- shape=5de96021 vocab=f871c0d6
-/
theorem exists_polyFun_eq_of_continuous_of_rightFinite
    (Φ : O2 → ℂ) (hc : Continuous Φ)
    (hfin : ∃ s : Finset (O2 → ℂ), ∀ k : O2,
      (fun x => Φ (x * k)) ∈ Submodule.span ℂ (s : Set (O2 → ℂ))) :
    ∃ F ∈ polyFun, ∀ k : O2, Φ k = F (k : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨s, hfin⟩ := hfin
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (s : Set (O2 → ℂ))) :=
    FiniteDimensional.span_of_finite ℂ s.finite_toSet
  set V : Submodule ℂ (O2 → ℂ) := Submodule.span ℂ (s : Set (O2 → ℂ)) with hVdef
  set R : Submodule ℂ (O2 → ℂ) := polyFun.map restrictO2 with hRdef
  have hmem : ∀ n : ℕ, fejerConv n Φ ∈ V ⊓ R := by
    intro n
    refine Submodule.mem_inf.mpr ⟨fejerConv_mem_span hc hfin n, ?_⟩
    obtain ⟨F, hF, hFeq⟩ := exists_polyFun_fejerConv hc n
    exact Submodule.mem_map.mpr ⟨F, hF, by funext k; exact (hFeq k).symm⟩
  haveI : FiniteDimensional ℂ (V ⊓ R : Submodule ℂ (O2 → ℂ)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hclosed : IsClosed ((V ⊓ R : Submodule ℂ (O2 → ℂ)) : Set (O2 → ℂ)) :=
    Submodule.closed_of_finiteDimensional _
  have htend : Filter.Tendsto (fun n => fejerConv n Φ) Filter.atTop (nhds Φ) := by
    rw [tendsto_pi_nhds]
    exact fun k => fejerConv_tendsto hc k
  have hΦ : Φ ∈ V ⊓ R :=
    hclosed.mem_of_tendsto htend (Filter.Eventually.of_forall hmem)
  obtain ⟨F, hF, hFΦ⟩ := Submodule.mem_map.mp (Submodule.mem_inf.mp hΦ).2
  exact ⟨F, hF, fun k => by rw [← hFΦ]; rfl⟩

end M4aP3C.O2Finite
open scoped _root_.P2MW.S_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite.M4aP3C _root_.P2MW.S_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite.M4aP3C.O2Finite
open scoped _root_.P2MW.S_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite.M4aP3C

end
open scoped _root_.P2MW.S_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite.M4aP3C _root_.P2MW.S_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite.M4aP3C.O2Finite

noncomputable section

/--
@isnad1 id=ex.2h1v.s13.ead5ab76f758 from=translated src=- shape=2f8fb30a vocab=f6a88011
-/
theorem solution
    (Φ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ) (hc : Continuous Φ)
    (hfin : ∃ s : Finset (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ),
      ∀ k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ),
        (fun x => Φ (x * k)) ∈ Submodule.span ℂ (s : Set (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ))) :
    ∃ F ∈ Submodule.span ℂ
        {F : Matrix (Fin 2) (Fin 2) ℝ → ℂ |
          ∃ l : List (Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod},
      ∀ k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ), Φ k = F (k : Matrix (Fin 2) (Fin 2) ℝ) :=
  M4aP3C.O2Finite.exists_polyFun_eq_of_continuous_of_rightFinite Φ hc hfin

end
open scoped _root_.P2MW.S_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite.M4aP3C _root_.P2MW.S_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite.M4aP3C.O2Finite

