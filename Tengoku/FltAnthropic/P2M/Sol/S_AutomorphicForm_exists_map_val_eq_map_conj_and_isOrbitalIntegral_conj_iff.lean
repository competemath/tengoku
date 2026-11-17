import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_LocalOrbitalBase

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_exists_map_val_eq_map_conj_and_isOrbitalIntegral_conj_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_exists_map_val_eq_map_conj_and_isOrbitalIntegral_conj_iff.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_exists_map_val_eq_map_conj_and_isOrbitalIntegral_conj_iff

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

namespace KcOrbitalConjTransport

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => v.adicCompletion K
local notation "G₂" => GL (Fin 2) (v.adicCompletion K)

/--
@isnad1 id=iff.0h5v.s12.62f5a500690a from=translated src=- shape=8a637558 vocab=d2167110
-/
theorem mem_localCentralizer_conj_iff (x γ g : G₂) :
    x * g * x⁻¹ ∈ localCentralizer K v (x * γ * x⁻¹) ↔ g ∈ localCentralizer K v γ := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * γ = x⁻¹ * (x * g * x⁻¹ * (x * γ * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * γ * x⁻¹ * (x * g * x⁻¹)) * x := by rw [h]
      _ = γ * g := by group
  · intro h
    calc x * g * x⁻¹ * (x * γ * x⁻¹) = x * (g * γ) * x⁻¹ := by group
      _ = x * (γ * g) * x⁻¹ := by rw [h]
      _ = x * γ * x⁻¹ * (x * g * x⁻¹) := by group

noncomputable def conjEquiv (x γ : G₂) : localCentralizer K v γ ≃ₜ* localCentralizer K v (x * γ * x⁻¹) where
  toFun t := ⟨x * t * x⁻¹, (mem_localCentralizer_conj_iff K v x γ t).2 t.2⟩
  invFun t' := ⟨x⁻¹ * t' * x, by
    have h := (mem_localCentralizer_conj_iff K v x⁻¹ (x * γ * x⁻¹) t').2 t'.2
    simpa [mul_assoc] using h⟩
  left_inv t := by ext; simp [mul_assoc]
  right_inv t' := by ext; simp [mul_assoc]
  map_mul' s t := by ext; simp [mul_assoc]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

/--
@isnad1 id=eq.0h5v.s15.ea400c1e00a1 from=translated src=- shape=6bcef77a vocab=28e331df
-/
@[scoped simp] theorem coe_conjEquiv (x γ : G₂) (t : localCentralizer K v γ) :
    ((conjEquiv K v x γ t : localCentralizer K v (x * γ * x⁻¹)) : G₂) = x * t * x⁻¹ := rfl

/--
@isnad1 id=eq.0h5v.s15.98313a7c2423 from=translated src=- shape=6e03baa3 vocab=34e6abff
-/
@[scoped simp] theorem coe_conjEquiv_symm (x γ : G₂) (t' : localCentralizer K v (x * γ * x⁻¹)) :
    (((conjEquiv K v x γ).symm t' : localCentralizer K v γ) : G₂) = x⁻¹ * t' * x := rfl

/--
@isnad1 id=eq.0h4v.s15.9aa8f1a6e9ab from=translated src=- shape=f4c89f75 vocab=1e6bca45
-/
theorem val_comp_conjEquiv (x γ : G₂) :
    (Subtype.val : localCentralizer K v (x * γ * x⁻¹) → G₂) ∘ (conjEquiv K v x γ) =
      (fun g : G₂ => x * g * x⁻¹) ∘ (Subtype.val : localCentralizer K v γ → G₂) := rfl

/--
@isnad1 id=eq.0h4v.s16.1c24ca0d6699 from=translated src=- shape=ac2e6506 vocab=d2c691bd
-/
theorem conjEquiv_symm_comp (x γ : G₂) :
    ((conjEquiv K v x γ).symm : localCentralizer K v (x * γ * x⁻¹) → localCentralizer K v γ) ∘
        (conjEquiv K v x γ) = id := by
  funext t
  exact (conjEquiv K v x γ).symm_apply_apply t

/--
@isnad1 id=isorbita.1h7v.s15.6063f788b6f7 from=translated src=- shape=c4b312e9 vocab=8e5e03e8
-/
theorem isOrbitalIntegral_of_conj (f : G₂ → ℂ) (x t : G₂)
    (τ' : @Measure (localCentralizer K v (x * t * x⁻¹)) (localCentralizerBorel K v (x * t * x⁻¹)))
    (I : ℂ) (h : IsOrbitalIntegral K v (x * t * x⁻¹) τ' f I) :
    IsOrbitalIntegral K v t
      (@Measure.map _ _ (localCentralizerBorel K v (x * t * x⁻¹)) (localCentralizerBorel K v t)
        (conjEquiv K v x t).symm τ') f I := by
  letI : MeasurableSpace G₂ := localGLBorel K v
  haveI : BorelSpace G₂ := borelSpace_localGLBorel K v
  letI := localCentralizerBorel K v (x * t * x⁻¹)
  letI := localCentralizerBorel K v t
  haveI : BorelSpace (localCentralizer K v (x * t * x⁻¹)) := ⟨rfl⟩
  haveI : BorelSpace (localCentralizer K v t) := ⟨rfl⟩
  haveI := isHaarMeasure_localHaar K v
  obtain ⟨w', ⟨hw'0, hw'm, hw'c, hw's⟩, hI⟩ := h
  refine ⟨fun y => w' (x * y), ⟨fun y => hw'0 _, hw'm.comp (measurable_const_mul x), ?_, ?_⟩, ?_⟩
  · exact hw'c.comp_homeomorph (Homeomorph.mulLeft x)
  · intro y hy
    have hy' : f ((x * y)⁻¹ * (x * t * x⁻¹) * (x * y)) ≠ 0 := by
      have : (x * y)⁻¹ * (x * t * x⁻¹) * (x * y) = y⁻¹ * t * y := by group
      rwa [this]
    have hemb : MeasurableEmbedding ((conjEquiv K v x t).symm : localCentralizer K v (x * t * x⁻¹) → _) :=
      (conjEquiv K v x t).symm.toHomeomorph.measurableEmbedding
    rw [hemb.integral_map]
    have hpt : ∀ s' : localCentralizer K v (x * t * x⁻¹),
        w' (x * ((((conjEquiv K v x t).symm s' : localCentralizer K v t) : G₂) * y)) = w' ((s' : G₂) * (x * y)) := by
      intro s'
      rw [coe_conjEquiv_symm]
      congr 1
      group
    simp_rw [hpt]
    exact hw's (x * y) hy'
  · rw [hI]
    have hL := integral_mul_left_eq_self (μ := localHaar K v)
      (fun z : G₂ => f (z⁻¹ * t * z) * ((w' (x * z) : ℝ) : ℂ)) x⁻¹
    rw [← hL]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    have h1 : (x⁻¹ * z)⁻¹ * t * (x⁻¹ * z) = z⁻¹ * (x * t * x⁻¹) * z := by group
    rw [h1, mul_inv_cancel_left]

/--
@isnad1 id=isorbita.1h7v.s15.4ea91c0ac40d from=translated src=- shape=a474b803 vocab=f83a8df4
-/
theorem isOrbitalIntegral_conj (f : G₂ → ℂ) (x t : G₂)
    (τ : @Measure (localCentralizer K v t) (localCentralizerBorel K v t))
    (I : ℂ) (h : IsOrbitalIntegral K v t τ f I) :
    IsOrbitalIntegral K v (x * t * x⁻¹)
      (@Measure.map _ _ (localCentralizerBorel K v t) (localCentralizerBorel K v (x * t * x⁻¹))
        (conjEquiv K v x t) τ) f I := by
  letI : MeasurableSpace G₂ := localGLBorel K v
  haveI : BorelSpace G₂ := borelSpace_localGLBorel K v
  letI := localCentralizerBorel K v (x * t * x⁻¹)
  letI := localCentralizerBorel K v t
  haveI : BorelSpace (localCentralizer K v (x * t * x⁻¹)) := ⟨rfl⟩
  haveI : BorelSpace (localCentralizer K v t) := ⟨rfl⟩
  haveI := isHaarMeasure_localHaar K v
  obtain ⟨w, ⟨hw0, hwm, hwc, hws⟩, hI⟩ := h
  refine ⟨fun y => w (x⁻¹ * y), ⟨fun y => hw0 _, hwm.comp (measurable_const_mul x⁻¹), ?_, ?_⟩, ?_⟩
  · exact hwc.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
  · intro y hy
    have hy' : f ((x⁻¹ * y)⁻¹ * t * (x⁻¹ * y)) ≠ 0 := by
      have : (x⁻¹ * y)⁻¹ * t * (x⁻¹ * y) = y⁻¹ * (x * t * x⁻¹) * y := by group
      rwa [this]
    have hemb : MeasurableEmbedding (conjEquiv K v x t : localCentralizer K v t → _) :=
      (conjEquiv K v x t).toHomeomorph.measurableEmbedding
    rw [hemb.integral_map]
    have hpt : ∀ s : localCentralizer K v t,
        w (x⁻¹ * (((conjEquiv K v x t s : localCentralizer K v (x * t * x⁻¹)) : G₂) * y)) =
          w ((s : G₂) * (x⁻¹ * y)) := by
      intro s
      rw [coe_conjEquiv]
      congr 1
      group
    simp_rw [hpt]
    exact hws (x⁻¹ * y) hy'
  · rw [hI]
    have hL := integral_mul_left_eq_self (μ := localHaar K v)
      (fun z : G₂ => f (z⁻¹ * (x * t * x⁻¹) * z) * ((w (x⁻¹ * z) : ℝ) : ℂ)) x
    rw [← hL]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    have h1 : (x * z)⁻¹ * (x * t * x⁻¹) * (x * z) = z⁻¹ * t * z := by group
    rw [h1, inv_mul_cancel_left]

/--
@isnad1 id=eq.0h5v.s15.a65ff4c6b152 from=translated src=- shape=0947b648 vocab=a4ed67eb
-/
theorem map_val_map_conjEquiv (x γ : G₂) (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    @Measure.map _ _ (localCentralizerBorel K v (x * γ * x⁻¹)) (localGLBorel K v) Subtype.val
        (@Measure.map _ _ (localCentralizerBorel K v γ) (localCentralizerBorel K v (x * γ * x⁻¹))
          (conjEquiv K v x γ) τ) =
      @Measure.map _ _ (localGLBorel K v) (localGLBorel K v) (fun g : G₂ => x * g * x⁻¹)
        (@Measure.map _ _ (localCentralizerBorel K v γ) (localGLBorel K v) Subtype.val τ) := by
  letI : MeasurableSpace G₂ := localGLBorel K v
  haveI : BorelSpace G₂ := borelSpace_localGLBorel K v
  letI := localCentralizerBorel K v γ
  letI := localCentralizerBorel K v (x * γ * x⁻¹)
  haveI : BorelSpace (localCentralizer K v γ) := ⟨rfl⟩
  haveI : BorelSpace (localCentralizer K v (x * γ * x⁻¹)) := ⟨rfl⟩
  have hvalγ : Measurable (Subtype.val : localCentralizer K v γ → G₂) := continuous_subtype_val.measurable
  have hvalγ' : Measurable (Subtype.val : localCentralizer K v (x * γ * x⁻¹) → G₂) :=
    continuous_subtype_val.measurable
  have hcx : Measurable fun h : G₂ => x * h * x⁻¹ :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have he : Measurable (conjEquiv K v x γ : localCentralizer K v γ → localCentralizer K v (x * γ * x⁻¹)) :=
    (map_continuous (conjEquiv K v x γ)).measurable
  rw [Measure.map_map hvalγ' he, val_comp_conjEquiv, ← Measure.map_map hcx hvalγ]

/--
@isnad1 id=ishaarme.1h5v.s15.4fe4beb0a409 from=translated src=- shape=1124bc85 vocab=03fa475b
-/
theorem isHaarMeasure_map_conjEquiv (x γ : G₂) (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ) :
    @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v (x * γ * x⁻¹))
      (@Measure.map _ _ (localCentralizerBorel K v γ) (localCentralizerBorel K v (x * γ * x⁻¹))
        (conjEquiv K v x γ) τ) := by
  letI : MeasurableSpace G₂ := localGLBorel K v
  haveI : BorelSpace G₂ := borelSpace_localGLBorel K v
  letI := localCentralizerBorel K v γ
  letI := localCentralizerBorel K v (x * γ * x⁻¹)
  haveI : BorelSpace (localCentralizer K v γ) := ⟨rfl⟩
  haveI : BorelSpace (localCentralizer K v (x * γ * x⁻¹)) := ⟨rfl⟩
  haveI := hτ
  exact (conjEquiv K v x γ).isHaarMeasure_map τ

/--
@isnad1 id=ex.0h5v.s14.e5503eddb937 from=translated src=- shape=ca84ac9d vocab=6760022b
-/
theorem main (γ x : G₂) (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    ∃ τ' : @Measure (localCentralizer K v (x * γ * x⁻¹)) (localCentralizerBorel K v (x * γ * x⁻¹)),
      @Measure.map _ _ (localCentralizerBorel K v (x * γ * x⁻¹)) (localGLBorel K v) Subtype.val τ' =
        @Measure.map _ _ (localGLBorel K v) (localGLBorel K v) (fun g : G₂ => x * g * x⁻¹)
          (@Measure.map _ _ (localCentralizerBorel K v γ) (localGLBorel K v) Subtype.val τ) ∧
      (@Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ →
        @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v (x * γ * x⁻¹)) τ') ∧
      ∀ (f : G₂ → ℂ) (I : ℂ), IsOrbitalIntegral K v (x * γ * x⁻¹) τ' f I ↔ IsOrbitalIntegral K v γ τ f I := by
  letI := localCentralizerBorel K v γ
  letI := localCentralizerBorel K v (x * γ * x⁻¹)
  haveI : BorelSpace (localCentralizer K v γ) := ⟨rfl⟩
  haveI : BorelSpace (localCentralizer K v (x * γ * x⁻¹)) := ⟨rfl⟩
  refine ⟨Measure.map (conjEquiv K v x γ) τ, map_val_map_conjEquiv K v x γ τ,
    isHaarMeasure_map_conjEquiv K v x γ τ, fun f I => ⟨fun h => ?_, fun h => isOrbitalIntegral_conj K v f x γ τ I h⟩⟩

  have h' := isOrbitalIntegral_of_conj K v f x γ (Measure.map (conjEquiv K v x γ) τ) I h
  have he : Measurable (conjEquiv K v x γ : localCentralizer K v γ → localCentralizer K v (x * γ * x⁻¹)) :=
    (map_continuous (conjEquiv K v x γ)).measurable
  have he' : Measurable ((conjEquiv K v x γ).symm : localCentralizer K v (x * γ * x⁻¹) → localCentralizer K v γ) :=
    (map_continuous (conjEquiv K v x γ).symm).measurable
  rwa [Measure.map_map he' he, conjEquiv_symm_comp, Measure.map_id] at h'

end KcOrbitalConjTransport
open scoped _root_.P2MW.S_AutomorphicForm_exists_map_val_eq_map_conj_and_isOrbitalIntegral_conj_iff.KcOrbitalConjTransport

/--
@isnad1 id=ex.0h5v.s14.e5503eddb937 from=translated src=- shape=ca84ac9d vocab=6760022b
-/
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ x : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ)) :
    ∃ τ' : @Measure (AutomorphicForm.localCentralizer K v (x * γ * x⁻¹))
        (AutomorphicForm.localCentralizerBorel K v (x * γ * x⁻¹)),
      @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v (x * γ * x⁻¹)) (AutomorphicForm.localGLBorel K v)
          Subtype.val τ' =
        @Measure.map _ _ (AutomorphicForm.localGLBorel K v) (AutomorphicForm.localGLBorel K v)
          (fun g : GL (Fin 2) (v.adicCompletion K) => x * g * x⁻¹)
          (@Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
            Subtype.val τ) ∧
      (@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
        @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (x * γ * x⁻¹)) τ') ∧
      ∀ (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ),
        AutomorphicForm.IsOrbitalIntegral K v (x * γ * x⁻¹) τ' f I ↔
          AutomorphicForm.IsOrbitalIntegral K v γ τ f I :=
  KcOrbitalConjTransport.main K v γ x τ
