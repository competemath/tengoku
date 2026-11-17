import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_LocalOrbitalBase

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped ENNReal NNReal

noncomputable section

namespace AutomorphicForm
export _root_.AutomorphicForm (localIntegralSet isOpen_localIntegralSet localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localHaar_localIntegralSet localCentralizer localCentralizerBorel IsOrbitalIntegral)
open _root_.AutomorphicForm

namespace CentValue

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/--
@isnad1 id=eq.0h4v.s12.9941a5898967 from=translated src=- shape=dbac80b5 vocab=c8950fb1
-/
theorem scalar_mul_comm (c : (v.adicCompletion K)ˣ) (g : GL (Fin 2) (v.adicCompletion K)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (c : v.adicCompletion K) (fun r => Commute.all _ r) _).eq

/--
@isnad1 id=eq.0h4v.s12.2a8220b793da from=translated src=- shape=0ab018e2 vocab=f711e221
-/
theorem conj_scalar (c : (v.adicCompletion K)ˣ) (x : GL (Fin 2) (v.adicCompletion K)) :
    x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c * x = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  rw [mul_assoc, scalar_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

/--
@isnad1 id=mem.0h4v.s11.ecd6fa2c2863 from=translated src=- shape=7ba7a844 vocab=afa78432
-/
theorem mem_localCentralizer_scalar (c : (v.adicCompletion K)ˣ) (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact scalar_mul_comm K v c g

/--
@isnad1 id=secondco.0h2v.s8.28d8c3eb92a3 from=translated src=- shape=98b1da0d vocab=fb83635a
-/
theorem secondCountableTopology_localGL : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

def centralizerEquiv (c : (v.adicCompletion K)ˣ) :
    localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ≃* GL (Fin 2) (v.adicCompletion K) where
  toFun := Subtype.val
  invFun g := ⟨g, mem_localCentralizer_scalar K v c g⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def centralizerHomeo (c : (v.adicCompletion K)ˣ) :
    localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ≃ₜ GL (Fin 2) (v.adicCompletion K) where
  toEquiv := (centralizerEquiv K v c).toEquiv
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

end CentValue

end AutomorphicForm

end

open _root_.AutomorphicForm open _root_.P2MW.S_AutomorphicForm_mul_measure_localIntegralSet_eq_apply_of_isOrbitalIntegral_scalar.AutomorphicForm

/--
@isnad1 id=eq.3h6v.s13.b22e90604638 from=translated src=- shape=09bd600e vocab=a7f025b1
-/
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : ∃ c : (v.adicCompletion K)ˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegral K v γ τ fv I) :
    letI := AutomorphicForm.localCentralizerBorel K v γ
    I * ((τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v}).toReal : ℂ) =
      fv γ := by
  obtain ⟨c, rfl⟩ := hγ

  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := borelSpace_localGLBorel K v
  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion K)) := locallyCompactSpace_localGL K v
  haveI : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) := CentValue.secondCountableTopology_localGL K v
  haveI : (localHaar K v).IsHaarMeasure := isHaarMeasure_localHaar K v
  letI : MeasurableSpace (localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :=
    localCentralizerBorel K v _
  haveI : BorelSpace (localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) := ⟨rfl⟩
  haveI := hτ
  obtain ⟨w, ⟨hw0, hwm, hwc, hsec⟩, rfl⟩ := hI

  simp only [CentValue.conj_scalar] at hsec ⊢
  rw [integral_const_mul]
  by_cases hf : fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 0
  · rw [hf, zero_mul, zero_mul]

  set e := CentValue.centralizerHomeo K v c with he_def
  have he : (e : localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) → GL (Fin 2) (v.adicCompletion K))
      = Subtype.val := rfl
  have h1 : ∫ t : localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c), w (e t) ∂τ = 1 := by
    simpa only [he, mul_one] using hsec 1 hf
  haveI hτG : Measure.IsHaarMeasure (Measure.map (⇑e) τ) :=
    (CentValue.centralizerEquiv K v c).isHaarMeasure_map τ continuous_subtype_val (continuous_id.subtype_mk _)

  have huniq := Measure.isMulLeftInvariant_eq_smul (Measure.map (⇑e) τ) (localHaar K v)

  have hmass : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ localIntegralSet K v} =
      ((Measure.map (⇑e) τ).haarScalarFactor (localHaar K v) : ℝ≥0∞) := by
    have hK : MeasurableSet (localIntegralSet K v) := (isOpen_localIntegralSet K v).measurableSet
    have h := congrArg (fun m : Measure (GL (Fin 2) (v.adicCompletion K)) => m (localIntegralSet K v)) huniq
    simp only [Measure.smul_apply, localHaar_localIntegralSet, ENNReal.smul_def, smul_eq_mul, mul_one] at h
    rw [Measure.map_apply e.continuous.measurable hK] at h
    exact h

  have hint : ∫ t : localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c), w (e t) ∂τ =
      ((Measure.map (⇑e) τ).haarScalarFactor (localHaar K v) : ℝ) * ∫ x, w x ∂(localHaar K v) := by
    have h := integral_map_equiv (μ := τ) e.toMeasurableEquiv w
    simp only [Homeomorph.toMeasurableEquiv_coe] at h
    rw [← h]
    conv_lhs => rw [huniq]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have key : (∫ x, w x ∂(localHaar K v)) * ((Measure.map (⇑e) τ).haarScalarFactor (localHaar K v) : ℝ) = 1 := by
    rw [mul_comm, ← hint]
    exact h1
  rw [hmass, integral_complex_ofReal, ENNReal.coe_toReal, mul_assoc, ← Complex.ofReal_mul, key, Complex.ofReal_one,
    mul_one]
