import Tengoku.Seed.NumberTheory.NumberField.Completion.InfinitePlace
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Circle
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.Seed.Topology.Instances.RealVectorSpace
import Tengoku.FltAnthropic.Theorems.Thm_AddChar_exists_continuousLinearMap_fourierChar_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_InfinitePlace_Completion_exists_forall_apply_eq_cpow_of_extensionEmbedding_eq_of_continuous.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_InfinitePlace_Completion_exists_forall_apply_eq_cpow_of_extensionEmbedding_eq_of_continuous

set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped FourierTransform

namespace R4ArchChar

variable {F : Type} [Field F] (w : InfinitePlace F)

open scoped Classical in

def posLift (r : ℝ) : w.Completion :=
  if hw : w.IsReal then (ringEquivRealOfIsReal hw).symm r
  else (ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm r

/--
@isnad1 id=eq.0h3v.s6.77d3ef5589aa from=translated src=- shape=2689c96d vocab=938d2271
-/
theorem extensionEmbedding_posLift (r : ℝ) : extensionEmbedding w (posLift w r) = (r : ℂ) := by
  unfold posLift
  split_ifs with hw
  · rw [← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply hw, RingEquiv.apply_symm_apply]
  · rw [← ringEquivComplexOfIsComplex_apply (not_isReal_iff_isComplex.mp hw), RingEquiv.apply_symm_apply]

/--
@isnad1 id=continuo.0h2v.s5.602c4e64ab59 from=translated src=- shape=ada3b6e4 vocab=a32d5250
-/
theorem continuous_posLift : Continuous (posLift w) := by
  unfold posLift
  split_ifs with hw
  · exact (isometryEquivRealOfIsReal hw).symm.continuous.comp continuous_id
  · exact (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm.continuous.comp
      Complex.continuous_ofReal

/--
@isnad1 id=eq.0h4v.s6.8da722e6a183 from=translated src=- shape=86a01b02 vocab=bd3c4d23
-/
theorem posLift_mul (a b : ℝ) : posLift w (a * b) = posLift w a * posLift w b := by
  apply (extensionEmbedding w).injective
  rw [map_mul, extensionEmbedding_posLift, extensionEmbedding_posLift, extensionEmbedding_posLift, Complex.ofReal_mul]

/--
@isnad1 id=eq.0h2v.s6.6d2bad4dfe78 from=translated src=- shape=2bc9fad4 vocab=ea16c2e1
-/
theorem posLift_one : posLift w 1 = 1 := by
  apply (extensionEmbedding w).injective
  rw [extensionEmbedding_posLift, map_one, Complex.ofReal_one]

/--
@isnad1 id=ne.1h3v.s6.406fa6953de4 from=translated src=- shape=af1e8163 vocab=ea16c2e1
-/
theorem posLift_ne_zero {r : ℝ} (hr : r ≠ 0) : posLift w r ≠ 0 := by
  intro h
  have := extensionEmbedding_posLift w r
  rw [h, map_zero] at this
  exact hr (by exact_mod_cast this.symm)

theorem eq_posLift_of_extensionEmbedding_eq {x : w.Completion} {r : ℝ} (h : extensionEmbedding w x = (r : ℂ)) :
    x = posLift w r := by
  apply (extensionEmbedding w).injective
  rw [h, extensionEmbedding_posLift]

def expUnit (t : ℝ) : (w.Completion)ˣ :=
  Units.mk0 (posLift w (Real.exp t)) (posLift_ne_zero w (Real.exp_pos t).ne')

/--
@isnad1 id=eq.0h3v.s5.a1de9ee6dc80 from=translated src=- shape=43368e1c vocab=02bd3231
-/
theorem expUnit_val (t : ℝ) : ((expUnit w t : (w.Completion)ˣ) : w.Completion) = posLift w (Real.exp t) := rfl

/--
@isnad1 id=eq.0h4v.s7.e736f3d60a75 from=translated src=- shape=632bba84 vocab=2c61c19e
-/
theorem expUnit_add (s t : ℝ) : expUnit w (s + t) = expUnit w s * expUnit w t := by
  apply Units.ext
  rw [Units.val_mul, expUnit_val, expUnit_val, expUnit_val, Real.exp_add, posLift_mul]

/--
@isnad1 id=eq.0h2v.s7.3dd0153ba23b from=translated src=- shape=f04bb258 vocab=e6746aca
-/
theorem expUnit_zero : expUnit w 0 = 1 := by
  apply Units.ext
  rw [expUnit_val, Real.exp_zero, posLift_one, Units.val_one]

/--
@isnad1 id=eq.0h3v.s7.d66554daa96d from=translated src=- shape=cea47f91 vocab=9f781e53
-/
theorem expUnit_inv_val (t : ℝ) :
    (((expUnit w t)⁻¹ : (w.Completion)ˣ) : w.Completion) = posLift w (Real.exp (-t)) := by
  have h : expUnit w t * expUnit w (-t) = 1 := by rw [← expUnit_add, add_neg_cancel, expUnit_zero]
  rw [← expUnit_val, ← inv_eq_of_mul_eq_one_right h]

/--
@isnad1 id=continuo.0h2v.s6.bd7bfd0086ba from=translated src=- shape=d6de7ab3 vocab=8b8fdcfc
-/
theorem continuous_expUnit : Continuous (expUnit w) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous fun t => ((expUnit w t : (w.Completion)ˣ) : w.Completion)
    simp only [expUnit_val]
    exact (continuous_posLift w).comp Real.continuous_exp
  · simp only [expUnit_inv_val]
    exact (continuous_posLift w).comp (Real.continuous_exp.comp continuous_neg)

theorem eq_mul_of_continuous_additive (m : ℝ → ℝ) (hm : ∀ a b, m (a + b) = m a + m b) (hc : Continuous m) (t : ℝ) :
    m t = t * m 1 := by
  let A : ℝ →+ ℝ := { toFun := m, map_zero' := by have := hm 0 0; simp at this; linarith, map_add' := hm }
  have hlin := (A.toRealLinearMap hc).map_smul t (1 : ℝ)
  simp only [AddMonoidHom.coe_toRealLinearMap, smul_eq_mul, mul_one] at hlin
  exact hlin

variable {w}

/--
@isnad1 id=ex.1h3v.s10.3c40992901f9 from=translated src=- shape=fbb2da1a vocab=38946801
-/
theorem main (χ : (w.Completion)ˣ →* ℂˣ)
    (hχc : Continuous fun x : (w.Completion)ˣ => ((χ x : ℂˣ) : ℂ)) :
    ∃ s : ℂ,
      (∀ (u : (w.Completion)ˣ) (r : ℝ), 0 < r → extensionEmbedding w (u : w.Completion) = (r : ℂ) →
        ((χ u : ℂˣ) : ℂ) = (r : ℂ) ^ s) ∧
      ((∀ u : (w.Completion)ˣ, ‖((χ u : ℂˣ) : ℂ)‖ = 1) → s.re = 0) := by

  set ψ : ℝ → ℂ := fun t => ((χ (expUnit w t) : ℂˣ) : ℂ) with hψ_def
  have hψc : Continuous ψ := hχc.comp (continuous_expUnit w)
  have hψadd : ∀ a b, ψ (a + b) = ψ a * ψ b := fun a b => by
    simp only [hψ_def, expUnit_add, map_mul, Units.val_mul]
  have hψ0 : ψ 0 = 1 := by simp only [hψ_def, expUnit_zero, map_one, Units.val_one]
  have hψne : ∀ t, ψ t ≠ 0 := fun t => Units.ne_zero _
  have hψnorm_pos : ∀ t, 0 < ‖ψ t‖ := fun t => norm_pos_iff.mpr (hψne t)

  set m : ℝ → ℝ := fun t => Real.log ‖ψ t‖ with hm_def
  have hmadd : ∀ a b, m (a + b) = m a + m b := fun a b => by
    simp only [hm_def, hψadd, norm_mul]
    rw [Real.log_mul (hψnorm_pos a).ne' (hψnorm_pos b).ne']
  have hmc : Continuous m := (hψc.norm).log fun t => (hψnorm_pos t).ne'
  set σ : ℝ := m 1 with hσ
  have hnorm : ∀ t, ‖ψ t‖ = Real.exp (t * σ) := fun t => by
    rw [← eq_mul_of_continuous_additive m hmadd hmc t, hm_def, Real.exp_log (hψnorm_pos t)]

  have hmem : ∀ t, ψ t / (‖ψ t‖ : ℂ) ∈ Submonoid.unitSphere ℂ := fun t => by
    rw [Submonoid.unitSphere, Submonoid.mem_mk, Subsemigroup.mem_mk, mem_sphere_zero_iff_norm, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hψnorm_pos t), div_self (hψnorm_pos t).ne']
  let n : AddChar ℝ Circle :=
    { toFun := fun t => ⟨ψ t / (‖ψ t‖ : ℂ), hmem t⟩
      map_zero_eq_one' := by
        apply Circle.ext
        show ψ 0 / (‖ψ 0‖ : ℂ) = ((1 : Circle) : ℂ)
        rw [hψ0, norm_one, Complex.ofReal_one, div_one, Circle.coe_one]
      map_add_eq_mul' := fun a b => by
        apply Circle.ext
        show ψ (a + b) / (‖ψ (a + b)‖ : ℂ) = ψ a / (‖ψ a‖ : ℂ) * (ψ b / (‖ψ b‖ : ℂ))
        rw [hψadd, norm_mul, Complex.ofReal_mul]
        have ha : (‖ψ a‖ : ℂ) ≠ 0 := by exact_mod_cast (hψnorm_pos a).ne'
        have hb : (‖ψ b‖ : ℂ) ≠ 0 := by exact_mod_cast (hψnorm_pos b).ne'
        field_simp }
  have hnapply : ∀ t, ((n t : Circle) : ℂ) = ψ t / (‖ψ t‖ : ℂ) := fun _ => rfl
  have hnc : Continuous n := by
    apply Continuous.subtype_mk
    exact hψc.div (Complex.continuous_ofReal.comp hψc.norm) fun t => by exact_mod_cast (hψnorm_pos t).ne'
  obtain ⟨l, hl⟩ := AddChar.exists_continuousLinearMap_fourierChar_eq n hnc
  set a : ℝ := l 1 with ha
  have hl1 : ∀ t, l t = t * a := fun t => by
    have := l.map_smul t (1 : ℝ)
    simp only [smul_eq_mul, mul_one] at this
    rw [ha, ← this]
  set s : ℂ := (σ : ℂ) + 2 * Real.pi * a * Complex.I with hs
  have hψexp : ∀ t, ψ t = Complex.exp (t * s) := fun t => by
    have h1 : ψ t = (‖ψ t‖ : ℂ) * (ψ t / (‖ψ t‖ : ℂ)) := by
      have : (‖ψ t‖ : ℂ) ≠ 0 := by exact_mod_cast (hψnorm_pos t).ne'
      field_simp
    have h2 : ψ t / (‖ψ t‖ : ℂ) = Complex.exp (↑(2 * Real.pi * (t * a)) * Complex.I) := by
      rw [← hnapply, hl t, Real.fourierChar_apply, hl1]
    rw [h1, h2, hnorm, Complex.ofReal_exp, ← Complex.exp_add, hs]
    congr 1
    push_cast
    ring
  refine ⟨s, fun u r hr hu => ?_, fun hunit => ?_⟩
  · have hval : (u : w.Completion) = posLift w r := eq_posLift_of_extensionEmbedding_eq w hu
    have hueq : u = expUnit w (Real.log r) := by
      apply Units.ext
      rw [expUnit_val, Real.exp_log hr, hval]
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [hueq, Complex.cpow_def_of_ne_zero hr0, ← Complex.ofReal_log hr.le]
    exact hψexp (Real.log r)
  · have h1 : ‖ψ 1‖ = 1 := hunit _
    have hσ0 : σ = 0 := by rw [hσ, hm_def]; simp only [h1, Real.log_one]
    rw [hs, hσ0]
    simp

end R4ArchChar

end

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

/--
@isnad1 id=ex.1h3v.s10.3c40992901f9 from=translated src=- shape=fbb2da1a vocab=38946801
-/
theorem solution
    (F : Type) [Field F] (w : InfinitePlace F)
    (χ : (w.Completion)ˣ →* ℂˣ)
    (_hχc : Continuous fun x : (w.Completion)ˣ => ((χ x : ℂˣ) : ℂ)) :
    ∃ s : ℂ,
      (∀ (u : (w.Completion)ˣ) (r : ℝ), 0 < r → extensionEmbedding w (u : w.Completion) = (r : ℂ) →
        ((χ u : ℂˣ) : ℂ) = (r : ℂ) ^ s) ∧
      ((∀ u : (w.Completion)ˣ, ‖((χ u : ℂˣ) : ℂ)‖ = 1) → s.re = 0) :=
  R4ArchChar.main χ _hχc
