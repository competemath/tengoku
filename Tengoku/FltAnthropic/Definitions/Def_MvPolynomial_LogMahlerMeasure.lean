import Tengoku.Seed.Analysis.Polynomial.MahlerMeasure
import Tengoku.Seed.MeasureTheory.Integral.TorusIntegral
import Tengoku.Seed.Topology.Algebra.MvPolynomial
import Tengoku.Seed.Algebra.MvPolynomial.Equiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Real

namespace MvPolynomial

variable {n : ℕ}

def torusBox (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ : Fin n ↦ Set.Ioc 0 (2 * π)

/--
@isnad1 id=eq.0h1v.s5.89256326ef8e from=translated src=- shape=2c71991f vocab=0dc42604
-/
theorem torusBox_def (n : ℕ) :
    torusBox n = Set.pi Set.univ fun _ : Fin n ↦ Set.Ioc 0 (2 * π) := rfl

/--
@isnad1 id=iff.0h2v.s5.777ad99de324 from=translated src=- shape=8469a66a vocab=e3d0725e
-/
theorem mem_torusBox {θ : Fin n → ℝ} : θ ∈ torusBox n ↔ ∀ i, θ i ∈ Set.Ioc 0 (2 * π) := by
  simp [torusBox]

/--
@isnad1 id=measurab.0h1v.s4.d1edd21eace3 from=translated src=- shape=fe6f4f64 vocab=8c7de4a6
-/
theorem measurableSet_torusBox : MeasurableSet (torusBox n) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioc

/--
@isnad1 id=eq.0h1v.s6.29dbb6a6e2b9 from=translated src=- shape=65b2eea7 vocab=04311813
-/
@[simp]
theorem volume_torusBox : volume (torusBox n) = ENNReal.ofReal (2 * π) ^ n := by
  simp [torusBox, volume_pi_pi, Real.volume_Ioc]

/--
@isnad1 id=eq.0h1v.s6.a59b9e9a4e03 from=translated src=- shape=1d1b5e87 vocab=5f440438
-/
theorem volume_torusBox_toReal : (volume (torusBox n)).toReal = (2 * π) ^ n := by
  rw [volume_torusBox, ENNReal.toReal_pow, ENNReal.toReal_ofReal two_pi_pos.le]

/--
@isnad1 id=eq.0h1v.s6.cd25c838e920 from=translated src=- shape=0e649443 vocab=7afd1d24
-/
@[simp]
theorem volume_real_torusBox : volume.real (torusBox n) = (2 * π) ^ n := by
  rw [measureReal_def, volume_torusBox_toReal]

/--
@isnad1 id=lt.0h1v.s6.04323b2b44a1 from=translated src=- shape=4387ef5c vocab=837d68a6
-/
theorem volume_torusBox_lt_top : volume (torusBox n) < ⊤ := by
  rw [volume_torusBox]
  exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

/--
@isnad1 id=eq.0h1v.s6.bc76d676a94e from=translated src=- shape=4d25a1c7 vocab=2086e5ef
-/
theorem volume_restrict_torusBox (n : ℕ) :
    (volume : Measure (Fin n → ℝ)).restrict (torusBox n) =
      Measure.pi fun _ : Fin n ↦ (volume : Measure ℝ).restrict (Set.Ioc 0 (2 * π)) := by
  rw [torusBox, volume_pi, Measure.restrict_pi_pi]

/--
@isnad1 id=ne.0h1v.s6.f27f20b8ab35 from=translated src=- shape=529c28aa vocab=1ce916b0
-/
theorem volume_torusBox_ne_zero : volume (torusBox n) ≠ 0 := by
  rw [volume_torusBox]
  exact pow_ne_zero _ (by simp [pi_pos])

/--
@isnad1 id=le.0h1v.s6.8be0ae03e70a from=translated src=- shape=8ad172a7 vocab=b64902e3
-/
theorem torusBox_subset_Icc : torusBox n ⊆ Set.Icc 0 (fun _ ↦ 2 * π) := fun _ hθ ↦
  ⟨fun i ↦ ((mem_torusBox.1 hθ) i).1.le, fun i ↦ ((mem_torusBox.1 hθ) i).2⟩

/--
@isnad1 id=eventual.0h1v.s7.643979d1c7bb from=translated src=- shape=46524372 vocab=8a9d6abb
-/
theorem torusBox_ae_eq_Icc : torusBox n =ᵐ[volume] Set.Icc (0 : Fin n → ℝ) (fun _ ↦ 2 * π) := by
  rw [volume_pi]
  exact Measure.univ_pi_Ioc_ae_eq_Icc

/--
@isnad1 id=eq.0h3v.s7.777fb5923346 from=translated src=- shape=2ce4bd2c vocab=59dbad43
-/
theorem setIntegral_torusBox_eq_setIntegral_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin n → ℝ) → E) :
    ∫ θ in torusBox n, f θ = ∫ θ in Set.Icc (0 : Fin n → ℝ) (fun _ ↦ 2 * π), f θ :=
  setIntegral_congr_set torusBox_ae_eq_Icc

/--
@isnad1 id=iff.0h3v.s7.daaadca07f56 from=translated src=- shape=205fba81 vocab=85cdb8d9
-/
theorem integrableOn_torusBox_iff_integrableOn_Icc {E : Type*} [NormedAddCommGroup E]
    {f : (Fin n → ℝ) → E} :
    IntegrableOn f (torusBox n) ↔ IntegrableOn f (Set.Icc (0 : Fin n → ℝ) (fun _ ↦ 2 * π)) :=
  ⟨fun h ↦ h.congr_set_ae torusBox_ae_eq_Icc.symm, fun h ↦ h.congr_set_ae torusBox_ae_eq_Icc⟩

/--
@isnad1 id=iff.0h3v.s7.51c89a49113c from=translated src=- shape=f7974877 vocab=10d1ba1f
-/
theorem cons_mem_torusBox_iff {x : ℝ} {θ : Fin n → ℝ} :
    (Fin.cons x θ : Fin (n + 1) → ℝ) ∈ torusBox (n + 1) ↔ x ∈ Set.Ioc 0 (2 * π) ∧ θ ∈ torusBox n := by
  simp [mem_torusBox, Fin.forall_fin_succ]

/--
@isnad1 id=iff.0h4v.s7.de36eedbdf9f from=translated src=- shape=ff208cb2 vocab=5be888ab
-/
theorem insertNth_mem_torusBox_iff (i : Fin (n + 1)) {x : ℝ} {θ : Fin n → ℝ} :
    i.insertNth x θ ∈ torusBox (n + 1) ↔ x ∈ Set.Ioc 0 (2 * π) ∧ θ ∈ torusBox n := by
  simp [mem_torusBox, i.forall_iff_succAbove]

/--
@isnad1 id=eq.0h2v.s9.46a284957d47 from=translated src=- shape=9fe6fc5a vocab=a5817024
-/
theorem piFinSuccAbove_symm_preimage_torusBox (i : Fin (n + 1)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) i).symm ⁻¹' torusBox (n + 1) =
      Set.Ioc 0 (2 * π) ×ˢ torusBox n := by
  ext ⟨x, θ⟩
  simp only [Set.mem_preimage, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, insertNth_mem_torusBox_iff, Set.mem_prod]

/--
@isnad1 id=eq.0h2v.s8.5fb5bbc1f97e from=translated src=- shape=98e05c61 vocab=571cea31
-/
theorem piFinSuccAbove_image_torusBox (i : Fin (n + 1)) :
    MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) i '' torusBox (n + 1) =
      Set.Ioc 0 (2 * π) ×ˢ torusBox n := by
  rw [MeasurableEquiv.image_eq_preimage_symm, piFinSuccAbove_symm_preimage_torusBox]

/--
@isnad1 id=eq.0h2v.s7.dfa2c8b9d4b8 from=translated src=- shape=38051540 vocab=8b3a97f0
-/
theorem inv_two_pi_pow_mul_setIntegral_torusBox_const (a : ℝ) :
    ((2 * π)⁻¹) ^ n * ∫ _ in torusBox n, a = a := by
  rw [setIntegral_const, volume_real_torusBox, smul_eq_mul, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ two_pi_pos.ne', one_pow, one_mul]

def logMahlerMeasure (P : MvPolynomial (Fin n) ℂ) : ℝ :=
  ((2 * π)⁻¹) ^ n * ∫ θ in torusBox n, Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖

/--
@isnad1 id=eq.0h2v.s7.96fbb4569a10 from=translated src=- shape=64b51976 vocab=b50a42af
-/
theorem logMahlerMeasure_def (P : MvPolynomial (Fin n) ℂ) :
    P.logMahlerMeasure =
      ((2 * π)⁻¹) ^ n * ∫ θ in torusBox n, Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖ :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.53bc04d7dcc0 from=translated src=- shape=aa39330d vocab=a5bcc359
-/
theorem circleMap_eq_torusMap (θ : Fin n → ℝ) :
    (fun i ↦ circleMap 0 1 (θ i)) = torusMap 0 1 θ := by
  ext i; simp [torusMap, circleMap]

/--
@isnad1 id=eq.0h1v.s4.8741aa758e03 from=translated src=- shape=83bc905a vocab=f06d24b1
-/
@[simp]
theorem norm_circleMap_zero_one (t : ℝ) : ‖circleMap 0 1 t‖ = 1 := by
  simp

/--
@isnad1 id=continuo.0h2v.s7.a08454f3d51e from=translated src=- shape=accaeb47 vocab=b2391e39
-/
@[fun_prop]
theorem continuous_eval_circleMap (P : MvPolynomial (Fin n) ℂ) :
    Continuous fun θ : Fin n → ℝ ↦ eval (fun i ↦ circleMap 0 1 (θ i)) P :=
  (continuous_eval P).comp
    (continuous_pi fun i ↦ (continuous_circleMap 0 1).comp (continuous_apply i))

/--
@isnad1 id=measurab.0h2v.s7.4118fc0a7181 from=translated src=- shape=adcfc053 vocab=d9baa884
-/
@[fun_prop]
theorem measurable_log_norm_eval_circleMap (P : MvPolynomial (Fin n) ℂ) :
    Measurable fun θ : Fin n → ℝ ↦ Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖ :=
  measurable_log.comp (continuous_eval_circleMap P).norm.measurable

/--
@isnad1 id=aestrong.0h3v.s7.48693fbce1f9 from=translated src=- shape=85d5df41 vocab=3e3bb2d0
-/
theorem aestronglyMeasurable_log_norm_eval_circleMap (P : MvPolynomial (Fin n) ℂ)
    (μ : Measure (Fin n → ℝ)) :
    AEStronglyMeasurable (fun θ : Fin n → ℝ ↦ Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖) μ :=
  (measurable_log_norm_eval_circleMap P).aestronglyMeasurable

/--
@isnad1 id=le.0h3v.s7.f0fcb018e3a3 from=translated src=- shape=f44e7ebf vocab=d1820cfb
-/
theorem norm_eval_circleMap_le_sum_norm_coeff (P : MvPolynomial (Fin n) ℂ) (θ : Fin n → ℝ) :
    ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖ ≤ ∑ m ∈ P.support, ‖coeff m P‖ := by
  rw [eval_eq]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun m _ ↦ ?_))
  simp [norm_prod, norm_pow]

/--
@isnad1 id=eq.0h1v.s5.548d213f3a94 from=translated src=- shape=49ea7328 vocab=cedf042c
-/
@[simp]
theorem logMahlerMeasure_zero : (0 : MvPolynomial (Fin n) ℂ).logMahlerMeasure = 0 := by
  simp [logMahlerMeasure]

/--
@isnad1 id=eq.0h2v.s6.537576bd3671 from=translated src=- shape=549e8751 vocab=c157e149
-/
@[simp]
theorem logMahlerMeasure_C (c : ℂ) : (C c : MvPolynomial (Fin n) ℂ).logMahlerMeasure = log ‖c‖ := by
  simp only [logMahlerMeasure, eval_C]
  exact inv_two_pi_pow_mul_setIntegral_torusBox_const _

/--
@isnad1 id=eq.0h1v.s5.cb2605250843 from=translated src=- shape=49ea7328 vocab=cedf042c
-/
@[simp]
theorem logMahlerMeasure_one : (1 : MvPolynomial (Fin n) ℂ).logMahlerMeasure = 0 := by
  rw [← C_1, logMahlerMeasure_C, norm_one, log_one]

/--
@isnad1 id=eq.0h3v.s7.0175f276c55a from=translated src=- shape=ab264139 vocab=596c6d0f
-/
@[simp]
theorem logMahlerMeasure_monomial (m : Fin n →₀ ℕ) (c : ℂ) :
    (monomial m c).logMahlerMeasure = log ‖c‖ := by
  simp only [logMahlerMeasure, eval_monomial, norm_mul, Finsupp.prod, norm_prod, norm_pow,
    norm_circleMap_zero_one, one_pow, Finset.prod_const_one, mul_one]
  exact inv_two_pi_pow_mul_setIntegral_torusBox_const _

/--
@isnad1 id=eq.0h2v.s4.6c5287d03ac7 from=translated src=- shape=4e417191 vocab=04844d1e
-/
@[simp]
theorem logMahlerMeasure_X (i : Fin n) : (X i : MvPolynomial (Fin n) ℂ).logMahlerMeasure = 0 := by
  rw [X, logMahlerMeasure_monomial, norm_one, log_one]

/--
@isnad1 id=eq.0h1v.s7.016661196961 from=translated src=- shape=7ef28c32 vocab=b5bb989f
-/
theorem logMahlerMeasure_eq_log_norm_constantCoeff (P : MvPolynomial (Fin 0) ℂ) :
    P.logMahlerMeasure = log ‖constantCoeff P‖ := by
  rw [P.eq_C_of_isEmpty, logMahlerMeasure_C, constantCoeff_C]

end MvPolynomial

end
