import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace AutomorphicForm
namespace ArchMirabolic

variable {A : Type} [NormedCommRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]

private def _root_.AutomorphicForm.ArchMirabolic.mk (c₁ c₂ b d : A) : Fin 2 → Fin 2 → A := ![![c₁, b], ![c₂, d]]

export _root_.AutomorphicForm.ArchMirabolic (mk)

def un (x : A) : Matrix (Fin 2) (Fin 2) A := !![(1 : A), x; 0, 1]

noncomputable def ρ (t : A) : ℝ≥0∞ := (ENNReal.ofReal |Algebra.norm ℝ t| ^ 2)⁻¹

/--
@isnad1 id=eq.0h5v.s9.e51463aba923 from=translated src=- shape=97b66f83 vocab=cc1d6112
-/
lemma of_mk (c₁ c₂ b d : A) : Matrix.of (mk c₁ c₂ b d) = !![c₁, b; c₂, d] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/--
@isnad1 id=eq.0h5v.s8.d90de248a693 from=translated src=- shape=2cf244e0 vocab=20ace38a
-/
lemma det_mk (c₁ c₂ b d : A) : (Matrix.of (mk c₁ c₂ b d)).det = c₁ * d - b * c₂ := by
  rw [of_mk, Matrix.det_fin_two_of]

/--
@isnad1 id=eq.0h5v.s7.8434e520da9f from=translated src=- shape=f21ec053 vocab=a6518741
-/
lemma col_mk (c₁ c₂ b d : A) : (fun i => mk c₁ c₂ b d i 0) = ![c₁, c₂] := by
  funext i; fin_cases i <;> rfl

/--
@isnad1 id=eq.0h6v.s9.592f9a4d8ed7 from=translated src=- shape=088bebac vocab=92f326b4
-/
lemma mk_mul_un (c₁ c₂ b d x : A) :
    Matrix.of.symm (Matrix.of (mk c₁ c₂ b d) * un x) = mk c₁ c₂ (c₁ * x + b) (c₂ * x + d) := by
  apply Matrix.of.injective
  rw [Equiv.apply_symm_apply, of_mk, of_mk, un]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h3v.s7.68e4eec6833a from=translated src=- shape=033fdbaa vocab=c1e7602d
-/
lemma un_mul_un (x y : A) : un x * un y = un (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [un, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/--
@isnad1 id=eq.0h4v.s10.5eecf3b54062 from=translated src=- shape=709d4b69 vocab=552770ee
-/
lemma of_symm_mul_un_mul_un (Y : Fin 2 → Fin 2 → A) (x y : A) :
    Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of Y * un y)) * un x) =
      Matrix.of.symm (Matrix.of Y * un (y + x)) := by
  rw [Equiv.apply_symm_apply, Matrix.mul_assoc, un_mul_un]

/--
@isnad1 id=continuo.0h1v.s7.cfe3830cfeec from=translated src=- shape=e2d43fdc vocab=acbf1e40
-/
lemma continuous_algNorm : Continuous (Algebra.norm ℝ : A → ℝ) := by
  have h1 : Continuous fun a : A => (ContinuousLinearMap.mul ℝ A a).det :=
    ContinuousLinearMap.continuous_det.comp (ContinuousLinearMap.mul ℝ A).continuous
  have h2 : (fun a : A => (ContinuousLinearMap.mul ℝ A a).det) = (Algebra.norm ℝ : A → ℝ) := by
    funext a; rw [Algebra.norm_apply]; rfl
  rwa [h2] at h1

/--
@isnad1 id=measurab.0h1v.s6.29151ae25487 from=translated src=- shape=f000bd08 vocab=80d87c69
-/
lemma measurable_ρ : Measurable (ρ : A → ℝ≥0∞) := by
  unfold ρ
  exact ((ENNReal.continuous_ofReal.measurable.comp
    (continuous_abs.measurable.comp continuous_algNorm.measurable)).pow_const 2).inv

/--
@isnad1 id=isopen.0h1v.s6.f70ec9d138dc from=translated src=- shape=745cb67b vocab=9630b9da
-/
lemma isOpen_isUnit : IsOpen {t : A | IsUnit t} := Units.isOpen

/--
@isnad1 id=measurab.0h1v.s6.99c833be3db4 from=translated src=- shape=745cb67b vocab=a732aea6
-/
lemma measurableSet_isUnit : MeasurableSet {t : A | IsUnit t} := isOpen_isUnit.measurableSet

private lemma _root_.AutomorphicForm.ArchMirabolic.continuous_det : Continuous fun X : Fin 2 → Fin 2 → A => (Matrix.of X).det :=
  Continuous.matrix_det (A := fun X : Fin 2 → Fin 2 → A => Matrix.of X) continuous_id

export _root_.AutomorphicForm.ArchMirabolic (continuous_det)
/--
@isnad1 id=measurab.0h1v.s8.d07b9dd5e3a1 from=translated src=- shape=6bf8c803 vocab=c52de116
-/
lemma measurable_det : Measurable fun X : Fin 2 → Fin 2 → A => (Matrix.of X).det :=
  continuous_det.measurable

/--
@isnad1 id=measurab.0h1v.s8.34ba6c43ba5e from=translated src=- shape=c32abba3 vocab=b36a3909
-/
lemma measurableSet_U : MeasurableSet {X : Fin 2 → Fin 2 → A | IsUnit (Matrix.of X).det} :=
  measurableSet_isUnit.preimage measurable_det

/--
@isnad1 id=measurab.0h1v.s7.a8d23c3b590e from=translated src=- shape=201dad37 vocab=09fd4cad
-/
lemma measurable_col : Measurable fun X : Fin 2 → Fin 2 → A => fun i => X i 0 :=
  measurable_pi_lambda _ fun i => (measurable_pi_apply 0).comp (measurable_pi_apply i)

/--
@isnad1 id=continuo.0h1v.s6.450d75fd5488 from=translated src=- shape=f1609845 vocab=0fc7cc62
-/
lemma continuous_un : Continuous (un : A → Matrix (Fin 2) (Fin 2) A) := by
  unfold un
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/--
@isnad1 id=continuo.0h1v.s9.acd25c8c9c2b from=translated src=- shape=8ebfcb64 vocab=7ee5a2d6
-/
lemma continuous_mulUn :
    Continuous fun p : (Fin 2 → Fin 2 → A) × A => Matrix.of.symm (Matrix.of p.1 * un p.2) := by
  have : Continuous fun p : (Fin 2 → Fin 2 → A) × A => Matrix.of p.1 * un p.2 :=
    Continuous.matrix_mul (continuous_fst) (continuous_un.comp continuous_snd)
  exact this

/--
@isnad1 id=continuo.0h1v.s8.018298cb952d from=translated src=- shape=3988b797 vocab=b795ce2c
-/
lemma continuous_mk4 :
    Continuous fun p : (A × A) × (A × A) => mk p.1.1 p.2.1 p.1.2 p.2.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [mk] <;> fun_prop

/--
@isnad1 id=measurab.0h1v.s7.c9580bada43e from=translated src=- shape=3988b797 vocab=186631dc
-/
lemma measurable_mk4 :
    Measurable fun p : (A × A) × (A × A) => mk p.1.1 p.2.1 p.1.2 p.2.2 :=
  continuous_mk4.measurable

/--
@isnad1 id=measurab.4h6v.s7.6fd0a8bbf2dc from=translated src=- shape=b01ffd3b vocab=5554ccf4
-/
lemma measurable_mk {X : Type*} [MeasurableSpace X] {f₁ f₂ f₃ f₄ : X → A}
    (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃) (h₄ : Measurable f₄) :
    Measurable fun p => mk (f₁ p) (f₂ p) (f₃ p) (f₄ p) :=
  measurable_mk4.comp ((h₁.prodMk h₃).prodMk (h₂.prodMk h₄))

/--
@isnad1 id=continuo.0h1v.s7.143010934ae2 from=translated src=- shape=50fb8be6 vocab=a856a1e2
-/
lemma continuous_vec2 : Continuous fun p : A × A => (![p.1, p.2] : Fin 2 → A) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop

variable (μ : Measure A)

noncomputable def fib (w : (Fin 2 → Fin 2 → A) → ℝ≥0∞) (Y : Fin 2 → Fin 2 → A) : ℝ≥0∞ :=
  ∫⁻ x, w (Matrix.of.symm (Matrix.of Y * un x)) ∂μ

variable {μ}

/--
@isnad1 id=measurab.1h3v.s7.19952c193dd1 from=translated src=- shape=ab55f323 vocab=e98ce2ab
-/
lemma measurable_fib [SFinite μ] {w : (Fin 2 → Fin 2 → A) → ℝ≥0∞} (hw : Measurable w) :
    Measurable (fib μ w) :=
  Measurable.lintegral_prod_right' (f := fun p : (Fin 2 → Fin 2 → A) × A =>
    w (Matrix.of.symm (Matrix.of p.1 * un p.2))) (hw.comp continuous_mulUn.measurable)

/--
@isnad1 id=eq.0h5v.s9.795f90b9bae4 from=translated src=- shape=d55e5655 vocab=34ee8866
-/
lemma fib_mul_un [μ.IsAddLeftInvariant] (w : (Fin 2 → Fin 2 → A) → ℝ≥0∞)
    (Y : Fin 2 → Fin 2 → A) (y : A) :
    fib μ w (Matrix.of.symm (Matrix.of Y * un y)) = fib μ w Y := by
  unfold fib
  simp_rw [of_symm_mul_un_mul_un]
  exact lintegral_add_left_eq_self (fun x => w (Matrix.of.symm (Matrix.of Y * un x))) y

section Iterated

variable [SFinite μ] [SigmaFinite μ]

def rowsEquiv : (Fin 2 → Fin 2 → A) ≃ᵐ (A × A) × (A × A) :=
  (MeasurableEquiv.finTwoArrow (α := Fin 2 → A)).trans
    (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow MeasurableEquiv.finTwoArrow)

/--
@isnad1 id=eq.0h2v.s9.77166341743b from=translated src=- shape=8838f170 vocab=0a8c31fa
-/
lemma rowsEquiv_symm_apply (p : (A × A) × (A × A)) :
    (rowsEquiv.symm p : Fin 2 → Fin 2 → A) = mk p.1.1 p.2.1 p.1.2 p.2.2 := by
  rcases p with ⟨⟨c₁, b⟩, ⟨c₂, d⟩⟩
  rfl

/--
@isnad1 id=measurep.0h2v.s9.5db36271385e from=translated src=- shape=73553eae vocab=068ed2a8
-/
lemma measurePreserving_rowsEquiv :
    MeasurePreserving (rowsEquiv (A := A))
      (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) ((μ.prod μ).prod (μ.prod μ)) := by
  unfold rowsEquiv
  exact ((measurePreserving_finTwoArrow μ).prod (measurePreserving_finTwoArrow μ)).comp
    (measurePreserving_finTwoArrow (Measure.pi fun _ : Fin 2 => μ))

/--
@isnad1 id=eq.1h3v.s8.bcf943dad9d8 from=translated src=- shape=7f3de24b vocab=bd5bdf2f
-/
lemma lintegral_eq_iterated_rows {F : (Fin 2 → Fin 2 → A) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ X, F X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) =
      ∫⁻ c₁, ∫⁻ b, ∫⁻ c₂, ∫⁻ d, F (mk c₁ c₂ b d) ∂μ ∂μ ∂μ ∂μ := by
  have hG : Measurable fun p : (A × A) × (A × A) => F (mk p.1.1 p.2.1 p.1.2 p.2.2) :=
    hF.comp measurable_mk4
  have h1 : ∫⁻ X, F X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) =
      ∫⁻ p, F (mk p.1.1 p.2.1 p.1.2 p.2.2) ∂((μ.prod μ).prod (μ.prod μ)) := by
    rw [(measurePreserving_rowsEquiv (μ := μ)).lintegral_map_equiv]
    refine lintegral_congr fun X => ?_
    rw [← rowsEquiv_symm_apply, MeasurableEquiv.symm_apply_apply]
  rw [h1, lintegral_prod _ hG.aemeasurable]
  dsimp only
  have hq : Measurable fun q : A × A => ∫⁻ r, F (mk q.1 r.1 q.2 r.2) ∂(μ.prod μ) :=
    Measurable.lintegral_prod_right'
      (f := fun p : (A × A) × (A × A) => F (mk p.1.1 p.2.1 p.1.2 p.2.2)) hG
  rw [lintegral_prod _ hq.aemeasurable]
  refine lintegral_congr fun c₁ => lintegral_congr fun b => ?_
  have hr : Measurable fun r : A × A => F (mk c₁ r.1 b r.2) :=
    measurable_mk measurable_const measurable_fst measurable_const measurable_snd |> hF.comp
  rw [lintegral_prod _ hr.aemeasurable]

omit [SFinite μ] in

/--
@isnad1 id=eq.1h3v.s7.07e5120daeea from=translated src=- shape=d9e5051d vocab=3b620547
-/
lemma lintegral_eq_iterated_vec {G : (Fin 2 → A) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ c, G c ∂(Measure.pi fun _ : Fin 2 => μ) = ∫⁻ c₁, ∫⁻ c₂, G ![c₁, c₂] ∂μ ∂μ := by
  have h : ∫⁻ c, G c ∂(Measure.pi fun _ : Fin 2 => μ) =
      ∫⁻ c, (fun p : A × A => G ![p.1, p.2]) (MeasurableEquiv.finTwoArrow c)
        ∂(Measure.pi fun _ : Fin 2 => μ) := by
    refine lintegral_congr fun c => ?_
    congr 1
    funext i; fin_cases i <;> rfl
  rw [h, ← (measurePreserving_finTwoArrow μ).lintegral_map_equiv (fun p : A × A => G ![p.1, p.2]),
    lintegral_prod (fun p : A × A => G ![p.1, p.2]) (hG.comp continuous_vec2.measurable).aemeasurable]

end Iterated

section CoV

variable [μ.IsAddHaarMeasure]

def mulLeftEquiv (a : Aˣ) : A ≃ᵐ A where
  toFun x := (a : A) * x
  invFun x := ((a⁻¹ : Aˣ) : A) * x
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]
  measurable_toFun := (continuous_const.mul continuous_id).measurable
  measurable_invFun := (continuous_const.mul continuous_id).measurable

/--
@isnad1 id=ne.0h2v.s7.3c35545a3af7 from=translated src=- shape=d4ff76bb vocab=713e7835
-/
lemma algNorm_unit_ne_zero (a : Aˣ) : Algebra.norm ℝ (a : A) ≠ 0 :=
  (a.isUnit.map (Algebra.norm ℝ)).ne_zero

/--
@isnad1 id=eq.0h4v.s8.3a6f84fadf16 from=translated src=- shape=03af661e vocab=583b7173
-/
lemma lintegral_comp_mul_unit (a : Aˣ) (f : A → ℝ≥0∞) :
    ∫⁻ x, f ((a : A) * x) ∂μ = ENNReal.ofReal |(Algebra.norm ℝ (a : A))⁻¹| * ∫⁻ x, f x ∂μ := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ (a : A)) = Algebra.norm ℝ (a : A) := by
    rw [Algebra.norm_apply]; rfl
  have hmap : Measure.map (mulLeftEquiv a) μ =
      ENNReal.ofReal |(Algebra.norm ℝ (a : A))⁻¹| • μ := by
    have : (⇑(mulLeftEquiv a) : A → A) = ⇑(LinearMap.mulLeft ℝ (a : A)) := by
      funext x; rfl
    rw [this, Measure.map_linearMap_addHaar_eq_smul_addHaar μ
      (by rw [hdet]; exact algNorm_unit_ne_zero a), hdet]
  have := lintegral_map_equiv f (mulLeftEquiv (A := A) a) (μ := μ)
  rw [hmap, lintegral_smul_measure] at this
  exact this.symm

/--
@isnad1 id=eq.0h5v.s8.16410d8beae2 from=translated src=- shape=eed9657a vocab=66699cb0
-/
lemma lintegral_lintegral_secondColumn (c₁ : Aˣ) (c₂ : A) (F : A → A → ℝ≥0∞) :
    ∫⁻ b, ∫⁻ d, F b d ∂μ ∂μ =
      ∫⁻ x, ∫⁻ δ, F ((c₁ : A) * x) (c₂ * x + ((c₁⁻¹ : Aˣ) : A) * δ) ∂μ ∂μ := by

  have hinner : ∀ x : A, ∫⁻ δ, F ((c₁ : A) * x) (c₂ * x + ((c₁⁻¹ : Aˣ) : A) * δ) ∂μ =
      ENNReal.ofReal |(Algebra.norm ℝ ((c₁⁻¹ : Aˣ) : A))⁻¹| * ∫⁻ δ, F ((c₁ : A) * x) δ ∂μ := by
    intro x
    have h1 := lintegral_comp_mul_unit (μ := μ) c₁⁻¹ (fun t => F ((c₁ : A) * x) (c₂ * x + t))
    rw [h1, lintegral_add_left_eq_self (μ := μ) (fun t => F ((c₁ : A) * x) t) (c₂ * x)]
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

  have h2 := lintegral_comp_mul_unit (μ := μ) c₁ (fun b => ∫⁻ δ, F b δ ∂μ)
  rw [h2, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, ← mul_inv,
    ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, inv_one, abs_one,
    ENNReal.ofReal_one, one_mul]

end CoV

section Main

variable [μ.IsAddHaarMeasure]

/--
@isnad1 id=eq.0h5v.s9.396bd7b73ab4 from=translated src=- shape=3b28deea vocab=9324c7d5
-/
lemma mk_secondColumn (c₁ : Aˣ) (c₂ x δ : A) :
    mk (c₁ : A) c₂ ((c₁ : A) * x) (c₂ * x + ((c₁⁻¹ : Aˣ) : A) * δ) =
      Matrix.of.symm (Matrix.of (mk (c₁ : A) c₂ 0 (((c₁⁻¹ : Aˣ) : A) * δ)) * un x) := by
  rw [mk_mul_un, add_zero]

/--
@isnad1 id=eq.0h4v.s8.bf333e775f66 from=translated src=- shape=6e3f37cc vocab=a0bf1e6d
-/
lemma det_g₀ (c₁ : Aˣ) (c₂ δ : A) :
    (Matrix.of (mk (c₁ : A) c₂ 0 (((c₁⁻¹ : Aˣ) : A) * δ))).det = δ := by
  rw [det_mk, zero_mul, sub_zero, ← mul_assoc, Units.mul_inv, one_mul]

/--
@isnad1 id=eq.0h3v.s9.bc4bf23db954 from=translated src=- shape=1b51ef75 vocab=44bb3564
-/
lemma det_mul_un (Y : Fin 2 → Fin 2 → A) (x : A) :
    (Matrix.of (Matrix.of.symm (Matrix.of Y * un x))).det = (Matrix.of Y).det := by
  rw [Equiv.apply_symm_apply, Matrix.det_mul, un, Matrix.det_fin_two_of]; simp

/--
@isnad1 id=eventual.3h3v.s9.290b1dc8f4e7 from=translated src=- shape=197383f5 vocab=fbae8c20
-/
lemma ae_fib_g₀_eq_one (hA : ∀ᵐ a ∂μ, IsUnit a)
    {w : (Fin 2 → Fin 2 → A) → ℝ≥0∞} (hw : Measurable w)
    (hw1 : ∀ᵐ X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ).restrict
        {X | IsUnit (Matrix.of X).det}, fib μ w X = 1) :
    ∀ᵐ c₁ ∂μ, ∀ u : Aˣ, (u : A) = c₁ → ∀ᵐ c₂ ∂μ, ∀ᵐ δ ∂μ, IsUnit δ →
      fib μ w (mk (u : A) c₂ 0 (((u⁻¹ : Aˣ) : A) * δ)) = 1 := by
  classical

  obtain ⟨Bad, hBad⟩ : ∃ Bad : Set (Fin 2 → Fin 2 → A),
      Bad = {X | IsUnit (Matrix.of X).det ∧ fib μ w X ≠ 1} := ⟨_, rfl⟩
  have hBadm : MeasurableSet Bad := by
    rw [hBad]
    exact measurableSet_U.inter ((measurable_fib hw) (measurableSet_singleton 1)).compl
  have hBad0 : (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) Bad = 0 := by
    rw [ae_restrict_iff' measurableSet_U] at hw1
    rw [← compl_mem_ae_iff]
    filter_upwards [hw1] with X hX
    simp only [hBad, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_not]
    exact hX
  obtain ⟨χ, hχ⟩ : ∃ χ : (Fin 2 → Fin 2 → A) → ℝ≥0∞, χ = Bad.indicator 1 := ⟨_, rfl⟩
  have hind : Measurable χ := by rw [hχ]; exact measurable_one.indicator hBadm

  have hI : ∫⁻ c₁, ∫⁻ b, ∫⁻ c₂, ∫⁻ d, χ (mk c₁ c₂ b d) ∂μ ∂μ ∂μ ∂μ = 0 := by
    rw [← lintegral_eq_iterated_rows hind, hχ, lintegral_indicator hBadm]
    simp [hBad0]

  have hswap : ∀ c₁ : A, ∫⁻ b, ∫⁻ c₂, ∫⁻ d, χ (mk c₁ c₂ b d) ∂μ ∂μ ∂μ =
      ∫⁻ c₂, ∫⁻ b, ∫⁻ d, χ (mk c₁ c₂ b d) ∂μ ∂μ ∂μ := by
    intro c₁
    refine lintegral_lintegral_swap ?_
    refine (Measurable.lintegral_prod_right' (f := fun p : (A × A) × A =>
      χ (mk c₁ p.1.2 p.1.1 p.2)) ?_).aemeasurable
    exact hind.comp (measurable_mk measurable_const measurable_fst.snd measurable_fst.fst
      measurable_snd)
  simp_rw [hswap] at hI

  have hm2 : ∀ c₁ : A, Measurable fun c₂ : A => ∫⁻ b, ∫⁻ d, χ (mk c₁ c₂ b d) ∂μ ∂μ := by
    intro c₁
    refine Measurable.lintegral_prod_right' (f := fun q : A × A =>
      ∫⁻ d, χ (mk c₁ q.1 q.2 d) ∂μ) ?_
    refine Measurable.lintegral_prod_right' (f := fun r : (A × A) × A =>
      χ (mk c₁ r.1.1 r.1.2 r.2)) ?_
    exact hind.comp (measurable_mk measurable_const measurable_fst.fst measurable_fst.snd
      measurable_snd)
  have hm3 : Measurable fun c₁ : A => ∫⁻ c₂, ∫⁻ b, ∫⁻ d, χ (mk c₁ c₂ b d) ∂μ ∂μ ∂μ := by
    refine Measurable.lintegral_prod_right' (f := fun p : A × A =>
      ∫⁻ b, ∫⁻ d, χ (mk p.1 p.2 b d) ∂μ ∂μ) ?_
    refine Measurable.lintegral_prod_right' (f := fun q : (A × A) × A =>
      ∫⁻ d, χ (mk q.1.1 q.1.2 q.2 d) ∂μ) ?_
    refine Measurable.lintegral_prod_right' (f := fun r : ((A × A) × A) × A =>
      χ (mk r.1.1.1 r.1.1.2 r.1.2 r.2)) ?_
    exact hind.comp (measurable_mk measurable_fst.fst.fst measurable_fst.fst.snd
      measurable_fst.snd measurable_snd)
  rw [lintegral_eq_zero_iff' hm3.aemeasurable] at hI
  filter_upwards [hI] with c₁ hc₁0 u hu
  subst hu
  have hc₁0' : ∫⁻ c₂, ∫⁻ b, ∫⁻ d, χ (mk (u : A) c₂ b d) ∂μ ∂μ ∂μ = 0 := hc₁0
  rw [lintegral_eq_zero_iff' (hm2 (u : A)).aemeasurable] at hc₁0'
  filter_upwards [hc₁0'] with c₂ hc₂0
  have hc₂0' : ∫⁻ b, ∫⁻ d, χ (mk (u : A) c₂ b d) ∂μ ∂μ = 0 := hc₂0

  rw [lintegral_lintegral_secondColumn (μ := μ) u c₂ fun b d => χ (mk (u : A) c₂ b d)] at hc₂0'

  have hinv : ∀ x δ : A, χ (mk (u : A) c₂ ((u : A) * x) (c₂ * x + ((u⁻¹ : Aˣ) : A) * δ)) =
      χ (mk (u : A) c₂ 0 (((u⁻¹ : Aˣ) : A) * δ)) := by
    intro x δ
    rw [mk_secondColumn]
    simp only [hχ, Set.indicator, hBad, Set.mem_ofPred_eq, det_mul_un, fib_mul_un, Pi.one_apply]
  simp_rw [hinv] at hc₂0'
  rw [lintegral_const, mul_eq_zero] at hc₂0'
  have hμ0 : μ Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
  have hδ0 : ∫⁻ δ, χ (mk (u : A) c₂ 0 (((u⁻¹ : Aˣ) : A) * δ)) ∂μ = 0 :=
    hc₂0'.resolve_right hμ0
  have hmδ : Measurable fun δ : A => χ (mk (u : A) c₂ 0 (((u⁻¹ : Aˣ) : A) * δ)) :=
    hind.comp (measurable_mk measurable_const measurable_const measurable_const
      (measurable_id.const_mul _))
  rw [lintegral_eq_zero_iff' hmδ.aemeasurable] at hδ0
  filter_upwards [hδ0] with δ hδ hδu
  have hδ' : χ (mk (u : A) c₂ 0 (((u⁻¹ : Aˣ) : A) * δ)) = 0 := hδ
  rw [hχ, Set.indicator_apply_eq_zero] at hδ'
  by_contra hne
  have hmem : mk (u : A) c₂ 0 (((u⁻¹ : Aˣ) : A) * δ) ∈ Bad := by
    rw [hBad, Set.mem_ofPred_eq, det_g₀]
    exact ⟨hδu, hne⟩
  exact one_ne_zero (hδ' hmem)

/--
@isnad1 id=eq.4h4v.s10.90067a1a31c5 from=translated src=- shape=e7a60829 vocab=6458b0b7
-/
theorem main (hA : ∀ᵐ a ∂μ, IsUnit a)
    (w : (Fin 2 → Fin 2 → A) → ℝ≥0∞) (hw : Measurable w)
    (hw1 : ∀ᵐ X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ).restrict
        {X | IsUnit (Matrix.of X).det}, fib μ w X = 1)
    (Ψ : (Fin 2 → A) × A → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ X in {X | IsUnit (Matrix.of X).det},
        w X * Ψ (fun i => X i 0, (Matrix.of X).det) * ρ (Matrix.of X).det
      ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) =
    ∫⁻ c, ∫⁻ δ in {δ | IsUnit δ}, Ψ (c, δ) * ρ δ ∂μ ∂(Measure.pi fun _ : Fin 2 => μ) := by
  classical

  obtain ⟨F, hF⟩ : ∃ F : (Fin 2 → Fin 2 → A) → ℝ≥0∞,
      F = {X : Fin 2 → Fin 2 → A | IsUnit (Matrix.of X).det}.indicator
        fun X => w X * Ψ (fun i => X i 0, (Matrix.of X).det) * ρ (Matrix.of X).det := ⟨_, rfl⟩
  have hFm : Measurable F := by
    rw [hF]
    exact ((hw.mul (hΨ.comp (measurable_col.prodMk measurable_det))).mul
      (measurable_ρ.comp measurable_det)).indicator measurableSet_U
  rw [← lintegral_indicator measurableSet_U, ← hF, lintegral_eq_iterated_rows hFm]

  obtain ⟨R, hR⟩ : ∃ R : (Fin 2 → A) → ℝ≥0∞,
      R = fun c => ∫⁻ δ, {δ : A | IsUnit δ}.indicator (fun δ => Ψ (c, δ) * ρ δ) δ ∂μ := ⟨_, rfl⟩
  have hRm : Measurable R := by
    rw [hR]
    refine Measurable.lintegral_prod_right' (f := fun p : (Fin 2 → A) × A =>
      {δ : A | IsUnit δ}.indicator (fun δ => Ψ (p.1, δ) * ρ δ) p.2) ?_
    have h1 : Measurable fun p : (Fin 2 → A) × A => Ψ p * ρ p.2 :=
      hΨ.mul (measurable_ρ.comp measurable_snd)
    have h2 : (fun p : (Fin 2 → A) × A =>
        {δ : A | IsUnit δ}.indicator (fun δ => Ψ (p.1, δ) * ρ δ) p.2) =
        (Prod.snd ⁻¹' {δ : A | IsUnit δ}).indicator fun p => Ψ p * ρ p.2 := by
      funext p
      simp only [Set.indicator, Set.mem_preimage, Set.mem_ofPred_eq, Prod.mk.eta]
    rw [h2]
    exact h1.indicator (measurableSet_isUnit.preimage measurable_snd)
  have hRHS : (∫⁻ c, ∫⁻ δ in {δ | IsUnit δ}, Ψ (c, δ) * ρ δ ∂μ ∂(Measure.pi fun _ : Fin 2 => μ)) =
      ∫⁻ c, R c ∂(Measure.pi fun _ : Fin 2 => μ) := by
    rw [hR]
    simp_rw [lintegral_indicator measurableSet_isUnit]
  rw [hRHS, lintegral_eq_iterated_vec hRm]

  have hswap : ∀ c₁ : A, ∫⁻ b, ∫⁻ c₂, ∫⁻ d, F (mk c₁ c₂ b d) ∂μ ∂μ ∂μ =
      ∫⁻ c₂, ∫⁻ b, ∫⁻ d, F (mk c₁ c₂ b d) ∂μ ∂μ ∂μ := by
    intro c₁
    refine lintegral_lintegral_swap ?_
    refine (Measurable.lintegral_prod_right' (f := fun p : (A × A) × A =>
      F (mk c₁ p.1.2 p.1.1 p.2)) ?_).aemeasurable
    exact hFm.comp (measurable_mk measurable_const measurable_fst.snd measurable_fst.fst
      measurable_snd)
  simp_rw [hswap]

  refine lintegral_congr_ae ?_
  filter_upwards [hA, ae_fib_g₀_eq_one (μ := μ) hA hw hw1] with c₁ hc₁ hgood
  obtain ⟨u, rfl⟩ := hc₁
  refine lintegral_congr_ae ?_
  filter_upwards [hgood u rfl] with c₂ hδ

  rw [lintegral_lintegral_secondColumn (μ := μ) u c₂ fun b d => F (mk (u : A) c₂ b d)]

  have hval : ∀ x δ : A, F (mk (u : A) c₂ ((u : A) * x) (c₂ * x + ((u⁻¹ : Aˣ) : A) * δ)) =
      {δ : A | IsUnit δ}.indicator (fun δ => Ψ (![(u : A), c₂], δ) * ρ δ) δ *
        w (mk (u : A) c₂ ((u : A) * x) (c₂ * x + ((u⁻¹ : Aˣ) : A) * δ)) := by
    intro x δ
    have hd : (Matrix.of (mk (u : A) c₂ ((u : A) * x) (c₂ * x + ((u⁻¹ : Aˣ) : A) * δ))).det =
        δ := by
      rw [mk_secondColumn, det_mul_un, det_g₀]
    rw [hF]
    simp only [Set.indicator, Set.mem_ofPred_eq, hd, col_mk]
    split_ifs with h
    · ring
    · simp
  simp_rw [hval]

  have hwx : ∀ δ : A, Measurable fun x : A =>
      w (mk (u : A) c₂ ((u : A) * x) (c₂ * x + ((u⁻¹ : Aˣ) : A) * δ)) := by
    intro δ
    exact hw.comp (measurable_mk measurable_const measurable_const (measurable_id.const_mul _)
      ((measurable_id.const_mul _).add_const _))
  have hm2 : Measurable fun p : A × A =>
      {δ : A | IsUnit δ}.indicator (fun δ => Ψ (![(u : A), c₂], δ) * ρ δ) p.2 *
        w (mk (u : A) c₂ ((u : A) * p.1) (c₂ * p.1 + ((u⁻¹ : Aˣ) : A) * p.2)) := by
    refine Measurable.mul ?_ ?_
    · have hc : Measurable fun δ : A => ((![(u : A), c₂] : Fin 2 → A), δ) :=
        measurable_const.prodMk measurable_id
      have h1 : Measurable fun δ : A => Ψ (![(u : A), c₂], δ) * ρ δ :=
        (hΨ.comp hc).mul measurable_ρ
      exact (h1.indicator measurableSet_isUnit).comp measurable_snd
    · exact hw.comp (measurable_mk measurable_const measurable_const (measurable_fst.const_mul _)
        ((measurable_fst.const_mul _).add (measurable_snd.const_mul _)))
  rw [lintegral_lintegral_swap hm2.aemeasurable, hR]
  beta_reduce
  refine lintegral_congr_ae ?_
  filter_upwards [hδ] with δ hδ1
  rw [lintegral_const_mul'' _ (hwx δ).aemeasurable]
  by_cases hδu : IsUnit δ
  · have h1 : fib μ w (mk (u : A) c₂ 0 (((u⁻¹ : Aˣ) : A) * δ)) = 1 := hδ1 hδu
    rw [fib] at h1
    simp_rw [← mk_secondColumn] at h1
    rw [h1, mul_one]
  · simp [Set.indicator, hδu]

end Main

end AutomorphicForm.ArchMirabolic
open scoped _root_.P2MW.S_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one.AutomorphicForm _root_.P2MW.S_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one.AutomorphicForm.ArchMirabolic
open scoped _root_.P2MW.S_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one.AutomorphicForm

open AutomorphicForm.ArchMirabolic in
/--
@isnad1 id=eq.5h4v.s11.df5be474d951 from=translated src=- shape=7a568651 vocab=f7539f6c
-/
theorem solution
    (A : Type) [NormedCommRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
    [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) (hμ : μ.IsAddHaarMeasure) (hA : ∀ᵐ a ∂μ, IsUnit a)
    (w : (Fin 2 → Fin 2 → A) → ℝ≥0∞) (hw : Measurable w)
    (hw1 : ∀ᵐ X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ).restrict
        {X | IsUnit (Matrix.of X).det},
      ∫⁻ x, w (Matrix.of.symm (Matrix.of X * !![(1 : A), x; 0, 1])) ∂μ = 1)
    (Ψ : (Fin 2 → A) × A → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ X in {X | IsUnit (Matrix.of X).det},
        w X * Ψ (fun i => X i 0, (Matrix.of X).det) *
          (ENNReal.ofReal |Algebra.norm ℝ (Matrix.of X).det| ^ 2)⁻¹
      ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) =
    ∫⁻ c, ∫⁻ δ in {δ | IsUnit δ}, Ψ (c, δ) * (ENNReal.ofReal |Algebra.norm ℝ δ| ^ 2)⁻¹ ∂μ
      ∂(Measure.pi fun _ : Fin 2 => μ) := by
  haveI := hμ
  exact main (μ := μ) hA w hw hw1 Ψ hΨ
