import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicHeight
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_WeylIntertwining
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_AdelicLsXi
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_WindowedSiegelTopology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_diagonal_mul_and_continuous.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_diagonal_mul_and_continuous

set_option autoImplicit false

open _root_.NumberField open _root_.IsDedekindDomain open _root_.AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace NumberField
export _root_.NumberField (place AdeleRing AdelicHeight.finLocalHeight_eq_one AdelicHeight.adelicHeight AdelicHeight.adelicHeight_pos AdelicHaar.fact_isOpen_adicCompletionIntegers AdelicHaar.glBorel)
namespace AdelicHeight
export _root_.NumberField.AdelicHeight (rowMaxNorm rowMaxNorm_pos finLocalHeight finLocalHeight_eq_one finHeight adelicHeight norm_le_one_of_mem_adicCompletionIntegers hasFiniteMulSupport_finLocalHeight adelicHeight_pos)
namespace WeightInv
open _root_.NumberField.AdelicHeight open _root_.NumberField

open AutomorphicForm.WindowedSiegel NumberField.AdelicLevel

section Local

variable {K : Type*} [NormedField K]

/--
@isnad1 id=eq.1h4v.s9.55741812753f from=translated src=- shape=819413a3 vocab=095946d9
-/
theorem diag_mul_apply_zero (d g : GL (Fin 2) K) (hd01 : (d : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) (j : Fin 2) :
    ((d * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 j =
      (d : Matrix (Fin 2) (Fin 2) K) 0 0 * (g : Matrix (Fin 2) (Fin 2) K) 0 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, hd01]

/--
@isnad1 id=eq.1h4v.s9.677ecc12c0aa from=translated src=- shape=819413a3 vocab=095946d9
-/
theorem diag_mul_apply_one (d g : GL (Fin 2) K) (hd10 : (d : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (j : Fin 2) :
    ((d * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 j =
      (d : Matrix (Fin 2) (Fin 2) K) 1 1 * (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, hd10]

/--
@isnad1 id=eq.1h4v.s9.ca9d73339d41 from=translated src=- shape=819413a3 vocab=095946d9
-/
theorem weyl_mul_apply_one (w M : GL (Fin 2) K) (hw11 : (w : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) (j : Fin 2) :
    ((w * M : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 j =
      (w : Matrix (Fin 2) (Fin 2) K) 1 0 * (M : Matrix (Fin 2) (Fin 2) K) 0 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, hw11]

/--
@isnad1 id=eq.1h2v.s8.426514c43e77 from=translated src=- shape=16e56aa6 vocab=5403415d
-/
theorem det_diag (d : GL (Fin 2) K) (hd10 : (d : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    (d : Matrix (Fin 2) (Fin 2) K).det = (d : Matrix (Fin 2) (Fin 2) K) 0 0 * (d : Matrix (Fin 2) (Fin 2) K) 1 1 := by
  rw [Matrix.det_fin_two, hd10, mul_zero, sub_zero]

/--
@isnad1 id=and.1h2v.s8.04bfcf566308 from=translated src=- shape=5c6bcf1e vocab=8300a5e6
-/
theorem diag_entries_ne_zero (d : GL (Fin 2) K) (hd10 : (d : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    (d : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 ∧ (d : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
  have h := (Matrix.isUnits_det_units d).ne_zero
  rw [det_diag d hd10] at h
  exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

/--
@isnad1 id=eq.1h3v.s9.65b21e184e43 from=translated src=- shape=b214fea7 vocab=cb6f4c85
-/
theorem rowMaxNorm_diag_mul (d g : GL (Fin 2) K) (hd10 : (d : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    rowMaxNorm ((d * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ‖(d : Matrix (Fin 2) (Fin 2) K) 1 1‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  unfold rowMaxNorm
  rw [diag_mul_apply_one d g hd10, diag_mul_apply_one d g hd10, norm_mul, norm_mul,
    mul_max_of_nonneg _ _ (norm_nonneg _)]

/--
@isnad1 id=eq.2h4v.s10.f01a9beadd42 from=translated src=- shape=99576ccf vocab=cb6f4c85
-/
theorem rowMaxNorm_weyl_diag_mul (w d g : GL (Fin 2) K) (hw11 : (w : Matrix (Fin 2) (Fin 2) K) 1 1 = 0)
    (hd01 : (d : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) :
    rowMaxNorm ((w * (d * g) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ‖(d : Matrix (Fin 2) (Fin 2) K) 0 0‖ * rowMaxNorm ((w * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  unfold rowMaxNorm
  rw [weyl_mul_apply_one w _ hw11, weyl_mul_apply_one w _ hw11, weyl_mul_apply_one w _ hw11,
    weyl_mul_apply_one w _ hw11, diag_mul_apply_zero d g hd01, diag_mul_apply_zero d g hd01]
  have e : ∀ x : K, ‖(w : Matrix (Fin 2) (Fin 2) K) 1 0 * ((d : Matrix (Fin 2) (Fin 2) K) 0 0 * x)‖ =
      ‖(d : Matrix (Fin 2) (Fin 2) K) 0 0‖ * ‖(w : Matrix (Fin 2) (Fin 2) K) 1 0 * x‖ := by
    intro x; rw [norm_mul, norm_mul, norm_mul]; ring
  rw [e, e, mul_max_of_nonneg _ _ (norm_nonneg _)]

/--
@isnad1 id=eq.1h3v.s9.730c3a2be70e from=translated src=- shape=7a771558 vocab=ccd12931
-/
theorem rowNormSq_diag_mul (d g : GL (Fin 2) K) (hd10 : (d : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    rowNormSq ((d * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ‖(d : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2 * rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  unfold rowNormSq
  rw [diag_mul_apply_one d g hd10, diag_mul_apply_one d g hd10, norm_mul, norm_mul]; ring

/--
@isnad1 id=eq.2h4v.s10.6020dcd69b91 from=translated src=- shape=bfe34226 vocab=ccd12931
-/
theorem rowNormSq_weyl_diag_mul (w d g : GL (Fin 2) K) (hw11 : (w : Matrix (Fin 2) (Fin 2) K) 1 1 = 0)
    (hd01 : (d : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) :
    rowNormSq ((w * (d * g) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ‖(d : Matrix (Fin 2) (Fin 2) K) 0 0‖ ^ 2 * rowNormSq ((w * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  unfold rowNormSq
  rw [weyl_mul_apply_one w _ hw11, weyl_mul_apply_one w _ hw11, weyl_mul_apply_one w _ hw11,
    weyl_mul_apply_one w _ hw11, diag_mul_apply_zero d g hd01, diag_mul_apply_zero d g hd01]
  simp only [norm_mul]; ring

/--
@isnad1 id=eq.1h3v.s9.a9ed0e2994cc from=translated src=- shape=5cf9e671 vocab=5403415d
-/
theorem det_diag_mul (d g : GL (Fin 2) K) (hd10 : (d : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    ((d * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
      (d : Matrix (Fin 2) (Fin 2) K) 0 0 * (d : Matrix (Fin 2) (Fin 2) K) 1 1 * (g : Matrix (Fin 2) (Fin 2) K).det := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, det_diag d hd10]

/--
@isnad1 id=eq.1h4v.s10.cbdfcfa80267 from=translated src=- shape=aa53c3e2 vocab=5403415d
-/
theorem det_weyl_diag_mul (w d g : GL (Fin 2) K) (hd10 : (d : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    ((w * (d * g) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
      (d : Matrix (Fin 2) (Fin 2) K) 0 0 * (d : Matrix (Fin 2) (Fin 2) K) 1 1 *
        ((w * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, det_diag_mul d g hd10, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.det_mul]; ring

/--
@isnad1 id=eq.3h4v.s10.99cc0cf41cb9 from=translated src=- shape=1e2c968f vocab=7b4171b7
-/
theorem finLocalHeight_key (w d g : GL (Fin 2) K) (hw11 : (w : Matrix (Fin 2) (Fin 2) K) 1 1 = 0)
    (hd10 : (d : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (hd01 : (d : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) :
    finLocalHeight (d * g) * finLocalHeight (w * (d * g)) = finLocalHeight g * finLocalHeight (w * g) := by
  obtain ⟨ha, hb⟩ := diag_entries_ne_zero d hd10
  have ha' : ‖(d : Matrix (Fin 2) (Fin 2) K) 0 0‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hb' : ‖(d : Matrix (Fin 2) (Fin 2) K) 1 1‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hr1 := (rowMaxNorm_pos g).ne'
  have hr2 := (rowMaxNorm_pos (w * g)).ne'
  unfold finLocalHeight
  rw [rowMaxNorm_diag_mul d g hd10, rowMaxNorm_weyl_diag_mul w d g hw11 hd01, det_diag_mul d g hd10,
    det_weyl_diag_mul w d g hd10, norm_mul, norm_mul, norm_mul, norm_mul]
  field_simp

/--
@isnad1 id=eq.3h4v.s10.f97f95cb8748 from=translated src=- shape=1e2c968f vocab=e11c63a9
-/
theorem localHeight_key (w d g : GL (Fin 2) K) (hw11 : (w : Matrix (Fin 2) (Fin 2) K) 1 1 = 0)
    (hd10 : (d : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (hd01 : (d : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) :
    localHeight (d * g) * localHeight (w * (d * g)) = localHeight g * localHeight (w * g) := by
  obtain ⟨ha, hb⟩ := diag_entries_ne_zero d hd10
  have ha' : ‖(d : Matrix (Fin 2) (Fin 2) K) 0 0‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hb' : ‖(d : Matrix (Fin 2) (Fin 2) K) 1 1‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hr1 := (localHeight_pos g)
  have hr2 := (localHeight_pos (w * g))
  have hq1 : rowNormSq (g : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
    intro h0; unfold localHeight at hr1; rw [h0, div_zero] at hr1; exact lt_irrefl _ hr1
  have hq2 : rowNormSq ((w * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
    intro h0; unfold localHeight at hr2; rw [h0, div_zero] at hr2; exact lt_irrefl _ hr2
  unfold localHeight
  rw [rowNormSq_diag_mul d g hd10, rowNormSq_weyl_diag_mul w d g hw11 hd01, det_diag_mul d g hd10,
    det_weyl_diag_mul w d g hd10, norm_mul, norm_mul, norm_mul, norm_mul]
  field_simp

/--
@isnad1 id=continuo.0h1v.s7.cd8b61ef498f from=translated src=- shape=9263210e vocab=c3365bc1
-/
theorem continuous_finLocalHeight : Continuous (finLocalHeight : GL (Fin 2) K → ℝ) := by
  unfold finLocalHeight
  refine Continuous.div ?_ ?_ fun g => (pow_pos (rowMaxNorm_pos g) 2).ne'
  · exact (Units.continuous_val.matrix_det).norm
  · refine Continuous.pow ?_ 2
    unfold rowMaxNorm
    exact ((Units.continuous_val.matrix_elem 1 0).norm).max ((Units.continuous_val.matrix_elem 1 1).norm)

end Local

section Adelic

variable (F : Type) [Field F] [NumberField F]

/--
@isnad1 id=eq.0h1v.s8.936e20c4501c from=translated src=- shape=8baec59f vocab=108177a5
-/
theorem adelicWeyl_apply_one_one :
    ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = 0 := by
  change algebraMap F (AdeleRing (𝓞 F) F) ((gl2Weyl : GL (Fin 2) F) 1 1) = 0
  have : ((gl2Weyl : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := rfl
  rw [this, map_zero]

/--
@isnad1 id=eq.2h3v.s12.8670ea42d0d0 from=translated src=- shape=364bd793 vocab=c3e00cc2
-/
theorem archHeight_key (h g : AdelicGL2 (𝓞 F) F)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 0) :
    archHeight F (glArch (𝓞 F) F (h * g)) * archHeight F (glArch (𝓞 F) F (adelicWeyl (𝓞 F) F * (h * g))) =
      archHeight F (glArch (𝓞 F) F g) * archHeight F (glArch (𝓞 F) F (adelicWeyl (𝓞 F) F * g)) := by
  unfold archHeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← mul_pow, ← mul_pow]
  congr 1
  simp only [map_mul]
  refine localHeight_key _ _ _ ?_ ?_ ?_
  · rw [archComponent_apply, glArch_apply, adelicWeyl_apply_one_one]; rfl
  · rw [archComponent_apply, glArch_apply, h10]; rfl
  · rw [archComponent_apply, glArch_apply, h01]; rfl

/--
@isnad1 id=eq.2h3v.s12.442d953a9d81 from=translated src=- shape=801d6323 vocab=766f5fc7
-/
theorem finHeight_key (h g : AdelicGL2 (𝓞 F) F)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 0) :
    finHeight F (glFin (𝓞 F) F (h * g)) * finHeight F (glFin (𝓞 F) F (adelicWeyl (𝓞 F) F * (h * g))) =
      finHeight F (glFin (𝓞 F) F g) * finHeight F (glFin (𝓞 F) F (adelicWeyl (𝓞 F) F * g)) := by
  unfold finHeight
  rw [← finprod_mul_distrib (hasFiniteMulSupport_finLocalHeight _) (hasFiniteMulSupport_finLocalHeight _),
    ← finprod_mul_distrib (hasFiniteMulSupport_finLocalHeight _) (hasFiniteMulSupport_finLocalHeight _)]
  refine finprod_congr fun v => ?_
  simp only [map_mul]
  refine finLocalHeight_key _ _ _ ?_ ?_ ?_
  · rw [finComponent_apply, glFin_apply, adelicWeyl_apply_one_one]; rfl
  · rw [finComponent_apply, glFin_apply, h10]; rfl
  · rw [finComponent_apply, glFin_apply, h01]; rfl

/--
@isnad1 id=eq.2h3v.s10.1085ac31f72b from=translated src=- shape=a8d27b1a vocab=84b1d139
-/
theorem adelicHeight_key (h g : AdelicGL2 (𝓞 F) F)
    (h10 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0)
    (h01 : (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 0) :
    adelicHeight F (h * g) * adelicHeight F (adelicWeyl (𝓞 F) F * (h * g)) =
      adelicHeight F g * adelicHeight F (adelicWeyl (𝓞 F) F * g) := by
  unfold adelicHeight
  have ha := archHeight_key F h g h10 h01
  have hf := finHeight_key F h g h10 h01
  calc archHeight F (glArch (𝓞 F) F (h * g)) * finHeight F (glFin (𝓞 F) F (h * g)) *
        (archHeight F (glArch (𝓞 F) F (adelicWeyl (𝓞 F) F * (h * g))) *
          finHeight F (glFin (𝓞 F) F (adelicWeyl (𝓞 F) F * (h * g))))
      = (archHeight F (glArch (𝓞 F) F (h * g)) * archHeight F (glArch (𝓞 F) F (adelicWeyl (𝓞 F) F * (h * g)))) *
        (finHeight F (glFin (𝓞 F) F (h * g)) * finHeight F (glFin (𝓞 F) F (adelicWeyl (𝓞 F) F * (h * g)))) := by ring
    _ = (archHeight F (glArch (𝓞 F) F g) * archHeight F (glArch (𝓞 F) F (adelicWeyl (𝓞 F) F * g))) *
        (finHeight F (glFin (𝓞 F) F g) * finHeight F (glFin (𝓞 F) F (adelicWeyl (𝓞 F) F * g))) := by rw [ha, hf]
    _ = archHeight F (glArch (𝓞 F) F g) * finHeight F (glFin (𝓞 F) F g) *
        (archHeight F (glArch (𝓞 F) F (adelicWeyl (𝓞 F) F * g)) * finHeight F (glFin (𝓞 F) F (adelicWeyl (𝓞 F) F * g))) := by
          ring

/--
@isnad1 id=continuo.0h1v.s8.94ad827308ae from=translated src=- shape=96b16265 vocab=c9ed7cfe
-/
theorem continuous_finHeight : Continuous (finHeight F) := by
  refine continuous_iff_continuousAt.mpr fun g₀ => ?_

  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (∀ i j, (g₀ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F) ∧
      ∀ i j, ((g₀⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F := by
    refine (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_).and
      (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_)
    · exact ((g₀ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j).2
    · exact (((g₀⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j).2
  obtain ⟨S, hS⟩ : ∃ S : Set (HeightOneSpectrum (𝓞 F)), S.Finite ∧ ∀ v, v ∉ S →
      (∀ i j, (g₀ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F) ∧
      ∀ i j, ((g₀⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F :=
    ⟨_, Filter.eventually_cofinite.mp hev, fun v hv => not_not.mp hv⟩

  have hO : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => (AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 F) F).out v
  have hV : IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem hO
  set U : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
    ⋂ i : Fin 2, ⋂ j : Fin 2,
      ((fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) ⁻¹'
          {x : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F} ∩
        (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
            ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) ⁻¹'
          {x : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F}) with hU
  have hUo : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
    · exact hV.preimage (Units.continuous_val.matrix_elem i j)
    · exact hV.preimage (Units.continuous_coe_inv.matrix_elem i j)
  have hg₀ : g₀ ∈ U := by
    simp only [hU, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    exact fun i j => ⟨fun v hv => (hS.2 v hv).1 i j, fun v hv => (hS.2 v hv).2 i j⟩
  have heq : ∀ g ∈ U, ∏ v ∈ hS.1.toFinset, finLocalHeight (finComponent (𝓞 F) F v g) = finHeight F g := by
    intro g hg
    simp only [hU, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] at hg
    unfold finHeight
    refine (finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_).symm
    rw [Set.Finite.coe_toFinset]
    by_contra hvS
    refine hv ?_
    refine finLocalHeight_eq_one _ (fun i j => ?_) (fun i j => ?_)
    · rw [finComponent_apply]
      exact norm_le_one_of_mem_adicCompletionIntegers ((hg i j).1 v hvS)
    · rw [← map_inv, finComponent_apply]
      exact norm_le_one_of_mem_adicCompletionIntegers ((hg i j).2 v hvS)
  have hcont : Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      ∏ v ∈ hS.1.toFinset, finLocalHeight (finComponent (𝓞 F) F v g) :=
    continuous_finsetProd _ fun v _ => continuous_finLocalHeight.comp (continuous_finComponent (𝓞 F) F v)
  exact hcont.continuousAt.congr (Filter.eventuallyEq_of_mem (hUo.mem_nhds hg₀) heq)

/--
@isnad1 id=continuo.0h1v.s7.7eda43131717 from=translated src=- shape=df608a4b vocab=457f2148
-/
theorem continuous_adelicHeight : Continuous (adelicHeight F) := by
  have : adelicHeight F = fun g => archHeight F (glArch (𝓞 F) F g) * finHeight F (glFin (𝓞 F) F g) := rfl
  rw [this]
  exact ((continuous_archHeight F).comp (continuous_glArch (𝓞 F) F)).mul
    ((continuous_finHeight F).comp (continuous_glFin (𝓞 F) F))

end Adelic

end NumberField.AdelicHeight.WeightInv

end

open NumberField.AdelicHeight.WeightInv in

/--
@isnad1 id=and.0h1v.s10.efa07cf01d09 from=translated src=- shape=5bfe3fa9 vocab=3cac2af5
-/
theorem solution
    (F : Type) [Field F] [NumberField F] :
    (∀ (h : AdelicGL2 (𝓞 F) F),
      (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 →
      (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 0 →
      ∀ g : AdelicGL2 (𝓞 F) F,
        -Real.log (NumberField.AdelicHeight.adelicHeight F (h * g))
            - Real.log (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * (h * g))) =
          -Real.log (NumberField.AdelicHeight.adelicHeight F g)
            - Real.log (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * g))) ∧
    Continuous (fun g : AdelicGL2 (𝓞 F) F =>
      -Real.log (NumberField.AdelicHeight.adelicHeight F g)
        - Real.log (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * g))) := by
  refine ⟨fun h h10 h01 g => ?_, ?_⟩
  · have h1 := NumberField.AdelicHeight.adelicHeight_pos (F := F) (h * g)
    have h2 := NumberField.AdelicHeight.adelicHeight_pos (F := F) (AutomorphicForm.adelicWeyl (𝓞 F) F * (h * g))
    have h3 := NumberField.AdelicHeight.adelicHeight_pos (F := F) g
    have h4 := NumberField.AdelicHeight.adelicHeight_pos (F := F) (AutomorphicForm.adelicWeyl (𝓞 F) F * g)
    have key := adelicHeight_key F h g h10 h01
    have e1 : -Real.log (NumberField.AdelicHeight.adelicHeight F (h * g))
        - Real.log (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * (h * g))) =
        -Real.log (NumberField.AdelicHeight.adelicHeight F (h * g) *
          NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * (h * g))) := by
      rw [Real.log_mul h1.ne' h2.ne']; ring
    have e2 : -Real.log (NumberField.AdelicHeight.adelicHeight F g)
        - Real.log (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * g)) =
        -Real.log (NumberField.AdelicHeight.adelicHeight F g *
          NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * g)) := by
      rw [Real.log_mul h3.ne' h4.ne']; ring
    rw [e1, e2, key]
  · have hc := continuous_adelicHeight F
    refine ((hc.log fun g => (NumberField.AdelicHeight.adelicHeight_pos g).ne').neg).sub ?_
    exact (hc.comp (continuous_const.mul continuous_id)).log
      fun g => (NumberField.AdelicHeight.adelicHeight_pos _).ne'
