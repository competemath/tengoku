import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing

set_option autoImplicit false

open MeasureTheory NumberField

noncomputable section

namespace AutomorphicForm
export _root_.AutomorphicForm (unipotentGL2 unipotentGL2_coe)
namespace ArchUnipotentCoord
open _root_.AutomorphicForm

open scoped Classical

section General

variable {E F : Type*} [CommRing E] [Field F] (χ : E →+* F)

def ucoχ (Y : Matrix (Fin 2) (Fin 2) E) : F :=
  if χ (Y 0 0) ≠ 0 then χ (Y 0 1) / χ (Y 0 0) else χ (Y 1 1) / χ (Y 1 0)

/--
@isnad1 id=eq.0h4v.s8.45b81676b1a2 from=translated src=- shape=ff748987 vocab=62f6e7df
-/
theorem mul_unip_apply_fst (Y : Matrix (Fin 2) (Fin 2) E) (t : E) (i : Fin 2) :
    (Y * !![(1 : E), t; 0, 1]) i 0 = Y i 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h4v.s8.85da7dec7395 from=translated src=- shape=15ec834a vocab=8167f5f8
-/
theorem mul_unip_apply_snd (Y : Matrix (Fin 2) (Fin 2) E) (t : E) (i : Fin 2) :
    (Y * !![(1 : E), t; 0, 1]) i 1 = Y i 0 * t + Y i 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.1h5v.s9.250776e3112e from=translated src=- shape=ad861898 vocab=09e17e8c
-/
theorem ucoχ_mul_unip (Y : Matrix (Fin 2) (Fin 2) E) (t : E) (hdet : χ Y.det ≠ 0) :
    ucoχ χ (Y * !![(1 : E), t; 0, 1]) = ucoχ χ Y + χ t := by
  unfold ucoχ
  rw [mul_unip_apply_fst, mul_unip_apply_fst, mul_unip_apply_snd, mul_unip_apply_snd]
  by_cases h0 : χ (Y 0 0) ≠ 0
  · rw [ite_eq_left h0, ite_eq_left h0, map_add, map_mul, add_div, mul_div_cancel_left₀ _ h0, add_comm]
  · rw [ite_eq_right h0, ite_eq_right h0]
    have h0' : χ (Y 0 0) = 0 := not_not.mp h0
    have h1 : χ (Y 1 0) ≠ 0 := by
      intro h1
      apply hdet
      rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, h0', h1, zero_mul, mul_zero, sub_zero]
    rw [map_add, map_mul, add_div, mul_div_cancel_left₀ _ h1, add_comm]

end General

section Arch

variable (K : Type) [Field K] [NumberField K]

abbrev Kinf : Type := InfiniteAdeleRing K

abbrev Mix : Type := mixedEmbedding.mixedSpace K

abbrev eK : Kinf K ≃+* Mix K := InfiniteAdeleRing.ringEquiv_mixedSpace K

/--
@isnad1 id=continuo.0h1v.s9.6144e8084526 from=translated src=- shape=cc48130c vocab=ec28dac1
-/
theorem continuous_eK : Continuous (eK K) := by
  have h : (eK K : Kinf K → Mix K) = fun x =>
      ((fun v : {w : InfinitePlace K // w.IsReal} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v.1)),
        (fun v : {w : InfinitePlace K // w.IsComplex} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v.1))) := rfl
  rw [h]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply v.1)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply v.1)

scoped instance mMK : MeasurableSpace (Matrix (Fin 2) (Fin 2) (Kinf K)) := borel _
/--
@isnad1 id=borelspa.0h1v.s5.0d004c9bd0c1 from=translated src=- shape=acd7839c vocab=24ef12a8
-/
scoped instance bMK : BorelSpace (Matrix (Fin 2) (Fin 2) (Kinf K)) := ⟨rfl⟩
scoped instance mME : MeasurableSpace (Matrix (Fin 2) (Fin 2) (Mix K)) := borel _
/--
@isnad1 id=borelspa.0h1v.s7.1363798aa864 from=translated src=- shape=acd7839c vocab=1c90a6a2
-/
scoped instance bME : BorelSpace (Matrix (Fin 2) (Fin 2) (Mix K)) := ⟨rfl⟩

def χR (w : {w : InfinitePlace K // w.IsReal}) : Mix K →+* ℝ :=
  (Pi.evalRingHom (fun _ : {w : InfinitePlace K // w.IsReal} => ℝ) w).comp (RingHom.fst _ _)

def χC (w : {w : InfinitePlace K // w.IsComplex}) : Mix K →+* ℂ :=
  (Pi.evalRingHom (fun _ : {w : InfinitePlace K // w.IsComplex} => ℂ) w).comp (RingHom.snd _ _)

/--
@isnad1 id=eq.0h3v.s8.d5f6d45187a6 from=translated src=- shape=fc895c17 vocab=96c57bce
-/
theorem χR_apply (w : {w : InfinitePlace K // w.IsReal}) (z : Mix K) : χR K w z = z.1 w := rfl

/--
@isnad1 id=eq.0h3v.s8.83239005cb19 from=translated src=- shape=fb300e77 vocab=fc50a7ba
-/
theorem χC_apply (w : {w : InfinitePlace K // w.IsComplex}) (z : Mix K) : χC K w z = z.2 w := rfl

/--
@isnad1 id=continuo.0h2v.s8.13cc01aa786c from=translated src=- shape=5539117d vocab=24c847f5
-/
theorem continuous_χR (w : {w : InfinitePlace K // w.IsReal}) : Continuous (χR K w) :=
  (continuous_apply w).comp continuous_fst

/--
@isnad1 id=continuo.0h2v.s8.0ef9d3926a91 from=translated src=- shape=5539117d vocab=3a49a5db
-/
theorem continuous_χC (w : {w : InfinitePlace K // w.IsComplex}) : Continuous (χC K w) :=
  (continuous_apply w).comp continuous_snd

def ucoE (Y : Matrix (Fin 2) (Fin 2) (Mix K)) : Mix K :=
  (fun w => ucoχ (χR K w) Y, fun w => ucoχ (χC K w) Y)

def uco (X : Matrix (Fin 2) (Fin 2) (Kinf K)) : Mix K := ucoE K (X.map (eK K))

/--
@isnad1 id=measurab.1h3v.s9.235d8a3c2c08 from=translated src=- shape=b36a34da vocab=3c15f1e3
-/
theorem measurable_ucoχ {F : Type*} [NormedField F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F]
    (χ : Mix K →+* F) (hχ : Continuous χ) : Measurable fun Y : Matrix (Fin 2) (Fin 2) (Mix K) => ucoχ χ Y := by
  have hij : ∀ i j : Fin 2, Measurable fun Y : Matrix (Fin 2) (Fin 2) (Mix K) => χ (Y i j) := fun i j =>
    (hχ.comp (continuous_id.matrix_elem i j)).measurable
  unfold ucoχ
  refine Measurable.ite ?_ ((hij 0 1).div (hij 0 0)) ((hij 1 1).div (hij 1 0))
  exact (hij 0 0) (measurableSet_singleton (0 : F)).compl

/--
@isnad1 id=measurab.0h1v.s7.5b809a65bb5c from=translated src=- shape=3a1addc8 vocab=ada1d41f
-/
theorem measurable_ucoE : Measurable (ucoE K) := by
  unfold ucoE
  exact (measurable_pi_lambda _ fun w => measurable_ucoχ K (χR K w) (continuous_χR K w)).prodMk
    (measurable_pi_lambda _ fun w => measurable_ucoχ K (χC K w) (continuous_χC K w))

/--
@isnad1 id=continuo.0h1v.s10.79ad215598b5 from=translated src=- shape=1778aecd vocab=0ac13e8c
-/
theorem continuous_mapE : Continuous fun X : Matrix (Fin 2) (Fin 2) (Kinf K) => X.map (eK K) :=
  continuous_id.matrix_map (continuous_eK K)

/--
@isnad1 id=measurab.0h1v.s7.5fee515c4827 from=translated src=- shape=e200eed2 vocab=b53805e4
-/
theorem measurable_uco : Measurable (uco K) :=
  (measurable_ucoE K).comp (continuous_mapE K).measurable

/--
@isnad1 id=eq.1h3v.s10.6ba5eadb5130 from=translated src=- shape=9b6d1a80 vocab=d968bf94
-/
theorem ucoE_mul_unip (Y : Matrix (Fin 2) (Fin 2) (Mix K)) (t : Mix K) (hdet : IsUnit Y.det) :
    ucoE K (Y * !![(1 : Mix K), t; 0, 1]) = ucoE K Y + t := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · show ucoχ (χR K w) (Y * !![(1 : Mix K), t; 0, 1]) = ucoχ (χR K w) Y + t.1 w
    rw [← χR_apply K w t]
    exact ucoχ_mul_unip (χR K w) Y t (hdet.map (χR K w)).ne_zero
  · show ucoχ (χC K w) (Y * !![(1 : Mix K), t; 0, 1]) = ucoχ (χC K w) Y + t.2 w
    rw [← χC_apply K w t]
    exact ucoχ_mul_unip (χC K w) Y t (hdet.map (χC K w)).ne_zero

/--
@isnad1 id=eq.0h2v.s11.c762bffd6505 from=translated src=- shape=bea04171 vocab=811c18be
-/
theorem map_unip (x : Kinf K) :
    (!![(1 : Kinf K), x; 0, 1] : Matrix (Fin 2) (Fin 2) (Kinf K)).map (eK K) = !![(1 : Mix K), eK K x; 0, 1] := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply]
  fin_cases i <;> fin_cases j <;>
    simp [-InfiniteAdeleRing.ringEquiv_mixedSpace_apply, map_one, map_zero]

/--
@isnad1 id=eq.0h3v.s10.bebd423fa571 from=translated src=- shape=b3e95d72 vocab=4f89ed14
-/
theorem uco_mul_unipotentGL2 (g : GL (Fin 2) (Kinf K)) (x : Kinf K) :
    uco K ((g * AutomorphicForm.unipotentGL2 x : GL (Fin 2) (Kinf K)) : Matrix (Fin 2) (Fin 2) (Kinf K)) =
      uco K (g : Matrix (Fin 2) (Fin 2) (Kinf K)) + eK K x := by
  unfold uco
  rw [Units.val_mul, AutomorphicForm.unipotentGL2_coe, Matrix.map_mul, map_unip]
  refine ucoE_mul_unip K _ _ ?_
  have h : ((g : Matrix (Fin 2) (Fin 2) (Kinf K)).map (eK K)).det =
      eK K (g : Matrix (Fin 2) (Fin 2) (Kinf K)).det := by
    have h0 := RingHom.map_det ((eK K).toRingHom) (g : Matrix (Fin 2) (Fin 2) (Kinf K))
    rw [RingHom.mapMatrix_apply] at h0
    exact h0.symm
  rw [h]
  have hu : IsUnit (g : Matrix (Fin 2) (Fin 2) (Kinf K)).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.isUnit _
  exact hu.map (eK K)

/--
@isnad1 id=ex.0h1v.s10.bb4bc8f0f55f from=translated src=- shape=3e309fa2 vocab=f2a1b139
-/
theorem main :
    ∃ y : Matrix (Fin 2) (Fin 2) (Kinf K) → Mix K,
      Measurable y ∧
      ∀ (g : GL (Fin 2) (Kinf K)) (x : Kinf K),
        y ((g * AutomorphicForm.unipotentGL2 x : GL (Fin 2) (Kinf K)) : Matrix (Fin 2) (Fin 2) (Kinf K)) =
          y (g : Matrix (Fin 2) (Fin 2) (Kinf K)) + eK K x :=
  ⟨uco K, measurable_uco K, uco_mul_unipotentGL2 K⟩

end Arch

end AutomorphicForm.ArchUnipotentCoord
open scoped _root_.P2MW.S_AutomorphicForm_exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing.AutomorphicForm.ArchUnipotentCoord
open scoped _root_.P2MW.S_AutomorphicForm_exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing.AutomorphicForm

end
open scoped _root_.P2MW.S_AutomorphicForm_exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_measurable_forall_apply_mul_unipotentGL2_eq_add_infiniteAdeleRing.AutomorphicForm.ArchUnipotentCoord

open MeasureTheory NumberField in
/--
@isnad1 id=ex.0h1v.s10.23377f8d2789 from=translated src=- shape=3e309fa2 vocab=5306fedf
-/
theorem solution
    (K : Type) [Field K] [NumberField K] :
    ∃ y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) → mixedEmbedding.mixedSpace K,
      Measurable[borel _] y ∧
      ∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (x : InfiniteAdeleRing K),
        y ((g * AutomorphicForm.unipotentGL2 x : GL (Fin 2) (InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) =
          y (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) + InfiniteAdeleRing.ringEquiv_mixedSpace K x :=
  AutomorphicForm.ArchUnipotentCoord.main K
