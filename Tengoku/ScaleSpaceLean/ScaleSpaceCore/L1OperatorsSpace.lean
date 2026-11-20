/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.L1Operators
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `L¹(E)` over a finite-dimensional space: translation, reflection, linear dilation, and
convolution by a measure

Home: none (standard analysis in Mathlib's types: `ScaleSpaceCore.L1Operators`'s operators over a
finite-dimensional space with an additive Haar measure; ref: @larsen1971introduction, Thm. 0.1.1,
p. 2)

Q-0332 (SSL-5 of Paper VII's `records/formalization/SECOND-DEMAND.md`). The operators of
`ScaleSpaceCore.L1Operators`, written over a finite-dimensional real normed space `E` carrying an
additive Haar measure as its `volume`, so that `EuclideanSpace ℝ (Fin d)` and `ℝ` are both
instances. This is a generalization written in the trunk, not an extraction: the author decided on
2026-10-05 (Q-0281) that the trunk writes the `d`-dimensional form first and Paper VII proves its
operator nodes against it.

## Design

* The setting is `[MeasureSpace E] [IsAddHaarMeasure (volume : Measure E)]`: translation
  invariance is what the translation and convolution operators use, and the `|det|` change of
  variables (`addHaar_preimage_continuousLinearEquiv`) is what the dilation uses.
* The general declarations carry the ℝ names with an `E` suffix (`transL1E`, `dilL1E`,
  `mconvL1E`, ...), so that a consumer opening `ScaleSpace` sees no overloaded name. The ℝ
  declarations of `L1Operators` stay as they are; `transL1E_real`, `reflL1E_real`,
  `dilL1E_homothety_real` and `mconvL1E_real` identify the general operator at `E = ℝ` with them.
* The dilation is indexed by `A : E ≃L[ℝ] E`:
  `D_A f = |det A|⁻¹ f(A⁻¹ ·)`, the mass-preserving normalisation, an isometry of `L¹(E)`. The
  isotropic dilation `D_λ f = λ^{-d} f(·/λ)` is `D_A` at `A = homothety λ`, and a rotation
  `R_Q f = f(Q⁻¹ ·)` is `D_Q` at `|det Q| = 1` (`coeFn_dilL1E_of_abs_det_eq_one`).
* `mconvE μ f x = ∫ f(x - y) dμ(y)`, packaged as `mconvL1E μ` for a finite measure `μ`.

## References

* @larsen1971introduction, Thm. 0.1.1 and Cor. 0.1.1, pp. 2–6: a continuous linear operator on
  `L¹(G)` commutes with every translation iff it is convolution by a (unique) bounded measure,
  stated for a general locally compact Abelian group — covers `mconvL1E`'s boundedness at
  `G = E` directly, with no generalisation needed.
* @folland1999real, §2.6, Theorem 2.44, p. 73: for `T ∈ GL(n, ℝ)`,
  `∫ f(x) dx = |det T| ∫ f ∘ T (x) dx` for `f ≥ 0` or `f ∈ L¹` (2.45), and
  `m(T(E)) = |det T| m(E)` for a Lebesgue measurable `E` — the linear change of variables the
  dilation `D_A f = |det A|⁻¹ f(A⁻¹ ·)` and its isometry rest on, through Mathlib's
  `addHaar_preimage_continuousLinearEquiv`, which states it for an additive Haar measure on a
  finite-dimensional space.
-/

namespace ScaleSpace

open MeasureTheory Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E]

section Translation

variable [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- The positive cone of `L¹(E)`.-/
def IsNonnegE (f : E →₁[volume] ℝ) : Prop := 0 ≤ᵐ[volume] (f : E → ℝ)

/-! ## Translation -/

/-- `x ↦ x - a` preserves the Haar measure.
@isnad1 id=measurep.0h2v.s6.6e025898d463 from=translated src=- shape=944eada1 vocab=a826e2b6
-/
theorem measurePreserving_sub_constE (a : E) :
    MeasurePreserving (fun x : E => x - a) volume volume :=
  measurePreserving_sub_right volume a

/--
@isnad1 id=eventual.1h4v.s7.9beb709cf5b1 from=translated src=- shape=312faf9d vocab=3db10075
-/
theorem translate_congr_aeE (a : E) {f g : E → ℝ} (h : f =ᵐ[volume] g) :
    (fun x => f (x - a)) =ᵐ[volume] fun x => g (x - a) :=
  (measurePreserving_sub_constE a).quasiMeasurePreserving.ae h

/--
@isnad1 id=integrab.1h3v.s7.b4b0941c7112 from=translated src=- shape=161d46b6 vocab=2ccdf86f
-/
theorem integrable_translateE {f : E → ℝ} (hf : Integrable f) (a : E) :
    Integrable (fun x => f (x - a)) :=
  ((measurePreserving_sub_constE a).integrable_comp hf.aestronglyMeasurable).mpr hf

/-- `T_a f = f(· - a)` as a linear map on `L¹(E)`.-/
noncomputable def transₗE (a : E) : (E →₁[volume] ℝ) →ₗ[ℝ] (E →₁[volume] ℝ) where
  toFun f := (integrable_translateE (L1.integrable_coeFn f) a).toL1 _
  map_add' f g := by
    rw [← Integrable.toL1_add]
    exact (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (translate_congr_aeE a (Lp.coeFn_add f g))
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← Integrable.toL1_smul']
    exact (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (translate_congr_aeE a (Lp.coeFn_smul c f))

/-- **Translation `T_a f = f(· - a)` is an isometry of `L¹(E)`.**-/
noncomputable def transL1E (a : E) : (E →₁[volume] ℝ) →L[ℝ] (E →₁[volume] ℝ) :=
  (transₗE a).mkContinuous 1 fun f => by
    rw [transₗE, LinearMap.coe_mk, AddHom.coe_mk, Integrable.norm_toL1_eq_lintegral_enorm,
      one_mul, Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
    exact le_of_eq (congrArg ENNReal.toReal
      (lintegral_sub_right_eq_self (fun x => ‖(f : E → ℝ) x‖ₑ) a))

/--
@isnad1 id=eventual.0h3v.s12.17190f9f35c9 from=translated src=- shape=9a9a5a9a vocab=2e65df63
-/
lemma coeFn_transL1E (a : E) (f : E →₁[volume] ℝ) :
    transL1E a f =ᵐ[volume] fun x => (f : E → ℝ) (x - a) :=
  Integrable.coeFn_toL1 (integrable_translateE (L1.integrable_coeFn f) a)

/--
@isnad1 id=le.0h3v.s12.dcc35f35fb22 from=translated src=- shape=c0876106 vocab=e899e6fc
-/
lemma norm_transL1E_le (a : E) (f : E →₁[volume] ℝ) : ‖transL1E a f‖ ≤ ‖f‖ := by
  have hop : ‖transL1E a‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  calc ‖transL1E a f‖ ≤ ‖transL1E a‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := by nlinarith [norm_nonneg f]
    _ = ‖f‖ := one_mul _

/-- **The relational form of translation.** `g = T_a f` in `L¹` exactly when `g = f(· - a)` a.e.
— the bridge from a statement written on representatives to the operator.-/
theorem eq_transL1E_iff (a : E) (f g : E →₁[volume] ℝ) :
    g = transL1E a f ↔ (g : E → ℝ) =ᵐ[volume] fun x => (f : E → ℝ) (x - a) := by
  constructor
  · rintro rfl
    exact coeFn_transL1E a f
  · intro h
    exact Lp.ext (h.trans (coeFn_transL1E a f).symm)

/--
@isnad1 id=eq.0h1v.s12.a798bcd87f2e from=translated src=- shape=c61e7e9a vocab=a12aeced
-/
theorem transL1E_zero : transL1E (0 : E) = ContinuousLinearMap.id ℝ (E →₁[volume] ℝ) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  refine (coeFn_transL1E 0 f).trans ?_
  simp only [sub_zero]
  rfl

/-- `T_a T_b = T_{a + b}`.
@isnad1 id=eq.0h3v.s12.916058357086 from=translated src=- shape=e54c8b36 vocab=7b980da1
-/
theorem transL1E_comp (a b : E) :
    (transL1E a).comp (transL1E b) = transL1E (a + b) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  simp only [ContinuousLinearMap.comp_apply]
  refine (coeFn_transL1E a _).trans ?_
  refine (translate_congr_aeE a (coeFn_transL1E b f)).trans ?_
  refine Filter.EventuallyEq.trans ?_ (coeFn_transL1E (a + b) f).symm
  filter_upwards with x
  rw [sub_sub]

/--
@isnad1 id=isnonneg.1h3v.s12.0586ba3c87cc from=translated src=- shape=7f9b7579 vocab=7c7b34d7
-/
theorem isNonnegE_transL1E (a : E) {f : E →₁[volume] ℝ} (hf : IsNonnegE f) :
    IsNonnegE (transL1E a f) := by
  filter_upwards [coeFn_transL1E a f,
    (measurePreserving_sub_constE a).quasiMeasurePreserving.ae hf] with x hx hfx
  simp only [Pi.zero_apply] at hfx ⊢
  rw [hx]
  exact hfx

end Translation

/-! ## Invertible linear maps: determinant, homothety, the dilated representative -/

variable [NormedSpace ℝ E]

/-- `|det A| ≠ 0` for an invertible `A`.
@isnad1 id=ne.0h2v.s9.151f51d123ab from=translated src=- shape=0f18f45d vocab=8d930bd8
-/
theorem det_ne_zeroE (A : E ≃L[ℝ] E) : LinearMap.det (A : E →ₗ[ℝ] E) ≠ 0 :=
  (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero

/-- `D_A f = |det A|⁻¹ f(A⁻¹ ·)`, the mass-preserving normalisation.-/
noncomputable def dilateE (A : E ≃L[ℝ] E) (f : E → ℝ) : E → ℝ :=
  fun x => |LinearMap.det (A : E →ₗ[ℝ] E)|⁻¹ * f (A.symm x)

/--
@isnad1 id=eq.0h4v.s10.317b7fcd50e8 from=translated src=- shape=819f2e68 vocab=db0d9ab0
-/
lemma dilateE_apply (A : E ≃L[ℝ] E) (f : E → ℝ) (x : E) :
    dilateE A f x = |LinearMap.det (A : E →ₗ[ℝ] E)|⁻¹ * f (A.symm x) := rfl

/-- The homothety `x ↦ λ x`, `λ ≠ 0`, as a continuous linear equivalence.-/
noncomputable def homothety [FiniteDimensional ℝ E] (lam : ℝ) (hlam : lam ≠ 0) : E ≃L[ℝ] E :=
  (LinearEquiv.smulOfNeZero ℝ E lam hlam).toContinuousLinearEquiv

/--
@isnad1 id=eq.1h3v.s8.30e9fdf1f81c from=translated src=- shape=4377e726 vocab=327db405
-/
@[simp] lemma homothety_apply [FiniteDimensional ℝ E] (lam : ℝ) (hlam : lam ≠ 0) (x : E) :
    homothety lam hlam x = lam • x := rfl

/--
@isnad1 id=eq.1h3v.s8.4ee5f7e76ee4 from=translated src=- shape=72571f46 vocab=c2754b8f
-/
@[simp] lemma homothety_symm_apply [FiniteDimensional ℝ E] (lam : ℝ) (hlam : lam ≠ 0) (x : E) :
    (homothety lam hlam).symm x = lam⁻¹ • x := rfl

/--
@isnad1 id=eq.1h2v.s9.05aca47deb8a from=translated src=- shape=1cbfa3c6 vocab=123e3569
-/
lemma det_homothety [FiniteDimensional ℝ E] (lam : ℝ) (hlam : lam ≠ 0) :
    LinearMap.det ((homothety lam hlam : E ≃L[ℝ] E) : E →ₗ[ℝ] E)
      = lam ^ Module.finrank ℝ E := by
  have h : ((homothety lam hlam : E ≃L[ℝ] E) : E →ₗ[ℝ] E) = lam • LinearMap.id := by
    ext x
    rfl
  rw [h, LinearMap.det_smul, LinearMap.det_id, mul_one]

/-- `|det (-id)| = |(-1)^d| = 1`.
@isnad1 id=eq.0h1v.s9.2f4f618f8dc2 from=translated src=- shape=bdf394b3 vocab=b076b412
-/
lemma abs_det_neg [FiniteDimensional ℝ E] :
    |LinearMap.det ((ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E) : E →ₗ[ℝ] E)| = 1 := by
  have h : ((ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E) : E →ₗ[ℝ] E)
      = (-1 : ℝ) • LinearMap.id := by
    ext x
    simp
  rw [h, LinearMap.det_smul, LinearMap.det_id, mul_one, abs_pow, abs_neg, abs_one, one_pow]

/--
@isnad1 id=eq.0h1v.s9.2e8470a28b11 from=translated src=- shape=bdc453d6 vocab=b4ad8ce6
-/
lemma det_refl :
    LinearMap.det ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →ₗ[ℝ] E) = 1 :=
  LinearMap.det_id

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

/-! ## Linear change of variables

For `A : E ≃L[ℝ] E` the pushforward of the Haar measure along `A⁻¹` is `|det A|` times it
(`addHaar_preimage_continuousLinearEquiv`). Everything the dilation does rests on this. -/

/-- **The change of variables**: `A⁻¹_* vol = |det A| · vol`.
@isnad1 id=eq.0h2v.s10.579c8db8a364 from=translated src=- shape=95d750d2 vocab=398d23eb
-/
theorem map_symm_volumeE (A : E ≃L[ℝ] E) :
    Measure.map A.symm volume = ENNReal.ofReal |LinearMap.det (A : E →ₗ[ℝ] E)| • volume := by
  ext s hs
  rw [Measure.map_apply A.symm.continuous.measurable hs,
    Measure.addHaar_preimage_continuousLinearEquiv, ContinuousLinearEquiv.symm_symm]
  rfl

/--
@isnad1 id=quasimea.0h2v.s8.e605dd81e7e5 from=translated src=- shape=33ccf8b9 vocab=d69d4f14
-/
theorem quasiMeasurePreserving_symmE (A : E ≃L[ℝ] E) :
    Measure.QuasiMeasurePreserving A.symm volume volume := by
  refine ⟨A.symm.continuous.measurable, ?_⟩
  rw [map_symm_volumeE]
  exact Measure.smul_absolutelyContinuous

/-- `∫⁻ g(A⁻¹ x) dx = |det A| ∫⁻ g`.
@isnad1 id=eq.0h3v.s10.98488094c93b from=translated src=- shape=886ad95a vocab=5d321b48
-/
theorem lintegral_comp_symmE (A : E ≃L[ℝ] E) (g : E → ℝ≥0∞) :
    ∫⁻ x, g (A.symm x) = ENNReal.ofReal |LinearMap.det (A : E →ₗ[ℝ] E)| * ∫⁻ x, g x := by
  have he : MeasurableEmbedding (A.symm : E → E) := A.symm.toHomeomorph.measurableEmbedding
  rw [← smul_eq_mul, ← lintegral_smul_measure, ← map_symm_volumeE, he.lintegral_map]

/-! ## Dilation -/

/--
@isnad1 id=eventual.1h4v.s7.4f215a6e42d2 from=translated src=- shape=1a75cc04 vocab=d33c5e19
-/
theorem dilateE_congr_ae (A : E ≃L[ℝ] E) {f g : E → ℝ} (h : f =ᵐ[volume] g) :
    dilateE A f =ᵐ[volume] dilateE A g := by
  filter_upwards [(quasiMeasurePreserving_symmE A).ae h] with x hx
  simp only [dilateE, hx]

/--
@isnad1 id=integrab.1h3v.s7.b93aba467bee from=translated src=- shape=23eb97a8 vocab=b5ab4565
-/
theorem integrable_dilateE (A : E ≃L[ℝ] E) {f : E → ℝ} (hf : Integrable f) :
    Integrable (dilateE A f) := by
  have hm : AEStronglyMeasurable (fun x => f (A.symm x)) volume :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving (quasiMeasurePreserving_symmE A)
  have hi : Integrable (fun x => f (A.symm x)) := by
    refine ⟨hm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_comp_symmE A (fun x => ‖f x‖ₑ)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2
  exact hi.const_mul _

/-- `D_A` as a linear map on `L¹(E)`.-/
noncomputable def dilₗE (A : E ≃L[ℝ] E) : (E →₁[volume] ℝ) →ₗ[ℝ] (E →₁[volume] ℝ) where
  toFun f := (integrable_dilateE A (L1.integrable_coeFn f)).toL1 _
  map_add' f g := by
    rw [← Integrable.toL1_add]
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (dilateE_congr_ae A (Lp.coeFn_add f g)).trans ?_
    filter_upwards with x
    simp only [dilateE, Pi.add_apply, mul_add]
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← Integrable.toL1_smul']
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (dilateE_congr_ae A (Lp.coeFn_smul c f)).trans ?_
    filter_upwards with x
    simp only [dilateE, Pi.smul_apply, smul_eq_mul]
    ring

/-- `∫⁻ ‖D_A f‖ = ∫⁻ ‖f‖`: the normalisation `|det A|⁻¹` cancels the Jacobian.
@isnad1 id=eq.0h3v.s7.d349f5b7c289 from=translated src=- shape=afb30845 vocab=4f544ab5
-/
theorem lintegral_enorm_dilateE (A : E ≃L[ℝ] E) (f : E → ℝ) :
    ∫⁻ x, ‖dilateE A f x‖ₑ = ∫⁻ x, ‖f x‖ₑ := by
  have hdet : 0 < |LinearMap.det (A : E →ₗ[ℝ] E)| := abs_pos.mpr (det_ne_zeroE A)
  have henorm : ∀ x, ‖dilateE A f x‖ₑ
      = ENNReal.ofReal |LinearMap.det (A : E →ₗ[ℝ] E)|⁻¹ * ‖f (A.symm x)‖ₑ := by
    intro x
    simp only [dilateE, enorm_mul, Real.enorm_eq_ofReal (inv_nonneg.mpr hdet.le)]
  simp only [henorm]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_comp_symmE A (fun x => ‖f x‖ₑ),
    ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hdet.le), inv_mul_cancel₀ hdet.ne',
    ENNReal.ofReal_one, one_mul]

/-- **The matrix dilation `D_A f = |det A|⁻¹ f(A⁻¹ ·)` is an isometry of `L¹(E)`.**-/
noncomputable def dilL1E (A : E ≃L[ℝ] E) : (E →₁[volume] ℝ) →L[ℝ] (E →₁[volume] ℝ) :=
  (dilₗE A).mkContinuous 1 fun f => by
    rw [dilₗE, LinearMap.coe_mk, AddHom.coe_mk, Integrable.norm_toL1_eq_lintegral_enorm,
      one_mul, Lp.norm_def, eLpNorm_one_eq_lintegral_enorm, lintegral_enorm_dilateE]

/--
@isnad1 id=eventual.0h3v.s12.61ca1d6575ff from=translated src=- shape=49df7c0d vocab=368ef10f
-/
lemma coeFn_dilL1E (A : E ≃L[ℝ] E) (f : E →₁[volume] ℝ) :
    dilL1E A f =ᵐ[volume] dilateE A (f : E → ℝ) :=
  Integrable.coeFn_toL1 (integrable_dilateE A (L1.integrable_coeFn f))

/-- **The relational form of dilation.** `g = D_A f` in `L¹` exactly when
`g = |det A|⁻¹ f(A⁻¹ ·)` a.e.-/
theorem eq_dilL1E_iff (A : E ≃L[ℝ] E) (f g : E →₁[volume] ℝ) :
    g = dilL1E A f ↔ (g : E → ℝ) =ᵐ[volume]
      fun x => |LinearMap.det (A : E →ₗ[ℝ] E)|⁻¹ * (f : E → ℝ) (A.symm x) := by
  constructor
  · rintro rfl
    exact coeFn_dilL1E A f
  · intro h
    exact Lp.ext (h.trans (coeFn_dilL1E A f).symm)

/-- **`D_A` preserves the norm.**
@isnad1 id=eq.0h3v.s12.c549ee91970e from=translated src=- shape=e08d602d vocab=02d7bb6a
-/
theorem norm_dilL1E (A : E ≃L[ℝ] E) (f : E →₁[volume] ℝ) : ‖dilL1E A f‖ = ‖f‖ := by
  have h : ∫⁻ x, ‖(dilL1E A f : E → ℝ) x‖ₑ = ∫⁻ x, ‖dilateE A (f : E → ℝ) x‖ₑ := by
    refine lintegral_congr_ae ?_
    filter_upwards [coeFn_dilL1E A f] with x hx
    rw [hx]
  rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm, Lp.norm_def, eLpNorm_one_eq_lintegral_enorm,
    h, lintegral_enorm_dilateE]

/-- `D_A` at the identity is the identity.
@isnad1 id=eq.0h1v.s12.52b97ec0e38d from=translated src=- shape=9fed7beb vocab=668f7c1b
-/
theorem dilL1E_refl :
    dilL1E (ContinuousLinearEquiv.refl ℝ E) = ContinuousLinearMap.id ℝ (E →₁[volume] ℝ) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  refine (coeFn_dilL1E _ f).trans ?_
  filter_upwards with x
  rw [dilateE_apply, det_refl, abs_one, inv_one, one_mul]
  rfl

/-- **`D_A D_B = D_{AB}`**, with `AB = B.trans A` the composite `x ↦ A (B x)`.
@isnad1 id=eq.0h3v.s12.49100dd1e155 from=translated src=- shape=b20337e8 vocab=4ff5b3bd
-/
theorem dilL1E_comp (A B : E ≃L[ℝ] E) :
    (dilL1E A).comp (dilL1E B) = dilL1E (B.trans A) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  simp only [ContinuousLinearMap.comp_apply]
  refine (coeFn_dilL1E A _).trans ?_
  refine (dilateE_congr_ae A (coeFn_dilL1E B f)).trans ?_
  refine Filter.EventuallyEq.trans ?_ (coeFn_dilL1E (B.trans A) f).symm
  filter_upwards with x
  have hdet : LinearMap.det ((B.trans A : E ≃L[ℝ] E) : E →ₗ[ℝ] E)
      = LinearMap.det (A : E →ₗ[ℝ] E) * LinearMap.det (B : E →ₗ[ℝ] E) := by
    rw [← LinearMap.det_comp]
    rfl
  simp only [dilateE, hdet, abs_mul, mul_inv, ContinuousLinearEquiv.symm_trans_apply]
  ring

/-- **`D_A` is a bijection with inverse `D_{A⁻¹}`.**
@isnad1 id=eq.0h2v.s13.d393b846a632 from=translated src=- shape=f1ae64d7 vocab=db6a7d01
-/
theorem dilL1E_symm_comp (A : E ≃L[ℝ] E) :
    (dilL1E A.symm).comp (dilL1E A) = ContinuousLinearMap.id ℝ (E →₁[volume] ℝ) := by
  rw [dilL1E_comp, ContinuousLinearEquiv.self_trans_symm, dilL1E_refl]

/--
@isnad1 id=eq.0h2v.s13.d90ab3bc0c57 from=translated src=- shape=279a1067 vocab=db6a7d01
-/
theorem dilL1E_comp_symm (A : E ≃L[ℝ] E) :
    (dilL1E A).comp (dilL1E A.symm) = ContinuousLinearMap.id ℝ (E →₁[volume] ℝ) := by
  rw [dilL1E_comp, ContinuousLinearEquiv.symm_trans_self, dilL1E_refl]

/-- `D_A` as a linear isometry equivalence of `L¹(E)`, inverse `D_{A⁻¹}`.-/
noncomputable def dilL1EEquiv (A : E ≃L[ℝ] E) :
    (E →₁[volume] ℝ) ≃ₗᵢ[ℝ] (E →₁[volume] ℝ) where
  toFun := dilL1E A
  invFun := dilL1E A.symm
  map_add' := (dilL1E A).map_add
  map_smul' := (dilL1E A).map_smul
  left_inv f := by
    change ((dilL1E A.symm).comp (dilL1E A)) f = f
    rw [dilL1E_symm_comp]
    rfl
  right_inv f := by
    change ((dilL1E A).comp (dilL1E A.symm)) f = f
    rw [dilL1E_comp_symm]
    rfl
  norm_map' := norm_dilL1E A

/--
@isnad1 id=eq.0h3v.s13.cd63c0d1e53b from=translated src=- shape=02d5a509 vocab=9a11d099
-/
@[simp] lemma dilL1EEquiv_apply (A : E ≃L[ℝ] E) (f : E →₁[volume] ℝ) :
    dilL1EEquiv A f = dilL1E A f := rfl

/--
@isnad1 id=eq.0h3v.s13.c010f3bd2419 from=translated src=- shape=c5092d22 vocab=2f6ff8da
-/
@[simp] lemma dilL1EEquiv_symm_apply (A : E ≃L[ℝ] E) (f : E →₁[volume] ℝ) :
    (dilL1EEquiv A).symm f = dilL1E A.symm f := rfl

/-- **`D_A T_a = T_{Aa} D_A`.**
@isnad1 id=eq.0h3v.s13.0addb9533edb from=translated src=- shape=b90c2bf9 vocab=ae16efe8
-/
theorem dilL1E_comp_transL1E (A : E ≃L[ℝ] E) (a : E) :
    (dilL1E A).comp (transL1E a) = (transL1E (A a)).comp (dilL1E A) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  simp only [ContinuousLinearMap.comp_apply]
  refine ((coeFn_dilL1E A _).trans (dilateE_congr_ae A (coeFn_transL1E a f))).trans ?_
  refine Filter.EventuallyEq.symm ?_
  refine ((coeFn_transL1E (A a) _).trans (translate_congr_aeE (A a) (coeFn_dilL1E A f))).trans ?_
  filter_upwards with x
  simp only [dilateE, map_sub, ContinuousLinearEquiv.symm_apply_apply]

/--
@isnad1 id=isnonneg.1h3v.s12.eadbc8b19312 from=translated src=- shape=db4f48ad vocab=da66ca5b
-/
theorem isNonnegE_dilL1E (A : E ≃L[ℝ] E) {f : E →₁[volume] ℝ} (hf : IsNonnegE f) :
    IsNonnegE (dilL1E A f) := by
  filter_upwards [coeFn_dilL1E A f, (quasiMeasurePreserving_symmE A).ae hf] with x hx hfx
  simp only [Pi.zero_apply] at hfx ⊢
  rw [hx, dilateE_apply]
  exact mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) hfx

/-- `D_A` preserves the integral.
@isnad1 id=eq.0h3v.s12.acae0b9887a2 from=translated src=- shape=17a363ff vocab=9bfcd7da
-/
theorem integral_dilL1E (A : E ≃L[ℝ] E) (f : E →₁[volume] ℝ) :
    ∫ x, (dilL1E A f : E → ℝ) x = ∫ x, (f : E → ℝ) x := by
  have hdet : 0 < |LinearMap.det (A : E →ₗ[ℝ] E)| := abs_pos.mpr (det_ne_zeroE A)
  rw [integral_congr_ae (coeFn_dilL1E A f)]
  simp only [dilateE]
  rw [integral_const_mul, ← integral_map A.symm.continuous.measurable.aemeasurable
      ((Lp.aestronglyMeasurable f).mono_ac
        (by rw [map_symm_volumeE]; exact Measure.smul_absolutelyContinuous)),
    map_symm_volumeE, integral_smul_measure, ENNReal.toReal_ofReal hdet.le, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hdet.ne', one_mul]

/-! ### Rotations and the isotropic dilation -/

/-- A rotation `R_Q f = f(Q⁻¹ ·)` is `D_Q` when `|det Q| = 1`.
@isnad1 id=eventual.1h3v.s12.c31b2380a423 from=translated src=- shape=bda523f8 vocab=2d5beff5
-/
theorem coeFn_dilL1E_of_abs_det_eq_one (Q : E ≃L[ℝ] E)
    (hQ : |LinearMap.det (Q : E →ₗ[ℝ] E)| = 1) (f : E →₁[volume] ℝ) :
    dilL1E Q f =ᵐ[volume] fun x => (f : E → ℝ) (Q.symm x) := by
  filter_upwards [coeFn_dilL1E Q f] with x hx
  rw [hx, dilateE_apply, hQ, inv_one, one_mul]

/-! ## Reflection -/

/-- `x ↦ -x` preserves the Haar measure.
@isnad1 id=measurep.0h1v.s6.093d580423e7 from=translated src=- shape=e4f70a32 vocab=f299fe9c
-/
theorem measurePreserving_negE : MeasurePreserving (fun x : E => -x) volume volume := by
  refine ⟨measurable_neg, ?_⟩
  have h := map_symm_volumeE (ContinuousLinearEquiv.neg ℝ : E ≃L[ℝ] E)
  rw [abs_det_neg, ENNReal.ofReal_one, one_smul] at h
  exact h

/--
@isnad1 id=eventual.1h3v.s7.b0aa6ab055d9 from=translated src=- shape=d29282ab vocab=b9661278
-/
theorem reflect_congr_aeE {f g : E → ℝ} (h : f =ᵐ[volume] g) :
    (fun x => f (-x)) =ᵐ[volume] fun x => g (-x) :=
  measurePreserving_negE.quasiMeasurePreserving.ae h

/--
@isnad1 id=integrab.1h2v.s7.8cab7ba63453 from=translated src=- shape=46d2f709 vocab=d3ada32b
-/
theorem integrable_reflectE {f : E → ℝ} (hf : Integrable f) :
    Integrable (fun x => f (-x)) :=
  (measurePreserving_negE.integrable_comp hf.aestronglyMeasurable).mpr hf

/-- `R f = f(-·)` as a linear map on `L¹(E)`.-/
noncomputable def reflₗE : (E →₁[volume] ℝ) →ₗ[ℝ] (E →₁[volume] ℝ) where
  toFun f := (integrable_reflectE (L1.integrable_coeFn f)).toL1 _
  map_add' f g := by
    rw [← Integrable.toL1_add]
    exact (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (reflect_congr_aeE (Lp.coeFn_add f g))
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← Integrable.toL1_smul']
    exact (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (reflect_congr_aeE (Lp.coeFn_smul c f))

/-- **Reflection `R f = f(-·)` is an isometry of `L¹(E)`.**-/
noncomputable def reflL1E : (E →₁[volume] ℝ) →L[ℝ] (E →₁[volume] ℝ) :=
  reflₗE.mkContinuous 1 fun f => by
    rw [reflₗE, LinearMap.coe_mk, AddHom.coe_mk, Integrable.norm_toL1_eq_lintegral_enorm,
      one_mul, Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
    refine le_of_eq (congrArg ENNReal.toReal ?_)
    exact measurePreserving_negE.lintegral_comp_emb
      (Homeomorph.neg E).toMeasurableEquiv.measurableEmbedding fun x => ‖(f : E → ℝ) x‖ₑ

/--
@isnad1 id=eventual.0h2v.s12.9443be5807c9 from=translated src=- shape=42d29cd3 vocab=33be7aca
-/
lemma coeFn_reflL1E (f : E →₁[volume] ℝ) :
    reflL1E f =ᵐ[volume] fun x => (f : E → ℝ) (-x) :=
  Integrable.coeFn_toL1 (integrable_reflectE (L1.integrable_coeFn f))

/-- Reflection is the dilation by `-id`.
@isnad1 id=eq.0h1v.s11.7d1942a20f61 from=translated src=- shape=3e880a19 vocab=601d2c14
-/
theorem reflL1E_eq_dilL1E :
    (reflL1E : (E →₁[volume] ℝ) →L[ℝ] (E →₁[volume] ℝ)) = dilL1E (ContinuousLinearEquiv.neg ℝ) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  refine (coeFn_reflL1E f).trans ?_
  refine Filter.EventuallyEq.symm ((coeFn_dilL1E_of_abs_det_eq_one _ abs_det_neg f).trans ?_)
  filter_upwards with x
  rfl

/-! ## Convolution by a measure -/

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- `(μ * f)(x) = ∫ f(x - y) μ(dy)`.-/
noncomputable def mconvE (μ : Measure E) (f : E → ℝ) : E → ℝ := fun x => ∫ y, f (x - y) ∂μ

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/--
@isnad1 id=eq.0h4v.s6.ce953b42940c from=translated src=- shape=9f19f173 vocab=17a3ba84
-/
lemma mconvE_apply (μ : Measure E) (f : E → ℝ) (x : E) :
    mconvE μ f x = ∫ y, f (x - y) ∂μ := rfl

/--
@isnad1 id=eq.1h3v.s7.9db49d8e4860 from=translated src=- shape=83ad3f7d vocab=df9fb7e3
-/
theorem lintegral_lintegral_sub_eqE (μ : Measure E) [SFinite μ] {g : E → ℝ≥0∞}
    (hg : AEMeasurable g) :
    ∫⁻ x, (∫⁻ y, g (x - y) ∂μ) = μ univ * ∫⁻ x, g x := by
  have huncurry : AEMeasurable (Function.uncurry fun x y : E => g (x - y)) (volume.prod μ) :=
    hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume μ)
  calc ∫⁻ x, (∫⁻ y, g (x - y) ∂μ)
      = ∫⁻ y, (∫⁻ x, g (x - y) ∂volume) ∂μ := lintegral_lintegral_swap huncurry
    _ = ∫⁻ _, (∫⁻ x, g x) ∂μ := lintegral_congr fun y => lintegral_sub_right_eq_self _ y
    _ = μ univ * ∫⁻ x, g x := by rw [lintegral_const, mul_comm]

/--
@isnad1 id=le.1h3v.s7.78964e4362ba from=translated src=- shape=e6cdbeff vocab=aa2aa152
-/
theorem lintegral_enorm_mconv_leE (μ : Measure E) [SFinite μ] {f : E → ℝ}
    (hf : AEStronglyMeasurable f) :
    ∫⁻ x, ‖mconvE μ f x‖ₑ ≤ μ univ * ∫⁻ x, ‖f x‖ₑ := by
  calc ∫⁻ x, ‖mconvE μ f x‖ₑ ≤ ∫⁻ x, (∫⁻ y, ‖f (x - y)‖ₑ ∂μ) :=
        lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
    _ = μ univ * ∫⁻ x, ‖f x‖ₑ := lintegral_lintegral_sub_eqE μ hf.enorm

/--
@isnad1 id=integrab.2h3v.s7.75d5782f6a6a from=translated src=- shape=36bd3a80 vocab=d21dd87b
-/
theorem integrable_uncurry_subE (μ : Measure E) [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f) :
    Integrable (Function.uncurry fun x y : E => f (x - y)) (volume.prod μ) := by
  have hm : AEStronglyMeasurable (Function.uncurry fun x y : E => f (x - y)) (volume.prod μ) :=
    hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume μ)
  refine ⟨hm, ?_⟩
  have hprod : ∫⁻ p, ‖Function.uncurry (fun x y : E => f (x - y)) p‖ₑ ∂(volume.prod μ)
      = ∫⁻ x, (∫⁻ y, ‖f (x - y)‖ₑ ∂μ) := lintegral_prod _ hm.enorm
  rw [hasFiniteIntegral_iff_enorm, hprod, lintegral_lintegral_sub_eqE μ hf.enorm]
  exact ENNReal.mul_lt_top (measure_lt_top μ univ) hfi.2

/-- `μ * f` is integrable.
@isnad1 id=integrab.2h3v.s7.428fa2b8df84 from=translated src=- shape=27d17493 vocab=71765f5d
-/
theorem integrable_mconvE (μ : Measure E) [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f) : Integrable (mconvE μ f) :=
  (integrable_uncurry_subE μ hf hfi).integral_prod_left

/--
@isnad1 id=eventual.1h3v.s7.093116fc36f4 from=translated src=- shape=390fa847 vocab=fc398cf5
-/
theorem ae_ae_sub_of_aeE (μ : Measure E) [SFinite μ] {p : E → Prop} (h : ∀ᵐ u ∂volume, p u) :
    ∀ᵐ x ∂volume, ∀ᵐ y ∂μ, p (x - y) :=
  Measure.ae_ae_of_ae_prod ((quasiMeasurePreserving_sub volume μ).ae h)

/--
@isnad1 id=eventual.1h4v.s7.17d91275cf61 from=translated src=- shape=43714a43 vocab=d4eb9886
-/
theorem mconvE_congr_ae (μ : Measure E) [SFinite μ] {f g : E → ℝ} (h : f =ᵐ[volume] g) :
    mconvE μ f =ᵐ[volume] mconvE μ g := by
  filter_upwards [ae_ae_sub_of_aeE μ h] with x hx
  exact integral_congr_ae hx

/--
@isnad1 id=eventual.4h4v.s8.fae986988b2d from=translated src=- shape=0e8cdf16 vocab=b168d933
-/
theorem mconvE_add_ae (μ : Measure E) [IsFiniteMeasure μ] {f g : E → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f)
    (hg : AEStronglyMeasurable g) (hgi : Integrable g) :
    mconvE μ (f + g) =ᵐ[volume] mconvE μ f + mconvE μ g := by
  filter_upwards [(integrable_uncurry_subE μ hf hfi).prod_right_ae,
    (integrable_uncurry_subE μ hg hgi).prod_right_ae] with x h1 h2
  simp only [Function.uncurry] at h1 h2
  simp only [mconvE_apply, Pi.add_apply]
  exact integral_add h1 h2

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/--
@isnad1 id=eq.0h4v.s6.0652cadf5908 from=translated src=- shape=8784fcdb vocab=04b9757d
-/
theorem mconvE_smul (μ : Measure E) (c : ℝ) (f : E → ℝ) :
    mconvE μ (c • f) = c • mconvE μ f := by
  funext x
  simp only [mconvE_apply, Pi.smul_apply, smul_eq_mul, integral_const_mul]

/-- `f ↦ μ * f` as a linear map on `L¹(E)`.-/
noncomputable def mconvₗE (μ : Measure E) [IsFiniteMeasure μ] :
    (E →₁[volume] ℝ) →ₗ[ℝ] (E →₁[volume] ℝ) where
  toFun f := (integrable_mconvE μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f)).toL1 _
  map_add' f g := by
    rw [← Integrable.toL1_add]
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (mconvE_congr_ae μ (Lp.coeFn_add f g)).trans ?_
    exact mconvE_add_ae μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f)
      (Lp.aestronglyMeasurable g) (L1.integrable_coeFn g)
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← Integrable.toL1_smul']
    refine (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr ?_
    refine (mconvE_congr_ae μ (Lp.coeFn_smul c f)).trans ?_
    rw [mconvE_smul]

/-- **Convolution by a finite measure `f ↦ μ * f` is a bounded operator on `L¹(E)`**, of norm at
most `μ(E)`.-/
noncomputable def mconvL1E (μ : Measure E) [IsFiniteMeasure μ] :
    (E →₁[volume] ℝ) →L[ℝ] (E →₁[volume] ℝ) :=
  (mconvₗE μ).mkContinuous (μ univ).toReal fun f => by
    rw [mconvₗE, LinearMap.coe_mk, AddHom.coe_mk, Integrable.norm_toL1_eq_lintegral_enorm,
      Lp.norm_def, eLpNorm_one_eq_lintegral_enorm, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono ?_ (lintegral_enorm_mconv_leE μ (Lp.aestronglyMeasurable f))
    exact ENNReal.mul_ne_top (measure_ne_top μ univ) (L1.integrable_coeFn f).2.ne

/--
@isnad1 id=eventual.0h3v.s12.e373cc9e37e5 from=translated src=- shape=f7eb0ecc vocab=24cb3f6d
-/
lemma coeFn_mconvL1E (μ : Measure E) [IsFiniteMeasure μ] (f : E →₁[volume] ℝ) :
    mconvL1E μ f =ᵐ[volume] mconvE μ (f : E → ℝ) :=
  Integrable.coeFn_toL1 (integrable_mconvE μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f))

/-- **The relational form of convolution.** An operator is `μ * ·` exactly when it is
`f ↦ ∫ f(· - y) dμ(y)` a.e. on every `f`.-/
theorem eq_mconvL1E_iff (μ : Measure E) [IsFiniteMeasure μ]
    (Φ : (E →₁[volume] ℝ) →L[ℝ] (E →₁[volume] ℝ)) :
    Φ = mconvL1E μ ↔ ∀ f : E →₁[volume] ℝ, (Φ f : E → ℝ) =ᵐ[volume] mconvE μ (f : E → ℝ) := by
  constructor
  · rintro rfl f
    exact coeFn_mconvL1E μ f
  · intro h
    exact ContinuousLinearMap.ext fun f => Lp.ext ((h f).trans (coeFn_mconvL1E μ f).symm)

/-! ## What `mconvL1E` does: translation, positivity, mass, composition -/

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/--
@isnad1 id=eq.0h4v.s6.22ede85332c7 from=translated src=- shape=2e10e827 vocab=3a24a603
-/
theorem mconvE_comp_sub (μ : Measure E) (f : E → ℝ) (a : E) :
    mconvE μ (fun x => f (x - a)) = fun x => mconvE μ f (x - a) := by
  funext x
  simp only [mconvE_apply, sub_right_comm]

/-- `∫ (μ * f) = μ(E) ∫ f`.
@isnad1 id=eq.2h3v.s7.82ca058b0c2c from=translated src=- shape=600fbf09 vocab=3c4f34be
-/
theorem integral_mconvE (μ : Measure E) [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f) :
    ∫ x, mconvE μ f x = (μ univ).toReal * ∫ x, f x := by
  simp only [mconvE_apply]
  rw [integral_integral_swap (integrable_uncurry_subE μ hf hfi)]
  simp_rw [integral_sub_right_eq_self]
  rw [integral_const, smul_eq_mul, measureReal_def]

/-- `ν * (μ * f) = (μ ∗ ν) * f`, a.e.
@isnad1 id=eventual.2h4v.s7.55eee71517d5 from=translated src=- shape=adc47851 vocab=0c19d340
-/
theorem mconvE_conv (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : E → ℝ}
    (hf : AEStronglyMeasurable f) (hfi : Integrable f) :
    mconvE ν (mconvE μ f) =ᵐ[volume] mconvE (μ ∗ ν) f := by
  filter_upwards [(integrable_uncurry_subE (μ ∗ ν) hf hfi).prod_right_ae] with x hx
  simp only [Function.uncurry] at hx
  have hadd : AEMeasurable (fun p : E × E => p.1 + p.2) (μ.prod ν) :=
    (measurable_fst.add measurable_snd).aemeasurable
  have hprod : Integrable (fun p : E × E => f (x - (p.1 + p.2))) (μ.prod ν) := by
    rw [Measure.conv] at hx
    exact (integrable_map_measure hx.aestronglyMeasurable hadd).mp hx
  have hmap : ∫ u, f (x - u) ∂(μ ∗ ν) = ∫ p : E × E, f (x - (p.1 + p.2)) ∂(μ.prod ν) := by
    rw [Measure.conv]
    exact integral_map hadd (by rw [← Measure.conv]; exact hx.aestronglyMeasurable)
  simp only [mconvE_apply]
  rw [hmap, integral_prod_symm _ hprod]
  simp only [sub_add_eq_sub_sub, sub_right_comm]

omit [(volume : Measure E).IsAddHaarMeasure] in
/--
@isnad1 id=eq.0h2v.s6.5a8cf461a3d1 from=translated src=- shape=7b58e842 vocab=c7dac6f8
-/
theorem mconvE_dirac_zero (f : E → ℝ) : mconvE (Measure.dirac 0) f = f := by
  funext x
  rw [mconvE_apply, integral_dirac, sub_zero]

/-- Equal measures give equal operators (the instance argument blocks a plain `rw`).
@isnad1 id=eq.1h3v.s11.8c466ae8623a from=translated src=- shape=219f9cd2 vocab=32024500
-/
theorem mconvL1E_congr {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ = ν) :
    mconvL1E μ = mconvL1E ν := by
  subst h
  congr 1

/-- **`μ * ·` is a contraction** for a probability measure.
@isnad1 id=le.0h3v.s12.94bcd363fc5b from=translated src=- shape=894b0457 vocab=bb7a1514
-/
theorem norm_mconvL1E_le (μ : Measure E) [IsProbabilityMeasure μ] (f : E →₁[volume] ℝ) :
    ‖mconvL1E μ f‖ ≤ ‖f‖ := by
  have hop : ‖mconvL1E μ‖ ≤ 1 := by
    rw [mconvL1E]
    refine le_trans (LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _) ?_
    rw [measure_univ, ENNReal.toReal_one]
  calc ‖mconvL1E μ f‖ ≤ ‖mconvL1E μ‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := by nlinarith [norm_nonneg f]
    _ = ‖f‖ := one_mul _

/-- **`μ * ·` commutes with translation.**
@isnad1 id=eq.0h4v.s14.49799b572386 from=translated src=- shape=9b958c27 vocab=7bb9d96c
-/
theorem mconvL1E_transL1E (μ : Measure E) [IsFiniteMeasure μ] (a : E) (f : E →₁[volume] ℝ) :
    mconvL1E μ (transL1E a f) = transL1E a (mconvL1E μ f) := by
  refine Lp.ext ?_
  refine (coeFn_mconvL1E μ (transL1E a f)).trans ?_
  refine (mconvE_congr_ae μ (coeFn_transL1E a f)).trans ?_
  rw [mconvE_comp_sub]
  refine Filter.EventuallyEq.symm ?_
  refine (coeFn_transL1E a (mconvL1E μ f)).trans ?_
  exact translate_congr_aeE a (coeFn_mconvL1E μ f)

/-- **`μ * ·` preserves nonnegativity.**
@isnad1 id=isnonneg.1h3v.s12.728dd81b2a29 from=translated src=- shape=299a1c5d vocab=44c4c726
-/
theorem isNonnegE_mconvL1E (μ : Measure E) [IsFiniteMeasure μ] {f : E →₁[volume] ℝ}
    (hf : IsNonnegE f) : IsNonnegE (mconvL1E μ f) := by
  filter_upwards [coeFn_mconvL1E μ f, ae_ae_sub_of_aeE μ hf] with x hcoe hx
  rw [Pi.zero_apply, hcoe, mconvE_apply]
  exact integral_nonneg_of_ae hx

/-- **`μ * ·` preserves the integral** for a probability measure, for every `f`.
@isnad1 id=eq.0h3v.s12.0e2723f5692e from=translated src=- shape=f9eee136 vocab=8e838c34
-/
theorem integral_mconvL1E (μ : Measure E) [IsProbabilityMeasure μ] (f : E →₁[volume] ℝ) :
    ∫ x, (mconvL1E μ f : E → ℝ) x = ∫ x, (f : E → ℝ) x := by
  rw [integral_congr_ae (coeFn_mconvL1E μ f),
    integral_mconvE μ (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f),
    measure_univ, ENNReal.toReal_one, one_mul]

/-- **`(μ * ·) ∘ (ν * ·)`**: composing the operators convolves the measures.
@isnad1 id=eq.0h3v.s12.abb759f2b8bc from=translated src=- shape=294850cf vocab=b9d97c55
-/
theorem mconvL1E_comp (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (mconvL1E ν).comp (mconvL1E μ) = mconvL1E (μ ∗ ν) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  refine ((coeFn_mconvL1E ν (mconvL1E μ f)).trans
    (mconvE_congr_ae ν (coeFn_mconvL1E μ f))).trans ?_
  refine Filter.EventuallyEq.trans ?_ (coeFn_mconvL1E (μ ∗ ν) f).symm
  exact mconvE_conv μ ν (Lp.aestronglyMeasurable f) (L1.integrable_coeFn f)

/-- **`δ₀ * f = f`.**
@isnad1 id=eq.0h1v.s12.81b6f511f8ea from=translated src=- shape=ba260779 vocab=b03e57d5
-/
theorem mconvL1E_dirac_zero :
    mconvL1E (Measure.dirac (0 : E)) = ContinuousLinearMap.id ℝ (E →₁[volume] ℝ) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  refine (coeFn_mconvL1E _ f).trans ?_
  rw [mconvE_dirac_zero]
  rfl

/-! ## Transport: `D_A (μ * f) = (A_* μ) * D_A f` -/

omit [(volume : Measure E).IsAddHaarMeasure] in
/-- **Transport** at the level of functions.
@isnad1 id=eq.1h4v.s8.2eebe0349816 from=translated src=- shape=5bb2b283 vocab=37238cc1
-/
theorem dilateE_mconvE (A : E ≃L[ℝ] E) (μ : Measure E) {f : E → ℝ} (hf : Measurable f) :
    dilateE A (mconvE μ f) = mconvE (μ.map A) (dilateE A f) := by
  have hmeas : Measurable (dilateE A f) :=
    (hf.comp A.symm.continuous.measurable).const_mul _
  funext x
  have hcomp : AEStronglyMeasurable (fun y : E => dilateE A f (x - y)) (μ.map A) :=
    (hmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  rw [mconvE_apply, integral_map A.continuous.measurable.aemeasurable hcomp]
  simp only [dilateE_apply, mconvE_apply, map_sub, ContinuousLinearEquiv.symm_apply_apply]
  rw [integral_const_mul]

/-- **Transport `D_A (μ * f) = (A_* μ) * D_A f`**, as operators.
@isnad1 id=eq.0h3v.s13.a55b89e36d2f from=translated src=- shape=eca2dd6c vocab=f462ad55
-/
theorem dilL1E_comp_mconvL1E (A : E ≃L[ℝ] E) (μ : Measure E) [IsFiniteMeasure μ]
    [IsFiniteMeasure (μ.map A)] :
    (dilL1E A).comp (mconvL1E μ) = (mconvL1E (μ.map A)).comp (dilL1E A) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  set g := (Lp.aestronglyMeasurable f).mk (f : E → ℝ) with hg_def
  have hgm : Measurable g := (Lp.aestronglyMeasurable f).stronglyMeasurable_mk.measurable
  have hfg : (f : E → ℝ) =ᵐ[volume] g := (Lp.aestronglyMeasurable f).ae_eq_mk
  simp only [ContinuousLinearMap.comp_apply]
  have h1 : (dilL1E A (mconvL1E μ f) : E → ℝ)
      =ᵐ[volume] mconvE (μ.map A) (dilateE A (f : E → ℝ)) := by
    refine (coeFn_dilL1E A (mconvL1E μ f)).trans ?_
    refine (dilateE_congr_ae A (coeFn_mconvL1E μ f)).trans ?_
    refine (dilateE_congr_ae A (mconvE_congr_ae μ hfg)).trans ?_
    rw [dilateE_mconvE A μ hgm]
    exact mconvE_congr_ae _ (dilateE_congr_ae A hfg.symm)
  have h2 : (mconvL1E (μ.map A) (dilL1E A f) : E → ℝ)
      =ᵐ[volume] mconvE (μ.map A) (dilateE A (f : E → ℝ)) :=
    (coeFn_mconvL1E _ (dilL1E A f)).trans (mconvE_congr_ae _ (coeFn_dilL1E A f))
  exact h1.trans h2.symm

/-- **Conjugating `μ * ·` by `D_A` gives `ν * ·` when `A_* μ = ν`.** The converse needs
uniqueness of the representing measure, which this module does not state.
@isnad1 id=eq.1h4v.s13.2cff134cb61a from=translated src=- shape=6b562df0 vocab=35ab0c77
-/
theorem dilL1E_conj_mconvL1E (A : E ≃L[ℝ] E) (μ ν : Measure E) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : μ.map A = ν) :
    ((dilL1E A).comp (mconvL1E μ)).comp (dilL1E A.symm) = mconvL1E ν := by
  haveI : IsFiniteMeasure (μ.map A) := h ▸ inferInstance
  rw [dilL1E_comp_mconvL1E, ContinuousLinearMap.comp_assoc, dilL1E_comp_symm,
    ContinuousLinearMap.comp_id]
  exact mconvL1E_congr h

/-! ## The relational form of intertwining

Paper VII states "`Ψ ∘ D = D ∘ Φ`" for `D f = c · f(A⁻¹ ·)` on representatives. Since `c · f(A⁻¹ ·)`
is `(c |det A|) · D_A f`, for `c ≠ 0` that relational statement is the operator identity. -/

/-- **Relational intertwining is the operator identity.**
@isnad1 id=iff.1h5v.s14.b135c04a87c0 from=translated src=- shape=0624e3d6 vocab=3c71c7d7
-/
theorem intertwines_iff_dilL1E (c : ℝ) (hc : c ≠ 0) (A : E ≃L[ℝ] E)
    (Φ Ψ : (E →₁[volume] ℝ) →L[ℝ] (E →₁[volume] ℝ)) :
    (∀ f g : E →₁[volume] ℝ, ((g : E → ℝ) =ᵐ[volume] fun x => c * (f : E → ℝ) (A.symm x)) →
      ((Ψ g : E → ℝ) =ᵐ[volume] fun x => c * (Φ f : E → ℝ) (A.symm x))) ↔
    Ψ.comp (dilL1E A) = (dilL1E A).comp Φ := by
  set k := c * |LinearMap.det (A : E →ₗ[ℝ] E)| with hk
  have hdet : |LinearMap.det (A : E →ₗ[ℝ] E)| ≠ 0 := abs_ne_zero.mpr (det_ne_zeroE A)
  have hk0 : k ≠ 0 := mul_ne_zero hc hdet
  -- the representative `c · h(A⁻¹ ·)` is `k • D_A h`
  have hrep : ∀ h : E →₁[volume] ℝ,
      ((k • dilL1E A h : E →₁[volume] ℝ) : E → ℝ) =ᵐ[volume]
        fun x => c * (h : E → ℝ) (A.symm x) := by
    intro h
    filter_upwards [Lp.coeFn_smul k (dilL1E A h), coeFn_dilL1E A h] with x h1 h2
    rw [h1, Pi.smul_apply, h2, dilateE_apply, smul_eq_mul, hk]
    field_simp
  constructor
  · intro H
    refine ContinuousLinearMap.ext fun f => ?_
    have := H f (k • dilL1E A f) (hrep f)
    have h2 : Ψ (k • dilL1E A f) = k • dilL1E A (Φ f) :=
      Lp.ext (this.trans (hrep (Φ f)).symm)
    rw [map_smul] at h2
    simpa [ContinuousLinearMap.comp_apply] using smul_right_injective _ hk0 h2
  · intro H f g hg
    have hg' : g = k • dilL1E A f := Lp.ext (hg.trans (hrep f).symm)
    have : Ψ g = k • dilL1E A (Φ f) := by
      rw [hg', map_smul]
      congr 1
      exact congrArg (fun L : (E →₁[volume] ℝ) →L[ℝ] (E →₁[volume] ℝ) => L f) H
    rw [this]
    exact hrep (Φ f)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Relational translation covariance is the operator identity.**
@isnad1 id=iff.0h2v.s14.062dac0bd967 from=translated src=- shape=7aa93159 vocab=5c0b3378
-/
theorem translation_iff_transL1E (Φ : (E →₁[volume] ℝ) →L[ℝ] (E →₁[volume] ℝ)) :
    (∀ (a : E) (f g : E →₁[volume] ℝ), ((g : E → ℝ) =ᵐ[volume] fun x => (f : E → ℝ) (x - a)) →
      ((Φ g : E → ℝ) =ᵐ[volume] fun x => (Φ f : E → ℝ) (x - a))) ↔
    ∀ a : E, Φ.comp (transL1E a) = (transL1E a).comp Φ := by
  constructor
  · intro H a
    refine ContinuousLinearMap.ext fun f => ?_
    exact (eq_transL1E_iff a (Φ f) _).mpr (H a f _ (coeFn_transL1E a f))
  · intro H a f g hg
    rw [(eq_transL1E_iff a f g).mpr hg]
    have := congrArg (fun L : (E →₁[volume] ℝ) →L[ℝ] (E →₁[volume] ℝ) => L f) (H a)
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [this]
    exact coeFn_transL1E a (Φ f)

/-! ## ℝ is the case `d = 1`

The general operators at `E = ℝ` are the line's operators of `ScaleSpaceCore.L1Operators`, on the
same type `ℝ →₁[volume] ℝ = X`. -/

/--
@isnad1 id=eq.0h1v.s11.f2a220e2dce4 from=translated src=- shape=47579fbb vocab=2e2901af
-/
theorem transL1E_real (a : ℝ) : transL1E a = transL1 a :=
  ContinuousLinearMap.ext fun f => Lp.ext ((coeFn_transL1E a f).trans (coeFn_transL1 a f).symm)

/--
@isnad1 id=eq.0h0v.s11.5d73f442b8f5 from=translated src=- shape=b416faa2 vocab=864b7e6e
-/
theorem reflL1E_real : (reflL1E : X →L[ℝ] X) = reflL1 :=
  ContinuousLinearMap.ext fun f => Lp.ext ((coeFn_reflL1E f).trans (coeFn_reflL1 f).symm)

/--
@isnad1 id=eq.0h1v.s11.166232bb888e from=translated src=- shape=66ee9a86 vocab=b071ba90
-/
theorem mconvL1E_real (μ : Measure ℝ) [IsFiniteMeasure μ] : mconvL1E μ = mconvL1 μ :=
  ContinuousLinearMap.ext fun f => Lp.ext ((coeFn_mconvL1E μ f).trans (coeFn_mconvL1 μ f).symm)

/--
@isnad1 id=eq.0h2v.s4.104789cc3ee2 from=translated src=- shape=791c3675 vocab=80f2fbcb
-/
theorem mconvE_real (μ : Measure ℝ) (f : ℝ → ℝ) : mconvE μ f = mconv μ f := rfl

/-- `dilate`'s `lam⁻¹ f(lam⁻¹ x)` is `|det A|⁻¹ f(A⁻¹ x)` at `A = lam`.
@isnad1 id=eq.1h2v.s5.8fb845484aff from=translated src=- shape=509711b3 vocab=b6ee32f3
-/
theorem dilateE_homothety_real {lam : ℝ} (hlam : 0 < lam) (f : ℝ → ℝ) :
    dilateE (homothety lam hlam.ne') f = dilate lam f := by
  funext x
  rw [dilateE_apply, det_homothety, Module.finrank_self, pow_one, abs_of_pos hlam,
    homothety_symm_apply, smul_eq_mul]
  rfl

/-- **The matrix dilation at `E = ℝ`, `A = lam`, is the line's dilation.**
@isnad1 id=eq.1h1v.s11.9f489fbdfd15 from=translated src=- shape=2499dd47 vocab=b2bb5f56
-/
theorem dilL1E_homothety_real {lam : ℝ} (hlam : 0 < lam) :
    dilL1E (homothety lam hlam.ne') = dilL1 hlam := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  refine (coeFn_dilL1E _ f).trans ?_
  rw [dilateE_homothety_real hlam]
  exact (coeFn_dilL1 hlam f).symm

/--
@isnad1 id=iff.0h1v.s7.7200d008817d from=translated src=- shape=a45b90ce vocab=eee43b9a
-/
theorem isNonnegE_real (f : X) : IsNonnegE f ↔ IsNonneg f := Iff.rfl

end ScaleSpace
