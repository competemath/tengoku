import Tengoku.NavierStokesEuler.Euler.MeanCoefficientSpatial

/-! All-order parameter regularity of actual bounded smooth coefficient translations. -/

noncomputable section

namespace EulerMeanCoefficients

open EulerSmoothLimit MeasureTheory InnerProductSpace
open scoped ContDiff BoundedContinuousFunction

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/--
@isnad1 id=le.0h2v.s10.33000c20b400 from=translated src=- shape=6449eab1 vocab=1ee46836
-/
theorem fieldDerivativeMap_norm_le (DA : Space →ᵇ (Space →L[ℝ] V)) :
    ‖fieldDerivativeMap DA‖ ≤ ‖DA‖ :=
  (fieldDerivativeMap DA).opNorm_le_bound (norm_nonneg DA) (fieldDirection_norm_le DA)

def derivativeBundlingLinear : (Space →ᵇ (Space →L[ℝ] V)) →ₗ[ℝ]
    (Space →L[ℝ] (Space →ᵇ V)) where
  toFun := fieldDerivativeMap
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro v
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  map_smul' c A := by
    apply ContinuousLinearMap.ext
    intro v
    apply BoundedContinuousFunction.ext
    intro x
    rfl

/-- Currying a bounded field of linear maps is itself a bounded linear operation. -/
def derivativeBundling : (Space →ᵇ (Space →L[ℝ] V)) →L[ℝ]
    (Space →L[ℝ] (Space →ᵇ V)) where
  toLinearMap := derivativeBundlingLinear
  cont := AddMonoidHomClass.continuous_of_bound derivativeBundlingLinear 1 (fun A => by
    change ‖fieldDerivativeMap A‖ ≤ 1 * ‖A‖
    simpa only [one_mul] using fieldDerivativeMap_norm_le A)

/--
@isnad1 id=eq.0h2v.s13.ec52de1d74ed from=translated src=- shape=c0038846 vocab=3a462898
-/
@[simp] theorem derivativeBundling_apply (A : Space →ᵇ (Space →L[ℝ] V)) :
    derivativeBundling A = fieldDerivativeMap A := rfl

/-- A concrete smooth coefficient with globally bounded actual derivatives of every order. -/
structure BoundedSmoothField (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  field : Space →ᵇ V
  smooth : ContDiff ℝ ∞ (field : Space → V)
  bounded : ∀ n : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n (field : Space → V) x‖ ≤ C

namespace BoundedSmoothField

def derivative (A : BoundedSmoothField V) : BoundedSmoothField (Space →L[ℝ] V) where
  field := boundedDerivative A.field A.smooth (Classical.choose (A.bounded 1)) (fun x => by
    rw [← norm_iteratedFDeriv_one]
    exact Classical.choose_spec (A.bounded 1) x)
  smooth := A.smooth.fderiv_right (m := ∞) (by simp)
  bounded n := by
    change ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n (fderiv ℝ (A.field : Space → V)) x‖ ≤ C
    simpa only [norm_iteratedFDeriv_fderiv] using A.bounded (n+1)

/--
@isnad1 id=eq.0h3v.s11.98360fa703d5 from=translated src=- shape=3f6b0c8a vocab=bdbcd064
-/
@[simp] theorem derivative_field_apply (A : BoundedSmoothField V) (x : Space) :
    A.derivative.field x = fderiv ℝ (A.field : Space → V) x := rfl

/--
@isnad1 id=hasfderi.0h3v.s10.3bd5f8a41869 from=translated src=- shape=64fac3aa vocab=9723b1a9
-/
theorem translation_hasFDerivAt (A : BoundedSmoothField V) (a : Space) :
    HasFDerivAt (translated A.field) (fieldDerivativeMap (translated A.derivative.field a)) a := by
  obtain ⟨M, hM⟩ := A.bounded 2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  apply translated_hasFDerivAt A.field A.derivative.field A.smooth (fun _ => rfl) M hM0
  intro x
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact hM x

/--
@isnad1 id=eq.0h2v.s13.d6c61870a7ed from=translated src=- shape=18a627b0 vocab=db02f8bb
-/
theorem translation_fderiv (A : BoundedSmoothField V) :
    fderiv ℝ (translated A.field) = fun a => derivativeBundling (translated A.derivative.field a) :=
  funext (fun a => (A.translation_hasFDerivAt a).fderiv)

private theorem translation_contDiff_nat_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : BoundedSmoothField V),
      ContDiff ℝ n (translated A.field) := by
  induction n with
  | zero =>
    intro V _ _ A
    apply contDiff_zero.mpr
    exact continuous_iff_continuousAt.mpr (fun a => (A.translation_hasFDerivAt a).continuousAt)
  | succ n ih =>
    intro V _ _ A
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun a => (A.translation_hasFDerivAt a).differentiableAt, by simp, ?_⟩
    rw [A.translation_fderiv]
    exact (derivativeBundling (V := V)).contDiff.comp (ih (Space →L[ℝ] V) A.derivative)

/-- Every spatial translation of an actual globally bounded smooth coefficient depends smoothly on its parameter.
@isnad1 id=contdiff.0h2v.s8.a62468318d78 from=translated src=- shape=e7ce5ddd vocab=9e6d49b6
-/
theorem translation_contDiff (A : BoundedSmoothField V) : ContDiff ℝ ∞ (translated A.field) :=
  contDiff_infty.mpr (fun n => translation_contDiff_nat_aux n V A)

end BoundedSmoothField

end EulerMeanCoefficients
