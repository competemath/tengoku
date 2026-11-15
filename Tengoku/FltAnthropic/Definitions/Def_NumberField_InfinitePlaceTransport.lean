import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open NumberField

namespace NumberField.InfinitePlaceTransport

section general
variable {R S : Type*} [Field R] [Field S]

/--
@isnad1 id=uniformc.1h5v.s10.1de2020ddb9b from=translated src=- shape=768dcb20 vocab=9319bcc1
-/
theorem uniformContinuous_congr_of_forall_eq (v : AbsoluteValue R ℝ) (v' : AbsoluteValue S ℝ) (f : R ≃+* S)
    (h : ∀ x, v' (f x) = v x) : UniformContinuous (WithAbs.congr v v' f) :=
  (AddMonoidHomClass.isometry_of_norm (WithAbs.congr v v' f) fun x => by
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_apply]
    exact h _).uniformContinuous

end general

variable {E K : Type*} [Field E] [Field K] [Algebra E K]

/--
@isnad1 id=eq.1h6v.s8.80b0be102bee from=translated src=- shape=c9d279f6 vocab=d440dec4
-/
theorem apply_apply_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : InfinitePlace K} (h : σ • w = w') (x : K) : w' (σ x) = w x := by
  rw [← h, InfinitePlace.smul_apply, AlgEquiv.symm_apply_apply]

/--
@isnad1 id=eq.1h5v.s9.685fc00d9d6c from=translated src=- shape=9095ba76 vocab=35fc9999
-/
theorem inv_smul_eq_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : InfinitePlace K} (h : σ • w = w') : σ⁻¹ • w' = w := by
  rw [← h, inv_smul_smul]

/--
@isnad1 id=uniformc.1h5v.s12.8aca5be5ebc1 from=translated src=- shape=ebfd7a98 vocab=c127c3a7
-/
theorem uniformContinuous_congr_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : InfinitePlace K} (h : σ • w = w') :
    UniformContinuous (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) :=
  uniformContinuous_congr_of_forall_eq w.1 w'.1 _ (apply_apply_of_smul_eq h)

noncomputable def transport (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') : w.Completion ≃+* w'.Completion :=
  (InfinitePlace.Completion.equiv w).trans
    ((UniformSpace.Completion.mapRingEquiv (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_smul_eq h).continuous
      ((uniformContinuous_congr_of_smul_eq (inv_smul_eq_of_smul_eq h)).continuous.congr fun _ => rfl)).trans
    (InfinitePlace.Completion.equiv w').symm)

/--
@isnad1 id=eq.1h6v.s12.f5382c823885 from=translated src=- shape=aa900e55 vocab=e9d056e0
-/
theorem transport_apply (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (x : w.Completion) :
    transport σ h x = .ofCompletion
      (UniformSpace.Completion.map (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) x.toCompletion) :=
  rfl

/--
@isnad1 id=eq.1h6v.s12.ca9ea0618e72 from=translated src=- shape=bd18d2ca vocab=d8bd74b3
-/
theorem toCompletion_transport (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (x : w.Completion) :
    (transport σ h x).toCompletion
      = UniformSpace.Completion.map (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) x.toCompletion :=
  rfl

/--
@isnad1 id=eq.1h6v.s12.ccd7c62e3773 from=translated src=- shape=617ef62e vocab=ca130812
-/
theorem transport_coe (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (x : WithAbs w.1) :
    transport σ h (x : w.Completion) = ((WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K) x : WithAbs w'.1) : w'.Completion) := by
  rw [transport_apply, InfinitePlace.Completion.coe_toCompletion,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_smul_eq h)]

/--
@isnad1 id=continuo.1h5v.s9.54d312b741d5 from=translated src=- shape=2eda3565 vocab=0c2b2683
-/
theorem continuous_transport (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') : Continuous (transport σ h) :=
  (InfinitePlace.Completion.continuous_ofCompletion w').comp
    (UniformSpace.Completion.continuous_map.comp (InfinitePlace.Completion.continuous_toCompletion w))

noncomputable abbrev transportUnits (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') :
    (w.Completion)ˣ ≃* (w'.Completion)ˣ :=
  Units.mapEquiv (transport σ h).toMulEquiv

/--
@isnad1 id=eq.1h6v.s10.7d2272d83b92 from=translated src=- shape=cbc86ea9 vocab=b74c0cff
-/
theorem coe_transportUnits (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (u : (w.Completion)ˣ) :
    ((transportUnits σ h u : (w'.Completion)ˣ) : w'.Completion) = transport σ h (u : w.Completion) := rfl

end NumberField.InfinitePlaceTransport
