import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_RepPi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open NumberField

namespace NumberField.InfPlaceDecomp

section general
variable {K : Type*} [Field K]

/--
@isnad1 id=uniformc.1h3v.s10.10fceb75fe7f from=translated src=- shape=07883905 vocab=9319bcc1
-/
theorem uniformContinuous_congr_of_forall_eq (v : AbsoluteValue K ℝ) (f : K ≃+* K) (h : ∀ x, v (f x) = v x) :
    UniformContinuous (WithAbs.congr v v f) :=
  (AddMonoidHomClass.isometry_of_norm (WithAbs.congr v v f) fun x => by
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_apply]
    exact h _).uniformContinuous

end general

variable (E K : Type*) [Field E] [Field K] [Algebra E K] (w : InfinitePlace K)

abbrev decomp : Subgroup (K ≃ₐ[E] K) := MulAction.stabilizer (K ≃ₐ[E] K) w

variable {E K w}

/--
@isnad1 id=eq.1h5v.s8.57830f830d57 from=translated src=- shape=b32a008a vocab=b9bcaef9
-/
theorem apply_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) (x : K) : w (σ x) = w x := by
  rw [MulAction.mem_stabilizer_iff] at hσ
  conv_lhs => rw [← hσ]
  rw [InfinitePlace.smul_apply, AlgEquiv.symm_apply_apply]

/--
@isnad1 id=uniformc.1h4v.s12.f0e876ad8ea6 from=translated src=- shape=4a826d4d vocab=f4a3774e
-/
theorem uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) :
    UniformContinuous (WithAbs.congr w.1 w.1 (σ : K ≃+* K)) :=
  uniformContinuous_congr_of_forall_eq w.1 (σ : K ≃+* K) (apply_of_mem σ hσ)

noncomputable def actRingEquiv (σ : decomp E K w) : w.Completion ≃+* w.Completion :=
  ((InfinitePlace.Completion.equiv w).trans
    (UniformSpace.Completion.mapRingEquiv (WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2).continuous
      (by
        rw [WithAbs.congr_symm]
        exact (uniformContinuous_congr_of_mem ((σ⁻¹ : decomp E K w) : K ≃ₐ[E] K) (σ⁻¹).2).continuous))).trans
    (InfinitePlace.Completion.equiv w).symm

/--
@isnad1 id=eq.0h5v.s12.806675c18c7e from=translated src=- shape=41aab794 vocab=70a860c3
-/
theorem actRingEquiv_apply (σ : decomp E K w) (x : w.Completion) :
    (actRingEquiv σ x).toCompletion =
      UniformSpace.Completion.map (WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) x.toCompletion :=
  rfl

/--
@isnad1 id=eq.0h5v.s12.8df6ba6ab1d1 from=translated src=- shape=316f222a vocab=a13a962d
-/
theorem actRingEquiv_coe (σ : decomp E K w) (x : WithAbs w.1) :
    actRingEquiv σ (x : w.Completion) = ((WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K) x : WithAbs w.1) : w.Completion) := by
  apply InfinitePlace.Completion.ext
  rw [actRingEquiv_apply, InfinitePlace.Completion.coe_toCompletion,
    InfinitePlace.Completion.coe_toCompletion,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]

/--
@isnad1 id=continuo.0h4v.s9.a126caec04a2 from=translated src=- shape=980c4686 vocab=86e91636
-/
theorem continuous_actRingEquiv (σ : decomp E K w) : Continuous (actRingEquiv σ) := by
  have : (actRingEquiv σ : w.Completion → w.Completion) =
      InfinitePlace.Completion.ofCompletion ∘
        UniformSpace.Completion.map (WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) ∘
        InfinitePlace.Completion.toCompletion :=
    funext fun x => InfinitePlace.Completion.ext (h := actRingEquiv_apply σ x)
  rw [this]
  exact (InfinitePlace.Completion.continuous_ofCompletion w).comp
    (UniformSpace.Completion.continuous_map.comp (InfinitePlace.Completion.continuous_toCompletion w))

/--
@isnad1 id=eq.0h3v.s9.4209491110b3 from=translated src=- shape=07f54402 vocab=f1c513b8
-/
theorem actRingEquiv_one : actRingEquiv (1 : decomp E K w) = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro x
  apply InfinitePlace.Completion.ext
  rw [actRingEquiv_apply]
  change _ = id x.toCompletion
  refine congrFun (UniformSpace.Completion.ext UniformSpace.Completion.continuous_map continuous_id
    fun a => ?_) _
  rw [UniformSpace.Completion.map_coe
    (uniformContinuous_congr_of_mem ((1 : decomp E K w) : K ≃ₐ[E] K) (1 : decomp E K w).2)]
  rfl

/--
@isnad1 id=eq.0h5v.s10.a49d3f3c2d57 from=translated src=- shape=dc49dd43 vocab=a7fe744f
-/
theorem actRingEquiv_mul (σ τ : decomp E K w) : actRingEquiv (σ * τ) = (actRingEquiv τ).trans (actRingEquiv σ) := by
  apply RingEquiv.ext
  intro x
  apply InfinitePlace.Completion.ext
  change (actRingEquiv (σ * τ) x).toCompletion = (actRingEquiv σ (actRingEquiv τ x)).toCompletion
  rw [actRingEquiv_apply, actRingEquiv_apply, actRingEquiv_apply]
  refine congrFun (UniformSpace.Completion.ext UniformSpace.Completion.continuous_map
    (UniformSpace.Completion.continuous_map.comp UniformSpace.Completion.continuous_map) fun a => ?_) _
  change _ = UniformSpace.Completion.map _ (UniformSpace.Completion.map _ _)
  rw [UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem ((σ * τ : decomp E K w) : K ≃ₐ[E] K) (σ * τ).2),
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (τ : K ≃ₐ[E] K) τ.2),
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]
  rfl

noncomputable def actHom : decomp E K w →* (w.Completion ≃+* w.Completion) where
  toFun := actRingEquiv
  map_one' := actRingEquiv_one
  map_mul' σ τ := actRingEquiv_mul σ τ

/--
@isnad1 id=eq.0h5v.s11.36b3d0354c29 from=translated src=- shape=4cfbab65 vocab=51db3bec
-/
theorem smul_withAbs_def (σ : decomp E K w) (y : WithAbs w.1) : σ • y = WithAbs.toAbs w.1 ((σ : K ≃ₐ[E] K) y.ofAbs) := rfl

noncomputable scoped instance instMulActionWithAbs : MulAction (decomp E K w) (WithAbs w.1) where
  one_smul y := by rw [smul_withAbs_def]; rfl
  mul_smul σ τ y := by rw [smul_withAbs_def, smul_withAbs_def, smul_withAbs_def]; rfl

noncomputable scoped instance instDistribMulActionWithAbs : DistribMulAction (decomp E K w) (WithAbs w.1) where
  smul_zero σ := by rw [smul_withAbs_def]; show WithAbs.toAbs _ ((σ : K ≃ₐ[E] K) 0) = 0; rw [map_zero]; rfl
  smul_add σ x y := by
    rw [smul_withAbs_def, smul_withAbs_def, smul_withAbs_def]
    show WithAbs.toAbs _ ((σ : K ≃ₐ[E] K) (x.ofAbs + y.ofAbs)) = _
    rw [map_add]; rfl

/--
@isnad1 id=uniformc.0h3v.s10.e8e3e09e2854 from=translated src=- shape=e9fc41fb vocab=0b0966b0
-/
noncomputable scoped instance instUniformContinuousConstSMul : UniformContinuousConstSMul (decomp E K w) (WithAbs w.1) :=
  ⟨fun σ => uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2⟩

noncomputable scoped instance instMulSemiringAction : MulSemiringAction (decomp E K w) w.Completion where
  smul σ x := actRingEquiv σ x
  one_smul x := by change actRingEquiv 1 x = x; rw [actRingEquiv_one]; rfl
  mul_smul σ τ x := by
    change actRingEquiv (σ * τ) x = actRingEquiv σ (actRingEquiv τ x); rw [actRingEquiv_mul]; rfl
  smul_zero σ := by change actRingEquiv σ 0 = 0; rw [map_zero]
  smul_add σ x y := by change actRingEquiv σ (x + y) = actRingEquiv σ x + actRingEquiv σ y; rw [map_add]
  smul_one σ := by change actRingEquiv σ 1 = 1; rw [map_one]
  smul_mul σ x y := by change actRingEquiv σ (x * y) = actRingEquiv σ x * actRingEquiv σ y; rw [map_mul]

/--
@isnad1 id=eq.0h5v.s11.406bc1365260 from=translated src=- shape=6f8e4a49 vocab=198b5d82
-/
theorem smul_def (σ : decomp E K w) (x : w.Completion) : σ • x = actRingEquiv σ x := rfl

/--
@isnad1 id=continuo.0h3v.s10.f2471812f9b6 from=translated src=- shape=03571cec vocab=31318566
-/
scoped instance instContinuousConstSMul : ContinuousConstSMul (decomp E K w) w.Completion :=
  ⟨fun σ => continuous_actRingEquiv σ⟩

noncomputable scoped instance instMulDistribMulActionUnits : MulDistribMulAction (decomp E K w) (w.Completion)ˣ :=
  Units.mulDistribMulActionRight

noncomputable scoped instance instMulActionUnits : MulAction (decomp E K w) (w.Completion)ˣ :=
  (instMulDistribMulActionUnits (E := E) (K := K) (w := w)).toMulAction

noncomputable scoped instance instSMulUnits : SMul (decomp E K w) (w.Completion)ˣ :=
  (instMulActionUnits (E := E) (K := K) (w := w)).toSMul

/--
@isnad1 id=eq.0h5v.s11.1d19af81d8d5 from=translated src=- shape=36271cb5 vocab=05ff86de
-/
theorem coe_smul_units (σ : decomp E K w) (u : (w.Completion)ˣ) : ((σ • u : (w.Completion)ˣ) : w.Completion) = σ • (u : w.Completion) := rfl

variable (E K w) in

noncomputable abbrev localUnits : Rep ℤ (decomp E K w) := Rep.ofMulDistribMulAction (decomp E K w) (w.Completion)ˣ

end NumberField.InfPlaceDecomp

namespace NumberField.ArchIdele

open scoped NumberField.InfPlaceDecomp

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

/--
@isnad1 id=ex.0h3v.s6.6df69aa10098 from=translated src=- shape=120adf72 vocab=5bc4ee60
-/
theorem exists_above (v : InfinitePlace E) : ∃ w : InfinitePlace K, w.comap (algebraMap E K) = v :=
  InfinitePlace.comap_surjective v

noncomputable def above (v : InfinitePlace E) : InfinitePlace K := (exists_above E K v).choose

/--
@isnad1 id=eq.0h3v.s6.5fa4240af5e4 from=translated src=- shape=928ea855 vocab=a4c4d457
-/
theorem comap_above (v : InfinitePlace E) : (above E K v).comap (algebraMap E K) = v := (exists_above E K v).choose_spec

noncomputable abbrev fibre (v : InfinitePlace E) : Rep ℤ (K ≃ₐ[E] K) :=
  Rep.coind (InfPlaceDecomp.decomp E K (above E K v)).subtype (InfPlaceDecomp.localUnits E K (above E K v))

noncomputable abbrev obj : Rep ℤ (K ≃ₐ[E] K) := GroupCohomology.RepPi.obj (fibre E K)

end NumberField.ArchIdele
