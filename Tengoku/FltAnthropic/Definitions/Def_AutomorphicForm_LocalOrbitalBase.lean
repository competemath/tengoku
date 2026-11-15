import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_FactorizableTestFn

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

noncomputable section

namespace AutomorphicForm

section IntegralUnits

variable {A : Type*}

def integralMatrixSet (U : Set A) : Set (Matrix (Fin 2) (Fin 2) A) := {m | ∀ i j, m i j ∈ U}

/--
@isnad1 id=eq.0h2v.s6.bd9bcdd3f475 from=translated src=- shape=55d5dbd3 vocab=4c5992f7
-/
theorem integralMatrixSet_eq_pi (U : Set A) :
    integralMatrixSet U = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => U := by
  ext m
  exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩

/--
@isnad1 id=iscompac.1h2v.s5.79c1a8c7e004 from=translated src=- shape=7a9889e3 vocab=db0852c6
-/
theorem isCompact_integralMatrixSet [TopologicalSpace A] {U : Set A} (hU : IsCompact U) :
    IsCompact (integralMatrixSet U) := by
  rw [integralMatrixSet_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hU

/--
@isnad1 id=isopen.1h2v.s5.b2214eed5780 from=translated src=- shape=7a9889e3 vocab=ae23e4a6
-/
theorem isOpen_integralMatrixSet [TopologicalSpace A] {U : Set A} (hU : IsOpen U) : IsOpen (integralMatrixSet U) := by
  rw [integralMatrixSet_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hU

variable [CommRing A]

def integralUnitsSet (U : Set A) : Set (GL (Fin 2) A) :=
  {g | (g : Matrix (Fin 2) (Fin 2) A) ∈ integralMatrixSet U ∧
    ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) ∈ integralMatrixSet U}

/--
@isnad1 id=iff.0h3v.s8.21740fb4ebe5 from=translated src=- shape=eeae9aad vocab=1a4e148a
-/
theorem mem_integralUnitsSet {U : Set A} {g : GL (Fin 2) A} :
    g ∈ integralUnitsSet U ↔ (∀ i j, (g : Matrix (Fin 2) (Fin 2) A) i j ∈ U) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j ∈ U :=
  Iff.rfl

/--
@isnad1 id=mem.2h2v.s7.2f4060b566a6 from=translated src=- shape=d94c976a vocab=69cd019c
-/
theorem one_mem_integralUnitsSet {U : Set A} (h0 : (0 : A) ∈ U) (h1 : (1 : A) ∈ U) :
    (1 : GL (Fin 2) A) ∈ integralUnitsSet U := by
  have hmat : (1 : Matrix (Fin 2) (Fin 2) A) ∈ integralMatrixSet U := fun i j => by
    by_cases h : i = j
    · subst h; rw [Matrix.one_apply_eq]; exact h1
    · rw [Matrix.one_apply_ne h]; exact h0
  refine ⟨?_, ?_⟩
  · rw [Units.val_one]; exact hmat
  · rw [inv_one, Units.val_one]; exact hmat

/--
@isnad1 id=eq.0h2v.s10.543a59f897b6 from=translated src=- shape=31ed324d vocab=482a5608
-/
theorem integralUnitsSet_eq_preimage (U : Set A) :
    integralUnitsSet U = (Units.embedProduct (Matrix (Fin 2) (Fin 2) A)) ⁻¹'
      (integralMatrixSet U ×ˢ (MulOpposite.op '' integralMatrixSet U)) := by
  ext g
  simp only [integralUnitsSet, Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, _, h2, rfl⟩
  · rintro ⟨h1, m, hm, hm'⟩
    refine ⟨h1, ?_⟩
    have : m = ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) := MulOpposite.op_injective hm'
    rw [← this]
    exact hm

/--
@isnad1 id=iscompac.1h2v.s7.bb9ea361bb76 from=translated src=- shape=94b09121 vocab=e99ebd96
-/
theorem isCompact_integralUnitsSet [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] {U : Set A}
    (hU : IsCompact U) :
    IsCompact (integralUnitsSet U) := by
  rw [integralUnitsSet_eq_preimage]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    ((isCompact_integralMatrixSet hU).prod
      ((isCompact_integralMatrixSet hU).image MulOpposite.continuous_op))

/--
@isnad1 id=isopen.1h2v.s7.8cf5686cd03f from=translated src=- shape=94b09121 vocab=07b0ffed
-/
theorem isOpen_integralUnitsSet [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] {U : Set A}
    (hU : IsOpen U) : IsOpen (integralUnitsSet U) := by
  rw [integralUnitsSet_eq_preimage]
  exact ((isOpen_integralMatrixSet hU).prod
    (MulOpposite.opHomeomorph.isOpenMap _ (isOpen_integralMatrixSet hU))).preimage
    Units.continuous_embedProduct

end IntegralUnits

section Local

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def IsLocalTestFn (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) : Prop :=
  IsLocallyConstant fv ∧ HasCompactSupport fv

/--
@isnad1 id=islocalt.0h2v.s6.8ab5428580a9 from=translated src=- shape=00521b2a vocab=bceffbee
-/
theorem isLocalTestFn_zero : IsLocalTestFn K v (fun _ => 0) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

def localAt : GL (Fin 2) (AdeleRing (𝓞 K) K) →* GL (Fin 2) (v.adicCompletion K) :=
  (AdelicLevel.finComponent (𝓞 K) K v).comp (AdelicLevel.glFin (𝓞 K) K)

/--
@isnad1 id=continuo.0h2v.s11.320614cbb1db from=translated src=- shape=5fd8a2cd vocab=438ce934
-/
theorem continuous_localAt : Continuous (localAt K v) :=
  (AdelicLevel.continuous_finComponent (𝓞 K) K v).comp (AdelicLevel.continuous_glFin (𝓞 K) K)

def localIntegralSet : Set (GL (Fin 2) (v.adicCompletion K)) :=
  integralUnitsSet (v.adicCompletionIntegers K : Set (v.adicCompletion K))

/--
@isnad1 id=iff.0h3v.s10.7c535df2a4d8 from=translated src=- shape=92ac67ff vocab=dae13557
-/
theorem mem_localIntegralSet {g : GL (Fin 2) (v.adicCompletion K)} :
    g ∈ localIntegralSet K v ↔
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
        ∈ v.adicCompletionIntegers K :=
  Iff.rfl

/--
@isnad1 id=mem.0h2v.s9.66ffa81954af from=translated src=- shape=dd2316ee vocab=ad627fac
-/
theorem one_mem_localIntegralSet : (1 : GL (Fin 2) (v.adicCompletion K)) ∈ localIntegralSet K v :=
  one_mem_integralUnitsSet (zero_mem _) (one_mem _)

/--
@isnad1 id=iscompac.0h2v.s8.9bf8ff809ee1 from=translated src=- shape=a0d59138 vocab=2df7b78d
-/
theorem isCompact_localIntegralSet : IsCompact (localIntegralSet K v) :=
  isCompact_integralUnitsSet
    (isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v))

/--
@isnad1 id=isopen.0h2v.s8.7c353e83ccbb from=translated src=- shape=a0d59138 vocab=b83b1fa5
-/
theorem isOpen_localIntegralSet : IsOpen (localIntegralSet K v) :=
  isOpen_integralUnitsSet ((AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 K) K).out v)

def localIntegralCompacts : PositiveCompacts (GL (Fin 2) (v.adicCompletion K)) where
  carrier := localIntegralSet K v
  isCompact' := isCompact_localIntegralSet K v
  interior_nonempty' := by
    rw [(isOpen_localIntegralSet K v).interior_eq]
    exact ⟨1, one_mem_localIntegralSet K v⟩

/--
@isnad1 id=eq.0h2v.s9.c3506dbf6963 from=translated src=- shape=dc3832c0 vocab=48af358d
-/
theorem coe_localIntegralCompacts :
    (localIntegralCompacts K v : Set (GL (Fin 2) (v.adicCompletion K))) = localIntegralSet K v :=
  rfl

/--
@isnad1 id=islocall.2h2v.s5.9b45af4b2c10 from=translated src=- shape=80de0fd3 vocab=689b7a54
-/
theorem isLocallyConstant_indicator_one {X : Type*} [TopologicalSpace X] {U : Set X}
    (hU : IsOpen U) (hU' : IsClosed U) : IsLocallyConstant (U.indicator fun _ => (1 : ℂ)) := by
  intro s
  by_cases h1 : (1 : ℂ) ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = Set.univ := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact isOpen_univ
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = U := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact hU
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = Uᶜ := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact hU'.isOpen_compl
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = ∅ := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact isOpen_empty

/--
@isnad1 id=islocalt.0h2v.s7.5892adc7191d from=translated src=- shape=8e85d6db vocab=ff4f652e
-/
theorem isLocalTestFn_indicator_localIntegralSet :
    IsLocalTestFn K v ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) :=
  ⟨isLocallyConstant_indicator_one (isOpen_localIntegralSet K v)
      (isCompact_localIntegralSet K v).isClosed,
    HasCompactSupport.intro (isCompact_localIntegralSet K v) fun _ hg => by simp [hg]⟩

@[reducible] def localGLBorel : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := borel _

/--
@isnad1 id=borelspa.0h2v.s8.8b5043e06a3c from=translated src=- shape=6ea00ab0 vocab=18bf8e41
-/
theorem borelSpace_localGLBorel :
    @BorelSpace (GL (Fin 2) (v.adicCompletion K)) _ (localGLBorel K v) :=
  @BorelSpace.mk _ _ (localGLBorel K v) rfl

/--
@isnad1 id=locallyc.0h2v.s6.0a3486a4f7d0 from=translated src=- shape=7bcbd025 vocab=325de3c6
-/
theorem locallyCompactSpace_matrix_adicCompletion :
    LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → v.adicCompletion K))

/--
@isnad1 id=locallyc.0h2v.s8.51bd4db1fa82 from=translated src=- shape=6ea00ab0 vocab=04c8f06c
-/
theorem locallyCompactSpace_localGL : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion K)) := by
  haveI := locallyCompactSpace_matrix_adicCompletion K v
  infer_instance

def localHaar : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v) := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := locallyCompactSpace_localGL K v
  exact Measure.haarMeasure (localIntegralCompacts K v)

/--
@isnad1 id=ishaarme.0h2v.s8.740d0725d940 from=translated src=- shape=a0d59138 vocab=4ea96b51
-/
theorem isHaarMeasure_localHaar :
    @Measure.IsHaarMeasure (GL (Fin 2) (v.adicCompletion K)) _ _ (localGLBorel K v) (localHaar K v) := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := locallyCompactSpace_localGL K v
  exact Measure.isHaarMeasure_haarMeasure _

/--
@isnad1 id=eq.0h2v.s8.ce6e3600d9eb from=translated src=- shape=fbe513b9 vocab=4fdd6621
-/
theorem localHaar_localIntegralSet : localHaar K v (localIntegralSet K v) = 1 := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := locallyCompactSpace_localGL K v
  exact Measure.haarMeasure_self

end Local

section OrbitalIntegral

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    Subgroup (GL (Fin 2) (v.adicCompletion K)) :=
  Subgroup.centralizer {γ}

@[reducible] def localCentralizerBorel (γ : GL (Fin 2) (v.adicCompletion K)) :
    MeasurableSpace (localCentralizer K v γ) := borel _

def IsSectionFn (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (w : GL (Fin 2) (v.adicCompletion K) → ℝ) : Prop :=
  letI := localGLBorel K v
  letI := localCentralizerBorel K v γ
  (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
    ∀ x, fv (x⁻¹ * γ * x) ≠ 0 → ∫ t : localCentralizer K v γ, w (t * x) ∂τ = 1

def IsOrbitalIntegral (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ) : Prop :=
  letI := localGLBorel K v
  ∃ w : GL (Fin 2) (v.adicCompletion K) → ℝ, IsSectionFn K v γ τ fv w ∧
    I = ∫ x, fv (x⁻¹ * γ * x) * (w x : ℂ) ∂(localHaar K v)

/--
@isnad1 id=issectio.0h4v.s10.bfc972f01a0d from=translated src=- shape=4008aaa5 vocab=973b92a2
-/
theorem isSectionFn_zero (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    IsSectionFn K v γ τ (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun _ h => absurd rfl h⟩

/--
@isnad1 id=isorbita.0h4v.s10.2f7d66d8768e from=translated src=- shape=0495ebba vocab=ebc5f66d
-/
theorem isOrbitalIntegral_zero (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    IsOrbitalIntegral K v γ τ (fun _ => 0) 0 :=
  ⟨fun _ => 0, isSectionFn_zero K v γ τ, by simp⟩

/--
@isnad1 id=not.0h4v.s10.1b0da6b77a11 from=translated src=- shape=33888827 vocab=ebc5f66d
-/
theorem not_isOrbitalIntegral_zero_one (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    ¬ IsOrbitalIntegral K v γ τ (fun _ => 0) 1 := by
  rintro ⟨w, -, h⟩
  simp at h

end OrbitalIntegral

section UnitFactor

variable (K : Type) [Field K] [NumberField K]

def unitFinSet : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :=
  {h | ∀ v : HeightOneSpectrum (𝓞 K), AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v}

/--
@isnad1 id=eq.0h1v.s7.713f1604267e from=translated src=- shape=5b22ea65 vocab=8fe151e6
-/
theorem unitFinSet_eq :
    unitFinSet K = integralUnitsSet (AdelicLevel.integralFiniteAdeles (𝓞 K) K) := by
  ext h
  simp only [unitFinSet, Set.mem_ofPred_eq, mem_localIntegralSet, mem_integralUnitsSet,
    AdelicLevel.integralFiniteAdeles, ← map_inv, AdelicLevel.finComponent_apply]
  exact ⟨fun H => ⟨fun i j v => (H v).1 i j, fun i j v => (H v).2 i j⟩,
    fun H v => ⟨fun i j => H.1 i j v, fun i j => H.2 i j v⟩⟩

/--
@isnad1 id=mem.0h1v.s9.666197334414 from=translated src=- shape=cfa09007 vocab=23e0aeef
-/
theorem one_mem_unitFinSet : (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) ∈ unitFinSet K :=
  fun v => by rw [map_one]; exact one_mem_localIntegralSet K v

/--
@isnad1 id=iscompac.0h1v.s8.c2c1220de6ee from=translated src=- shape=0f6ae64a vocab=7a6db454
-/
theorem isCompact_unitFinSet : IsCompact (unitFinSet K) := by
  rw [unitFinSet_eq]
  exact isCompact_integralUnitsSet (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 K) K)

/--
@isnad1 id=isopen.0h1v.s8.de49c2cb7b7a from=translated src=- shape=0f6ae64a vocab=1dccb1b7
-/
theorem isOpen_unitFinSet : IsOpen (unitFinSet K) := by
  rw [unitFinSet_eq]
  exact isOpen_integralUnitsSet (AdelicLevel.isOpen_integralFiniteAdeles (𝓞 K) K)

/--
@isnad1 id=isfintes.0h1v.s7.7b2b2c6276b5 from=translated src=- shape=3f76f98c vocab=59edb394
-/
theorem isFinTestFactor_indicator_unitFinSet :
    IsFinTestFactor K ((unitFinSet K).indicator fun _ => (1 : ℂ)) :=
  ⟨isLocallyConstant_indicator_one (isOpen_unitFinSet K) (isCompact_unitFinSet K).isClosed,
    HasCompactSupport.intro (isCompact_unitFinSet K) fun _ hg => by simp [hg]⟩

end UnitFactor

section Tier

variable (K : Type) [Field K] [NumberField K]

/--
@isnad1 id=eq.0h1v.s9.0b5a1cd221fe from=translated src=- shape=1f2177df vocab=32ce9392
-/
theorem unitFinSet_eq_finiteIntegralGL2 :
    unitFinSet K = (AdelicLevel.finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := by
  ext h
  rw [unitFinSet_eq, SetLike.mem_coe, AdelicLevel.mem_finiteIntegralGL2_iff]
  exact Iff.rfl

/--
@isnad1 id=eq.1h3v.s10.9f900774812a from=translated src=- shape=0d075c37 vocab=e7589481
-/
theorem indicator_unitFinSet_mul_left {u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hu : u ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (unitFinSet K).indicator (fun _ => (1 : ℂ)) (u * x) =
      (unitFinSet K).indicator (fun _ => (1 : ℂ)) x := by
  have key : u * x ∈ unitFinSet K ↔ x ∈ unitFinSet K := by
    rw [unitFinSet_eq_finiteIntegralGL2, SetLike.mem_coe, SetLike.mem_coe]
    exact Subgroup.mul_mem_cancel_left _ hu
  by_cases hx : x ∈ unitFinSet K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (key.2 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (key.1 h))]

/--
@isnad1 id=eq.1h3v.s10.49958273fc7b from=translated src=- shape=2eed3364 vocab=e7589481
-/
theorem indicator_unitFinSet_mul_right {u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hu : u ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (unitFinSet K).indicator (fun _ => (1 : ℂ)) (x * u) =
      (unitFinSet K).indicator (fun _ => (1 : ℂ)) x := by
  have key : x * u ∈ unitFinSet K ↔ x ∈ unitFinSet K := by
    rw [unitFinSet_eq_finiteIntegralGL2, SetLike.mem_coe, SetLike.mem_coe]
    exact Subgroup.mul_mem_cancel_right _ hu
  by_cases hx : x ∈ unitFinSet K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (key.2 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (key.1 h))]

def IsBiInvariantUnder (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) : Prop :=
  ∀ u ∈ U, ∀ g, f (u * g) = f g ∧ f (g * u) = f g

/--
@isnad1 id=isbiinva.2h4v.s10.4554473cd797 from=translated src=- shape=b5203a47 vocab=3fce724b
-/
theorem IsBiInvariantUnder.mono {U V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hUV : U ≤ V)
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsBiInvariantUnder K V f) :
    IsBiInvariantUnder K U f :=
  fun u hu => hf u (hUV hu)

/--
@isnad1 id=isbiinva.0h2v.s9.4260f0f58b2b from=translated src=- shape=94ded61e vocab=459a31ac
-/
theorem isBiInvariantUnder_bot (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    IsBiInvariantUnder K ⊥ f := by
  intro u hu g
  rw [Subgroup.mem_bot.1 hu, one_mul, mul_one]
  exact ⟨rfl, rfl⟩

def IsUnitFactorizableAt (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) : Prop :=
  IsBiInvariantUnder K U f ∧
  ∃ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
    IsArchTestFactor K fa ∧ IsFinTestFactor K ff ∧ (∀ v ∈ S, IsLocalTestFn K v (fS v)) ∧
    (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
        ff h = ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
    (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) → ff h = 0) ∧
    ∀ g, f g = fa (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g)

/--
@isnad1 id=isunitfa.2h5v.s10.d2a070f5986d from=translated src=- shape=dc635620 vocab=2579969b
-/
theorem IsUnitFactorizableAt.mono {U V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hUV : U ≤ V)
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableAt K V S f) : IsUnitFactorizableAt K U S f :=
  ⟨hf.1.mono K hUV, hf.2⟩

/--
@isnad1 id=isbiinva.1h4v.s8.ed1d93679694 from=translated src=- shape=00a9b5a0 vocab=722cbe6a
-/
theorem IsUnitFactorizableAt.isBiInvariantUnder {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableAt K U S f) : IsBiInvariantUnder K U f :=
  hf.1

/--
@isnad1 id=isfactor.1h4v.s8.cdb8bb9b6406 from=translated src=- shape=c40e63ab vocab=c516a144
-/
theorem IsUnitFactorizableAt.isFactorizableTestFn {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableAt K U S f) : IsFactorizableTestFn K f := by
  obtain ⟨-, fa, ff, _, hfa, hff, -, -, -, hf⟩ := hf
  exact ⟨fa, ff, hfa, hff, hf⟩

def IsIntegralLevel (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))) : Prop :=
  ∀ u ∈ U, AdelicLevel.glArch (𝓞 K) K u = 1 ∧
    AdelicLevel.glFin (𝓞 K) K u ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K

/--
@isnad1 id=isintegr.0h1v.s8.023b5d5e7f79 from=translated src=- shape=194783ed vocab=b2e36022
-/
theorem isIntegralLevel_bot : IsIntegralLevel K ⊥ := by
  intro u hu
  rw [Subgroup.mem_bot.1 hu, map_one, map_one]
  exact ⟨rfl, one_mem _⟩

/--
@isnad1 id=isintegr.0h2v.s9.82d9a1feafc7 from=translated src=- shape=a11f7409 vocab=5b8ffac2
-/
theorem isIntegralLevel_levelOne_inf_ker (N : Ideal (𝓞 K)) :
    IsIntegralLevel K (AdelicLevel.levelOne (𝓞 K) K N ⊓ (AdelicLevel.glArch (𝓞 K) K).ker) := by
  intro u hu
  obtain ⟨hlev, harch⟩ := Subgroup.mem_inf.1 hu
  refine ⟨MonoidHom.mem_ker.1 harch, ?_⟩
  have h0 := AdelicLevel.finiteLevelOne_le_finiteLevelZero (𝓞 K) K N (AdelicLevel.mem_levelOne_iff.1 hlev)
  exact AdelicLevel.mem_finiteIntegralGL2_iff.2 ⟨h0.1.integral, h0.2.integral⟩

/--
@isnad1 id=isunitfa.2h4v.s11.c9b237718a21 from=translated src=- shape=b33380eb vocab=2e0c6270
-/
theorem isUnitFactorizableAt_mul_indicator_unitFinSet {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (hfa : IsArchTestFactor K fa) {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    (hU : IsIntegralLevel K U) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsUnitFactorizableAt K U S fun g => fa (AdelicLevel.glArch (𝓞 K) K g) *
      (unitFinSet K).indicator (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 K) K g) := by
  refine ⟨fun u hu g => ?_, fa, (unitFinSet K).indicator fun _ => (1 : ℂ),
    fun v => (localIntegralSet K v).indicator fun _ => (1 : ℂ), hfa,
    isFinTestFactor_indicator_unitFinSet K, fun v _ => isLocalTestFn_indicator_localIntegralSet K v,
    fun h hS => ?_, fun h hS => ?_, fun _ => rfl⟩
  · obtain ⟨hu1, hu2⟩ := hU u hu
    constructor
    · dsimp only
      rw [map_mul, map_mul, hu1, one_mul, indicator_unitFinSet_mul_left K hu2]
    · dsimp only
      rw [map_mul, map_mul, hu1, mul_one, indicator_unitFinSet_mul_right K hu2]
  · by_cases hall : h ∈ unitFinSet K
    · rw [Set.indicator_of_mem hall]
      exact (Finset.prod_eq_one fun v _ => Set.indicator_of_mem (hall v) _).symm
    · rw [Set.indicator_of_notMem hall]
      obtain ⟨v, hv⟩ : ∃ v, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v := by
        by_contra hcon
        exact hall fun v => by_contra fun hv => hcon ⟨v, hv⟩
      have hvS : v ∈ S := by
        by_contra hvS
        exact hv (hS v hvS)
      exact (Finset.prod_eq_zero hvS (Set.indicator_of_notMem hv _)).symm
  · obtain ⟨v, -, hv⟩ := hS
    have hnot : h ∉ unitFinSet K := fun hall => hv (hall v)
    exact Set.indicator_of_notMem hnot _

/--
@isnad1 id=isunitfa.0h3v.s8.30057787a74d from=translated src=- shape=00b76e88 vocab=83f2af4c
-/
theorem isUnitFactorizableAt_zero (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) : IsUnitFactorizableAt K U S fun _ => 0 := by
  refine ⟨fun _ _ _ => ⟨rfl, rfl⟩, ?_⟩
  simpa using
    (isUnitFactorizableAt_mul_indicator_unitFinSet K (isArchTestFactor_zero K) (isIntegralLevel_bot K) S).2

end Tier

section RegularSemisimple

variable {A : Type*} [CommRing A]

def IsRegularSemisimple (g : GL (Fin 2) A) : Prop :=
  IsUnit (Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) A))

/--
@isnad1 id=iff.0h2v.s8.f9c5a150c1a7 from=translated src=- shape=eb792a88 vocab=35791bde
-/
theorem isRegularSemisimple_iff (g : GL (Fin 2) A) :
    IsRegularSemisimple g ↔
      IsUnit (Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) A)) :=
  Iff.rfl

/--
@isnad1 id=iff.0h2v.s8.8eb9e6c04ce7 from=translated src=- shape=835acaa5 vocab=0ae95dd5
-/
theorem isRegularSemisimple_iff_ne_zero {F : Type*} [Field F] (g : GL (Fin 2) F) :
    IsRegularSemisimple g ↔
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) F) ≠ 0 :=
  isUnit_iff_ne_zero

/--
@isnad1 id=isregula.1h3v.s8.84b34882fae3 from=translated src=- shape=f863ba6c vocab=819eef9c
-/
theorem IsRegularSemisimple.conj {g : GL (Fin 2) A} (hg : IsRegularSemisimple g) (x : GL (Fin 2) A) :
    IsRegularSemisimple (x⁻¹ * g * x) := by
  unfold IsRegularSemisimple at hg ⊢
  have htr : Matrix.trace ((x⁻¹ * g * x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  have hdet : Matrix.det ((x⁻¹ * g * x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      Matrix.det (g : Matrix (Fin 2) (Fin 2) A) := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]
  rw [htr, hdet]
  exact hg

end RegularSemisimple

end AutomorphicForm

end
