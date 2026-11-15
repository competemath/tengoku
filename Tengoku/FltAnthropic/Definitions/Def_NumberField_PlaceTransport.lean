import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace NumberField.PlaceTransport

section general
variable {R S : Type*} [Field R] [Field S] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/--
@isnad1 id=uniformc.2h6v.s9.dd10802b06ec from=translated src=- shape=026d552e vocab=08048c31
-/
theorem uniformContinuous_congr_of_forall_eq (v : Valuation R Γ₀) (v' : Valuation S Γ₀) (hv : Function.Surjective v)
    (f : R ≃+* S) (h : ∀ x, v' (f x) = v x) : UniformContinuous (WithVal.congr v v' f) := by
  apply uniformContinuous_addMonoidHom_of_continuous
  apply continuous_of_continuousAt_zero (WithVal.congr v v' f).toAddMonoidHom
  rw [ContinuousAt, map_zero]
  intro s hs
  rw [Filter.mem_map]
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  obtain ⟨x₀, hx₀⟩ := hv (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have hx₀' : Valued.v.restrict (WithVal.toVal v x₀) ≠ 0 := fun h0 => by
    have h1 := (Valuation.restrict_eq_zero_iff Valued.v).1 h0
    rw [WithVal.valued_toVal, hx₀] at h1
    exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h1.trans (map_zero _).symm))
  refine Valued.mem_nhds_zero.2 ⟨Units.mk0 _ hx₀', fun x hx => hγ ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff, WithVal.valued_toVal, hx₀] at hx
  show Valued.v.restrict (WithVal.congr v v' f x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, WithVal.congr_apply, WithVal.valued_toVal, h, WithVal.apply_ofVal]
  exact hx

end general

variable (E K : Type*) [Field E] [Field K] [Algebra E K]

noncomputable scoped instance instMulActionHeightOneSpectrum : MulAction (K ≃ₐ[E] K) (HeightOneSpectrum (𝓞 K)) where
  smul σ w := HeightOneSpectrum.comap (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ⁻¹ : 𝓞 K →+* 𝓞 K)
    (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ⁻¹).surjective w
  one_smul w := HeightOneSpectrum.ext (Ideal.ext fun x => by
    show (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) 1⁻¹) x ∈ w.asIdeal ↔ x ∈ w.asIdeal
    rw [MulSemiringAction.toRingEquiv_apply_apply, inv_one, one_smul])
  mul_smul σ τ w := HeightOneSpectrum.ext (Ideal.ext fun x => by
    show (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) (σ * τ)⁻¹) x ∈ w.asIdeal ↔
      (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) τ⁻¹) ((MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ⁻¹) x) ∈ w.asIdeal
    rw [MulSemiringAction.toRingEquiv_apply_apply, MulSemiringAction.toRingEquiv_apply_apply, MulSemiringAction.toRingEquiv_apply_apply,
      mul_inv_rev, mul_smul])

variable {E K}

/--
@isnad1 id=eq.0h4v.s11.945ead1f8016 from=translated src=- shape=659e28d2 vocab=b632000a
-/
theorem smul_asIdeal (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    (σ • w).asIdeal = w.asIdeal.comap (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ⁻¹ : 𝓞 K →+* 𝓞 K) := rfl

/--
@isnad1 id=iff.0h5v.s10.b7f639bf4884 from=translated src=- shape=b017a36e vocab=5fab6720
-/
theorem mem_smul_asIdeal_iff (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    x ∈ (σ • w).asIdeal ↔ σ⁻¹ • x ∈ w.asIdeal := Iff.rfl

/--
@isnad1 id=iff.0h5v.s9.ae9df246e74c from=translated src=- shape=a8971504 vocab=3f7c47df
-/
theorem smul_mem_smul_asIdeal_iff (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    σ • x ∈ (σ • w).asIdeal ↔ x ∈ w.asIdeal := by
  rw [mem_smul_asIdeal_iff, inv_smul_smul]

/--
@isnad1 id=eq.0h4v.s11.c1e2a3fc4f26 from=translated src=- shape=b035f929 vocab=4b2e3c18
-/
theorem smul_asIdeal_eq_map (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    (σ • w).asIdeal = Ideal.map ((MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ : 𝓞 K ≃+* 𝓞 K) : 𝓞 K →+* 𝓞 K) w.asIdeal := by
  rw [Ideal.map_comap_of_equiv]
  ext x
  rw [mem_smul_asIdeal_iff, Ideal.mem_comap, MulSemiringAction.toRingEquiv_apply_symm_apply]

/--
@isnad1 id=iff.0h6v.s10.61250fbec032 from=translated src=- shape=bc35a7f7 vocab=605eef53
-/
theorem smul_mem_smul_asIdeal_pow_iff (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (n : ℕ) :
    σ • x ∈ (σ • w).asIdeal ^ n ↔ x ∈ w.asIdeal ^ n := by
  rw [smul_asIdeal_eq_map, ← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap, MulSemiringAction.toRingEquiv_apply_symm_apply,
    inv_smul_smul]

/--
@isnad1 id=eq.1h5v.s9.2a0942de7836 from=translated src=- shape=9b28ab1d vocab=0b06f2e7
-/
theorem inv_smul_eq_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') : σ⁻¹ • w' = w := by
  rw [← h, inv_smul_smul]

variable [NumberField K]

/--
@isnad1 id=eq.0h5v.s9.738ea6381ec2 from=translated src=- shape=6dcbf604 vocab=2f790659
-/
theorem intValuation_smul_apply (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    (σ • w).intValuation (σ • r) = w.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [smul_zero, Valuation.map_zero, Valuation.map_zero]
  · have hσr : σ • r ≠ 0 := fun h0 => hr (by rw [← inv_smul_smul σ r, h0, smul_zero])
    apply le_antisymm
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, w.intValuation r = WithZero.exp (-(n : ℤ)) := ⟨_, w.intValuation_if_neg hr⟩
      rw [hn, HeightOneSpectrum.intValuation_le_pow_iff_mem, smul_mem_smul_asIdeal_pow_iff,
        ← HeightOneSpectrum.intValuation_le_pow_iff_mem, hn]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (σ • w).intValuation (σ • r) = WithZero.exp (-(n : ℤ)) := ⟨_, (σ • w).intValuation_if_neg hσr⟩
      rw [hn, HeightOneSpectrum.intValuation_le_pow_iff_mem, ← smul_mem_smul_asIdeal_pow_iff σ,
        ← HeightOneSpectrum.intValuation_le_pow_iff_mem, hn]

/--
@isnad1 id=eq.0h5v.s9.831ec670b9fa from=translated src=- shape=b78cec96 vocab=5e68a917
-/
theorem valuation_smul_apply (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    (σ • w).valuation K (σ x) = w.valuation K x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have h1 : ∀ c : 𝓞 K, σ (algebraMap (𝓞 K) K c) = algebraMap (𝓞 K) K (σ • c) := fun c => rfl
  rw [map_div₀, map_div₀, map_div₀, h1, h1, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, intValuation_smul_apply,
    intValuation_smul_apply]

/--
@isnad1 id=eq.1h6v.s9.eb283e7e1813 from=translated src=- shape=a16f4f14 vocab=5e68a917
-/
theorem valuation_apply_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x : K) :
    w'.valuation K (σ x) = w.valuation K x := by
  subst h
  exact valuation_smul_apply σ w x

/--
@isnad1 id=uniformc.1h5v.s10.49b78d8d3aee from=translated src=- shape=d3c648b7 vocab=1f58b764
-/
theorem uniformContinuous_congr_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') :
    UniformContinuous (WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K)) :=
  uniformContinuous_congr_of_forall_eq (w.valuation K) (w'.valuation K) (w.valuation_surjective K) _ (valuation_apply_of_smul_eq h)

noncomputable def transport (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') :
    w.adicCompletion K ≃+* w'.adicCompletion K :=
  ((HeightOneSpectrum.adicCompletion.equiv K w).trans
    (UniformSpace.Completion.mapRingEquiv (WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_smul_eq h).continuous
      ((uniformContinuous_congr_of_smul_eq (inv_smul_eq_of_smul_eq h)).continuous.congr fun _ => rfl))).trans
    (HeightOneSpectrum.adicCompletion.equiv K w').symm

/--
@isnad1 id=eq.1h6v.s11.12ad2ba98a1a from=translated src=- shape=1257cfaa vocab=bdf23c93
-/
theorem transport_apply (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x : w.adicCompletion K) :
    (transport σ h x).toCompletion
      = UniformSpace.Completion.map (WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K)) x.toCompletion :=
  rfl

/--
@isnad1 id=eq.1h6v.s11.0fe540e20080 from=translated src=- shape=5c30a001 vocab=fa977f5f
-/
theorem transport_coe (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x : WithVal (w.valuation K)) :
    transport σ h (x : w.adicCompletion K)
      = ((WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K) x : WithVal (w'.valuation K)) : w'.adicCompletion K) := by
  apply HeightOneSpectrum.adicCompletion.ext
  rw [transport_apply, HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion,
    HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_smul_eq h)]

/--
@isnad1 id=continuo.1h5v.s10.9794b40fd95a from=translated src=- shape=3ae8a06d vocab=166abaa6
-/
theorem continuous_transport (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') : Continuous (transport σ h) := by
  have : (transport σ h : w.adicCompletion K → w'.adicCompletion K)
      = HeightOneSpectrum.adicCompletion.ofCompletion ∘
        UniformSpace.Completion.map (WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K)) ∘
        HeightOneSpectrum.adicCompletion.toCompletion :=
    funext fun x => HeightOneSpectrum.adicCompletion.ext (h := transport_apply σ h x)
  rw [this]
  exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w').comp
    (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion K w))

/--
@isnad1 id=isclopen.1h3v.s8.fb77ace2e6f4 from=translated src=- shape=b1e07854 vocab=4ec94870
-/
theorem isClopen_setOf_valued_le (w : HeightOneSpectrum (𝓞 K)) {c : WithZero (Multiplicative ℤ)} (hc : c ≠ 0) :
    IsClopen {y : w.adicCompletion K | Valued.v y ≤ c} := by
  obtain ⟨y₁, rfl⟩ := w.valuedAdicCompletion_surjective K c
  have hr : Valued.v.restrict y₁ ≠ 0 := fun h0 => hc ((Valuation.restrict_eq_zero_iff Valued.v).1 h0)
  have : {y : w.adicCompletion K | Valued.v y ≤ Valued.v y₁} = {y | Valued.v.restrict y ≤ Valued.v.restrict y₁} :=
    Set.ext fun y => (Valuation.restrict_le_iff Valued.v (x := y) (y := y₁)).symm
  rw [this]
  exact Valued.isClopen_closedBall (w.adicCompletion K) hr

/--
@isnad1 id=eq.1h6v.s11.7db02dd97492 from=translated src=- shape=f31621f7 vocab=5590631f
-/
theorem valued_transport (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x : w.adicCompletion K) :
    Valued.v (transport σ h x) = Valued.v x := by

  have key : ∀ c : WithZero (Multiplicative ℤ), c ≠ 0 → ∀ y : w.adicCompletion K, (Valued.v (transport σ h y) ≤ c ↔ Valued.v y ≤ c) := by
    intro c hc y
    have hclosed : IsClosed {y : w.adicCompletion K | Valued.v (transport σ h y) ≤ c ↔ Valued.v y ≤ c} := by
      have h1 : IsClopen {y : w.adicCompletion K | Valued.v (transport σ h y) ≤ c} :=
        (isClopen_setOf_valued_le w' hc).preimage (continuous_transport σ h)
      have h2 : IsClopen {y : w.adicCompletion K | Valued.v y ≤ c} := isClopen_setOf_valued_le w hc
      have : {y : w.adicCompletion K | Valued.v (transport σ h y) ≤ c ↔ Valued.v y ≤ c}
          = ({y | Valued.v (transport σ h y) ≤ c} ∩ {y | Valued.v y ≤ c}) ∪ ({y | Valued.v (transport σ h y) ≤ c}ᶜ ∩ {y | Valued.v y ≤ c}ᶜ) := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
        tauto
      rw [this]
      exact ((h1.inter h2).union (h1.compl.inter h2.compl)).isClosed
    obtain ⟨y, rfl⟩ := HeightOneSpectrum.adicCompletion.ofCompletion_surjective K w y
    refine UniformSpace.Completion.induction_on
      (p := fun y => Valued.v (transport σ h (.ofCompletion y)) ≤ c ↔
        Valued.v (HeightOneSpectrum.adicCompletion.ofCompletion y : w.adicCompletion K) ≤ c) y
      (by simpa only [Set.preimage_ofPred_eq] using
        hclosed.preimage (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w)) fun a => ?_
    show Valued.v (transport σ h (a : w.adicCompletion K)) ≤ c ↔ Valued.v (a : w.adicCompletion K) ≤ c
    rw [transport_coe, HeightOneSpectrum.adicCompletion.valued_ofCompletion,
      HeightOneSpectrum.adicCompletion.valued_ofCompletion, Valued.valuedCompletion_apply, Valued.valuedCompletion_apply, ← WithVal.apply_ofVal, ← WithVal.apply_ofVal,
      WithVal.congr_apply, WithVal.ofVal_toVal, AlgEquiv.coe_ringEquiv, valuation_apply_of_smul_eq h]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, Valuation.map_zero, Valuation.map_zero]
  · have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    have h0' : Valued.v (transport σ h x) ≠ 0 := (Valuation.ne_zero_iff _).2 ((map_ne_zero (transport σ h)).2 hx)
    exact le_antisymm ((key _ h0 x).2 le_rfl) ((key _ h0' x).1 le_rfl)

/--
@isnad1 id=iff.1h6v.s10.2d5557cb5af1 from=translated src=- shape=313f3346 vocab=5ebbce48
-/
theorem transport_mem_adicCompletionIntegers_iff (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w')
    (x : w.adicCompletion K) : transport σ h x ∈ w'.adicCompletionIntegers K ↔ x ∈ w.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, valued_transport]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

noncomputable def transportIntegers (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') :
    w.adicCompletionIntegers K ≃+* w'.adicCompletionIntegers K where
  toFun x := ⟨transport σ h x, (transport_mem_adicCompletionIntegers_iff σ h _).2 x.2⟩
  invFun y := ⟨(transport σ h).symm y, (transport_mem_adicCompletionIntegers_iff σ h _).1 (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext ((transport σ h).symm_apply_apply x)
  right_inv y := Subtype.ext ((transport σ h).apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul (transport σ h) (x : w.adicCompletion K) (y : w.adicCompletion K))
  map_add' x y := Subtype.ext (map_add (transport σ h) (x : w.adicCompletion K) (y : w.adicCompletion K))

set_option synthInstance.maxHeartbeats 200000 in
/--
@isnad1 id=eq.1h6v.s13.59a4289660ec from=translated src=- shape=406b512b vocab=a24aeee6
-/
theorem coe_transportIntegers (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x : w.adicCompletionIntegers K) :
    ((transportIntegers σ h x : w'.adicCompletionIntegers K) : w'.adicCompletion K) = transport σ h (x : w.adicCompletion K) := rfl

set_option synthInstance.maxHeartbeats 200000 in

noncomputable abbrev transportUnits (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') :
    (w.adicCompletion K)ˣ ≃* (w'.adicCompletion K)ˣ :=
  Units.mapEquiv (transport σ h).toMulEquiv

set_option synthInstance.maxHeartbeats 200000 in

noncomputable abbrev transportIntegerUnits (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') :
    (w.adicCompletionIntegers K)ˣ ≃* (w'.adicCompletionIntegers K)ˣ :=
  Units.mapEquiv (transportIntegers σ h).toMulEquiv

end NumberField.PlaceTransport
