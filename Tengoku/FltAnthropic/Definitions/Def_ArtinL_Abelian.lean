import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArtinFrobenius

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped Classical

namespace ArtinL.Abelian

section Finite

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

variable (K M) in

def inertiaGroup (v : HeightOneSpectrum (𝓞 K)) : Subgroup (M ≃ₐ[K] M) :=
  (LanglandsTunnell.P2.Artin.primeAbove K M v).inertia (M ≃ₐ[K] M)

variable (K M) in

def ramificationGroup (v : HeightOneSpectrum (𝓞 K)) (i : ℕ) : Subgroup (M ≃ₐ[K] M) :=
  (LanglandsTunnell.P2.Artin.primeAbove K M v ^ (i + 1)).inertia (M ≃ₐ[K] M)

omit [NumberField M] [IsGalois K M] in
/--
@isnad1 id=eq.0h3v.s6.06e79903fd53 from=translated src=- shape=3e85796a vocab=7a4f2428
-/
theorem ramificationGroup_zero (v : HeightOneSpectrum (𝓞 K)) :
    ramificationGroup K M v 0 = inertiaGroup K M v := by
  rw [ramificationGroup, zero_add, pow_one, inertiaGroup]

def IsUnramifiedAt (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ σ ∈ inertiaGroup K M v, ψ σ = 1

def localValue (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if IsUnramifiedAt ψ v then ((ψ (LanglandsTunnell.P2.Artin.artinFrob K M v) : ℂˣ) : ℂ) else 0

def idealValue (ψ : (M ≃ₐ[K] M) →* ℂˣ) (I : Ideal (𝓞 K)) : ℂ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    localValue ψ v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors

def coeff (ψ : (M ≃ₐ[K] M) →* ℂˣ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else ∑ I ∈ (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).toFinset, idealValue ψ I

def LSeries (ψ : (M ≃ₐ[K] M) →* ℂˣ) (s : ℂ) : ℂ :=
  _root_.LSeries (coeff ψ) s

def swanConductor (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℚ :=
  ∑ᶠ i : ℕ,
    (Nat.card (ramificationGroup K M v (i + 1)) : ℚ) / (Nat.card (inertiaGroup K M v) : ℚ) *
      (if ∀ σ ∈ ramificationGroup K M v (i + 1), ψ σ = 1 then 0 else 1)

def conductorExponent (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (if IsUnramifiedAt ψ v then 0 else 1) + ⌈swanConductor ψ v⌉₊

def conductor (ψ : (M ≃ₐ[K] M) →* ℂˣ) : Ideal (𝓞 K) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ conductorExponent ψ v

end Finite

section Archimedean

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

def IsPlusAt (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : InfinitePlace K) : Prop :=
  ∀ w : InfinitePlace M, w.comap (algebraMap K M) = v →
    ∀ σ ∈ MulAction.stabilizer (M ≃ₐ[K] M) w, ψ σ = 1

def nPlus (ψ : (M ≃ₐ[K] M) →* ℂˣ) : ℕ :=
  Nat.card {v : InfinitePlace K // v.IsReal ∧ IsPlusAt ψ v}

def nMinus (ψ : (M ≃ₐ[K] M) →* ℂˣ) : ℕ :=
  nrRealPlaces K - nPlus ψ

end Archimedean

section Completed

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

def completedLSeries (ψ : (M ≃ₐ[K] M) →* ℂˣ) (s : ℂ) : ℂ :=
  ((|(discr K : ℝ)| * (Ideal.absNorm (conductor ψ) : ℝ) : ℝ) : ℂ) ^ (s / 2) *
    Complex.Gammaℝ s ^ nPlus ψ * Complex.Gammaℝ (s + 1) ^ nMinus ψ *
    Complex.Gammaℂ s ^ nrComplexPlaces K * LSeries ψ s

end Completed

section OfSubgroup

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [FiniteDimensional k F]

def ofSubgroup (H : Subgroup (F ≃ₐ[k] F)) (χ : H →* ℂˣ) :
    (F ≃ₐ[IntermediateField.fixedField H] F) →* ℂˣ :=
  χ.comp
    ((MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField H)).toMonoidHom.comp
      (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)).symm.toMonoidHom)

/--
@isnad1 id=eq.0h5v.s12.4394110a1203 from=translated src=- shape=096f6b07 vocab=cf2ad1e6
-/
theorem ofSubgroup_apply (H : Subgroup (F ≃ₐ[k] F)) (χ : H →* ℂˣ)
    (σ : F ≃ₐ[IntermediateField.fixedField H] F) :
    ofSubgroup H χ σ =
      χ ⟨σ.restrictScalars k,
        (IntermediateField.fixingSubgroup_fixedField H).le (fun x => σ.commutes x)⟩ :=
  rfl

omit [FiniteDimensional k F] in
/--
@isnad1 id=eq.0h4v.s12.b578a04ee101 from=translated src=- shape=fc60373e vocab=117c5a47
-/
theorem restrictScalars_fixingSubgroupEquiv (E : IntermediateField k F) (σ : E.fixingSubgroup) :
    (IntermediateField.fixingSubgroupEquiv E σ).restrictScalars k = σ := by
  ext; rfl

/--
@isnad1 id=eq.0h5v.s13.2d8560dde6ee from=translated src=- shape=65b15024 vocab=e9bc4fe8
-/
theorem ofSubgroup_fixingSubgroupEquiv (H : Subgroup (F ≃ₐ[k] F)) (χ : H →* ℂˣ) (h : H) :
    ofSubgroup H χ (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)
      ⟨h, by rw [IntermediateField.fixingSubgroup_fixedField H]; exact h.2⟩) = χ h := by
  rw [ofSubgroup, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl

end OfSubgroup

section Basic

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

/--
@isnad1 id=eq.0h3v.s7.28c2e0034099 from=translated src=- shape=064767b5 vocab=9d7f2f8b
-/
@[simp] theorem coeff_zero (ψ : (M ≃ₐ[K] M) →* ℂˣ) : coeff ψ 0 = 0 := by
  simp [coeff]

omit [IsGalois K M] in

/--
@isnad1 id=ne.0h3v.s8.d46f457c9b4b from=translated src=- shape=8d57d07b vocab=8e1168ff
-/
theorem conductor_ne_bot (ψ : (M ≃ₐ[K] M) →* ℂˣ) : conductor ψ ≠ ⊥ := by
  unfold conductor
  refine finprod_induction (fun I : Ideal (𝓞 K) => I ≠ ⊥) ?_ (fun I J hI hJ => mul_ne_zero hI hJ)
    (fun v => pow_ne_zero _ v.ne_bot)
  exact one_ne_zero

omit [IsGalois K M] in

/--
@isnad1 id=lt.0h3v.s8.544ad48c998f from=translated src=- shape=6b7b2b23 vocab=113db782
-/
theorem absNorm_conductor_pos (ψ : (M ≃ₐ[K] M) →* ℂˣ) : 0 < Ideal.absNorm (conductor ψ) :=
  Nat.pos_of_ne_zero fun h => conductor_ne_bot ψ (Ideal.absNorm_eq_zero_iff.1 h)

omit [NumberField M] [IsGalois K M] in

/--
@isnad1 id=le.0h3v.s7.8ef67e6933ab from=translated src=- shape=df65ed5c vocab=530b7fe8
-/
theorem nPlus_le (ψ : (M ≃ₐ[K] M) →* ℂˣ) : nPlus ψ ≤ nrRealPlaces K := by
  rw [nPlus, nrRealPlaces, ← Nat.card_eq_fintype_card]
  exact Nat.card_mono (Set.toFinite _) fun v hv => hv.1

omit [NumberField M] [IsGalois K M] in

/--
@isnad1 id=eq.0h3v.s7.a6c81a815512 from=translated src=- shape=14814c71 vocab=24d12fc5
-/
theorem nPlus_add_nMinus (ψ : (M ≃ₐ[K] M) →* ℂˣ) : nPlus ψ + nMinus ψ = nrRealPlaces K := by
  rw [nMinus, Nat.add_sub_cancel' (nPlus_le ψ)]

/--
@isnad1 id=eq.0h4v.s9.de70e4ed4f07 from=translated src=- shape=2e3ce141 vocab=da1e9004
-/
theorem norm_apply (ψ : (M ≃ₐ[K] M) →* ℂˣ) (σ : M ≃ₐ[K] M) : ‖((ψ σ : ℂˣ) : ℂ)‖ = 1 := by
  have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
  obtain ⟨n, hn, hσ⟩ := hfin.exists_pow_eq_one
  have h1 : ((ψ σ : ℂˣ) : ℂ) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hσ, map_one, Units.val_one]
  have h2 : ‖((ψ σ : ℂˣ) : ℂ)‖ ^ n = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

/--
@isnad1 id=eq.0h4v.s10.6c336e6a881b from=translated src=- shape=2d99d243 vocab=ae4b68c8
-/
theorem coe_inv_apply (ψ : (M ≃ₐ[K] M) →* ℂˣ) (σ : M ≃ₐ[K] M) :
    ((ψ⁻¹ σ : ℂˣ) : ℂ) = starRingEnd ℂ ((ψ σ : ℂˣ) : ℂ) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  exact (Complex.inv_eq_conj (norm_apply ψ σ))

omit [NumberField M] [IsGalois K M] in
/--
@isnad1 id=iff.0h4v.s9.4e26bc4f990c from=translated src=- shape=788edcdd vocab=36dab8ef
-/
theorem isUnramifiedAt_inv_iff (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    IsUnramifiedAt ψ⁻¹ v ↔ IsUnramifiedAt ψ v := by
  simp [IsUnramifiedAt]

/--
@isnad1 id=eq.0h4v.s9.9692b071fbf3 from=translated src=- shape=7dc37713 vocab=eb823b9a
-/
theorem localValue_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    localValue ψ⁻¹ v = starRingEnd ℂ (localValue ψ v) := by
  unfold localValue
  rw [isUnramifiedAt_inv_iff]
  split_ifs
  · exact coe_inv_apply ψ _
  · simp

/--
@isnad1 id=eq.0h4v.s9.f11ec90640c6 from=translated src=- shape=7dc37713 vocab=1ec50908
-/
theorem idealValue_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) (I : Ideal (𝓞 K)) :
    idealValue ψ⁻¹ I = starRingEnd ℂ (idealValue ψ I) := by
  unfold idealValue
  rw [show starRingEnd ℂ (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      localValue ψ v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors) =
      (starRingAut (R := ℂ)).toMulEquiv (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      localValue ψ v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors) from rfl,
    MulEquiv.map_finprod]
  exact finprod_congr fun v => by
    rw [localValue_inv, map_pow]
    rfl

omit [IsGalois K M] in
/--
@isnad1 id=eq.0h4v.s9.09dfe959716b from=translated src=- shape=5b1fa0d9 vocab=57eaba64
-/
theorem swanConductor_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    swanConductor ψ⁻¹ v = swanConductor ψ v := by
  simp [swanConductor]

omit [IsGalois K M] in
/--
@isnad1 id=eq.0h4v.s9.58dfb2782e2d from=translated src=- shape=5b1fa0d9 vocab=4180937d
-/
theorem conductorExponent_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    conductorExponent ψ⁻¹ v = conductorExponent ψ v := by
  rw [conductorExponent, conductorExponent, swanConductor_inv, isUnramifiedAt_inv_iff]

omit [IsGalois K M] in

/--
@isnad1 id=eq.0h3v.s9.4b723f0b60f4 from=translated src=- shape=4d52a3a3 vocab=9bd78f5e
-/
theorem conductor_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) : conductor ψ⁻¹ = conductor ψ := by
  simp [conductor, conductorExponent_inv]

omit [NumberField K] [NumberField M] [IsGalois K M] in
/--
@isnad1 id=iff.0h4v.s8.610f05afb4c3 from=translated src=- shape=88861e4f vocab=6fe0eefc
-/
theorem isPlusAt_inv_iff (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : InfinitePlace K) :
    IsPlusAt ψ⁻¹ v ↔ IsPlusAt ψ v := by
  simp [IsPlusAt]

omit [NumberField M] [IsGalois K M] in
/--
@isnad1 id=eq.0h3v.s8.3512fa2f0d1f from=translated src=- shape=21011160 vocab=4820e0b2
-/
theorem nPlus_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) : nPlus ψ⁻¹ = nPlus ψ := by
  simp [nPlus, isPlusAt_inv_iff]

omit [NumberField M] [IsGalois K M] in
/--
@isnad1 id=eq.0h3v.s8.0cb6cca0ec13 from=translated src=- shape=21011160 vocab=7b3b65aa
-/
theorem nMinus_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) : nMinus ψ⁻¹ = nMinus ψ := by
  rw [nMinus, nMinus, nPlus_inv]

/--
@isnad1 id=eq.0h4v.s9.38e46cdab4c2 from=translated src=- shape=b935752a vocab=147a01e1
-/
theorem coeff_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) (n : ℕ) :
    coeff ψ⁻¹ n = starRingEnd ℂ (coeff ψ n) := by
  unfold coeff
  split_ifs
  · simp
  · rw [map_sum]
    exact Finset.sum_congr rfl fun I _ => idealValue_inv ψ I

end Basic

end ArtinL.Abelian

end
