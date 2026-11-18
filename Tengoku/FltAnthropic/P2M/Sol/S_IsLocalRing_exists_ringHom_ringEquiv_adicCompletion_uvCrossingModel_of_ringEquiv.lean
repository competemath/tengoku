import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_exists_ringHom_ringEquiv_adicCompletion_uvCrossingModel_of_ringEquiv.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_exists_ringHom_ringEquiv_adicCompletion_uvCrossingModel_of_ringEquiv

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace M3cC2

section functorial

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

/--
@isnad1 id=le.1h6v.s8.7a209452e44b from=translated src=- shape=97abe355 vocab=c552be7d
-/
lemma pow_le_comap (g : R →+* S) (hg : I.map g ≤ J) (n : ℕ) : I ^ n ≤ (J ^ n).comap g := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono hg n

/--
@isnad1 id=eq.2h7v.s11.366d7ae82cae from=translated src=- shape=17b2908f vocab=c9ab17b6
-/
lemma complMap_compat (g : R →+* S) (hg : I.map g ≤ J) :
    ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp
      ((Ideal.quotientMap (J ^ n) g (pow_le_comap I J g hg n)).comp (AdicCompletion.evalₐ I n).toRingHom) =
      (Ideal.quotientMap (J ^ m) g (pow_le_comap I J g hg m)).comp (AdicCompletion.evalₐ I m).toRingHom := by
  intro m n hle
  ext x
  obtain ⟨y, rfl⟩ := AdicCompletion.mk_surjective I R x
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq, ← map_sub]
  have : y.val n - y.val m ∈ I ^ m := by
    rw [← Ideal.Quotient.eq]; exact AdicCompletion.Ideal.mk_eq_mk I hle y
  exact pow_le_comap I J g hg m this

noncomputable def complMap (g : R →+* S) (hg : I.map g ≤ J) : AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J
    (fun n => (Ideal.quotientMap (J ^ n) g (pow_le_comap I J g hg n)).comp (AdicCompletion.evalₐ I n).toRingHom)
    (complMap_compat I J g hg)

/--
@isnad1 id=eq.1h7v.s11.e2311648beb8 from=translated src=- shape=924bb86e vocab=c4a6b63e
-/
lemma evalₐ_complMap (g : R →+* S) (hg : I.map g ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (complMap I J g hg x) =
      Ideal.quotientMap (J ^ n) g (pow_le_comap I J g hg n) (AdicCompletion.evalₐ I n x) := by
  unfold complMap
  exact AdicCompletion.evalₐ_liftRingHom J _ (complMap_compat I J g hg) n x

/--
@isnad1 id=eq.1h6v.s10.8a3fdb4f9a39 from=translated src=- shape=9b3743ae vocab=c7d6829e
-/
lemma complMap_of (g : R →+* S) (hg : I.map g ≤ J) (r : R) :
    complMap I J g hg (AdicCompletion.of I R r) = AdicCompletion.of J S (g r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_complMap, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

end functorial

section equiv

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

noncomputable def complEquiv (θ : R ≃+* S) (h₁ : I.map θ.toRingHom ≤ J) (h₂ : J.map θ.symm.toRingHom ≤ I) :
    AdicCompletion I R ≃+* AdicCompletion J S :=
  RingEquiv.ofRingHom (complMap I J θ.toRingHom h₁) (complMap J I θ.symm.toRingHom h₂)
    (RingHom.ext fun x => by
      apply AdicCompletion.ext_evalₐ
      intro n
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, evalₐ_complMap]
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
      rw [← ha, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
      simp)
    (RingHom.ext fun x => by
      apply AdicCompletion.ext_evalₐ
      intro n
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, evalₐ_complMap]
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
      rw [← ha, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
      simp)

/--
@isnad1 id=eq.2h6v.s10.e60cd9f5d948 from=translated src=- shape=2c5c600b vocab=c3b358ba
-/
lemma complEquiv_of (θ : R ≃+* S) (h₁ : I.map θ.toRingHom ≤ J) (h₂ : J.map θ.symm.toRingHom ≤ I) (r : R) :
    complEquiv I J θ h₁ h₂ (AdicCompletion.of I R r) = AdicCompletion.of J S (θ r) :=
  complMap_of I J θ.toRingHom h₁ r

end equiv

end M3cC2

open M3cC2 in
/--
@isnad1 id=other.1h8v.s15.c110bf110725 from=translated src=- shape=a6ade945 vocab=f7d78089
-/
theorem solution
    {A₀ : Type} [CommRing A₀] [IsLocalRing A₀] (ϖ₀ : A₀) (w : ℕ)
    {R : Type} [CommRing R] [IsLocalRing R] (b : A₀ →+* R)
    (e : AdicCompletion (maximalIdeal R) R ≃+*
      UVCrossingModel (AdicCompletion (maximalIdeal A₀) A₀)
        ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w))
    (he : ∀ a : A₀,
      e (algebraMap R (AdicCompletion (maximalIdeal R) R) (b a)) =
        const ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)
          (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))
    {N : Type} [CommRing N] [IsLocalRing N] (θ : R ≃+* N) :
    let Â₀ := AdicCompletion (maximalIdeal A₀) A₀
    ∃ (σ : Â₀ →+* AdicCompletion (maximalIdeal N) N)
      (ι : AdicCompletion (maximalIdeal N) N ≃+* UVCrossingModel Â₀ ((algebraMap A₀ Â₀ ϖ₀) ^ w)),
      (∀ a : A₀, σ (algebraMap A₀ Â₀ a) = algebraMap N (AdicCompletion (maximalIdeal N) N) (θ (b a))) ∧
      (∀ o : Â₀, ι (σ o) = const ((algebraMap A₀ Â₀ ϖ₀) ^ w) o) ∧
      (∀ r : R, ι (algebraMap N (AdicCompletion (maximalIdeal N) N) (θ r)) =
        e (algebraMap R (AdicCompletion (maximalIdeal R) R) r)) := by
  intro Â₀

  have hunit : ∀ r : R, IsUnit (θ r) → IsUnit r := fun r h => by
    simpa using h.map θ.symm.toRingHom
  have hunit' : ∀ s : N, IsUnit (θ.symm s) → IsUnit s := fun s h => by
    simpa using h.map θ.toRingHom
  have h₁ : (maximalIdeal R).map θ.toRingHom ≤ maximalIdeal N := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => ((mem_maximalIdeal _).mp hr) (hunit r hu)
  have h₂ : (maximalIdeal N).map θ.symm.toRingHom ≤ maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => ((mem_maximalIdeal _).mp hs) (hunit' s hu)
  let T := complEquiv (maximalIdeal R) (maximalIdeal N) θ h₁ h₂
  have hT : ∀ r : R, T (algebraMap R _ r) = algebraMap N _ (θ r) := fun r =>
    complEquiv_of (maximalIdeal R) (maximalIdeal N) θ h₁ h₂ r
  let ι : AdicCompletion (maximalIdeal N) N ≃+* UVCrossingModel Â₀ ((algebraMap A₀ Â₀ ϖ₀) ^ w) :=
    T.symm.trans e
  have hι : ∀ r : R, ι (algebraMap N _ (θ r)) = e (algebraMap R _ r) := fun r => by
    show e (T.symm (algebraMap N _ (θ r))) = _
    rw [← hT, RingEquiv.symm_apply_apply]
  let σ : Â₀ →+* AdicCompletion (maximalIdeal N) N :=
    ι.symm.toRingHom.comp (constHom ((algebraMap A₀ Â₀ ϖ₀) ^ w))
  have hσ : ∀ o, σ o = ι.symm (const ((algebraMap A₀ Â₀ ϖ₀) ^ w) o) := fun o => rfl
  refine ⟨σ, ι, fun a => ?_, fun o => ?_, hι⟩
  · rw [hσ, RingEquiv.symm_apply_eq, hι, he]
  · rw [hσ, RingEquiv.apply_symm_apply]
