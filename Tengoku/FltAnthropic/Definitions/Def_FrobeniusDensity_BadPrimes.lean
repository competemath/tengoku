import Tengoku.FltAnthropic.Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import Tengoku.Seed.RingTheory.DedekindDomain.Factorization
import Tengoku.Seed.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Tengoku.Seed.Data.ZMod.QuotientRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace FrobeniusDensity

open NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid

/--
@isnad1 id=eq.0h1v.s4.ebced7ac0c8f from=translated src=- shape=7ccdb69f vocab=137fb32d
-/
theorem card_quotient_ratPrimeIdeal (ℓ : ℕ) :
    Nat.card (ℤ ⧸ ratPrimeIdeal ℓ) = ℓ := by
  rw [ratPrimeIdeal, Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv, Nat.card_zmod]

/--
@isnad1 id=eq.0h3v.s6.44a5cf5bdbda from=translated src=- shape=843a6140 vocab=aa233527
-/
theorem card_quotient_under_int {L : Type*} [Field L] [NumberField L] {ℓ : ℕ}
    (Q : Ideal (𝓞 L)) [Q.LiesOver (ratPrimeIdeal ℓ)] :
    Nat.card (ℤ ⧸ Q.under ℤ) = ℓ := by
  rw [← Q.over_def (ratPrimeIdeal ℓ), card_quotient_ratPrimeIdeal]

section Ramified

variable {K : Type*} [Field K] [NumberField K]

/--
@isnad1 id=finite.1h2v.s7.b9003442d858 from=translated src=- shape=4bfc1d5b vocab=f4a51262
-/
lemma finite_setOf_dvd {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ I}.Finite := by
  have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
      {v | v.asIdeal ∣ I} := fun v _ w _ h => HeightOneSpectrum.ext h
  refine Set.Finite.of_finite_image ?_ hinj
  refine (normalizedFactors I).toFinset.finite_toSet.subset ?_
  rintro J ⟨v, hv, rfl⟩
  simpa [Multiset.mem_toFinset] using
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨v.prime, hv⟩

variable (L : Type*) [Field L] [NumberField L]

/--
@isnad1 id=ex.1h2v.s9.568d4c0dd8f6 from=translated src=- shape=f05e2cae vocab=2a0a6069
-/
theorem exists_smul_ne {g : L ≃ₐ[ℚ] L} (hg : g ≠ 1) :
    ∃ x : 𝓞 L, g • x ≠ x := by
  by_contra hcon'
  have hcon : ∀ x : 𝓞 L, g • x = x := fun x => not_not.mp fun h => hcon' ⟨x, h⟩
  refine hg (AlgEquiv.ext fun z => ?_)
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (K := L) z
  have hx : g (algebraMap (𝓞 L) L x) = algebraMap (𝓞 L) L x :=
    congrArg (algebraMap (𝓞 L) L) (hcon x)
  have hy' : g (algebraMap (𝓞 L) L y) = algebraMap (𝓞 L) L y :=
    congrArg (algebraMap (𝓞 L) L) (hcon y)
  rw [← hxy, map_div₀, hx, hy', AlgEquiv.one_apply]

/--
@isnad1 id=finite.0h1v.s9.aef868212f54 from=translated src=- shape=bebdc2a3 vocab=8e2adbfe
-/
theorem finite_setOf_inertia_ne_bot_heightOneSpectrum :
    {v : HeightOneSpectrum (𝓞 L) | v.asIdeal.inertia (L ≃ₐ[ℚ] L) ≠ ⊥}.Finite := by
  classical
  choose x hx using fun g : {g : L ≃ₐ[ℚ] L // g ≠ 1} => exists_smul_ne L g.2
  refine Set.Finite.subset (Set.Finite.biUnion
    (Set.finite_univ (α := {g : L ≃ₐ[ℚ] L // g ≠ 1}))
    (fun g _ => finite_setOf_dvd (I := Ideal.span {g.1 • x g - x g}) ?_)) ?_
  · rw [Ne, Ideal.span_singleton_eq_bot, sub_eq_zero]
    exact hx g
  · intro v hv
    simp only [Set.mem_ofPred_eq] at hv
    obtain ⟨g, hgmem, hgne⟩ := (v.asIdeal.inertia (L ≃ₐ[ℚ] L)).bot_or_exists_ne_one.resolve_left hv
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨⟨g, hgne⟩, Set.mem_univ _, ?_⟩
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hgmem (x ⟨g, hgne⟩)

noncomputable def badPrimes : Finset ℕ :=
  insert 0 (insert 1 (((finite_setOf_inertia_ne_bot_heightOneSpectrum L).image
    (fun v => Nat.card (ℤ ⧸ v.asIdeal.under ℤ))).toFinset))

/--
@isnad1 id=eq.2h3v.s9.40d13ebfda82 from=translated src=- shape=dee37ebf vocab=d509a5ff
-/
theorem inertia_eq_bot_of_notMem_badPrimes {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓbad : ℓ ∉ badPrimes L) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] :
    Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  by_contra hcon
  apply hℓbad
  have hQbot : Q ≠ ⊥ := ne_bot_of_liesOver_ratPrimeIdeal hℓ
  refine Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr ?_)))
  rw [Set.Finite.mem_toFinset]
  exact ⟨⟨Q, inferInstance, hQbot⟩, hcon, card_quotient_under_int (ℓ := ℓ) Q⟩

end Ramified

section DegOneCount

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
/--
@isnad1 id=eq.1h2v.s4.8f0e32ff1563 from=translated src=- shape=39644e7c vocab=9675fc5e
-/
theorem degOneCount_of_not_prime {ℓ : ℕ} (hℓ : ¬ ℓ.Prime) : degOneCount K ℓ = 0 := by
  rw [degOneCount, ite_eq_right hℓ]

omit [NumberField K] in
/--
@isnad1 id=eq.1h2v.s7.24f9fe30dc25 from=translated src=- shape=5201a7d5 vocab=a4c8a6ff
-/
theorem degOneCount_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) :
    degOneCount K ℓ
      = {𝔮 ∈ (ratPrimeIdeal ℓ).primesOver (𝓞 K) | Nat.card ((𝓞 K) ⧸ 𝔮) = ℓ}.ncard := by
  rw [degOneCount, ite_eq_left hℓ]

end DegOneCount

section Frob

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

/--
@isnad1 id=isconj.1h4v.s9.2f7bb259cb72 from=translated src=- shape=78cc82c0 vocab=b7c6f653
-/
theorem isConj_arithFrobAt_of_liesOver {ℓ : ℕ} (hℓ : ℓ.Prime) (Q₁ Q₂ : Ideal (𝓞 L))
    [Q₁.IsPrime] [Q₂.IsPrime] [Q₁.LiesOver (ratPrimeIdeal ℓ)] [Q₂.LiesOver (ratPrimeIdeal ℓ)] :
    letI : Finite (𝓞 L ⧸ Q₁) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    letI : Finite (𝓞 L ⧸ Q₂) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    IsConj (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₁) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₂) := by
  letI : Finite (𝓞 L ⧸ Q₁) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  letI : Finite (𝓞 L ⧸ Q₂) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  exact isConj_arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₁ Q₂
    ((Q₁.over_def (ratPrimeIdeal ℓ)).symm.trans (Q₂.over_def (ratPrimeIdeal ℓ)))

variable (L)

/--
@isnad1 id=realizes.2h4v.s9.24737d607b2c from=translated src=- shape=bc8dbcbd vocab=bd7625d8
-/
theorem realizesCyclicAt_of_exists (σ : L ≃ₐ[ℚ] L) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (Q₀ : Ideal (𝓞 L)) [Q₀.IsPrime] [Q₀.LiesOver (ratPrimeIdeal ℓ)]
    (h : ∀ _ : Finite (𝓞 L ⧸ Q₀),
      ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀)) :
    RealizesCyclicAt L σ ℓ := by
  refine ⟨hℓ, fun Q hQp hQl hQf => ?_⟩
  haveI : Finite (𝓞 L ⧸ Q₀) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  obtain ⟨k, hk, hconj⟩ := h ‹_›
  exact ⟨k, hk, hconj.trans (isConj_arithFrobAt_of_liesOver hℓ Q₀ Q)⟩

end Frob

end FrobeniusDensity
