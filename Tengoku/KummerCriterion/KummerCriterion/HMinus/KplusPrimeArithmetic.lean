module

public import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.Galois
public import Tengoku.KummerCriterion.KummerCriterion.HMinus.KplusLocalCharacters
public import Tengoku.KummerCriterion.KummerCriterion.TotallyRealSubfield.ClassGroup
public import Tengoku.KummerCriterion.KummerCriterion.TotallyRealSubfield.ZetaPrime
import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.Ideal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `K⁺` prime arithmetic

Prime-ideal, contraction, and inertia-degree formulas for the maximal real subfield.
-/

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open scoped BigOperators Pointwise

namespace KummerCriterion

variable (p : ℕ) [hp : Fact p.Prime]

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The finite set of prime ideals of `𝓞 K⁺` lying above the rational prime
ideal `(ℓ)`.-/
noncomputable def primesOverFinsetPlus (ℓ : ℕ) : Finset (Ideal (𝓞 (K⁺))) :=
  IsDedekindDomain.primesOverFinset (rationalPrimeIdeal ℓ) (𝓞 (K⁺))

lemma primesOverFinsetPlus_card_eq_ncard (ℓ : ℕ) [Fact ℓ.Prime] :
    (primesOverFinsetPlus (K := K) ℓ).card =
      (Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺))).ncard := by
  classical
  have : (rationalPrimeIdeal ℓ).IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
  have hne : (rationalPrimeIdeal ℓ) ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  unfold primesOverFinsetPlus
  rw [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hne]

lemma mem_primesOverFinsetPlus_iff {ℓ : ℕ} [Fact ℓ.Prime] {P : Ideal (𝓞 (K⁺))} :
    P ∈ primesOverFinsetPlus (K := K) ℓ ↔
      P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺)) := by
  have : (rationalPrimeIdeal ℓ).IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
  have hne : (rationalPrimeIdeal ℓ) ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  exact IsDedekindDomain.mem_primesOverFinset_iff hne (𝓞 (K⁺))

lemma under_mem_primesOverFinsetPlus {ℓ : ℕ} [Fact ℓ.Prime] {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOverFinset K ℓ) :
    P.under (𝓞 (K⁺)) ∈ primesOverFinsetPlus (K := K) ℓ := by
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) :=
    (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hP
  have : P.IsPrime := hP_over.1
  rw [mem_primesOverFinsetPlus_iff]
  refine ⟨Ideal.IsPrime.under (𝓞 (K⁺)) P, ?_⟩
  rw [Ideal.liesOver_iff, Ideal.under_under]
  exact (Ideal.liesOver_iff _ _).1 hP_over.2

variable [IsCMField K]

lemma algEquiv_eq_one_or_complexConj (σ : K ≃ₐ[K⁺] K) :
    σ = 1 ∨ σ = complexConj K := by
  by_cases hσ : σ = 1
  · exact Or.inl hσ
  · right
    have hcard : Nat.card (K ≃ₐ[K⁺] K) = 2 :=
      (IsGalois.card_aut_eq_finrank K⁺ K).trans (finrank_K_over_Kplus (K := K))
    rw [Nat.card_eq_two_iff' (1 : K ≃ₐ[K⁺] K)] at hcard
    exact ExistsUnique.unique hcard hσ (complexConj_ne_one K)

lemma toRingHom_complexConj_eq_ringOfIntegersComplexConj :
    MulSemiringAction.toRingHom (K ≃ₐ[K⁺] K) (𝓞 K) (complexConj K) =
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  ext x
  change (((complexConj K) • x : 𝓞 K) : K) = ((ringOfIntegersComplexConj K x : 𝓞 K) : K)
  rfl

lemma pointwise_smul_complexConj_eq_map (P : Ideal (𝓞 K)) :
    complexConj K • P = P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  rw [Ideal.pointwise_smul_def, toRingHom_complexConj_eq_ringOfIntegersComplexConj (K := K)]

lemma map_ringOfIntegersComplexConj_mem_primesOverFinset {ℓ : ℕ} [Fact ℓ.Prime]
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom ∈ primesOverFinset K ℓ := by
  let PPlus : Ideal (𝓞 (K⁺)) := P.under (𝓞 (K⁺))
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) :=
    (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hP
  have hPPlus_mem : PPlus ∈ primesOverFinsetPlus (K := K) ℓ := by
    simpa [PPlus] using under_mem_primesOverFinsetPlus (K := K) hP
  have hPPlus_over : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺)) :=
    (mem_primesOverFinsetPlus_iff (K := K) (ℓ := ℓ)).1 hPPlus_mem
  have : P.IsPrime := hP_over.1
  have hmap_liesOver_PPlus :
      (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).LiesOver PPlus :=
    Ideal.LiesOver.of_eq_map_equiv PPlus (ringOfIntegersComplexConj K) rfl
  have : PPlus.LiesOver (rationalPrimeIdeal ℓ) := hPPlus_over.2
  have hmap_liesOver :
      (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).LiesOver
        (rationalPrimeIdeal ℓ) :=
    Ideal.LiesOver.trans (A := ℤ) (B := 𝓞 (K⁺)) (C := 𝓞 K)
      (𝔓 := P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
      (P := PPlus) (p := rationalPrimeIdeal ℓ)
  have : (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).IsPrime :=
    Ideal.map_isPrime_of_equiv (ringOfIntegersComplexConj K).toRingEquiv
  rw [mem_primesOverFinset_iff (K := K) (ℓ := ℓ)]
  exact ⟨inferInstance, hmap_liesOver⟩

lemma under_map_ringOfIntegersComplexConj_eq_under (P : Ideal (𝓞 K)) :
    (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).under (𝓞 (K⁺)) =
      P.under (𝓞 (K⁺)) := by
  let PPlus : Ideal (𝓞 (K⁺)) := P.under (𝓞 (K⁺))
  have hmap_liesOver_PPlus :
      (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).LiesOver PPlus :=
    Ideal.LiesOver.of_eq_map_equiv PPlus (ringOfIntegersComplexConj K) rfl
  simpa [PPlus] using
    (Ideal.over_def
      (P := P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
      (A := 𝓞 (K⁺)) (p := PPlus)).symm

lemma eq_or_eq_map_ringOfIntegersComplexConj_of_under_eq {ℓ : ℕ} [Fact ℓ.Prime]
    {P Q : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) (hQ : Q ∈ primesOverFinset K ℓ)
    (hunder : P.under (𝓞 (K⁺)) = Q.under (𝓞 (K⁺))) :
    Q = P ∨ Q = P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  let PPlus : Ideal (𝓞 (K⁺)) := P.under (𝓞 (K⁺))
  have hP_over : P ∈ Ideal.primesOver PPlus (𝓞 K) := by
    refine ⟨((mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hP).1,
      by simp [Ideal.liesOver_iff, PPlus]⟩
  have hQ_over : Q ∈ Ideal.primesOver PPlus (𝓞 K) := by
    refine ⟨((mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hQ).1,
      by simpa [Ideal.liesOver_iff, PPlus] using hunder⟩
  have : P.IsPrime := hP_over.1
  have : Q.IsPrime := hQ_over.1
  have : Q.LiesOver PPlus := hQ_over.2
  let _ : MulSemiringAction Gal(K/K⁺) (𝓞 K) := inferInstance
  have _ : IsGaloisGroup Gal(K/K⁺) (𝓞 (K⁺)) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (Gal(K/K⁺)) (𝓞 (K⁺)) (𝓞 K) (K⁺) K
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    (A := 𝓞 (K⁺)) (B := 𝓞 K) (p := PPlus) (P := P) (Q := Q) (G := Gal(K/K⁺))
  rcases algEquiv_eq_one_or_complexConj (K := K) σ with rfl | rfl
  · left
    simpa using hσ.symm
  · right
    rw [pointwise_smul_complexConj_eq_map (K := K) P] at hσ
    exact hσ.symm

lemma primesOverFinsetContractionToPlus_fiber_eq_singleton_or_pair {ℓ : ℕ} [Fact ℓ.Prime]
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    let Pconj := P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom
    let fiber := (primesOverFinset K ℓ).filter
      (fun Q => Q.under (𝓞 (K⁺)) = P.under (𝓞 (K⁺)))
    (Pconj = P ∧ fiber = ({P} : Finset (Ideal (𝓞 K)))) ∨
      (Pconj ≠ P ∧ fiber = {P, Pconj}) := by
  classical
  let Pconj : Ideal (𝓞 K) := P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom
  let fiber : Finset (Ideal (𝓞 K)) := (primesOverFinset K ℓ).filter
    (fun Q => Q.under (𝓞 (K⁺)) = P.under (𝓞 (K⁺)))
  have hPconj : Pconj ∈ primesOverFinset K ℓ := by
    simpa [Pconj] using map_ringOfIntegersComplexConj_mem_primesOverFinset (K := K) hP
  have hunder_conj : Pconj.under (𝓞 (K⁺)) = P.under (𝓞 (K⁺)) := by
    simpa [Pconj] using under_map_ringOfIntegersComplexConj_eq_under (K := K) P
  have hP_fiber : P ∈ fiber := by
    simp [fiber, hP]
  have hPconj_fiber : Pconj ∈ fiber := by
    simp [fiber, hPconj, hunder_conj]
  have hfiber_subset {Q : Ideal (𝓞 K)} (hQ : Q ∈ fiber) : Q = P ∨ Q = Pconj := by
    have hQ_mem : Q ∈ primesOverFinset K ℓ := (Finset.mem_filter.1 hQ).1
    have hQ_under : Q.under (𝓞 (K⁺)) = P.under (𝓞 (K⁺)) := (Finset.mem_filter.1 hQ).2
    rcases eq_or_eq_map_ringOfIntegersComplexConj_of_under_eq (K := K) hP hQ_mem hQ_under.symm with
      hQP | hQconj
    · exact Or.inl hQP
    · exact Or.inr (by simpa [Pconj] using hQconj)
  by_cases hfix : Pconj = P
  · left
    refine ⟨hfix, Finset.ext fun Q => ?_⟩
    constructor
    · intro hQ
      rcases hfiber_subset hQ with hQP | hQconj
      · rw [hQP]
        simp
      · rw [hQconj, hfix]
        simp
    · intro hQ
      have hQP : Q = P := by simpa using hQ
      subst hQP
      exact hP_fiber
  · right
    refine ⟨hfix, Finset.ext fun Q => ?_⟩
    constructor
    · intro hQ
      rcases hfiber_subset hQ with hQP | hQconj
      · rw [hQP]
        simp
      · rw [hQconj]
        simp [Pconj]
    · intro hQ
      have hQ' : Q = P ∨ Q = Pconj := by
        simpa [hfix] using! hQ
      rcases hQ' with hQP | hQconj
      · rw [hQP]
        exact hP_fiber
      · rw [hQconj]
        exact hPconj_fiber

noncomputable def complexConjRat (hp_odd : p ≠ 2) : Gal(K/ℚ) := by
  letI : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  exact
    { (complexConj K).toRingEquiv with
      commutes' := fun q => by
        exact map_ratCast ((complexConj K).toRingEquiv.toRingHom) q }

@[simp] private lemma complexConjRat_apply (hp_odd : p ≠ 2) (x : K) :
    complexConjRat (p := p) (K := K) hp_odd x = complexConj K x := by
  rfl

lemma toRingHom_complexConjRat_eq_ringOfIntegersComplexConj (hp_odd : p ≠ 2) :
    MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K)
        (complexConjRat (p := p) (K := K) hp_odd) =
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  ext x
  change complexConjRat (p := p) (K := K) hp_odd x =
      ((ringOfIntegersComplexConj K x : 𝓞 K) : K)
  simp [complexConjRat_apply, coe_ringOfIntegersComplexConj]

lemma pointwise_smul_complexConjRat_eq_map (hp_odd : p ≠ 2) (P : Ideal (𝓞 K)) :
    (complexConjRat (p := p) (K := K) hp_odd • P) =
      P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  rw [Ideal.pointwise_smul_def, toRingHom_complexConjRat_eq_ringOfIntegersComplexConj
    (p := p) (K := K) hp_odd]

omit [IsCMField K] in
lemma galEquivZMod_complexConj_eq_neg_one (hp_odd : p ≠ 2) :
    IsCyclotomicExtension.Rat.galEquivZMod p K
        (complexConjRat (p := p) (K := K) hp_odd) = -1 := by
  have : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  let c : Gal(K/ℚ) := complexConjRat (p := p) (K := K) hp_odd
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  have hc :
      c (IsCyclotomicExtension.zeta p ℚ K) =
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := by
    have hc' := congrArg (fun x : 𝓞 K => (x : K)) (complexConj_apply_zeta (p := p) (K := K))
    rw [coe_ringOfIntegersComplexConj] at hc'
    change (complexConj K) hζ.toInteger.1 =
      hζ.toInteger.1 ^ (p - 1) at hc'
    simpa [c, complexConjRat_apply, hζ.coe_toInteger] using hc'
  have hpow :
      (IsCyclotomicExtension.zeta p ℚ K) ^
          (IsCyclotomicExtension.Rat.galEquivZMod p K c).val.val =
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := by
    calc
      (IsCyclotomicExtension.zeta p ℚ K) ^ (IsCyclotomicExtension.Rat.galEquivZMod p K c).val.val
          = c (IsCyclotomicExtension.zeta p ℚ K) := by
              symm
              exact IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
                (n := p) (K := K) c hζ.pow_eq_one
      _ = (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := hc
  apply Units.ext
  have hpow' := hpow
  rw [(hζ.isOfFinOrder (NeZero.ne p)).pow_inj_mod, ← hζ.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_val, Nat.cast_sub hp.out.one_le,
    ZMod.natCast_self, zero_sub, Nat.cast_one] at hpow'
  simpa [c] using hpow'

lemma unitOfPrimeNe_pow_localResidueDegreePlus_eq_neg_one_of_even
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (hd_even : Even (localResidueDegree (p := p) ℓ hℓp)) :
    unitOfPrimeNe (p := p) ℓ hℓp ^ localResidueDegreePlus (p := p) ℓ hℓp =
      (-1 : (ZMod p)ˣ) := by
  let u : (ZMod p)ˣ := unitOfPrimeNe (p := p) ℓ hℓp
  let d : ℕ := localResidueDegree (p := p) ℓ hℓp
  rcases unitOfPrimeNe_pow_localResidueDegreePlus_eq_one_or_neg_one (p := p) hℓp with hpow | hpow
  · have hpow_units : u ^ localResidueDegreePlus (p := p) ℓ hℓp = 1 := by
      apply Units.ext
      simpa [u, Units.val_pow_eq_pow_val] using hpow
    have hdvd : d ∣ localResidueDegreePlus (p := p) ℓ hℓp := by
      simpa [d, localResidueDegree, u] using (orderOf_dvd_iff_pow_eq_one (x := u)).2 hpow_units
    have hd_pos : 0 < d := by
      dsimp [d, localResidueDegree, u]
      exact orderOf_pos u
    have hhalf : localResidueDegreePlus (p := p) ℓ hℓp = d / 2 := by
      simpa [d] using localResidueDegreePlus_eq_half (p := p) hℓp hd_even
    have hhalf_pos : 0 < d / 2 := by
      rcases hd_even with ⟨k, hk⟩
      rw [show d = 2 * k by omega]
      omega
    have hle : d ≤ d / 2 := by
      rw [hhalf] at hdvd
      exact Nat.le_of_dvd hhalf_pos hdvd
    omega
  · apply Units.ext
    simpa [u, Units.val_pow_eq_pow_val] using hpow

lemma neg_one_mem_zpowers_unitOfPrimeNe_iff_even_localResidueDegree
    (hp_odd : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (-1 : (ZMod p)ˣ) ∈ Subgroup.zpowers (unitOfPrimeNe (p := p) ℓ hℓp) ↔
      Even (localResidueDegree (p := p) ℓ hℓp) := by
  let u : (ZMod p)ˣ := unitOfPrimeNe (p := p) ℓ hℓp
  constructor
  · intro hneg
    have htwo : 2 ∣ orderOf u := by
      have horder_neg : orderOf (-1 : (ZMod p)ˣ) = 2 := by
        rw [← orderOf_units, Units.coe_neg_one, orderOf_neg_one, ringChar.eq (ZMod p) p,
          ite_eq_right hp_odd]
      exact horder_neg ▸ orderOf_dvd_of_mem_zpowers hneg
    simpa [u, localResidueDegree, even_iff_two_dvd] using htwo
  · intro hd_even
    refine Subgroup.mem_zpowers_iff.mpr ⟨localResidueDegreePlus (p := p) ℓ hℓp, ?_⟩
    rw [zpow_natCast]
    exact unitOfPrimeNe_pow_localResidueDegreePlus_eq_neg_one_of_even (p := p) hℓp hd_even

omit [IsCMField K] in
lemma complexConjRat_mem_stabilizer_iff_even_localResidueDegree
    (hp_odd : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    (complexConjRat (p := p) (K := K) hp_odd ∈ MulAction.stabilizer Gal(K/ℚ) P) ↔
      Even (localResidueDegree (p := p) ℓ hℓp) := by
  let c : Gal(K/ℚ) := complexConjRat (p := p) (K := K) hp_odd
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) :=
    (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hP
  have : P.LiesOver (Ideal.span {(ℓ : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hP_over.2
  have : (rationalPrimeIdeal ℓ).IsMaximal := by
    simpa [rationalPrimeIdeal] using Int.ideal_span_isMaximal_of_prime ℓ
  have : P.IsMaximal := Ideal.isMaximal_of_mem_primesOver hP_over
  constructor
  · intro hc
    have hmem_map : IsCyclotomicExtension.Rat.galEquivZMod p K c ∈
        (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
          (MulAction.stabilizer Gal(K/ℚ) P) := ⟨c, hc, rfl⟩
    rw [IsCyclotomicExtension.Rat.galEquivZMod_stabilizer (n := p) (K := K) (p := ℓ) (P := P)
      ((coprime_of_prime_ne (p := p) hℓp).symm), galEquivZMod_complexConj_eq_neg_one
      (p := p) (K := K) hp_odd] at hmem_map
    simpa [unitOfPrimeNe] using
      (neg_one_mem_zpowers_unitOfPrimeNe_iff_even_localResidueDegree
        (p := p) hp_odd hℓp).1 hmem_map
  · intro h_even
    have hneg_mem : (-1 : (ZMod p)ˣ) ∈ Subgroup.zpowers (unitOfPrimeNe (p := p) ℓ hℓp) :=
      (neg_one_mem_zpowers_unitOfPrimeNe_iff_even_localResidueDegree (p := p) hp_odd hℓp).2 h_even
    have hmem_map : IsCyclotomicExtension.Rat.galEquivZMod p K c ∈
        (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
          (MulAction.stabilizer Gal(K/ℚ) P) := by
      rw [IsCyclotomicExtension.Rat.galEquivZMod_stabilizer (n := p) (K := K) (p := ℓ) (P := P)
        ((coprime_of_prime_ne (p := p) hℓp).symm), galEquivZMod_complexConj_eq_neg_one
        (p := p) (K := K) hp_odd]
      simpa [unitOfPrimeNe] using hneg_mem
    rcases hmem_map with ⟨σ, hσ, hσeq⟩
    have hc_eq : σ = c := (IsCyclotomicExtension.Rat.galEquivZMod p K).injective hσeq
    subst hc_eq
    exact hσ

lemma map_ringOfIntegersComplexConj_eq_self_iff_even_localResidueDegree
    (hp_odd : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom = P ↔
      Even (localResidueDegree (p := p) ℓ hℓp) := by
  let c : Gal(K/ℚ) := complexConjRat (p := p) (K := K) hp_odd
  constructor
  · intro hmap
    have hsmul : c • P = P := by
      rw [pointwise_smul_complexConjRat_eq_map (p := p) (K := K) hp_odd]
      exact hmap
    have hc : c ∈ MulAction.stabilizer Gal(K/ℚ) P := by simpa [c] using hsmul
    exact (complexConjRat_mem_stabilizer_iff_even_localResidueDegree
      (p := p) (K := K) hp_odd hℓp hP).1 hc
  · intro h_even
    have hc : c ∈ MulAction.stabilizer Gal(K/ℚ) P :=
      (complexConjRat_mem_stabilizer_iff_even_localResidueDegree
        (p := p) (K := K) hp_odd hℓp hP).2 h_even
    have hsmul : c • P = P := by simpa [c] using hc
    rw [pointwise_smul_complexConjRat_eq_map (p := p) (K := K) hp_odd] at hsmul
    exact hsmul

lemma map_ringOfIntegersComplexConj_eq_self_iff_localResidueDegreePlus_eq_half
    (hp_odd : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom = P ↔
      localResidueDegreePlus (p := p) ℓ hℓp = localResidueDegree (p := p) ℓ hℓp / 2 := by
  rw [map_ringOfIntegersComplexConj_eq_self_iff_even_localResidueDegree
    (p := p) (K := K) hp_odd hℓp hP]
  constructor
  · exact localResidueDegreePlus_eq_half (p := p) hℓp
  · intro hhalf
    by_contra hodd
    have hself := localResidueDegreePlus_eq_self (p := p) hℓp hodd
    have hpos : 0 < localResidueDegree (p := p) ℓ hℓp := by
      unfold localResidueDegree unitOfPrimeNe
      exact orderOf_pos _
    rw [hself] at hhalf
    omega

omit [IsCMField K] in
lemma primesOverFinsetContractionToPlus_fiber_card_eq_ncard_primesOver {ℓ : ℕ} [Fact ℓ.Prime]
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ)
    {PPlus : Ideal (𝓞 (K⁺))} (hPPlus : P.under (𝓞 (K⁺)) = PPlus) :
    let fiber := (primesOverFinset K ℓ).filter
      (fun Q => Q.under (𝓞 (K⁺)) = PPlus)
    fiber.card = (Ideal.primesOver PPlus (𝓞 K)).ncard := by
  classical
  let fiber : Finset (Ideal (𝓞 K)) := (primesOverFinset K ℓ).filter
    (fun Q => Q.under (𝓞 (K⁺)) = PPlus)
  have hPPlus_mem : PPlus ∈ primesOverFinsetPlus (K := K) ℓ := by
    simpa [hPPlus] using under_mem_primesOverFinsetPlus (K := K) hP
  have hPPlus_over : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺)) :=
    (mem_primesOverFinsetPlus_iff (K := K) (ℓ := ℓ)).1 hPPlus_mem
  have : PPlus.LiesOver (rationalPrimeIdeal ℓ) := hPPlus_over.2
  have hfiber : (↑fiber : Set (Ideal (𝓞 K))) = Ideal.primesOver PPlus (𝓞 K) := by
    ext Q
    constructor
    · intro hQ
      rw [Finset.mem_coe, Finset.mem_filter] at hQ
      rcases hQ with ⟨hQ_fin, hQ_under⟩
      have hQ_over : Q ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) :=
        (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hQ_fin
      have : Q.IsPrime := hQ_over.1
      exact ⟨inferInstance, (Ideal.liesOver_iff _ _).2 hQ_under.symm⟩
    · intro hQ
      have : Q.IsPrime := hQ.1
      have : Q.LiesOver PPlus := hQ.2
      have hQ_over : Q.LiesOver (rationalPrimeIdeal ℓ) :=
        Ideal.LiesOver.trans (A := ℤ) (B := 𝓞 (K⁺)) (C := 𝓞 K)
          (𝔓 := Q) (P := PPlus) (p := rationalPrimeIdeal ℓ)
      have hQ_fin : Q ∈ primesOverFinset K ℓ := by
        rw [mem_primesOverFinset_iff (K := K) (ℓ := ℓ)]
        exact ⟨inferInstance, hQ_over⟩
      have hQ_under : Q.under (𝓞 (K⁺)) = PPlus :=
        ((Ideal.liesOver_iff _ _).1 (show Q.LiesOver PPlus from inferInstance)).symm
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨hQ_fin, hQ_under⟩
  simpa [fiber] using (show fiber.card = (Ideal.primesOver PPlus (𝓞 K)).ncard from by
    rw [← Set.ncard_coe_finset, hfiber])

omit [IsCMField K] in
lemma primesOver_inertiaDeg_eq_localResidueDegreePlus
    (hp_odd : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (PPlus : Ideal (𝓞 (K⁺)))
    (hPPlus : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺))) :
    PPlus.inertiaDeg ℤ = localResidueDegreePlus (p := p) ℓ hℓp := by
  classical
  have : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  have : PPlus.IsPrime := hPPlus.1
  have : PPlus.LiesOver (rationalPrimeIdeal ℓ) := hPPlus.2
  obtain ⟨⟨P, hP_prime, hP_over_PPlus⟩⟩ := PPlus.nonempty_primesOver (S := 𝓞 K)
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) := by
    refine ⟨hP_prime, ?_⟩
    exact Ideal.LiesOver.trans (A := ℤ) (B := 𝓞 (K⁺)) (C := 𝓞 K)
      (𝔓 := P) (P := PPlus) (p := rationalPrimeIdeal ℓ)
  have hP_fin : P ∈ primesOverFinset K ℓ :=
    (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).2 hP_over
  have hℓ_ne : rationalPrimeIdeal ℓ ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hPPlus_eq : P.under (𝓞 (K⁺)) = PPlus :=
    ((Ideal.liesOver_iff _ _).1 (show P.LiesOver PPlus from inferInstance)).symm
  let fiber : Finset (Ideal (𝓞 K)) := (primesOverFinset K ℓ).filter
    (fun Q => Q.under (𝓞 (K⁺)) = PPlus)
  have hfiber_ncard : fiber.card = (Ideal.primesOver PPlus (𝓞 K)).ncard := by
    simpa [fiber] using primesOverFinsetContractionToPlus_fiber_card_eq_ncard_primesOver
      (K := K) hP_fin hPPlus_eq
  have hram_tower :
      P.ramificationIdx ℤ =
        PPlus.ramificationIdx ℤ * P.ramificationIdx (𝓞 (K⁺)) := by
    simpa using Ideal.ramificationIdx_tower
      (R := ℤ) (S := 𝓞 (K⁺)) (T := 𝓞 K) (q := PPlus) (r := P)
  have hram_rel : P.ramificationIdx (𝓞 (K⁺)) = 1 := by
    apply Nat.eq_one_of_dvd_one
    refine ⟨PPlus.ramificationIdx ℤ, ?_⟩
    rw [mul_comm, ← hram_tower,
      primesOver_ramificationIdx_eq_one (p := p) (K := K) hℓp P hP_over]
  have hPPlus_ne_bot : PPlus ≠ ⊥ := by
    intro hbot
    have hlie : PPlus.LiesOver (rationalPrimeIdeal ℓ) := inferInstance
    have hover := (Ideal.liesOver_iff _ _).1 hlie
    have hcomap_bot :
        Ideal.comap (algebraMap ℤ (𝓞 (K⁺))) (⊥ : Ideal (𝓞 (K⁺))) = ⊥ := by
      ext x
      simp
    have hneq : rationalPrimeIdeal ℓ ≠ ⊥ := by
      rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    exact hneq (by simpa [Ideal.under_def, hbot, hcomap_bot] using hover)
  have _ : IsGaloisGroup Gal(K/K⁺) (𝓞 (K⁺)) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (Gal(K/K⁺)) (𝓞 (K⁺)) (𝓞 K) (K⁺) K
  have hquad : (Ideal.primesOver PPlus (𝓞 K)).ncard * P.inertiaDeg (𝓞 (K⁺)) = 2 := by
    have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := PPlus)
      (B := 𝓞 K) (G := Gal(K/K⁺))
    have hcard_gal : Nat.card Gal(K/K⁺) = 2 :=
      (IsGalois.card_aut_eq_finrank K⁺ K).trans (finrank_K_over_Kplus (K := K))
    rw [hcard_gal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (p := PPlus) (P := P) (G := Gal(K/K⁺)),
      Ideal.inertiaDegIn_eq_inertiaDeg (p := PPlus) (P := P) (G := Gal(K/K⁺)),
      hram_rel] at hfund
    simpa using hfund
  have hinertia_tower :
      P.inertiaDeg ℤ =
        PPlus.inertiaDeg ℤ * P.inertiaDeg (𝓞 (K⁺)) := by
    simpa using Ideal.inertiaDeg_tower
      (R := ℤ) (S := 𝓞 (K⁺)) (T := 𝓞 K) (q := PPlus) (r := P)
  have hP_inertia :
      P.inertiaDeg ℤ = localResidueDegree (p := p) ℓ hℓp :=
    primesOver_inertiaDeg_eq_localResidueDegree (p := p) (K := K) hℓp P hP_over
  by_cases hfix : P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom = P
  · have hfiber_card : fiber.card = 1 := by
      rcases primesOverFinsetContractionToPlus_fiber_eq_singleton_or_pair (K := K) hP_fin with
        hsingle | hpair
      · have hsingle_fiber : fiber = ({P} : Finset (Ideal (𝓞 K))) := by
          simpa [fiber, hPPlus_eq] using hsingle.2
        rw [hsingle_fiber]
        simp
      · exact (hpair.1 hfix).elim
    have hcard_primes : (Ideal.primesOver PPlus (𝓞 K)).ncard = 1 := by
      rw [← hfiber_ncard]
      exact hfiber_card
    have hrel_inertia : P.inertiaDeg (𝓞 (K⁺)) = 2 := by
      rw [hcard_primes] at hquad
      simpa using hquad
    have hhalf : localResidueDegreePlus (p := p) ℓ hℓp =
        localResidueDegree (p := p) ℓ hℓp / 2 :=
      (map_ringOfIntegersComplexConj_eq_self_iff_localResidueDegreePlus_eq_half
        (p := p) (K := K) hp_odd hℓp hP_fin).1 hfix
    rw [hhalf]
    rw [hP_inertia, hrel_inertia] at hinertia_tower
    omega
  · have hfiber_card : fiber.card = 2 := by
      rcases primesOverFinsetContractionToPlus_fiber_eq_singleton_or_pair (K := K) hP_fin with
        hsingle | hpair
      · exact (hfix hsingle.1).elim
      · have hpair_fiber :
            fiber =
              ({P, P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom} :
                Finset (Ideal (𝓞 K))) := by
          simpa [fiber, hPPlus_eq] using hpair.2
        rw [hpair_fiber]
        rw [Finset.card_eq_two]
        exact ⟨P, P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
          by simpa [eq_comm] using hpair.1, rfl⟩
    have hcard_primes : (Ideal.primesOver PPlus (𝓞 K)).ncard = 2 := by
      rw [← hfiber_ncard]
      exact hfiber_card
    have hrel_inertia : P.inertiaDeg (𝓞 (K⁺)) = 1 := by
      rw [hcard_primes] at hquad
      omega
    have hnot_even : ¬ Even (localResidueDegree (p := p) ℓ hℓp) := fun h_even =>
      hfix
        ((map_ringOfIntegersComplexConj_eq_self_iff_even_localResidueDegree
          (p := p) (K := K) hp_odd hℓp hP_fin).2 h_even)
    have hself : localResidueDegreePlus (p := p) ℓ hℓp =
        localResidueDegree (p := p) ℓ hℓp :=
      localResidueDegreePlus_eq_self (p := p) hℓp hnot_even
    rw [hself]
    rw [hP_inertia, hrel_inertia] at hinertia_tower
    omega

omit [IsCMField K] in
lemma primesOverPlus_ramificationIdx_eq_one {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (PPlus : Ideal (𝓞 (K⁺)))
    (hPPlus : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺))) :
    PPlus.ramificationIdx ℤ = 1 := by
  have : PPlus.IsPrime := hPPlus.1
  have : PPlus.LiesOver (rationalPrimeIdeal ℓ) := hPPlus.2
  obtain ⟨⟨P, hP_prime, hP_over_PPlus⟩⟩ := PPlus.nonempty_primesOver (S := 𝓞 K)
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) := by
    refine ⟨hP_prime, ?_⟩
    exact Ideal.LiesOver.trans (A := ℤ) (B := 𝓞 (K⁺)) (C := 𝓞 K)
      (𝔓 := P) (P := PPlus) (p := rationalPrimeIdeal ℓ)
  have hram_tower :
      P.ramificationIdx ℤ =
        PPlus.ramificationIdx ℤ * P.ramificationIdx (𝓞 (K⁺)) := by
    simpa using Ideal.ramificationIdx_tower
      (R := ℤ) (S := 𝓞 (K⁺)) (T := 𝓞 K) (q := PPlus) (r := P)
  have hram_abs : P.ramificationIdx ℤ = 1 :=
    KummerCriterion.primesOver_ramificationIdx_eq_one (p := p) (K := K) hℓp P hP_over
  apply Nat.eq_one_of_dvd_one
  refine ⟨P.ramificationIdx (𝓞 (K⁺)), ?_⟩
  rw [← hram_tower, hram_abs]

omit [IsCMField K] in
lemma zetaPrime_mem_primesOver_at_p :
    zetaPrime p K ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K) := by
  refine ⟨zetaPrime_isPrime p K, ?_⟩
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  simpa [zetaPrime, rationalPrimeIdeal] using
    (IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one (p := p) (k := 0)
      (K := K) (hζ := IsCyclotomicExtension.zeta_spec (p ^ (0 + 1)) ℚ K))

omit [IsCMField K] in
lemma primesOver_at_p_eq_singleton_zetaPrime :
    Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K) = {zetaPrime p K} := by
  classical
  obtain ⟨P, hP⟩ :=
    Set.ncard_eq_one.mp (ncard_primesOver_at_p_eq_one (p := p) (K := K))
  have hzeta : zetaPrime p K = P := by
    have hzeta_mem := zetaPrime_mem_primesOver_at_p (p := p) (K := K)
    rw [hP] at hzeta_mem
    simpa using hzeta_mem
  simpa [hzeta] using hP

lemma zetaPrimePlus_mem_primesOver_at_p :
    zetaPrimePlus p K ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 (K⁺)) := by
  refine ⟨inferInstance, ?_⟩
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  have hzeta_over : (zetaPrime p K).LiesOver (rationalPrimeIdeal p) := by
    simpa [zetaPrime, rationalPrimeIdeal] using
      (IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one (p := p) (k := 0)
        (K := K) (hζ := IsCyclotomicExtension.zeta_spec (p ^ (0 + 1)) ℚ K))
  rw [Ideal.liesOver_iff, zetaPrimePlus, Ideal.under_under]
  exact Ideal.over_def (P := zetaPrime p K) (A := ℤ) (p := rationalPrimeIdeal p)

lemma primesOverPlus_at_p_eq_singleton_zetaPrimePlus :
    Ideal.primesOver (rationalPrimeIdeal p) (𝓞 (K⁺)) = {zetaPrimePlus p K} := by
  classical
  ext PPlus
  constructor
  · intro hPPlus
    have : PPlus.IsPrime := hPPlus.1
    have : PPlus.LiesOver (rationalPrimeIdeal p) := hPPlus.2
    obtain ⟨⟨P, hP_prime, hP_over_PPlus⟩⟩ := PPlus.nonempty_primesOver (S := 𝓞 K)
    have hP : P ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K) := by
      refine ⟨hP_prime, ?_⟩
      exact Ideal.LiesOver.trans (A := ℤ) (B := 𝓞 (K⁺)) (C := 𝓞 K)
        (𝔓 := P) (P := PPlus) (p := rationalPrimeIdeal p)
    have hP_eq : P = zetaPrime p K := by
      rw [primesOver_at_p_eq_singleton_zetaPrime (p := p) (K := K)] at hP
      simpa using hP
    have hPPlus_eq : PPlus = zetaPrimePlus p K := by
      simpa [zetaPrimePlus, hP_eq] using
        (Ideal.liesOver_iff _ _).1 (show P.LiesOver PPlus from inferInstance)
    simp [hPPlus_eq]
  · intro hPPlus
    rw [Set.mem_singleton_iff] at hPPlus
    simpa [hPPlus] using zetaPrimePlus_mem_primesOver_at_p (p := p) (K := K)

lemma ncard_primesOverPlus_at_p_eq_one :
    (Ideal.primesOver (rationalPrimeIdeal p) (𝓞 (K⁺))).ncard = 1 := by
  rw [primesOverPlus_at_p_eq_singleton_zetaPrimePlus (p := p) (K := K)]
  simp

lemma zetaPrimePlus_inertiaDeg_eq_one_at_p :
    (zetaPrimePlus p K).inertiaDeg ℤ = 1 := by
  have hinertia_tower :
      (zetaPrime p K).inertiaDeg ℤ =
        (zetaPrimePlus p K).inertiaDeg ℤ *
          (zetaPrime p K).inertiaDeg (𝓞 (K⁺)) := by
    simpa using Ideal.inertiaDeg_tower
      (R := ℤ) (S := 𝓞 (K⁺)) (T := 𝓞 K) (q := zetaPrimePlus p K) (r := zetaPrime p K)
  have hzeta_inertia :
      (zetaPrime p K).inertiaDeg ℤ = 1 :=
    primesOver_inertiaDeg_eq_one_at_p (p := p) (K := K) (zetaPrime p K)
        (zetaPrime_mem_primesOver_at_p (p := p) (K := K))
  rw [hzeta_inertia] at hinertia_tower
  exact Nat.eq_one_of_dvd_one <|
    ⟨(zetaPrime p K).inertiaDeg (𝓞 (K⁺)), hinertia_tower⟩

lemma primesOverPlus_inertiaDeg_eq_one_at_p (PPlus : Ideal (𝓞 (K⁺)))
    (hPPlus : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 (K⁺))) :
    PPlus.inertiaDeg ℤ = 1 := by
  have hPPlus_eq : PPlus = zetaPrimePlus p K := by
    rw [primesOverPlus_at_p_eq_singleton_zetaPrimePlus (p := p) (K := K)] at hPPlus
    simpa using hPPlus
  simpa [hPPlus_eq] using zetaPrimePlus_inertiaDeg_eq_one_at_p (p := p) (K := K)

end KummerCriterion
