import Tengoku.FltAnthropic.Theorems.Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test
import Tengoku.FltAnthropic.Theorems.Thm_FrobeniusDensity_idealSum_ne_top
import Tengoku.FltAnthropic.Definitions.Def_FrobeniusDensity_PrimeSums
import Tengoku.Seed.NumberTheory.NumberField.DedekindZeta

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 3 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO

set_option autoImplicit false

open _root_.Ideal open _root_.NumberField open _root_.Filter open _root_.Topology open _root_.Asymptotics open _root_.IsDedekindDomain open _root_.Ideal.IsDedekindDomain open _root_.UniqueFactorizationMonoid

open scoped ENNReal NNReal

namespace FrobeniusDensity
export _root_.FrobeniusDensity (tendsto_sub_one_mul_idealSum_test normRpow idealSum primeSum primeSqSum IsFactoredBy factoredSum one_le_absNorm primeFactors idealSum_ne_top)
open _root_.FrobeniusDensity

variable {K : Type*} [Field K] [NumberField K]

private lemma tsum_equiv {α β : Type*} (e : α ≃ β) (f : β → ℝ≥0∞) :
    ∑' a, f (e a) = ∑' b, f b := by
  refine le_antisymm (ENNReal.tsum_comp_le_tsum_of_injective e.injective f) ?_
  simpa using ENNReal.tsum_comp_le_tsum_of_injective e.symm.injective fun a => f (e a)

section normRpow

variable {s : ℝ}

/--
@isnad1 id=le.0h2v.s7.bf5d89febbc3 from=translated src=- shape=0bd4bc8f vocab=c6fb666b
-/
lemma two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  rw [Nat.two_le_iff]
  exact ⟨fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h),
    fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)⟩

/--
@isnad1 id=le.1h2v.s8.004b4f43eaab from=translated src=- shape=e6d4aee3 vocab=dbb6355b
-/
lemma one_le_cast_absNorm {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (1 : ℝ≥0∞) ≤ (Ideal.absNorm I : ℝ≥0∞) := by
  exact_mod_cast one_le_absNorm hI

/--
@isnad1 id=le.2h3v.s7.d6871dfe5ac4 from=translated src=- shape=b0b09cff vocab=40282a41
-/
lemma normRpow_le_one {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hs : 0 ≤ s) : normRpow K s I ≤ 1 := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [normRpow]
  · exact ENNReal.rpow_le_one_of_one_le_of_neg (one_le_cast_absNorm hI) (neg_neg_iff_pos.mpr hs)

/--
@isnad1 id=ne.2h3v.s7.6a786f40a138 from=translated src=- shape=e19cbb7b vocab=9085089a
-/
lemma normRpow_ne_top {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hs : 0 ≤ s) : normRpow K s I ≠ ∞ :=
  ((normRpow_le_one hI hs).trans_lt ENNReal.one_lt_top).ne

/--
@isnad1 id=lt.0h2v.s8.6e796e136d8a from=translated src=- shape=46d1201b vocab=45369bc8
-/
lemma one_lt_cast_absNorm (v : HeightOneSpectrum (𝓞 K)) :
    (1 : ℝ≥0∞) < (Ideal.absNorm v.asIdeal : ℝ≥0∞) := by
  exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two (two_le_absNorm v)

/--
@isnad1 id=lt.1h3v.s5.b7a6d86fcc31 from=translated src=- shape=c5f2ad46 vocab=e78a130c
-/
lemma normRpow_lt_one (v : HeightOneSpectrum (𝓞 K)) (hs : 0 < s) :
    normRpow K s v.asIdeal < 1 :=
  ENNReal.rpow_lt_one_of_one_lt_of_neg (one_lt_cast_absNorm v) (neg_neg_iff_pos.mpr hs)

/--
@isnad1 id=eq.0h2v.s6.8770182f40dd from=translated src=- shape=9c519702 vocab=19357853
-/
lemma normRpow_top : normRpow K s (⊤ : Ideal (𝓞 K)) = 1 := by
  simp [normRpow]

/--
@isnad1 id=eq.0h4v.s7.c8e708ed4590 from=translated src=- shape=e94573be vocab=c400b3c3
-/
lemma normRpow_mul {I J : Ideal (𝓞 K)} :
    normRpow K s (I * J) = normRpow K s I * normRpow K s J := by
  unfold normRpow
  rw [map_mul, Nat.cast_mul, ENNReal.mul_rpow_of_ne_top (by simp) (by simp)]

/--
@isnad1 id=eq.0h4v.s7.4b0e6faf2996 from=translated src=- shape=bbfa46b4 vocab=78363091
-/
lemma normRpow_pow {I : Ideal (𝓞 K)} (e : ℕ) :
    normRpow K s (I ^ e) = normRpow K s I ^ e := by
  induction e with
  | zero => simpa using normRpow_top
  | succ n ih => rw [pow_succ, pow_succ, normRpow_mul, ih]

end normRpow

section Factors
/--
@isnad1 id=iff.1h3v.s8.20d666fc79bb from=translated src=- shape=a31e9088 vocab=a3a000f9
-/
lemma mem_primeFactors {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ primeFactors K I ↔ v.asIdeal ∣ I := by
  simp [primeFactors, hI]

/--
@isnad1 id=isfactor.1h2v.s6.295e880bbd40 from=translated src=- shape=8f3019a4 vocab=ba0a31bc
-/
lemma isFactoredBy_primeFactors {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    IsFactoredBy (primeFactors K I) I :=
  ⟨hI, fun _ hv => (mem_primeFactors hI).mpr hv⟩

namespace IsFactoredBy
omit [NumberField K] in
private lemma _root_.FrobeniusDensity.IsFactoredBy.mono {T T' : Finset (HeightOneSpectrum (𝓞 K))} (hTT' : T ⊆ T')
    {I : Ideal (𝓞 K)} (hI : IsFactoredBy T I) : IsFactoredBy T' I :=
  ⟨hI.1, fun v hv => hTT' (hI.2 v hv)⟩

end IsFactoredBy
export _root_.FrobeniusDensity (IsFactoredBy.mono)
omit [NumberField K] in
/--
@isnad1 id=isfactor.0h2v.s6.28d7e65ebd84 from=translated src=- shape=2d32ffe0 vocab=70459c56
-/
lemma isFactoredBy_top (T : Finset (HeightOneSpectrum (𝓞 K))) :
    IsFactoredBy T (⊤ : Ideal (𝓞 K)) := by
  refine ⟨by simp, fun v hv => absurd ?_ v.isPrime.ne_top⟩
  exact top_le_iff.mp (Ideal.le_of_dvd hv)

lemma eq_top_of_isFactoredBy_empty {I : Ideal (𝓞 K)}
    (hI : IsFactoredBy (∅ : Finset (HeightOneSpectrum (𝓞 K))) I) : I = ⊤ := by
  by_contra hne
  obtain ⟨P, hP⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors hI.1
    fun h => hne (Ideal.isUnit_iff.mp h)
  obtain ⟨hP1, hP2⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI.1).mp hP
  exact absurd (hI.2 ⟨P, Ideal.isPrime_of_prime hP1, hP1.ne_zero⟩ hP2) (Finset.notMem_empty _)

end Factors

section EulerProduct

variable {s : ℝ}

noncomputable def consFactored (v : HeightOneSpectrum (𝓞 K))
    {T : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∉ T)
    (p : ℕ × {I : Ideal (𝓞 K) // IsFactoredBy T I}) :
    {I : Ideal (𝓞 K) // IsFactoredBy (T.cons v hv) I} := by
  refine ⟨v.asIdeal ^ p.1 * p.2.1, mul_ne_zero (pow_ne_zero _ v.ne_bot) p.2.2.1, fun w hw => ?_⟩
  rcases (Prime.dvd_mul w.prime).mp hw with hw | hw
  · have h1 : w.asIdeal ∣ v.asIdeal := w.prime.dvd_of_dvd_pow hw
    have h2 : w = v := HeightOneSpectrum.ext <|
      associated_iff_eq.mp ((Prime.dvd_prime_iff_associated w.prime v.prime).mp h1)
    simp [h2]
  · exact Finset.mem_cons_of_mem (p.2.2.2 w hw)

/--
@isnad1 id=injectiv.1h3v.s7.b5807d2a97af from=translated src=- shape=f16d8cc9 vocab=d8e2c8e3
-/
lemma consFactored_injective (v : HeightOneSpectrum (𝓞 K))
    {T : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∉ T) :
    Function.Injective (consFactored v hv) := by
  classical
  have hcount : ∀ (e : ℕ) (J : {I : Ideal (𝓞 K) // IsFactoredBy T I}),
      Multiset.count v.asIdeal (normalizedFactors (v.asIdeal ^ e * J.1)) = e := by
    intro e J
    rw [normalizedFactors_mul (pow_ne_zero _ v.ne_bot) J.2.1, normalizedFactors_pow,
      normalizedFactors_irreducible v.prime.irreducible, Multiset.count_add,
      Multiset.count_nsmul, normalize_eq, Multiset.count_singleton_self, mul_one,
      Multiset.count_eq_zero_of_notMem, add_zero]
    intro hmem
    exact hv (J.2.2 v ((UniqueFactorizationMonoid.mem_normalizedFactors_iff J.2.1).mp hmem).2)
  rintro ⟨e, J⟩ ⟨e', J'⟩ h
  have h' : v.asIdeal ^ e * J.1 = v.asIdeal ^ e' * J'.1 := congrArg Subtype.val h
  have he : e = e' := by rw [← hcount e J, ← hcount e' J', h']
  subst he
  exact Prod.ext rfl (Subtype.ext (mul_left_cancel₀ (pow_ne_zero _ v.ne_bot) h'))

/--
@isnad1 id=surjecti.1h3v.s7.e273e29bea2f from=translated src=- shape=f16d8cc9 vocab=77458a79
-/
lemma consFactored_surjective (v : HeightOneSpectrum (𝓞 K))
    {T : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∉ T) :
    Function.Surjective (consFactored v hv) := by
  rintro ⟨I, hI0, hIfac⟩
  have hfin : FiniteMultiplicity v.asIdeal I := .of_prime_left v.prime hI0
  obtain ⟨J, hJ, hvJ⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    exact hI0 (by simpa using hJ)
  refine ⟨⟨multiplicity v.asIdeal I, J, hJ0, fun w hw => ?_⟩, Subtype.ext hJ.symm⟩
  have hwI : w.asIdeal ∣ I := hw.trans ((dvd_mul_left J _).trans (dvd_of_eq hJ.symm))
  rcases Finset.mem_cons.mp (hIfac w hwI) with rfl | hmem
  · exact absurd hw hvJ
  · exact hmem

noncomputable def consFactoredEquiv (v : HeightOneSpectrum (𝓞 K))
    {T : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∉ T) :
    ℕ × {I : Ideal (𝓞 K) // IsFactoredBy T I} ≃
      {I : Ideal (𝓞 K) // IsFactoredBy (T.cons v hv) I} :=
  Equiv.ofBijective _ ⟨consFactored_injective v hv, consFactored_surjective v hv⟩

/--
@isnad1 id=eq.0h2v.s5.c0d4b0c8b5c1 from=translated src=- shape=5626f454 vocab=7bbbbda7
-/
lemma factoredSum_empty (s : ℝ) :
    factoredSum K (∅ : Finset (HeightOneSpectrum (𝓞 K))) s = 1 := by
  have huniq : ∀ I : {I : Ideal (𝓞 K) // IsFactoredBy ∅ I},
      I = ⟨⊤, isFactoredBy_top ∅⟩ := fun I => Subtype.ext (eq_top_of_isFactoredBy_empty I.2)
  rw [factoredSum, tsum_eq_single (⟨⊤, isFactoredBy_top ∅⟩ : {I : Ideal (𝓞 K) // IsFactoredBy ∅ I})
    (fun b hb => absurd (huniq b) hb)]
  exact normRpow_top

/--
@isnad1 id=eq.1h4v.s7.19bef16b8e20 from=translated src=- shape=2ac87efe vocab=44b2c9b2
-/
lemma factoredSum_cons (v : HeightOneSpectrum (𝓞 K))
    {T : Finset (HeightOneSpectrum (𝓞 K))} (hv : v ∉ T) (s : ℝ) :
    factoredSum K (T.cons v hv) s =
      (1 - normRpow K s v.asIdeal)⁻¹ * factoredSum K T s := by
  have h1 : factoredSum K (T.cons v hv) s =
      ∑' p : ℕ × {I : Ideal (𝓞 K) // IsFactoredBy T I},
        normRpow K s ((consFactoredEquiv v hv p).1) :=
    (tsum_equiv (consFactoredEquiv v hv) fun I => normRpow K s I.1).symm
  have h2 : ∀ p : ℕ × {I : Ideal (𝓞 K) // IsFactoredBy T I},
      normRpow K s ((consFactoredEquiv v hv p).1) =
        normRpow K s v.asIdeal ^ p.1 * normRpow K s p.2.1 := by
    intro p
    show normRpow K s (v.asIdeal ^ p.1 * p.2.1) = _
    rw [normRpow_mul, normRpow_pow]
  calc factoredSum K (T.cons v hv) s
      = ∑' p : ℕ × {I : Ideal (𝓞 K) // IsFactoredBy T I},
          normRpow K s v.asIdeal ^ p.1 * normRpow K s p.2.1 := by rw [h1]; exact tsum_congr h2
    _ = ∑' (e : ℕ) (J : {I : Ideal (𝓞 K) // IsFactoredBy T I}),
          normRpow K s v.asIdeal ^ e * normRpow K s J.1 :=
        ENNReal.tsum_prod
          (f := fun e (J : {I : Ideal (𝓞 K) // IsFactoredBy T I}) =>
            normRpow K s v.asIdeal ^ e * normRpow K s J.1)
    _ = ∑' e : ℕ, normRpow K s v.asIdeal ^ e * factoredSum K T s := by
          simp_rw [ENNReal.tsum_mul_left]; rfl
    _ = (∑' e : ℕ, normRpow K s v.asIdeal ^ e) * factoredSum K T s := ENNReal.tsum_mul_right
    _ = (1 - normRpow K s v.asIdeal)⁻¹ * factoredSum K T s := by rw [ENNReal.tsum_geometric]

/--
@isnad1 id=eq.0h3v.s6.c55605d0653e from=translated src=- shape=c0b23890 vocab=9a3c6659
-/
lemma factoredSum_eq_prod (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℝ) :
    factoredSum K T s = ∏ v ∈ T, (1 - normRpow K s v.asIdeal)⁻¹ := by
  induction T using Finset.cons_induction_on with
  | empty => simpa using factoredSum_empty s
  | cons v T hv ih => rw [factoredSum_cons v hv, ih, Finset.prod_cons]

/--
@isnad1 id=le.0h3v.s5.66c342b583c1 from=translated src=- shape=d194c0d9 vocab=d46e9194
-/
lemma factoredSum_le_idealSum (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℝ) :
    factoredSum K T s ≤ idealSum K s := by
  have hinj : Function.Injective
      (fun I : {I : Ideal (𝓞 K) // IsFactoredBy T I} =>
        (⟨I.1, I.2.1⟩ : {I : Ideal (𝓞 K) // I ≠ ⊥})) := by
    rintro ⟨I, hI⟩ ⟨J, hJ⟩ h
    simp only [Subtype.mk.injEq] at h ⊢
    exact h
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj fun I => normRpow K s I.1

/--
@isnad1 id=eq.0h2v.s5.dc2c68e8b6ce from=translated src=- shape=0d43d98b vocab=0c520cd1
-/
lemma idealSum_eq_iSup_factoredSum (s : ℝ) :
    idealSum K s = ⨆ T : Finset (HeightOneSpectrum (𝓞 K)), factoredSum K T s := by
  classical
  refine le_antisymm ?_ (iSup_le fun T => factoredSum_le_idealSum T s)
  rw [idealSum, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  set T : Finset (HeightOneSpectrum (𝓞 K)) := F.biUnion fun I => primeFactors K I.1 with hT
  have hmem : ∀ I ∈ F, IsFactoredBy T I.1 := fun I hI =>
    (isFactoredBy_primeFactors I.2).mono (Finset.subset_biUnion_of_mem _ hI)
  have hinj : Function.Injective
      (fun I : F => (⟨I.1.1, hmem I.1 I.2⟩ : {I : Ideal (𝓞 K) // IsFactoredBy T I})) := by
    rintro ⟨⟨I, hI0⟩, hIF⟩ ⟨⟨J, hJ0⟩, hJF⟩ h
    simp only [Subtype.mk.injEq] at h ⊢
    exact h
  calc ∑ I ∈ F, normRpow K s I.1
      = ∑ I ∈ F.attach, normRpow K s I.1.1 := (Finset.sum_attach F _).symm
    _ = ∑' I : F, normRpow K s I.1.1 := by rw [tsum_fintype, Finset.univ_eq_attach]
    _ ≤ ∑' I : {I : Ideal (𝓞 K) // IsFactoredBy T I}, normRpow K s I.1 :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj fun I => normRpow K s I.1
    _ = factoredSum K T s := rfl
    _ ≤ ⨆ T : Finset (HeightOneSpectrum (𝓞 K)), factoredSum K T s :=
        le_iSup (fun T => factoredSum K T s) T

end EulerProduct

section Comparisons

/--
@isnad1 id=le.0h2v.s4.72395887de41 from=translated src=- shape=7858f812 vocab=9944f801
-/
lemma primeSum_le_idealSum (s : ℝ) : primeSum K s ≤ idealSum K s := by
  have hinj : Function.Injective
      (fun v : HeightOneSpectrum (𝓞 K) => (⟨v.asIdeal, v.ne_bot⟩ : {I : Ideal (𝓞 K) // I ≠ ⊥})) :=
    fun v w h => HeightOneSpectrum.ext (by simpa using congrArg Subtype.val h)
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj fun I => normRpow K s I.1

/--
@isnad1 id=le.1h2v.s5.cd64a05c5a72 from=translated src=- shape=0425ee2b vocab=7d9476e8
-/
lemma primeSqSum_le_idealSum_two {s : ℝ} (hs : 1 ≤ s) : primeSqSum K s ≤ idealSum K 2 := by
  refine le_trans (ENNReal.tsum_le_tsum fun v => ?_) (primeSum_le_idealSum (K := K) 2)
  have h1 : normRpow K s v.asIdeal ^ (2 : ℕ) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (-s * 2) := by
    rw [normRpow, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  rw [h1, normRpow]
  refine ENNReal.rpow_le_rpow_of_exponent_le (one_le_cast_absNorm v.ne_bot) ?_
  nlinarith

/--
@isnad1 id=le.0h2v.s4.18ca51e2443c from=translated src=- shape=c8279772 vocab=164cbbdb
-/
lemma one_le_idealSum (s : ℝ) : 1 ≤ idealSum K s := by
  have h : normRpow K s (⊤ : Ideal (𝓞 K)) ≤ idealSum K s :=
    ENNReal.le_tsum (⟨⊤, by simp⟩ : {I : Ideal (𝓞 K) // I ≠ ⊥})
  rwa [normRpow_top] at h

/--
@isnad1 id=le.0h3v.s5.c77363c05446 from=translated src=- shape=d484cdaf vocab=2bc07f47
-/
lemma one_le_factoredSum (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℝ) :
    1 ≤ factoredSum K T s := by
  have h : normRpow K s (⊤ : Ideal (𝓞 K)) ≤ factoredSum K T s :=
    ENNReal.le_tsum (⟨⊤, isFactoredBy_top T⟩ : {I : Ideal (𝓞 K) // IsFactoredBy T I})
  rwa [normRpow_top] at h

/--
@isnad1 id=lt.1h3v.s5.491bb94259fc from=translated src=- shape=1c5ea25f vocab=5480ce73
-/
lemma factoredSum_toReal_pos {T : Finset (HeightOneSpectrum (𝓞 K))} {s : ℝ}
    (hfin : idealSum K s ≠ ∞) : 0 < (factoredSum K T s).toReal := by
  refine ENNReal.toReal_pos_iff.mpr ⟨lt_of_lt_of_le zero_lt_one (one_le_factoredSum T s), ?_⟩
  exact lt_top_iff_ne_top.mpr fun h => hfin (eq_top_iff.mpr (h ▸ factoredSum_le_idealSum T s))

/--
@isnad1 id=ne.1h2v.s5.8ef6abfbb481 from=translated src=- shape=d5798753 vocab=48c76676
-/
lemma primeSum_ne_top {s : ℝ} (hfin : idealSum K s ≠ ∞) : primeSum K s ≠ ∞ :=
  fun h => hfin (eq_top_iff.mpr (h ▸ primeSum_le_idealSum s))

/--
@isnad1 id=lt.1h2v.s5.6814d72734fa from=translated src=- shape=50f969f3 vocab=8a482e78
-/
lemma idealSum_toReal_pos {s : ℝ} (hfin : idealSum K s ≠ ∞) : 0 < (idealSum K s).toReal :=
  ENNReal.toReal_pos_iff.mpr
    ⟨lt_of_lt_of_le zero_lt_one (one_le_idealSum s), lt_top_iff_ne_top.mpr hfin⟩

end Comparisons

section LogIneq

/--
@isnad1 id=le.1h1v.s5.07c89e81e87c from=translated src=- shape=5129ca7c vocab=71ad43e6
-/
lemma le_neg_log_one_sub {x : ℝ} (hx1 : x < 1) : x ≤ -Real.log (1 - x) := by
  have h := Real.log_le_sub_one_of_pos (x := 1 - x) (by linarith)
  linarith

/--
@isnad1 id=le.2h1v.s6.990030e688c6 from=translated src=- shape=840782ab vocab=41da6211
-/
lemma neg_log_one_sub_le {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ x + 2 * x ^ 2 := by
  have h1 : (1 - x)⁻¹ ≤ 1 + x + 2 * x ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    nlinarith
  have h2 : (1 + x + 2 * x ^ 2 : ℝ) ≤ Real.exp (x + 2 * x ^ 2) := by
    have := Real.add_one_le_exp (x + 2 * x ^ 2)
    linarith
  have h3 : Real.log (1 - x)⁻¹ ≤ x + 2 * x ^ 2 := by
    calc Real.log (1 - x)⁻¹ ≤ Real.log (Real.exp (x + 2 * x ^ 2)) :=
          Real.log_le_log (inv_pos.mpr (by linarith)) (h1.trans h2)
      _ = x + 2 * x ^ 2 := Real.log_exp _
  rwa [Real.log_inv] at h3

end LogIneq

section LogSandwich

variable {s : ℝ}

/--
@isnad1 id=le.0h3v.s5.d535c12321e1 from=translated src=- shape=8072bb16 vocab=3a81837d
-/
lemma normRpow_toReal_nonneg (v : HeightOneSpectrum (𝓞 K)) :
    0 ≤ (normRpow K s v.asIdeal).toReal := ENNReal.toReal_nonneg

/--
@isnad1 id=le.1h3v.s6.71349ece739d from=translated src=- shape=41640c56 vocab=5d3b1585
-/
lemma normRpow_toReal_le_half (v : HeightOneSpectrum (𝓞 K)) (hs : 1 ≤ s) :
    (normRpow K s v.asIdeal).toReal ≤ 1 / 2 := by
  have h1 : normRpow K s v.asIdeal ≤ (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (-1 : ℝ) :=
    ENNReal.rpow_le_rpow_of_exponent_le (one_le_cast_absNorm v.ne_bot) (by linarith)
  have h2 : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (-1 : ℝ) ≤ (2 : ℝ≥0∞) ^ (-1 : ℝ) := by
    rw [ENNReal.rpow_neg_one, ENNReal.rpow_neg_one]
    exact ENNReal.inv_le_inv' (by exact_mod_cast two_le_absNorm v)
  have h3 : ((2 : ℝ≥0∞) ^ (-1 : ℝ)).toReal = 1 / 2 := by
    rw [ENNReal.rpow_neg_one]
    simp
  calc (normRpow K s v.asIdeal).toReal
      ≤ ((2 : ℝ≥0∞) ^ (-1 : ℝ)).toReal := by
        refine (ENNReal.toReal_le_toReal ?_ (by simp [ENNReal.rpow_neg_one])).mpr (h1.trans h2)
        exact normRpow_ne_top v.ne_bot (by linarith)
    _ = 1 / 2 := h3

/--
@isnad1 id=lt.1h3v.s5.81799cf513f0 from=translated src=- shape=e93e323b vocab=94d22a7b
-/
lemma normRpow_toReal_lt_one (v : HeightOneSpectrum (𝓞 K)) (hs : 1 ≤ s) :
    (normRpow K s v.asIdeal).toReal < 1 :=
  lt_of_le_of_lt (normRpow_toReal_le_half v hs) (by norm_num)

/--
@isnad1 id=eq.1h3v.s6.45cac3d5305c from=translated src=- shape=67284a31 vocab=7aaaff57
-/
lemma toReal_eulerFactor (v : HeightOneSpectrum (𝓞 K)) (hs : 1 ≤ s) :
    ((1 - normRpow K s v.asIdeal)⁻¹).toReal =
      (1 - (normRpow K s v.asIdeal).toReal)⁻¹ := by
  rw [ENNReal.toReal_inv,
    ENNReal.toReal_sub_of_le (normRpow_lt_one v (by linarith)).le (by simp), ENNReal.toReal_one]

/--
@isnad1 id=eq.1h3v.s6.bc317654bb94 from=translated src=- shape=40fd8961 vocab=f72accae
-/
lemma log_factoredSum_toReal (T : Finset (HeightOneSpectrum (𝓞 K))) (hs : 1 ≤ s) :
    Real.log ((factoredSum K T s).toReal) =
      ∑ v ∈ T, -Real.log (1 - (normRpow K s v.asIdeal).toReal) := by
  rw [factoredSum_eq_prod, ENNReal.toReal_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [toReal_eulerFactor v hs, Real.log_inv]
  · intro v _
    rw [toReal_eulerFactor v hs]
    exact (inv_pos.mpr (by linarith [normRpow_toReal_lt_one v hs])).ne'

/--
@isnad1 id=le.2h3v.s6.c821285722f8 from=translated src=- shape=b05d8ed3 vocab=9d42e356
-/
lemma sum_normRpow_toReal_le (T : Finset (HeightOneSpectrum (𝓞 K))) (hs : 1 ≤ s)
    (hfin : primeSum K s ≠ ∞) :
    ∑ v ∈ T, (normRpow K s v.asIdeal).toReal ≤ (primeSum K s).toReal := by
  have hne : ∀ v ∈ T, normRpow K s v.asIdeal ≠ ∞ := fun v _ =>
    normRpow_ne_top v.ne_bot (by linarith)
  rw [← ENNReal.toReal_sum hne]
  exact (ENNReal.toReal_le_toReal
    (ENNReal.sum_lt_top.mpr fun v hv => (hne v hv).lt_top).ne hfin).mpr (ENNReal.sum_le_tsum T)

/--
@isnad1 id=le.2h3v.s6.18ed0e782848 from=translated src=- shape=81aea985 vocab=10669002
-/
lemma sum_normRpow_sq_toReal_le (T : Finset (HeightOneSpectrum (𝓞 K))) (hs : 1 ≤ s)
    (hfin2 : idealSum K 2 ≠ ∞) :
    ∑ v ∈ T, (normRpow K s v.asIdeal).toReal ^ 2 ≤ (idealSum K 2).toReal := by
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), normRpow K s v.asIdeal ^ (2:ℕ) ≠ ∞ := fun v =>
    ENNReal.pow_ne_top (normRpow_ne_top v.ne_bot (by linarith))
  have hsq : primeSqSum K s ≠ ∞ :=
    fun h => hfin2 (eq_top_iff.mpr (h ▸ primeSqSum_le_idealSum_two hs))
  calc ∑ v ∈ T, (normRpow K s v.asIdeal).toReal ^ 2
      = ∑ v ∈ T, (normRpow K s v.asIdeal ^ (2:ℕ)).toReal := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [ENNReal.toReal_pow]
    _ = (∑ v ∈ T, normRpow K s v.asIdeal ^ (2:ℕ)).toReal :=
        (ENNReal.toReal_sum (fun v _ => hne v)).symm
    _ ≤ (primeSqSum K s).toReal :=
        (ENNReal.toReal_le_toReal
          (ENNReal.sum_lt_top.mpr fun v _ => (hne v).lt_top).ne hsq).mpr
          (ENNReal.sum_le_tsum T)
    _ ≤ (idealSum K 2).toReal :=
        (ENNReal.toReal_le_toReal hsq hfin2).mpr (primeSqSum_le_idealSum_two hs)

/--
@isnad1 id=le.2h2v.s5.ff43f1d5f9c4 from=translated src=- shape=36fcf479 vocab=8418262e
-/
theorem primeSum_toReal_le_log_idealSum (hs : 1 ≤ s) (hfin : idealSum K s ≠ ∞) :
    (primeSum K s).toReal ≤ Real.log ((idealSum K s).toReal) := by

  rw [primeSum, ENNReal.tsum_toReal_eq
    (fun v => normRpow_ne_top v.ne_bot (by linarith))]
  refine Real.tsum_le_of_sum_le (fun v => ENNReal.toReal_nonneg) fun T => ?_
  calc ∑ v ∈ T, (normRpow K s v.asIdeal).toReal
      ≤ ∑ v ∈ T, -Real.log (1 - (normRpow K s v.asIdeal).toReal) :=
        Finset.sum_le_sum fun v _ => le_neg_log_one_sub (normRpow_toReal_lt_one v hs)
    _ = Real.log ((factoredSum K T s).toReal) := (log_factoredSum_toReal T hs).symm
    _ ≤ Real.log ((idealSum K s).toReal) := by
        refine Real.log_le_log (factoredSum_toReal_pos hfin)
          ((ENNReal.toReal_le_toReal ?_ hfin).mpr (factoredSum_le_idealSum T s))
        exact fun h => hfin (eq_top_iff.mpr (h ▸ factoredSum_le_idealSum T s))

/--
@isnad1 id=le.3h2v.s6.1ec66972ddc5 from=translated src=- shape=97b6f03b vocab=c629bc68
-/
theorem log_idealSum_le_primeSum_toReal (hs : 1 ≤ s) (hfin : idealSum K s ≠ ∞)
    (hfin2 : idealSum K 2 ≠ ∞) :
    Real.log ((idealSum K s).toReal) ≤
      (primeSum K s).toReal + 2 * (idealSum K 2).toReal := by
  set C : ℝ := (primeSum K s).toReal + 2 * (idealSum K 2).toReal with hC

  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 K)), Real.log ((factoredSum K T s).toReal) ≤ C := by
    intro T
    calc Real.log ((factoredSum K T s).toReal)
        = ∑ v ∈ T, -Real.log (1 - (normRpow K s v.asIdeal).toReal) := log_factoredSum_toReal T hs
      _ ≤ ∑ v ∈ T, ((normRpow K s v.asIdeal).toReal + 2 * (normRpow K s v.asIdeal).toReal ^ 2) :=
          Finset.sum_le_sum fun v _ => neg_log_one_sub_le (normRpow_toReal_nonneg v)
            (normRpow_toReal_le_half v hs)
      _ = (∑ v ∈ T, (normRpow K s v.asIdeal).toReal) +
            2 * ∑ v ∈ T, (normRpow K s v.asIdeal).toReal ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ C := by
          rw [hC]
          have h1 := sum_normRpow_toReal_le T hs (primeSum_ne_top hfin)
          have h2 := sum_normRpow_sq_toReal_le T hs hfin2
          linarith

  have hCnonneg : 0 ≤ C := by
    have : (0:ℝ) ≤ (primeSum K s).toReal := ENNReal.toReal_nonneg
    have : (0:ℝ) ≤ (idealSum K 2).toReal := ENNReal.toReal_nonneg
    linarith
  rw [Real.log_le_iff_le_exp (idealSum_toReal_pos hfin)]
  rw [← ENNReal.toReal_ofReal (Real.exp_nonneg C)]
  refine (ENNReal.toReal_le_toReal hfin (by simp)).mpr ?_
  rw [idealSum_eq_iSup_factoredSum]
  refine iSup_le fun T => ?_
  have hTfin : factoredSum K T s ≠ ∞ :=
    fun h => hfin (eq_top_iff.mpr (h ▸ factoredSum_le_idealSum T s))
  rw [← ENNReal.ofReal_toReal hTfin]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.exp_log (x := (factoredSum K T s).toReal) (factoredSum_toReal_pos hfin)]
  exact Real.exp_le_exp.mpr (key T)

end LogSandwich

variable (K)

private lemma log_idealSum_add_log_isBigO :
    (fun s : ℝ => Real.log ((idealSum K s).toReal) + Real.log (s - 1)) =O[𝓝[>] 1]
      (fun _ => (1:ℝ)) := by
  have h1 : Tendsto (fun s : ℝ => Real.log ((s - 1) * (idealSum K s).toReal)) (𝓝[>] 1)
      (𝓝 (Real.log (dedekindZeta_residue K))) :=
    (tendsto_sub_one_mul_idealSum_test K).log (dedekindZeta_residue_ne_zero K)
  refine (h1.isBigO_one ℝ).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  rw [Real.log_mul (by linarith) (idealSum_toReal_pos (idealSum_ne_top K hs)).ne']
  ring

private lemma primeSum_sub_log_idealSum_isBigO :
    (fun s : ℝ => (primeSum K s).toReal - Real.log ((idealSum K s).toReal)) =O[𝓝[>] 1]
      (fun _ => (1:ℝ)) := by
  rw [isBigO_one_iff]
  refine isBoundedUnder_of_eventually_le (a := 2 * (idealSum K 2).toReal) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Set.mem_Ioi] at hs
  have hfin := idealSum_ne_top K hs
  have hfin2 := idealSum_ne_top K (by norm_num : (1:ℝ) < 2)
  have hub := primeSum_toReal_le_log_idealSum hs.le hfin
  have hlb := log_idealSum_le_primeSum_toReal hs.le hfin hfin2
  have hC2 : (0:ℝ) ≤ 2 * (idealSum K 2).toReal := by positivity
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

end FrobeniusDensity

open _root_.FrobeniusDensity open _root_.P2MW.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.FrobeniusDensity

/--
@isnad1 id=isbigo.0h1v.s6.c250cad75475 from=translated src=- shape=938ffee7 vocab=a91a3bd0
-/
theorem solution (K : Type*) [Field K] [NumberField K] :
    (fun s : ℝ => (FrobeniusDensity.primeSum K s).toReal + Real.log (s - 1))
      =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1:ℝ)) := by
  have h := (primeSum_sub_log_idealSum_isBigO K).add (log_idealSum_add_log_isBigO K)
  refine h.congr' (Eventually.of_forall fun s => by ring) EventuallyEq.rfl
