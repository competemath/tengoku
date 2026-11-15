import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_NormClass
import Tengoku.FltAnthropic.Definitions.Def_NumberField_RayCharacterData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Definitions/Def_NumberField_NormResidueCharacter.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

noncomputable section

namespace NumberField.NormResidueChar

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply
open LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K] (m : ℕ) [NeZero m]

abbrev fm : Ideal (𝓞 K) := Ideal.span {(m : 𝓞 K)}

/--
@isnad1 id=ne.0h2v.s6.bc87c2deebc5 from=translated src=- shape=eaed1e00 vocab=d1ce8e5b
-/
theorem fm_ne_bot : fm K m ≠ ⊥ := by
  rw [fm, Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast NeZero.ne m

/--
@isnad1 id=finite.0h2v.s4.4f05b1bd1e6b from=translated src=- shape=f7f385a7 vocab=977bae9e
-/
instance finite_G : Finite (NarrowRayClassGroup K (fm K m)) := Deep.NTSupply.finite K (fm_ne_bot K m)

noncomputable instance fintype_G : Fintype (NarrowRayClassGroup K (fm K m)) := Fintype.ofFinite _

def nu : NarrowRayClassGroup K (fm K m) →* (ZMod m)ˣ := normClassChar K m (dvd_refl _)

def chi (ψ : DirichletCharacter ℂ m) : NarrowRayClassGroup K (fm K m) →* ℂ :=
  (Units.coeHom ℂ).comp ((MulChar.toUnitHom ψ).comp (nu K m))

/--
@isnad1 id=eq.0h4v.s13.0dc790aabb21 from=translated src=- shape=01aa9b5e vocab=bb90475d
-/
theorem chi_apply (ψ : DirichletCharacter ℂ m) (g : NarrowRayClassGroup K (fm K m)) :
    chi K m ψ g = ψ ((nu K m g : (ZMod m)ˣ) : ZMod m) := by
  simp [chi]

/--
@isnad1 id=eq.0h4v.s13.3fd02a68fc7c from=translated src=- shape=06f41165 vocab=def61498
-/
theorem chi_mul (ψ θ : DirichletCharacter ℂ m) : chi K m (ψ * θ) = chi K m ψ * chi K m θ := by
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.mul_apply, chi_apply, chi_apply, chi_apply, MulChar.mul_apply]

/--
@isnad1 id=eq.0h2v.s13.ba9635502405 from=translated src=- shape=2e6ed2e8 vocab=32e33b7f
-/
theorem chi_one : chi K m 1 = 1 := by
  refine MonoidHom.ext fun g => ?_
  rw [chi_apply, MonoidHom.one_apply, MulChar.one_apply_coe]

variable {K m}

/--
@isnad1 id=iff.0h3v.s8.901d5db25a35 from=translated src=- shape=2ceb2b8a vocab=1e5dcbb5
-/
theorem dvd_fm_iff (v : HeightOneSpectrum (𝓞 K)) : v.asIdeal ∣ fm K m ↔ (m : 𝓞 K) ∈ v.asIdeal := by
  rw [fm, Ideal.dvd_span_singleton]

/--
@isnad1 id=mem.0h2v.s8.b286ea5684f9 from=translated src=- shape=806f77dc vocab=c92a86e2
-/
theorem absNorm_mem (v : HeightOneSpectrum (𝓞 K)) : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ∈ v.asIdeal :=
  Ideal.absNorm_mem v.asIdeal

/--
@isnad1 id=not.1h3v.s8.54c8759facc4 from=translated src=- shape=d149f9cc vocab=689b6b92
-/
theorem not_coprime_of_mem {v : HeightOneSpectrum (𝓞 K)} (hv : (m : 𝓞 K) ∈ v.asIdeal) :
    ¬ (Ideal.absNorm v.asIdeal).Coprime m := by
  intro hcop
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have hg := Nat.gcd_eq_gcd_ab (Ideal.absNorm v.asIdeal) m
  rw [Nat.Coprime.gcd_eq_one hcop] at hg
  have h1' : (1 : 𝓞 K) = (Ideal.absNorm v.asIdeal : 𝓞 K) * (Nat.gcdA (Ideal.absNorm v.asIdeal) m : 𝓞 K) +
      (m : 𝓞 K) * (Nat.gcdB (Ideal.absNorm v.asIdeal) m : 𝓞 K) := by
    have := congrArg (fun z : ℤ => (z : 𝓞 K)) hg
    push_cast at this
    exact this
  rw [h1']
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ (absNorm_mem v)) (v.asIdeal.mul_mem_right _ hv)

/--
@isnad1 id=coprime.1h3v.s8.5e279a4bf104 from=translated src=- shape=01f51868 vocab=689b6b92
-/
theorem coprime_of_not_mem {v : HeightOneSpectrum (𝓞 K)} (hv : (m : 𝓞 K) ∉ v.asIdeal) :
    (Ideal.absNorm v.asIdeal).Coprime m :=
  absNorm_coprime_of_not_dvd K m v (by rwa [dvd_fm_iff] at *)

/--
@isnad1 id=iff.1h3v.s10.7e8855df70a6 from=translated src=- shape=522725f8 vocab=a01021de
-/
theorem mk0_prime_mem_iff {𝔣 : Ideal (𝓞 K)} (v : HeightOneSpectrum (𝓞 K))
    (h : (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) :
    Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) h ∈ coprimeToModulus K 𝔣 ↔ ¬ v.asIdeal ∣ 𝔣 := by
  rw [mem_coprimeToModulus_iff]
  constructor
  · intro hc hv
    have := hc v hv
    rw [Units.val_mk0, FractionalIdeal.count_self] at this
    exact one_ne_zero this
  · intro hv w hw
    rw [Units.val_mk0]
    exact FractionalIdeal.count_maximal_coprime K w (fun h => hv (h ▸ hw))

/--
@isnad1 id=eq.0h4v.s12.561f03e1758b from=translated src=- shape=5d5252fe vocab=b0cbb0b3
-/
theorem chiIdeal_prime {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (v : HeightOneSpectrum (𝓞 K)) :
    M4aP2.chiIdeal K 𝔣 χ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) =
      if hv : v.asIdeal ∣ 𝔣 then 0 else χ (primeClass K 𝔣 v hv) := by
  have h0 : (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact v.ne_bot
  rw [M4aP2.chiIdeal, dite_eq_left h0]
  by_cases hv : v.asIdeal ∣ 𝔣
  · rw [dite_eq_left hv, dite_eq_right (by rw [mk0_prime_mem_iff]; exact not_not.mpr hv)]
  · have hc : Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) h0 ∈ coprimeToModulus K 𝔣 := by
      rwa [mk0_prime_mem_iff]
    rw [dite_eq_right hv, dite_eq_left hc, primeClass]
    have heq : (⟨Units.mk0 _ h0, hc⟩ : ↥(coprimeToModulus K 𝔣)) =
        ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩ :=
      Subtype.ext (Units.ext (by rw [Units.val_mk0, primeUnit_val]))
    rw [heq]

/--
@isnad1 id=eq.1h4v.s12.c3d01ff7e1aa from=translated src=- shape=577c7b16 vocab=9bdb69a4
-/
theorem chi_primeClass (ψ : DirichletCharacter ℂ m) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ fm K m) :
    chi K m ψ (primeClass K (fm K m) v hv) = ψ (Ideal.absNorm v.asIdeal : ZMod m) := by
  rw [chi_apply, nu, normClassChar_primeClass, normClass_coe]
  exact coprime_of_not_mem (by rwa [dvd_fm_iff] at hv)

/--
@isnad1 id=eq.0h4v.s8.2349c45bf39c from=translated src=- shape=ff124ed5 vocab=815c0e66
-/
theorem chiIdeal_chi (ψ : DirichletCharacter ℂ m) (v : HeightOneSpectrum (𝓞 K)) :
    M4aP2.chiIdeal K (fm K m) (chi K m ψ) (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) =
      ψ (Ideal.absNorm v.asIdeal : ZMod m) := by
  rw [chiIdeal_prime]
  by_cases hv : v.asIdeal ∣ fm K m
  · rw [dite_eq_left hv, eq_comm]
    apply MulChar.map_nonunit
    rw [ZMod.isUnit_iff_coprime]
    exact not_coprime_of_mem ((dvd_fm_iff v).mp hv)
  · rw [dite_eq_right hv, chi_primeClass]

def paritySet (ψ : DirichletCharacter ℂ m) : Finset {w : InfinitePlace K // w.IsReal} :=
  if ψ (-1) = 1 then ∅ else Finset.univ

/--
@isnad1 id=eq.0h2v.s7.418d6fd1a257 from=translated src=- shape=e9df1815 vocab=f89997d6
-/
theorem psi_neg_one_sq (ψ : DirichletCharacter ℂ m) : ψ (-1) * ψ (-1) = 1 := by
  rw [← map_mul, neg_mul_neg, one_mul, map_one]

/--
@isnad1 id=or.0h2v.s7.c1e4d3408a8a from=translated src=- shape=60ece079 vocab=bddac641
-/
theorem psi_neg_one_eq (ψ : DirichletCharacter ℂ m) : ψ (-1) = 1 ∨ ψ (-1) = -1 := by
  have h := psi_neg_one_sq ψ
  have : (ψ (-1) - 1) * (ψ (-1) + 1) = 0 := by ring_nf; rw [sq, h]; ring
  rcases mul_eq_zero.mp this with h1 | h1
  · left; exact sub_eq_zero.mp h1
  · right; exact eq_neg_of_add_eq_zero_left h1

/--
@isnad1 id=eq.2h4v.s9.9352d8239799 from=translated src=- shape=d0cd7b12 vocab=67217d3e
-/
theorem chiIdeal_chi_span (ψ : DirichletCharacter ℂ m) {α : 𝓞 K} (hα : α ≠ 0)
    (h1 : α - 1 ∈ fm K m) :
    M4aP2.chiIdeal K (fm K m) (chi K m ψ) ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      ψ ((SignType.sign (Algebra.norm ℤ α) : ℤ) : ZMod m) := by
  have hspan : (Ideal.span {α} : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hα
  have h0 : ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact hspan
  have hcmem : Units.mk0 _ h0 ∈ coprimeToModulus K (fm K m) := by
    have h := principalUnit_mem_coprimeToModulus K hα h1
    rw [mem_coprimeToModulus_iff] at h ⊢
    intro v hv
    have := h v hv
    rwa [principalUnit_val] at this
  rw [M4aP2.chiIdeal, dite_eq_left h0, dite_eq_left hcmem, chi_apply, nu, normClassChar, raySymbolDescend_mk,
    raySymbolHom_apply]
  have hcop : (Ideal.span {α} : Ideal (𝓞 K)) ⊔ Ideal.span {(m : 𝓞 K)} = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1' : α - (α - 1) = 1 := by ring
    exact h1' ▸ Submodule.sub_mem _
      (Ideal.mem_sup_left (Ideal.subset_span rfl))
      (Ideal.mem_sup_right h1)
  have hval : ((⟨Units.mk0 _ h0, hcmem⟩ : ↥(coprimeToModulus K (fm K m))) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      Units.mk0 _ h0 := rfl
  rw [hval, Units.val_mk0, raySymbol_normClass_coe K m hspan hcop, Ideal.absNorm_span_singleton]
  congr 1

  have hN1 : ((Algebra.norm ℤ α : ℤ) : ZMod m) = 1 := norm_int_cast_eq_one_of_sub_one_mem K m h1
  have habs : ((Algebra.norm ℤ α).natAbs : ℤ) = (SignType.sign (Algebra.norm ℤ α) : ℤ) * Algebra.norm ℤ α := by
    rw [← Int.sign_eq_sign, Int.sign_mul_self_eq_natAbs]
  rw [← Int.cast_natCast (R := ZMod m) (Algebra.norm ℤ α).natAbs, habs, Int.cast_mul, hN1, mul_one]

section Cyclo

variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsCyclotomicExtension {m} K L]

/--
@isnad1 id=eq.2h4v.s8.f1d689a4228e from=translated src=- shape=a4b72043 vocab=ccdc83b8
-/
theorem absNorm_cast_eq_one {ζ : L} (hζ : IsPrimitiveRoot ζ m) (w : HeightOneSpectrum (𝓞 L))
    (hw : (m : 𝓞 L) ∉ w.asIdeal) : (Ideal.absNorm w.asIdeal : ZMod m) = 1 := by
  have hζ' : IsPrimitiveRoot hζ.toInteger m := hζ.toInteger_isPrimitiveRoot
  have hcop : (Ideal.absNorm w.asIdeal).Coprime m := coprime_of_not_mem hw
  have hN1 : Ideal.absNorm w.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
  haveI : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
  letI : Field (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  letI : Fintype (𝓞 L ⧸ w.asIdeal) := Fintype.ofFinite _
  have hinj := Ideal.rootsOfUnityMapQuot_injective (I := w.asIdeal) m hN1 hcop
  have hdvd := Subgroup.card_dvd_of_injective _ hinj
  rw [hζ'.card_rootsOfUnity, Nat.card_units, ← Submodule.cardQuot_apply,
    ← Ideal.absNorm_apply] at hdvd
  have hpos : 1 ≤ Ideal.absNorm w.asIdeal := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot)
  have : ((Ideal.absNorm w.asIdeal : ℕ) : ZMod m) = ((Ideal.absNorm w.asIdeal - 1 + 1 : ℕ) : ZMod m) := by
    rw [Nat.sub_add_cancel hpos]
  rw [this, Nat.cast_add, Nat.cast_one, (ZMod.natCast_eq_zero_iff _ _).mpr hdvd, zero_add]

/--
@isnad1 id=mem.1h4v.s7.be8a4e20eceb from=translated src=- shape=9e9e5010 vocab=f2ea017b
-/
theorem mem_primesOver_of_under_eq {w : HeightOneSpectrum (𝓞 L)} {v : HeightOneSpectrum (𝓞 K)}
    (h : w.under (𝓞 K) = v) : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 L) := by
  refine ⟨w.isPrime, ⟨?_⟩⟩
  rw [← h]
  rfl

include m in

/--
@isnad1 id=le.0h4v.s7.95760931fd80 from=translated src=- shape=f858dc96 vocab=e9428234
-/
theorem ncard_primesOver_le (v : HeightOneSpectrum (𝓞 K)) :
    (v.asIdeal.primesOver (𝓞 L)).ncard ≤ Module.finrank K L := by
  haveI : IsGalois K L := IsCyclotomicExtension.isGalois {m} K L
  haveI : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 L) (L ≃ₐ[K] L)
  rw [IsGalois.card_aut_eq_finrank] at h
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  have hne : v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    omega
  calc (v.asIdeal.primesOver (𝓞 L)).ncard
      ≤ (v.asIdeal.primesOver (𝓞 L)).ncard * (v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L)) :=
        Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
    _ = Module.finrank K L := h

/--
@isnad1 id=eq.0h3v.s7.02aa963d99c2 from=translated src=- shape=6268fa1d vocab=fcbe208b
-/
theorem ncard_fibre_eq (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) = v}.ncard = (v.asIdeal.primesOver (𝓞 L)).ncard := by
  have hinj : Set.InjOn (fun w : HeightOneSpectrum (𝓞 L) => w.asIdeal) {w | w.under (𝓞 K) = v} :=
    fun _ _ _ _ h => HeightOneSpectrum.ext h
  rw [← hinj.ncard_image]
  congr 1
  ext I
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact mem_primesOver_of_under_eq hw
  · rintro ⟨hI, hIo⟩
    have hIbot : I ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot I
    refine ⟨⟨I, hI, hIbot⟩, ?_, rfl⟩
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal]
    exact hIo.over.symm

/--
@isnad1 id=finite.0h3v.s6.08b7c06642f3 from=translated src=- shape=4989981e vocab=61179c12
-/
theorem finite_fibre (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) = v}.Finite := by
  have hinj : Set.InjOn (fun w : HeightOneSpectrum (𝓞 L) => w.asIdeal) {w | w.under (𝓞 K) = v} :=
    fun _ _ _ _ h => HeightOneSpectrum.ext h
  haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  refine Set.Finite.of_finite_image ?_ hinj
  refine (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  exact mem_primesOver_of_under_eq hw

include m in
/--
@isnad1 id=le.0h4v.s7.3253e1ad616e from=translated src=- shape=077c7a2a vocab=769adc2a
-/
theorem ncard_fibre_le (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) = v}.ncard ≤ Module.finrank K L := by
  rw [ncard_fibre_eq]
  exact ncard_primesOver_le (m := m) v

/--
@isnad1 id=eq.1h3v.s9.b0aae00f19ce from=translated src=- shape=d7ab1d86 vocab=5b557abd
-/
theorem absNorm_under_eq_of_prime (w : HeightOneSpectrum (𝓞 L)) (hp : (Ideal.absNorm w.asIdeal).Prime) :
    Ideal.absNorm (w.under (𝓞 K)).asIdeal = Ideal.absNorm w.asIdeal := by
  haveI : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
  set v := w.under (𝓞 K)
  haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.field _
  have hpow : Nat.card (𝓞 L ⧸ w.asIdeal) =
      Nat.card (𝓞 K ⧸ v.asIdeal) ^ Module.finrank (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w.asIdeal) :=
    Module.natCard_eq_pow_finrank
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, ← Submodule.cardQuot_apply,
    ← Ideal.absNorm_apply] at hpow
  rw [hpow] at hp
  have hf := Nat.Prime.eq_one_of_pow hp
  rw [hpow, hf, pow_one]

variable (K m)

def U0 {ζ : L} (hζ : IsPrimitiveRoot ζ m) : Subgroup (ZMod m)ˣ := (hζ.autToPow K).range

/--
@isnad1 id=eq.1h4v.s8.057a30be1e67 from=translated src=- shape=7ebd54ec vocab=4f4bdc83
-/
theorem card_U0 {ζ : L} (hζ : IsPrimitiveRoot ζ m) : Nat.card (U0 K m hζ) = Module.finrank K L := by
  haveI : IsGalois K L := IsCyclotomicExtension.isGalois {m} K L
  rw [U0, ← IsGalois.card_aut_eq_finrank K L, ← Nat.card_range_of_injective (hζ.autToPow_injective K)]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => MonoidHom.mem_range))

end Cyclo

end NumberField.NormResidueChar

end
