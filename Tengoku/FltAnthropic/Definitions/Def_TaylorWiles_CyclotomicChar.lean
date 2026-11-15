import Tengoku.FltAnthropic.Definitions.Def_TaylorWiles_Primes
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped Pointwise
open scoped commutatorElement

open Matrix MatrixGroups

namespace TaylorWiles

open NumberField FrobeniusDensity Ideal

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

section CycloChar

variable {m : ℕ} [NeZero m] {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ m)

noncomputable def cycloChar : (L ≃ₐ[ℚ] L) →* (ZMod m)ˣ :=
  (hζ.autToPow ℤ).comp (MulSemiringAction.toAlgAut (L ≃ₐ[ℚ] L) ℤ (𝓞 L))

omit [IsGalois ℚ L] in

/--
@isnad1 id=eq.1h4v.s10.43c3183c2ecd from=translated src=- shape=457fac63 vocab=146864f2
-/
lemma cycloChar_spec (σ : L ≃ₐ[ℚ] L) :
    ζ ^ ((cycloChar hζ σ : ZMod m)).val = σ • ζ := by
  simp [cycloChar]

omit [IsGalois ℚ L] in

/--
@isnad1 id=eq.3h4v.s9.a25bc4357e6d from=translated src=- shape=d8ef4fab vocab=dd164f01
-/
lemma smul_eq_self_of_mem_ker_cycloChar (hm : m ≠ 1) {σ : L ≃ₐ[ℚ] L}
    (hσ : σ ∈ (cycloChar hζ).ker) : σ • ζ = ζ := by
  have h1 : cycloChar hζ σ = 1 := MonoidHom.mem_ker.mp hσ
  have h2 := cycloChar_spec hζ σ
  rw [h1, Units.val_one, ZMod.val_one'' hm, pow_one] at h2
  exact h2.symm

omit [IsGalois ℚ L] in

/--
@isnad1 id=mem.1h5v.s8.55f606422283 from=translated src=- shape=87b87b2c vocab=1e53cd0f
-/
lemma commutatorElement_mem_ker_cycloChar (g h : L ≃ₐ[ℚ] L) :
    ⁅g, h⁆ ∈ (cycloChar hζ).ker := by
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)

end CycloChar

section Frobenius

variable {m : ℕ} [NeZero m]

omit [NumberField L] [IsGalois ℚ L] in

/--
@isnad1 id=eq.0h3v.s6.1dc3379ab253 from=translated src=- shape=151dca46 vocab=e4619eee
-/
lemma natCard_quotient_under_eq {ℓ : ℕ} (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)] : Nat.card (ℤ ⧸ Q.under ℤ) = ℓ := by
  rw [← Q.over_def (ratPrimeIdeal ℓ)]
  exact (Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv).trans (Nat.card_zmod ℓ)

omit [NumberField L] [IsGalois ℚ L] [NeZero m] in

/--
@isnad1 id=not.1h4v.s7.413c457cb8d8 from=translated src=- shape=303a393f vocab=94a44ad8
-/
lemma natCast_notMem_of_not_dvd {ℓ : ℕ} (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)] (h : ¬ ℓ ∣ m) : ((m : ℕ) : 𝓞 L) ∉ Q := by
  intro hmem
  apply h
  have h1 : ((m : ℤ)) ∈ Q.under ℤ := Ideal.mem_comap.mpr (by rwa [map_natCast])
  rw [← Q.over_def (ratPrimeIdeal ℓ), Ideal.mem_span_singleton] at h1
  exact_mod_cast h1

/--
@isnad1 id=modeq.5h5v.s8.02ab787a4eb5 from=translated src=- shape=dfc81a8c vocab=c2856c48
-/
theorem modEq_one_of_realizesCyclicAt {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 1)
    {σ : L ≃ₐ[ℚ] L} (hσ : σ ∈ (cycloChar hζ).ker) {ℓ : ℕ} (hℓm : ¬ ℓ ∣ m)
    (hreal : RealizesCyclicAt L σ ℓ) : ℓ ≡ 1 [MOD m] := by
  obtain ⟨hℓp, hQ⟩ := hreal
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  obtain ⟨⟨Q, hQp, hQl⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) (ratPrimeIdeal ℓ)
  haveI := hQp
  haveI := hQl
  haveI : Finite ((𝓞 L) ⧸ Q) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓp)
  obtain ⟨k, -, hconj⟩ := hQ Q hQp hQl ‹_›
  have hker : arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ∈ (cycloChar hζ).ker := by
    obtain ⟨τ, hτ⟩ := isConj_iff.mp hconj
    rw [← hτ]
    exact (MonoidHom.normal_ker _).conj_mem _ (pow_mem hσ k) τ
  have hfix : arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q • ζ = ζ :=
    smul_eq_self_of_mem_ker_cycloChar hζ hm hker
  have hpow : arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q • ζ = ζ ^ ℓ := by
    have h1 := (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q).apply_of_pow_eq_one
      hζ.pow_eq_one (natCast_notMem_of_not_dvd (ℓ := ℓ) Q hℓm)
    rwa [MulSemiringAction.toAlgHom_apply, natCard_quotient_under_eq (ℓ := ℓ) Q] at h1
  have hord : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨m, Nat.pos_of_ne_zero (NeZero.ne m), hζ.pow_eq_one⟩
  have heq : ζ ^ ℓ = ζ ^ 1 := by rw [pow_one, ← hpow, hfix]
  rw [hζ.eq_orderOf]
  exact hord.pow_eq_pow_iff_modEq.mp heq

end Frobenius

variable (L) in

structure CyclotomicLevelStructure (p n : ℕ) (S : Finset ℕ) where
  N : Subgroup (L ≃ₐ[ℚ] L)
  commutator_mem : ∀ g h : L ≃ₐ[ℚ] L, ⁅g, h⁆ ∈ N
  congruent : ∀ σ ∈ N, ∀ ℓ : ℕ, ℓ ∉ S → RealizesCyclicAt L σ ℓ → ℓ ≡ 1 [MOD p ^ n]

variable (L) in

noncomputable def cyclotomicLevelStructureOfIsPrimitiveRoot (p n : ℕ) [hp : Fact p.Prime]
    {S : Finset ℕ} (hpS : p ∈ S) {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    CyclotomicLevelStructure L p n S :=
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
  { N := (cycloChar hζ).ker
    commutator_mem := commutatorElement_mem_ker_cycloChar hζ
    congruent := by
      intro σ hσ ℓ hℓS hreal
      rcases Nat.eq_zero_or_pos n with hn | hn
      · rw [hn, pow_zero]
        exact Nat.modEq_one
      refine modEq_one_of_realizesCyclicAt hζ (Nat.one_lt_pow hn.ne' hp.out.one_lt).ne' hσ
        (fun hdvd => ?_) hreal
      obtain ⟨hℓp, -⟩ := hreal
      exact hℓS (((Nat.prime_dvd_prime_iff_eq hℓp hp.out).mp
        (hℓp.dvd_of_dvd_pow hdvd)) ▸ hpS) }

end TaylorWiles
