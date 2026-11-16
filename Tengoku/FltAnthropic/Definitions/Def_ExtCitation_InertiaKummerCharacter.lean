import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ExtEndgame_ProductionDatum
import Tengoku.FltAnthropic.Definitions.Def_EllipticCurve_FrobeniusTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

namespace ExtCitation

section RootsOfUnity

variable (q : Nat.Primes)

/--
@isnad1 id=iff.0h5v.s7.a3fb00a7f70d from=translated src=- shape=4c39380b vocab=dc9359c5
-/
theorem mem_nonunits_comap_iff {K L : Type*} [Field K] [Field L] {B : ValuationSubring L} {f : K →+* L} {x : K} :
    x ∈ (B.comap f).nonunits ↔ f x ∈ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap, map_inv₀]
  constructor
  · rintro (rfl | h)
    · exact Or.inl (map_zero f)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ((map_eq_zero f).mp h)
    · exact Or.inr h

open scoped NNReal in

/--
@isnad1 id=mem.0h1v.s6.a1859b32c440 from=translated src=- shape=316bf8c7 vocab=1e61304a
-/
theorem natCast_mem_nonunits_primeLocalPlace : ((q : ℕ) : AlgebraicClosure ℚ) ∈ (primeLocalPlace q).nonunits := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hq : Valued.v ((q : ℕ) : PadicAlgCl q) = 1 / ((q : ℕ) : ℝ≥0) := PadicAlgCl.valuation_p q
  have hq2 : (2 : ℕ) ≤ (q : ℕ) := (Fact.out : (q : ℕ).Prime).two_le
  show ((q : ℕ) : AlgebraicClosure ℚ) ∈ (padicPlace (q : ℕ)).nonunits
  rw [padicPlace, mem_nonunits_comap_iff, ValuationSubring.mem_nonunits_iff,
    ← (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one]
  change Valued.v ((padicEmbedding q) ((q : ℕ) : AlgebraicClosure ℚ)) < 1
  rw [map_natCast, hq, div_lt_one (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hq2)]
  exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hq2

/--
@isnad1 id=charp.0h1v.s8.a5c49ff60375 from=translated src=- shape=82f70cc5 vocab=3d48469e
-/
theorem charP_residueField_primeLocalPlace : CharP (IsLocalRing.ResidueField ↥(primeLocalPlace q)) q := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hq0 : ((q : ℕ) : IsLocalRing.ResidueField ↥(primeLocalPlace q)) = 0 := by
    rw [← map_natCast (IsLocalRing.residue ↥(primeLocalPlace q)), IsLocalRing.residue_eq_zero_iff,
      ← ValuationSubring.coe_mem_nonunits_iff]
    have : ((((q : ℕ) : ↥(primeLocalPlace q)) : AlgebraicClosure ℚ)) = ((q : ℕ) : AlgebraicClosure ℚ) := by simp
    rw [this]
    exact natCast_mem_nonunits_primeLocalPlace q
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : (q : ℕ).Prime)).mpr hq0

/--
@isnad1 id=eq.3h3v.s11.6b403281bed3 from=translated src=- shape=28cc26d2 vocab=171f8002
-/
theorem primeLocalPlace_eq_one_of_residue_eq_one {u : ↥(primeLocalPlace q)} {m : ℕ} (hum : u ^ m = 1)
    (hm : ¬ (q : ℕ) ∣ m) (hres : IsLocalRing.residue _ u = 1) : u = 1 := by
  haveI := charP_residueField_primeLocalPlace q
  have hmκ : (m : IsLocalRing.ResidueField ↥(primeLocalPlace q)) ≠ 0 := by
    rwa [Ne, CharP.cast_eq_zero_iff _ (q : ℕ)]
  by_contra hu
  have h1 : (∑ i ∈ Finset.range m, u ^ i) * (u - 1) = 0 := by rw [geom_sum_mul, hum, sub_self]
  have h2 : ∑ i ∈ Finset.range m, u ^ i = 0 := (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hu)
  apply hmκ
  have := congrArg (IsLocalRing.residue ↥(primeLocalPlace q)) h2
  rw [map_sum, map_zero] at this
  simpa [map_pow, hres] using this

noncomputable abbrev toDecomp : primeLocalGaloisGroup q →* ↥((primeLocalPlace q).decompositionSubgroup ℚ) :=
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  (primeLocalToGlobal q).codRestrict _ (fun g => localGaloisToGlobal_mem_decompositionSubgroup (q : ℕ) g)

/--
@isnad1 id=eq.0h3v.s13.06e692624c01 from=translated src=- shape=bc618974 vocab=d4e589ec
-/
theorem coe_toDecomp_smul (g : primeLocalGaloisGroup q) (a : ↥(primeLocalPlace q)) :
    ((toDecomp q g • a : ↥(primeLocalPlace q)) : AlgebraicClosure ℚ) = primeLocalToGlobal q g a := rfl

/--
@isnad1 id=mem.2h3v.s7.482a605aad80 from=translated src=- shape=83368bf9 vocab=ade22adc
-/
theorem mem_primeLocalPlace_of_pow_eq_one {ζ : AlgebraicClosure ℚ} {m : ℕ} (hm : m ≠ 0) (hζ : ζ ^ m = 1) :
    ζ ∈ primeLocalPlace q := by
  rw [← ValuationSubring.valuation_le_one_iff]
  have : ((primeLocalPlace q).valuation ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
  exact ((pow_eq_one_iff_of_nonneg zero_le hm).mp this).le

/--
@isnad1 id=eq.3h4v.s10.fe754e4531c6 from=translated src=- shape=d37eafd6 vocab=13759295
-/
theorem inertiaPullback_smul_eq_of_pow_eq_one {σ : primeLocalGaloisGroup q}
    (hσ : σ ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q))
    {ζ : AlgebraicClosure ℚ} {m : ℕ} (hm : ¬ (q : ℕ) ∣ m) (hζ : ζ ^ m = 1) :
    primeLocalToGlobal q σ ζ = ζ := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hζA : ζ ∈ primeLocalPlace q := mem_primeLocalPlace_of_pow_eq_one q hm0 hζ
  set z : ↥(primeLocalPlace q) := ⟨ζ, hζA⟩
  have hzm : z ^ m = 1 := Subtype.ext (by simp [z, hζ])

  have hres : IsLocalRing.residue _ (toDecomp q σ • z) = IsLocalRing.residue _ z := by
    rw [IsLocalRing.ResidueField.residue_smul]
    rw [Subgroup.mem_comap, ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map] at hσ
    obtain ⟨τ, hτ, hτσ⟩ := hσ
    have : toDecomp q σ = τ := Subtype.ext hτσ.symm
    rw [this]
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hτ
    have := congrArg (fun e => (e : IsLocalRing.ResidueField ↥(primeLocalPlace q) ≃+* _) (IsLocalRing.residue _ z)) hτ
    simpa using this

  have hw : (toDecomp q σ • z) * z ^ (m - 1) = 1 := by
    apply primeLocalPlace_eq_one_of_residue_eq_one q (m := m) _ hm
    · rw [map_mul, hres, ← map_mul, ← pow_succ', Nat.sub_add_cancel hm1, hzm, map_one]
    · rw [mul_pow, ← smul_pow', hzm, smul_one, one_mul, ← pow_mul, mul_comm, pow_mul, hzm, one_pow]
  have key : toDecomp q σ • z = z := by
    calc toDecomp q σ • z = (toDecomp q σ • z) * z ^ (m - 1) * z := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hm1, hzm, mul_one]
      _ = z := by rw [hw, one_mul]
  have := congrArg Subtype.val key
  rwa [coe_toDecomp_smul] at this

/--
@isnad1 id=eq.3h4v.s10.3dee3ce3259b from=translated src=- shape=4c9ddf11 vocab=60c4fbdb
-/
theorem frobenius_smul_eq_pow_of_pow_eq_one {φ : primeLocalGaloisGroup q}
    (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    {ζ : AlgebraicClosure ℚ} {m : ℕ} (hm : ¬ (q : ℕ) ∣ m) (hζ : ζ ^ m = 1) :
    primeLocalToGlobal q φ ζ = ζ ^ (q : ℕ) := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hζA : ζ ∈ primeLocalPlace q := mem_primeLocalPlace_of_pow_eq_one q hm0 hζ
  set z : ↥(primeLocalPlace q) := ⟨ζ, hζA⟩
  have hzm : z ^ m = 1 := Subtype.ext (by simp [z, hζ])
  have hres : IsLocalRing.residue _ (toDecomp q φ • z) = IsLocalRing.residue _ (z ^ (q : ℕ)) := by
    rw [IsLocalRing.ResidueField.residue_smul, map_pow]
    exact hφ.smul_residue_eq _
  have hw : (toDecomp q φ • z) * (z ^ (m - 1)) ^ (q : ℕ) = 1 := by
    apply primeLocalPlace_eq_one_of_residue_eq_one q (m := m) _ hm
    · rw [map_mul, hres, ← map_mul, ← mul_pow, ← pow_succ', Nat.sub_add_cancel hm1, hzm, one_pow, map_one]
    · rw [mul_pow, ← smul_pow', hzm, smul_one, one_mul, ← pow_mul, ← pow_mul,
        show (m - 1) * ((q : ℕ) * m) = m * ((m - 1) * (q : ℕ)) by ring, pow_mul, hzm, one_pow]
  have key : toDecomp q φ • z = z ^ (q : ℕ) := by
    calc toDecomp q φ • z = (toDecomp q φ • z) * (z ^ (m - 1)) ^ (q : ℕ) * z ^ (q : ℕ) := by
          rw [mul_assoc, ← mul_pow, ← pow_succ, Nat.sub_add_cancel hm1, hzm, one_pow, mul_one]
      _ = z ^ (q : ℕ) := by rw [hw, one_mul]
  have := congrArg Subtype.val key
  rwa [coe_toDecomp_smul, SubmonoidClass.coe_pow] at this

end RootsOfUnity

section Kummer

variable (p : ℕ) [Fact p.Prime] (q : Nat.Primes)

noncomputable def kummerRoot : AlgebraicClosure ℚ :=
  (IsAlgClosed.exists_pow_nat_eq ((q : ℕ) : AlgebraicClosure ℚ) (Fact.out : p.Prime).pos).choose

/--
@isnad1 id=eq.0h2v.s6.b84b60a3beb3 from=translated src=- shape=53b5d890 vocab=efc988ce
-/
theorem kummerRoot_pow : kummerRoot p q ^ p = ((q : ℕ) : AlgebraicClosure ℚ) :=
  (IsAlgClosed.exists_pow_nat_eq ((q : ℕ) : AlgebraicClosure ℚ) (Fact.out : p.Prime).pos).choose_spec

/--
@isnad1 id=ne.0h2v.s5.3baa732f67e0 from=translated src=- shape=53a31603 vocab=8d260553
-/
theorem kummerRoot_ne_zero : kummerRoot p q ≠ 0 := by
  intro h
  have := kummerRoot_pow p q
  rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at this
  exact (Nat.cast_ne_zero.mpr q.2.ne_zero) this.symm

noncomputable def primRoot : AlgebraicClosure ℚ :=
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p).choose

/--
@isnad1 id=isprimit.0h1v.s4.b39a8db5ed22 from=translated src=- shape=025085eb vocab=97a098d6
-/
theorem isPrimitiveRoot_primRoot : IsPrimitiveRoot (primRoot p) p := by
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  exact (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p).choose_spec

/--
@isnad1 id=ex.0h3v.s8.c3f371707ecd from=translated src=- shape=3fabb4e9 vocab=dddd4b53
-/
theorem exists_apply_kummerRoot_eq (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ i : ℕ, i < p ∧ g (kummerRoot p q) = primRoot p ^ i * kummerRoot p q := by
  have h1 : (g (kummerRoot p q) * (kummerRoot p q)⁻¹) ^ p = 1 := by
    rw [mul_pow, ← map_pow, kummerRoot_pow, map_natCast, inv_pow, kummerRoot_pow,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr q.2.ne_zero)]
  obtain ⟨i, hi, hζ⟩ := (isPrimitiveRoot_primRoot p).eq_pow_of_pow_eq_one h1
  exact ⟨i, hi, by rw [hζ, inv_mul_cancel_right₀ (kummerRoot_ne_zero p q)]⟩

noncomputable def kummerExp (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ZMod p :=
  ((exists_apply_kummerRoot_eq p q g).choose : ℕ)

/--
@isnad1 id=eq.0h3v.s8.d9383b859a25 from=translated src=- shape=206f5e9d vocab=4a283dde
-/
theorem apply_kummerRoot (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    g (kummerRoot p q) = primRoot p ^ (kummerExp p q g).val * kummerRoot p q := by
  have h := (exists_apply_kummerRoot_eq p q g).choose_spec
  rw [kummerExp, ZMod.val_natCast_of_lt h.1]
  exact h.2

/--
@isnad1 id=eq.1h4v.s8.b87337ec991e from=translated src=- shape=e4520376 vocab=64d71a30
-/
theorem kummerExp_eq_of_apply_eq (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {n : ℕ}
    (h : g (kummerRoot p q) = primRoot p ^ n * kummerRoot p q) : kummerExp p q g = n := by
  have h2 := apply_kummerRoot p q g
  rw [h] at h2
  have h3 : primRoot p ^ n = primRoot p ^ (kummerExp p q g).val := mul_right_cancel₀ (kummerRoot_ne_zero p q) h2
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hord : orderOf (primRoot p) = p := (isPrimitiveRoot_primRoot p).eq_orderOf.symm
  rw [← pow_mod_orderOf, hord] at h3
  have hlt : (kummerExp p q g).val < p := ZMod.val_lt _
  rw [← pow_mod_orderOf (primRoot p) (kummerExp p q g).val, hord, Nat.mod_eq_of_lt hlt] at h3
  have h4 : n % p = (kummerExp p q g).val := (isPrimitiveRoot_primRoot p).pow_inj (Nat.mod_lt _ hp) hlt h3
  rw [← ZMod.natCast_mod n p, h4, ZMod.natCast_zmod_val]

/--
@isnad1 id=not.1h2v.s4.3d19006b2b5f from=translated src=- shape=9a7d7795 vocab=e3334dca
-/
theorem not_dvd_of_ne (hqp : (q : ℕ) ≠ p) : ¬ (q : ℕ) ∣ p := fun h =>
  hqp (((Nat.prime_dvd_prime_iff_eq q.2 (Fact.out : p.Prime)).mp h))

noncomputable def kummerCharacter (hqp : (q : ℕ) ≠ p) :
    ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) →* Multiplicative (ZMod p) :=
  MonoidHom.mk' (fun σ => Multiplicative.ofAdd (kummerExp p q (primeLocalToGlobal q (σ : primeLocalGaloisGroup q))))
    (by
      intro σ τ
      rw [← ofAdd_add]
      congr 1
      have hζ : primeLocalToGlobal q (σ : primeLocalGaloisGroup q) (primRoot p) = primRoot p :=
        inertiaPullback_smul_eq_of_pow_eq_one q σ.2 (not_dvd_of_ne p q hqp) (isPrimitiveRoot_primRoot p).pow_eq_one
      have hrep : primeLocalToGlobal q ((σ * τ : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q))) :
            primeLocalGaloisGroup q) (kummerRoot p q)
          = primRoot p ^ ((kummerExp p q (primeLocalToGlobal q (σ : primeLocalGaloisGroup q))).val
              + (kummerExp p q (primeLocalToGlobal q (τ : primeLocalGaloisGroup q))).val) * kummerRoot p q := by
        rw [Subgroup.coe_mul, map_mul, AlgEquiv.mul_apply,
          apply_kummerRoot p q (primeLocalToGlobal q (τ : primeLocalGaloisGroup q)), map_mul, map_pow, hζ,
          apply_kummerRoot p q (primeLocalToGlobal q (σ : primeLocalGaloisGroup q)), ← mul_assoc, ← pow_add, add_comm]
      rw [kummerExp_eq_of_apply_eq p q _ hrep, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])

/--
@isnad1 id=eq.1h3v.s11.6e55aa10814d from=translated src=- shape=41820e68 vocab=ad340f84
-/
theorem kummerCharacter_apply (hqp : (q : ℕ) ≠ p)
    (σ : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q))) :
    kummerCharacter p q hqp σ = Multiplicative.ofAdd (kummerExp p q (primeLocalToGlobal q (σ : primeLocalGaloisGroup q))) :=
  rfl

/--
@isnad1 id=eq.3h4v.s12.3809a98e76b5 from=translated src=- shape=f08be723 vocab=eadfedd3
-/
theorem kummerCharacter_conj (hqp : (q : ℕ) ≠ p) {φ : primeLocalGaloisGroup q}
    (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (σ : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)))
    (h : φ * σ * φ⁻¹ ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) :
    kummerCharacter p q hqp ⟨φ * σ * φ⁻¹, h⟩ = kummerCharacter p q hqp σ ^ (q : ℕ) := by
  rw [kummerCharacter_apply, kummerCharacter_apply, ← ofAdd_nsmul, nsmul_eq_mul]
  congr 1

  set a := kummerExp p q (primeLocalToGlobal q (σ : primeLocalGaloisGroup q)) with ha
  obtain ⟨c, hc, hcφ⟩ := exists_apply_kummerRoot_eq p q (primeLocalToGlobal q φ⁻¹)
  have hζσ : primeLocalToGlobal q (σ : primeLocalGaloisGroup q) (primRoot p) = primRoot p :=
    inertiaPullback_smul_eq_of_pow_eq_one q σ.2 (not_dvd_of_ne p q hqp) (isPrimitiveRoot_primRoot p).pow_eq_one
  have hζφ : primeLocalToGlobal q φ (primRoot p) = primRoot p ^ (q : ℕ) :=
    frobenius_smul_eq_pow_of_pow_eq_one q hφ (not_dvd_of_ne p q hqp) (isPrimitiveRoot_primRoot p).pow_eq_one

  have hφα : primeLocalToGlobal q φ (kummerRoot p q) * primRoot p ^ ((q : ℕ) * c) = kummerRoot p q := by
    have : primeLocalToGlobal q φ (primeLocalToGlobal q φ⁻¹ (kummerRoot p q)) = kummerRoot p q := by
      rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
    rw [hcφ, map_mul, map_pow, hζφ, ← pow_mul] at this
    rwa [mul_comm] at this

  have hcalc : primeLocalToGlobal q (φ * σ * φ⁻¹) (kummerRoot p q) = primRoot p ^ ((q : ℕ) * a.val) * kummerRoot p q := by
    rw [map_mul, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hcφ, map_mul, map_pow, hζσ, apply_kummerRoot p q,
      ← ha, map_mul, map_mul, map_pow, map_pow, hζφ, ← pow_mul, ← pow_mul]

    calc primRoot p ^ ((q : ℕ) * c) * (primRoot p ^ ((q : ℕ) * a.val) * primeLocalToGlobal q φ (kummerRoot p q))
        = primRoot p ^ ((q : ℕ) * a.val) * (primeLocalToGlobal q φ (kummerRoot p q) * primRoot p ^ ((q : ℕ) * c)) := by ring
      _ = primRoot p ^ ((q : ℕ) * a.val) * kummerRoot p q := by rw [hφα]
  have := kummerExp_eq_of_apply_eq p q _ hcalc
  rw [this, Nat.cast_mul, ZMod.natCast_zmod_val]

end Kummer

end ExtCitation
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
