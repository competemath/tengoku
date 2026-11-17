import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic
import Tengoku.FltAnthropic.Theorems.Thm_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild
import Tengoku.Seed.RingTheory.Filtration
import Tengoku.Seed.FieldTheory.Normal.Closure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_exists_pow_prime_pow_eq_one_of_wild.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_exists_pow_prime_pow_eq_one_of_wild

set_option autoImplicit false
open Polynomial

namespace WildOrder

section Small

variable {A V : Type} [CommRing A] [AddCommGroup V] [Module A V]

def Small (I : Ideal A) (n : ℕ) (D : Module.End A V) : Prop :=
  ∀ v : V, D v ∈ (I ^ n • ⊤ : Submodule A V)

variable {I : Ideal A}

/--
@isnad1 id=small.2h6v.s6.e51484bb666e from=translated src=- shape=9df70e0c vocab=4b81543c
-/
theorem Small.mono {m n : ℕ} (h : m ≤ n) {D : Module.End A V} (hD : Small I n D) : Small I m D :=
  fun v => Submodule.smul_mono_left (Ideal.pow_le_pow_right h) (hD v)

/--
@isnad1 id=small.0h4v.s6.f10a5124ff4f from=translated src=- shape=c955e03b vocab=6d0a48f4
-/
theorem Small.zero (n : ℕ) : Small I n (0 : Module.End A V) :=
  fun v => by rw [LinearMap.zero_apply]; exact Submodule.zero_mem _

/--
@isnad1 id=small.2h6v.s7.b629d841bf2a from=translated src=- shape=133fa67b vocab=552777e3
-/
theorem Small.add {n : ℕ} {D D' : Module.End A V} (hD : Small I n D) (hD' : Small I n D') :
    Small I n (D + D') :=
  fun v => by rw [LinearMap.add_apply]; exact Submodule.add_mem _ (hD v) (hD' v)

/--
@isnad1 id=small.2h6v.s7.17350467c0d7 from=translated src=- shape=133fa67b vocab=0adaae02
-/
theorem Small.sub {n : ℕ} {D D' : Module.End A V} (hD : Small I n D) (hD' : Small I n D') :
    Small I n (D - D') :=
  fun v => by rw [LinearMap.sub_apply]; exact Submodule.sub_mem _ (hD v) (hD' v)

/--
@isnad1 id=small.1h6v.s7.ebea44b83f5c from=translated src=- shape=68f20b72 vocab=d2bc5fbf
-/
theorem Small.nsmul {n : ℕ} {D : Module.End A V} (hD : Small I n D) (N : ℕ) : Small I n (N • D) :=
  fun v => by rw [LinearMap.smul_apply]; exact nsmul_mem (hD v) N

/--
@isnad1 id=small.1h6v.s7.1ee483f06d46 from=translated src=- shape=e4049c1d vocab=9f1ae86e
-/
theorem Small.mul_right {n : ℕ} {D : Module.End A V} (hD : Small I n D) (D' : Module.End A V) :
    Small I n (D * D') :=
  fun v => by rw [Module.End.mul_apply]; exact hD (D' v)

/--
@isnad1 id=small.2h7v.s7.7676ba3000f3 from=translated src=- shape=9c6bdb75 vocab=538881b0
-/
theorem Small.mul {m n : ℕ} {D D' : Module.End A V} (hD : Small I n D) (hD' : Small I m D') :
    Small I (m + n) (D * D') := by
  intro v
  rw [Module.End.mul_apply]
  have h1 : D (D' v) ∈ (I ^ m • ⊤ : Submodule A V).map D := Submodule.mem_map_of_mem (hD' v)
  rw [Submodule.map_smul''] at h1
  have h2 : (⊤ : Submodule A V).map D ≤ I ^ n • ⊤ := by
    rintro w ⟨u, -, rfl⟩
    exact hD u
  have h3 : I ^ m • (⊤ : Submodule A V).map D ≤ I ^ (m + n) • ⊤ :=
    calc I ^ m • (⊤ : Submodule A V).map D ≤ I ^ m • (I ^ n • ⊤) := Submodule.smul_mono le_rfl h2
      _ = I ^ (m + n) • ⊤ := by rw [← Submodule.mul_smul, ← pow_add]
  exact h3 h1

/--
@isnad1 id=small.1h6v.s8.b9183f16b7bb from=translated src=- shape=547d3d90 vocab=52df1f7d
-/
theorem Small.one_add_pow_sub_one {n : ℕ} {D : Module.End A V} (hD : Small I n D) (N : ℕ) :
    Small I n ((1 + D) ^ N - 1) := by
  induction N with
  | zero =>
      rw [pow_zero, sub_self]
      exact Small.zero n
  | succ N ih =>
      have e : (1 + D) ^ (N + 1) - 1 = ((1 + D) ^ N - 1) + ((1 + D) ^ N - 1) * D + D := by
        rw [pow_succ, mul_add, mul_one, sub_mul, one_mul]
        abel
      rw [e]
      exact (ih.add (ih.mul_right D)).add hD

/--
@isnad1 id=small.1h6v.s9.453efa7a57c8 from=translated src=- shape=e6e57b8a vocab=5c5d99d6
-/
theorem Small.one_add_pow_sub_one_sub_nsmul {n : ℕ} {D : Module.End A V} (hD : Small I n D) (N : ℕ) :
    Small I (n + n) ((1 + D) ^ N - 1 - N • D) := by
  induction N with
  | zero =>
      rw [pow_zero, sub_self, zero_smul, sub_zero]
      exact Small.zero _
  | succ N ih =>
      have e : (1 + D) ^ (N + 1) - 1 - (N + 1) • D
          = ((1 + D) ^ N - 1 - N • D) + ((1 + D) ^ N - 1 - N • D) * D + N • (D * D) := by
        rw [pow_succ, mul_add, mul_one, succ_nsmul, sub_mul, sub_mul, one_mul, smul_mul_assoc]
        abel
      rw [e]
      exact (ih.add (ih.mul_right D)).add ((hD.mul hD).nsmul N)

end Small

/--
@isnad1 id=isunit.4h3v.s6.aaca29da8915 from=translated src=- shape=b9589d6e vocab=e18de9e3
-/
theorem isUnit_natCast_of_prime_ne {A : Type} [CommRing A] [IsLocalRing A] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hqp : q ≠ p) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) : IsUnit (q : A) := by
  have hcop : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hqp.symm)
  have hA : IsCoprime (p : A) (q : A) := by simpa using hcop.map (Int.castRingHom A)
  by_contra hqu
  have hqm : (q : A) ∈ IsLocalRing.maximalIdeal A := by
    by_contra h
    exact hqu (IsLocalRing.notMem_maximalIdeal.mp h)
  obtain ⟨u, v, huv⟩ := hA
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← huv]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpA) (Ideal.mul_mem_left _ _ hqm)
  exact Ideal.IsMaximal.ne_top (IsLocalRing.maximalIdeal.isMaximal A) ((Ideal.eq_top_iff_one _).mpr h1)

/--
@isnad1 id=mem.2h5v.s7.27c5282a1b52 from=translated src=- shape=3bf69b94 vocab=8e81558d
-/
theorem mem_of_isUnit_smul_mem {A V : Type} [CommRing A] [AddCommGroup V] [Module A V]
    (N : Submodule A V) {r : A} (hu : IsUnit r) {x : V} (h : r • x ∈ N) : x ∈ N := by
  rw [← hu.unit_spec, ← Units.smul_def] at h
  exact (N.smul_mem_iff' hu.unit).mp h

/--
@isnad1 id=ex.3h6v.s11.94b2ff0f08a2 from=translated src=- shape=214a9c46 vocab=4f92a92b
-/
theorem exists_small_pow_sub_one {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    {q : ℕ} (hq : q.Prime) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) (n : ℕ) :
    ∃ a : ℕ, Small (IsLocalRing.maximalIdeal A) n (ρ.ρ σ ^ q ^ a - 1) := by
  obtain ⟨L, hL, hcont⟩ := ρ.isAdicContinuous n
  haveI := hL
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ ↥(IntermediateField.normalClosure ℚ (↥L) (AlgebraicClosure ℚ)) :=
    normalClosure.is_finiteDimensional (F := ℚ) (K := ↥L) (L := AlgebraicClosure ℚ)
  haveI : Normal ℚ ↥(IntermediateField.normalClosure ℚ (↥L) (AlgebraicClosure ℚ)) :=
    normalClosure.normal (F := ℚ) (K := ↥L) (L := AlgebraicClosure ℚ)
  have hle : L ≤ IntermediateField.normalClosure ℚ (↥L) (AlgebraicClosure ℚ) := by
    have h := AlgHom.fieldRange_le_normalClosure L.val
    rwa [IntermediateField.fieldRange_val] at h
  obtain ⟨a, ha⟩ := ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild hq P hP hwild
    (IntermediateField.normalClosure ℚ (↥L) (AlgebraicClosure ℚ))
  refine ⟨a, fun v => ?_⟩
  have h1 : ρ.ρ (σ ^ (q ^ a)) v - v ∈ (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A ρ.V) :=
    hcont _ (fun x hx => ha x (hle hx)) v
  have e : (ρ.ρ σ ^ q ^ a - 1) v = ρ.ρ (σ ^ (q ^ a)) v - v := by
    rw [LinearMap.sub_apply, Module.End.one_apply, map_pow]
  rw [e]
  exact h1

end WildOrder

open WildOrder in
/--
@isnad1 id=ex.6h6v.s11.c4e734504643 from=translated src=- shape=9f55e6cb vocab=9174599e
-/
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) :
    ∃ k : ℕ, ρ.ρ σ ^ q ^ k = 1 := by
  classical
  have hqA : IsUnit (q : A) := isUnit_natCast_of_prime_ne hp hq hqp hpA

  obtain ⟨a, ha1⟩ := exists_small_pow_sub_one ρ hq P hP hwild 1
  refine ⟨a, ?_⟩

  have hstab : ∀ n : ℕ, 1 ≤ n → Small (IsLocalRing.maximalIdeal A) n (ρ.ρ σ ^ q ^ a - 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact ha1
    | succ n hn ih =>
        obtain ⟨b, hb⟩ := exists_small_pow_sub_one ρ hq P hP hwild (n + 1)
        have e1 : (1 + (ρ.ρ σ ^ q ^ a - 1)) = ρ.ρ σ ^ q ^ a := add_sub_cancel 1 _
        have e2 : (1 + (ρ.ρ σ ^ q ^ b - 1)) = ρ.ρ σ ^ q ^ b := add_sub_cancel 1 _

        have hpow : Small (IsLocalRing.maximalIdeal A) (n + 1)
            ((1 + (ρ.ρ σ ^ q ^ a - 1)) ^ q ^ b - 1) := by
          have h := hb.one_add_pow_sub_one (q ^ a)
          rwa [e2, ← pow_mul, mul_comm, pow_mul, ← e1] at h

        have hfirst : Small (IsLocalRing.maximalIdeal A) (n + 1)
            ((1 + (ρ.ρ σ ^ q ^ a - 1)) ^ q ^ b - 1 - q ^ b • (ρ.ρ σ ^ q ^ a - 1)) :=
          (ih.one_add_pow_sub_one_sub_nsmul (q ^ b)).mono (by omega)
        have hdiff := hpow.sub hfirst
        rw [sub_sub_cancel] at hdiff

        intro v
        have hv := hdiff v
        rw [LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul A] at hv
        have hu : IsUnit (((q ^ b : ℕ)) : A) := by
          rw [Nat.cast_pow]
          exact hqA.pow _
        exact mem_of_isUnit_smul_mem _ hu hv

  refine LinearMap.ext fun v => ?_
  have hmem : (ρ.ρ σ ^ q ^ a - 1) v ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A ρ.V) :=
    (Submodule.mem_iInf _).mpr fun n => (hstab (n + 1) (by omega)).mono (Nat.le_succ n) v
  rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top,
    Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hmem
  rw [hmem, Module.End.one_apply]
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
