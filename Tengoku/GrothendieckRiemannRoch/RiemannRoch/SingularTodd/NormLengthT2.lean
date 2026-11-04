/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.ProperPushforwardNormAlgebra
import Tengoku.Seed.RingTheory.LocalRing.Length

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The norm/length formula with residue degrees (Fulton Ex. 1.2.3, A.3; Stacks "lengths and norms")

Let `A` be a one-dimensional Noetherian local domain with fraction field `K`, and let `B` be a
finite `A`-algebra which is a domain with fraction field `L` (so `L/K` is finite and `B` is
semilocal).  For every `b ∈ L^×`,

`ord_A (N_{L/K} b) = Σ_{q ⊂ B maximal} [κ(q) : κ(m_A)] · ord_{B_q} b`.

This is the local statement making proper push-forward commute with `div` (Fulton Prop. 1.4).
The length form for `b ∈ B` (`ord_A (N b) = Σ_q ℓ_A (B_q / b)`) is already in B as
`RiemannRoch.ProperPushforwardNorm.local_formula`; here we

* convert `ℓ_A` into `ℓ_{B_q} · [κ(q) : κ(m_A)]` (Mathlib `IsLocalRing.length_restrictScalars`),
  `length_quot_toNat_eq`;
* identify `ℓ_{B_q}(B_q / b)` with Mathlib's `Ring.ord`/`Ring.ordFrac` (`ordFrac_algebraMap_eq`);
* extend from `b ∈ B` to `b ∈ L^×` by multiplicativity (`ordFrac_norm_eq_prod`).

Main results (all in `ℤᵐ⁰`, the multiplicative form of `Σ d_t · ord_t`):
* `ordFrac_norm_eq_ofAdd_sum` — `b ∈ S`, additive exponent form;
* `ordFrac_norm_eq_prod` — `b ∈ L^×`, general height-one-prime form (`A = R_p`, `D t = S_{Q t}`);
* `ordFrac_norm_eq_prod_local` — `A` local, `B` finite over `A`, `D t = B_{q_t}` over an enumeration
  of the maximal ideals of `B`.

`isLocalHom_algebraMap` and `isLocalization_atPrime_maximalIdeal` discharge the instance
hypotheses in the usual situations.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open IsLocalRing Module
open scoped WithZero

namespace RiemannRoch.NormLengthT2

/-! ### Residue degree and lengths along a local homomorphism -/

section Local

variable (A B : Type*) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]

/-- The residue degree `[κ(B) : κ(A)]` of a local homomorphism, as a natural number
(`0` if infinite).-/
def resDeg : ℕ := (Module.length (ResidueField A) (ResidueField B)).toNat

/-- `ℓ_A(B / x B) = ℓ_B(B / x B) · [κ(B) : κ(A)]` (as natural numbers).
@isnad1 id=eq.0h3v.s8.1399500c0df2 from=translated src=- shape=762b9d1d vocab=ecb0c440
-/
theorem length_quot_toNat_eq (x : B) :
    (Module.length A (B ⧸ Ideal.span {x})).toNat =
      (Ring.ord B x).toNat * resDeg A B := by
  rw [IsLocalRing.length_restrictScalars A B (B ⧸ Ideal.span {x}), ENat.toNat_mul]
  rfl

end Local

section OrdFrac

variable {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [Ring.KrullDimLE 1 B]
  {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]

/-- For `x ≠ 0` in a one-dimensional Noetherian domain, `ordFrac` is the length order.
@isnad1 id=eq.1h3v.s7.c1c13f88cf9a from=translated src=- shape=7b483c83 vocab=1264f7ef
-/
theorem ordFrac_algebraMap_eq {x : B} (hx : x ≠ 0) :
    Ring.ordFrac B (algebraMap B L x) =
      ((Multiplicative.ofAdd ((Ring.ord B x).toNat : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) := by
  rw [Ring.ordFrac_eq_ord B hx]
  exact Ring.ordMonoidWithZeroHom_eq_coe B (mem_nonZeroDivisors_of_ne_zero hx)
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hx))).symm

end OrdFrac

/--
@isnad1 id=eq.1h3v.s5.4c14bfa2381c from=translated src=- shape=82ec11d5 vocab=f0b581cf
-/
theorem toNat_sum_of_ne_top {T : Type*} (s : Finset T) (f : T → ℕ∞)
    (h : ∑ t ∈ s, f t ≠ ⊤) : (∑ t ∈ s, f t).toNat = ∑ t ∈ s, (f t).toNat := by
  have hf : ∀ t ∈ s, f t ≠ ⊤ := fun t ht ↦
    ne_top_of_le_ne_top h (Finset.single_le_sum (fun _ _ ↦ zero_le) ht)
  have heq : ∑ t ∈ s, f t = ((∑ t ∈ s, (f t).toNat : ℕ) : ℕ∞) := by
    push_cast
    exact Finset.sum_congr rfl (fun t ht ↦ (ENat.natCast_toNat (hf t ht)).symm)
  rw [heq, ENat.toNat_natCast]

/--
@isnad1 id=eq.0h3v.s7.c9820aaab817 from=translated src=- shape=f8c17350 vocab=29bdcda6
-/
theorem prod_coe_ofAdd_pow {T : Type*} [Fintype T] (n d : T → ℕ) :
    ∏ t, ((Multiplicative.ofAdd (n t : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) ^ d t =
      ((Multiplicative.ofAdd ((∑ t, n t * d t : ℕ) : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) := by
  rw [Nat.cast_sum, ofAdd_sum, ← WithZero.coeMonoidHom_apply, map_prod]
  refine Finset.prod_congr rfl (fun t _ ↦ ?_)
  rw [WithZero.coeMonoidHom_apply, ← WithZero.coe_pow, ← ofAdd_nsmul]
  congr 2
  push_cast
  rw [nsmul_eq_mul, mul_comm]

/--
@isnad1 id=ne.1h4v.s7.62690a025cdd from=translated src=- shape=7b9e3eb3 vocab=aba9386c
-/
theorem algebraMap_ne_zero_of_atPrime {S : Type*} [CommRing S] [IsDomain S] (P : Ideal S)
    [P.IsPrime] (D : Type*) [CommRing D] [Algebra S D] [IsLocalization.AtPrime D P]
    {b : S} (hb : b ≠ 0) : algebraMap S D b ≠ 0 := by
  intro h0
  exact hb (IsLocalization.injective D P.primeCompl_le_nonZeroDivisors
    (h0.trans (map_zero _).symm))

/-! ### The height-one-prime form -/

section General

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]
  {K L : Type*} [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
  [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
  [Module.Finite R S] [FiniteDimensional K L]
  (p : Ideal R) [p.IsPrime]
  {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [Algebra R A] [IsLocalization.AtPrime A p] [Algebra A K] [IsFractionRing A K]
  [IsScalarTower R A K] [IsLocalRing A]
  {T : Type*} [Fintype T] (Q : T → Ideal S) [hQ : ∀ t, (Q t).IsPrime]
  (D : T → Type*) [∀ t, CommRing (D t)] [∀ t, Algebra S (D t)]
  [∀ t, IsLocalization.AtPrime (D t) (Q t)] [∀ t, Algebra A (D t)]

variable [∀ t, IsLocalRing (D t)] [∀ t, IsLocalHom (algebraMap A (D t))]

/-- **Norm/length formula, exponent form** (`b ∈ S`):
`ord_A (N_{L/K} b) = Σ_t ord_{D_t}(b) · [κ(D_t) : κ(A)]`.
@isnad1 id=eq.5h10v.s10.a02677c43153 from=translated src=- shape=91bf1186 vocab=5ab58856
-/
theorem ordFrac_norm_eq_ofAdd_sum
    (hDtower : ∀ t r, algebraMap A (D t) (algebraMap R A r) =
      algebraMap S (D t) (algebraMap R S r))
    (hQover : ∀ t, (Q t).comap (algebraMap R S) = p)
    (hQinj : Function.Injective Q)
    (hQsurj : ∀ Q' : Ideal S, Q'.IsPrime → Q'.comap (algebraMap R S) = p → ∃ t, Q t = Q')
    (b : S) (hb : b ≠ 0) :
    Ring.ordFrac A (Algebra.norm K (algebraMap S L b)) =
      ((Multiplicative.ofAdd ((∑ t, (Ring.ord (D t) (algebraMap S (D t) b)).toNat *
        resDeg A (D t) : ℕ) : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) := by
  obtain ⟨hfin, hnorm⟩ := RiemannRoch.ProperPushforwardNorm.local_formula (K := K) (L := L)
    p (A := A) Q D hDtower hQover hQinj hQsurj b hb
  rw [hnorm, toNat_sum_of_ne_top _ _ hfin]
  congr 3
  refine Finset.sum_congr rfl (fun t _ ↦ ?_)
  exact length_quot_toNat_eq A (D t) _

variable [∀ t, IsDomain (D t)] [∀ t, IsNoetherianRing (D t)] [∀ t, Ring.KrullDimLE 1 (D t)]
  [∀ t, Algebra (D t) L] [∀ t, IsFractionRing (D t) L] [∀ t, IsScalarTower S (D t) L]

/-- **Norm/length formula, product form for `b ∈ S`**.
@isnad1 id=eq.5h10v.s10.7b254ca149b4 from=translated src=- shape=4b68ab73 vocab=00c280c4
-/
theorem ordFrac_norm_eq_prod_of_mem
    (hDtower : ∀ t r, algebraMap A (D t) (algebraMap R A r) =
      algebraMap S (D t) (algebraMap R S r))
    (hQover : ∀ t, (Q t).comap (algebraMap R S) = p)
    (hQinj : Function.Injective Q)
    (hQsurj : ∀ Q' : Ideal S, Q'.IsPrime → Q'.comap (algebraMap R S) = p → ∃ t, Q t = Q')
    (b : S) (hb : b ≠ 0) :
    Ring.ordFrac A (Algebra.norm K (algebraMap S L b)) =
      ∏ t, Ring.ordFrac (D t) (algebraMap S L b) ^ resDeg A (D t) := by
  rw [ordFrac_norm_eq_ofAdd_sum p Q D hDtower hQover hQinj hQsurj b hb, ← prod_coe_ofAdd_pow]
  refine Finset.prod_congr rfl (fun t _ ↦ ?_)
  rw [IsScalarTower.algebraMap_apply S (D t) L,
    ordFrac_algebraMap_eq (algebraMap_ne_zero_of_atPrime (Q t) (D t) hb)]

/-- **Norm/length formula** (Fulton Ex. 1.2.3 / A.3, general form): for `b ∈ L^×`,
`ord_A (N_{L/K} b) = ∏_t ord_{D_t}(b) ^ [κ(D_t) : κ(A)]` in `ℤᵐ⁰`, i.e.
`ord_A (N b) = Σ_t [κ(D_t):κ(A)] · ord_{D_t}(b)`.
@isnad1 id=eq.5h10v.s10.335dc6ee8ead from=translated src=- shape=ba7e4df5 vocab=00c280c4
-/
theorem ordFrac_norm_eq_prod
    (hDtower : ∀ t r, algebraMap A (D t) (algebraMap R A r) =
      algebraMap S (D t) (algebraMap R S r))
    (hQover : ∀ t, (Q t).comap (algebraMap R S) = p)
    (hQinj : Function.Injective Q)
    (hQsurj : ∀ Q' : Ideal S, Q'.IsPrime → Q'.comap (algebraMap R S) = p → ∃ t, Q t = Q')
    (b : L) (hb : b ≠ 0) :
    Ring.ordFrac A (Algebra.norm K b) =
      ∏ t, Ring.ordFrac (D t) b ^ resDeg A (D t) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := S) b
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyL : algebraMap S L y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S L)).mpr hy0
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb (by rw [map_zero, zero_div])
  set c := algebraMap S L x / algebraMap S L y with hc
  have hcy : c * algebraMap S L y = algebraMap S L x := div_mul_cancel₀ _ hyL
  have hX := ordFrac_norm_eq_prod_of_mem (K := K) (L := L) p Q D hDtower hQover hQinj hQsurj x hx0
  have hY := ordFrac_norm_eq_prod_of_mem (K := K) (L := L) p Q D hDtower hQover hQinj hQsurj y hy0
  have hNy : Ring.ordFrac A (Algebra.norm K (algebraMap S L y)) ≠ 0 := by
    rw [map_ne_zero]
    exact Algebra.norm_ne_zero_iff.mpr hyL
  rw [← hcy, map_mul, map_mul] at hX
  have hP : ∏ t, Ring.ordFrac (D t) (c * algebraMap S L y) ^ resDeg A (D t) =
      (∏ t, Ring.ordFrac (D t) c ^ resDeg A (D t)) *
        Ring.ordFrac A (Algebra.norm K (algebraMap S L y)) := by
    rw [hY, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun t _ ↦ ?_)
    rw [map_mul, mul_pow]
  rw [hP] at hX
  exact mul_right_cancel₀ hNy hX

end General

/-! ### The local form: `A` local, `B` finite over `A` -/

/-- A local ring is its own localization at the maximal ideal.
@isnad1 id=atprime.0h1v.s5.d24dc1b1b723 from=translated src=- shape=ac0af42f vocab=929ed0a2
-/
theorem isLocalization_atPrime_maximalIdeal (A : Type*) [CommRing A] [IsLocalRing A] :
    IsLocalization.AtPrime A (maximalIdeal A) :=
  IsLocalization.self (fun _ hx ↦ (IsLocalRing.notMem_maximalIdeal.mp hx))

section LocalForm

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [IsLocalRing A] {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
  {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L] [FiniteDimensional K L]
  {T : Type*} [Fintype T] (Q : T → Ideal B) [hQ : ∀ t, (Q t).IsMaximal]
  (D : T → Type*) [∀ t, CommRing (D t)] [∀ t, Algebra B (D t)]
  [∀ t, IsLocalization.AtPrime (D t) (Q t)] [∀ t, Algebra A (D t)]
  [∀ t, IsScalarTower A B (D t)]
  [∀ t, IsLocalRing (D t)] [∀ t, IsLocalHom (algebraMap A (D t))]
  [∀ t, IsDomain (D t)] [∀ t, IsNoetherianRing (D t)] [∀ t, Ring.KrullDimLE 1 (D t)]
  [∀ t, Algebra (D t) L] [∀ t, IsFractionRing (D t) L] [∀ t, IsScalarTower B (D t) L]

include hQ in
/--
@isnad1 id=eq.0h5v.s7.ddea5cc228aa from=translated src=- shape=d8e28cdc vocab=a693810d
-/
theorem comap_eq_maximalIdeal (t : T) : (Q t).comap (algebraMap A B) = maximalIdeal A := by
  haveI : (Ideal.under A (Q t)).IsMaximal := Ideal.IsMaximal.under A (Q t)
  exact IsLocalRing.eq_maximalIdeal this

/-- **Norm/length formula, local form** (Fulton Ex. 1.2.3): `A` a one-dimensional Noetherian
local domain, `B ⊇ A` a finite domain extension with fraction fields `K ⊆ L`, `Q` an enumeration
of the maximal ideals of `B` and `D t = B_{Q t}`.  For `b ∈ L^×`,
`ord_A (N_{L/K} b) = Σ_t [κ(Q t) : κ(m_A)] · ord_{B_{Q t}} b` (multiplicatively in `ℤᵐ⁰`).
@isnad1 id=eq.3h8v.s10.f278664e3c74 from=translated src=- shape=0900c6ec vocab=6953f4da
-/
theorem ordFrac_norm_eq_prod_local
    (hQinj : Function.Injective Q)
    (hQsurj : ∀ Q' : Ideal B, Q'.IsMaximal → ∃ t, Q t = Q')
    (b : L) (hb : b ≠ 0) :
    Ring.ordFrac A (Algebra.norm K b) =
      ∏ t, Ring.ordFrac (D t) b ^ resDeg A (D t) := by
  letI : IsLocalization.AtPrime A (maximalIdeal A) := isLocalization_atPrime_maximalIdeal A
  haveI : ∀ t, (Q t).IsPrime := fun t ↦ (hQ t).isPrime
  refine ordFrac_norm_eq_prod (R := A) (S := B) (K := K) (L := L) (maximalIdeal A) (A := A) Q D
    (fun t r ↦ ?_) (comap_eq_maximalIdeal Q) hQinj (fun Q' hQ' hover ↦ ?_) b hb
  · rw [Algebra.algebraMap_self, RingHom.id_apply, IsScalarTower.algebraMap_apply A B (D t)]
  · haveI := hQ'
    have hmax : Q'.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap Q'
      (by rw [hover]; exact IsLocalRing.maximalIdeal.isMaximal A)
    exact hQsurj Q' hmax

end LocalForm

end RiemannRoch.NormLengthT2
