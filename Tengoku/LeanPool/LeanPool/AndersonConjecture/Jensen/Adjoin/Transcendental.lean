/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import Tengoku.LeanPool.LeanPool.AndersonConjecture.Jensen.NSubring
public import Tengoku

/-!
# Transcendental Extension of N-subrings

Adjoining a transcendental element to an N-subring R of a complete
local domain T and localising at the intersection with the maximal
ideal yields a new N-subring.

Loepp, "Constructing local generic formal fibers", 1997, Lemma 11.
-/

@[expose] public section

noncomputable section

open Cardinal Ideal Polynomial Set Pointwise

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-!
## Localization Carrier

The subring R[x]_{R[x] ∩ M} inside T, consisting of fractions p(x)/q(x)
where q(x) is a unit in T (equivalently, q(x) ∉ M).
-/

/-- The carrier set of R[x] localized at R[x] ∩ M, viewed inside T.
An element t ∈ T is in this set iff t = p(x)/q(x) for some p,q ∈ R[X]
with q(x) a unit in T (i.e., q(x) ∉ M). -/
def adjoinLocSet (R : NSubring T) (x : T) : Set T :=
  { t : T | ∃ (p q : Polynomial R.carrier),
    (aeval x q : T) ∉ IsLocalRing.maximalIdeal T ∧
    t * (aeval x q : T) = (aeval x p : T) }

/-- The carrier set forms a subring of T. -/
lemma adjoinLocSet_subring (R : NSubring T) (x : T) :
    ∃ (S : Subring T), (S : Set T) = adjoinLocSet R x := by
  have hunit : ∀ (a : T), a ∉ IsLocalRing.maximalIdeal T → IsUnit a :=
    fun a ha => IsLocalRing.notMem_maximalIdeal.mp ha
  have hprod_notmem : ∀ (a b : T),
      a ∉ IsLocalRing.maximalIdeal T → b ∉ IsLocalRing.maximalIdeal T →
      a * b ∉ IsLocalRing.maximalIdeal T := by
    simp_all
  refine ⟨{
    carrier := adjoinLocSet R x
    zero_mem' := ⟨0, 1, by simp_all,
      by rw [map_one, mul_one, map_zero]⟩
    one_mem' := ⟨1, 1, by simp_all,
      by rw [map_one, mul_one]⟩
    neg_mem' := ?neg
    add_mem' := ?add
    mul_mem' := ?mul
  }, rfl⟩
  case neg =>
    intro t ⟨p, q, hq, h⟩
    exact ⟨-p, q, hq, by rw [map_neg, ← h, neg_mul]⟩
  case mul =>
    intro t₁ t₂ ⟨p₁, q₁, hq₁, h₁⟩ ⟨p₂, q₂, hq₂, h₂⟩
    refine ⟨p₁ * p₂, q₁ * q₂, ?_, ?_⟩
    · simp_all
    · rw [map_mul, map_mul, ← h₁, ← h₂]
      ring
  case add =>
    intro t₁ t₂ ⟨p₁, q₁, hq₁, h₁⟩ ⟨p₂, q₂, hq₂, h₂⟩
    refine ⟨p₁ * q₂ + p₂ * q₁, q₁ * q₂, ?_, ?_⟩
    · simp_all
    · rw [map_mul, map_add, map_mul, map_mul, ← h₁, ← h₂]
      ring

/-- R.carrier ≤ adjoinLocSet carrier -/
lemma adjoinLocSet_le (R : NSubring T) (x : T)
    (t : T) (ht : t ∈ (R.carrier : Set T)) : t ∈ adjoinLocSet R x := by
  refine ⟨Polynomial.C ⟨t, ht⟩, 1, ?_, ?_⟩
  · simp_all
  · rw [map_one, mul_one, aeval_C]
    rfl

/-- x ∈ adjoinLocSet carrier -/
lemma adjoinLocSet_mem_x (R : NSubring T) (x : T) :
    x ∈ adjoinLocSet R x := by
  refine ⟨Polynomial.X, 1, ?_, ?_⟩
  · simp_all
  · rw [map_one, mul_one, aeval_X]

/-!
## Transcendental Extension (Loepp Lemma 11)

If x ∈ T is transcendental over Frac(R) and avoids a suitable set of primes,
then R[x] localized at M is again an N-subring.
-/

lemma adjoin_height_case_bot
    (R : NSubring T)
    (x : T)
    (hx_trans : Transcendental R.carrier x)
    (S_sub : Subring T)
    (hS_eq : (S_sub : Set T) = adjoinLocSet R x)
    (hinv : ∀ (s : S_sub), (s : T) ∉ IsLocalRing.maximalIdeal T → IsUnit s)
    (P : Ideal T) (hP_prime : P.IsPrime)
    (hPR : P.comap R.carrier.subtype = ⊥) :
    (Ideal.comap S_sub.subtype P).height ≤ ↑(1 : ℕ) := by
  rw [Ideal.height_le_iff]
  intro q hq_prime hq_lt
  suffices q = ⊥ by simp_all
  by_contra hq_ne
  obtain ⟨s, hs_q, hs_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq_ne
  obtain ⟨x', hx_P, hx_nq⟩ := Set.exists_of_ssubset hq_lt
  have eval_mem' : ∀ f : Polynomial R.carrier, (aeval x f : T) ∈ S_sub := by
    intro f
    change _ ∈ (S_sub : Set T)
    rw [hS_eq]
    exact ⟨f, 1, by simp_all,
      by rw [map_one, mul_one]⟩
  let φ : Polynomial R.carrier →+* S_sub :=
    (aeval (R := R.carrier) (A := T) x).toRingHom.codRestrict
      S_sub.toSubsemiring eval_mem'
  have hφ_val : ∀ f, (φ f : T) = aeval x f := fun _ => rfl
  have hφ_inj : Function.Injective φ := by
    intro f g hfg
    exact (transcendental_iff_injective.mp hx_trans) (congrArg Subtype.val hfg)
  set J := Ideal.comap φ q
  set J' := Ideal.comap φ (Ideal.comap S_sub.subtype P)
  have hJ_prime : J.IsPrime := hq_prime.comap _
  have hJ'_prime : J'.IsPrime := (hP_prime.comap S_sub.subtype).comap _
  have hJJ' : J ≤ J' := fun f hf => hq_lt.le hf
  obtain ⟨ps, qs, hqs, heqs⟩ : (s : T) ∈ adjoinLocSet R x := hS_eq ▸ s.2
  have hps_J : ps ∈ J := show φ ps ∈ q from by
    have : s * ⟨aeval x qs, eval_mem' qs⟩ = φ ps := Subtype.ext heqs
    rw [← this]
    exact q.mul_mem_right _ hs_q
  have hps_ne : ps ≠ 0 := by
    intro h
    simp_all
  have hJ_ne : J ≠ ⊥ := by
    intro h
    simp_all
  have hJJ'_ne : J ≠ J' := by
    intro heq
    apply hx_nq
    obtain ⟨px', qx', hqx', heqx'⟩ : (x' : T) ∈ adjoinLocSet R x :=
      hS_eq ▸ x'.2
    have hpx'_J' : px' ∈ J' := by
      change (φ px' : T) ∈ P
      rw [hφ_val, ← heqx']
      exact P.mul_mem_right _ (hx_P : (x' : T) ∈ P)
    have hpx'_q : φ px' ∈ q := by
      change px' ∈ J
      simp_all
    have hmul_q : x' * ⟨aeval x qx', eval_mem' qx'⟩ ∈ q :=
      (Subtype.ext heqx' : x' * ⟨aeval x qx', eval_mem' qx'⟩ = φ px') ▸
        hpx'_q
    simp_all
  have hJJ'_strict : J < J' := lt_of_le_of_ne hJJ' hJJ'_ne
  have hJ_const_zero : ∀ (c : R.carrier), Polynomial.C c ∈ J → c = 0 := by
    intro c hc
    have hcq := (show φ (Polynomial.C c) ∈ q from hc)
    have hcval : S_sub.subtype (φ (Polynomial.C c)) = (c : T) := by
      change (aeval x (Polynomial.C c) : T) = c
      simp [Polynomial.aeval_C, Algebra.algebraMap_ofSubring]
    have hcP : (c : T) ∈ P := hcval ▸ (hq_lt.le hcq : S_sub.subtype (φ _) ∈ P)
    have := (show c ∈ Ideal.comap R.carrier.subtype P from hcP)
    simp_all
  -- Map J, J' to K[X] (PID, dim ≤ 1) to get contradiction via saturation
  set K := FractionRing R.carrier
  set ψ := Polynomial.mapRingHom (algebraMap R.carrier K)
  have hψ_inj : Function.Injective ψ :=
    Polynomial.map_injective _ (IsFractionRing.injective R.carrier K)
  set M' := Submonoid.map (Polynomial.C : R.carrier →+* _) (nonZeroDivisors R.carrier)
  have hJ'_const_zero : ∀ (c : R.carrier), Polynomial.C c ∈ J' → c = 0 := by
    intro c hc
    have : (φ (Polynomial.C c) : T) ∈ P := hc
    have hcval : (φ (Polynomial.C c) : T) = (c : T) := by
      simp [hφ_val, Polynomial.aeval_C, Algebra.algebraMap_ofSubring]
    have hcP : (c : T) ∈ P := hcval ▸ this
    have := (show c ∈ Ideal.comap R.carrier.subtype P from hcP)
    simp_all
  have hJ_disj : Disjoint (M' : Set (Polynomial R.carrier)) (J : Set _) := by
    rw [Set.disjoint_left]
    intro f hfM hfJ
    obtain ⟨c, hc_nzd, rfl⟩ := hfM
    exact (nonZeroDivisors.ne_zero hc_nzd) (hJ_const_zero c hfJ)
  have hJ'_disj : Disjoint (M' : Set (Polynomial R.carrier)) (J' : Set _) := by
    rw [Set.disjoint_left]
    intro f hfM hfJ'
    obtain ⟨c, hc_nzd, rfl⟩ := hfM
    exact (nonZeroDivisors.ne_zero hc_nzd) (hJ'_const_zero c hfJ')
  let : Algebra (Polynomial R.carrier) (Polynomial K) := ψ.toAlgebra
  have : IsLocalization M' (Polynomial K) :=
    Polynomial.isLocalization (nonZeroDivisors R.carrier) K
  have : (Ideal.map (algebraMap _ (Polynomial K)) J).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M' (Polynomial K) J hJ_prime hJ_disj
  have : (Ideal.map (algebraMap _ (Polynomial K)) J').IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M' (Polynomial K) J' hJ'_prime hJ'_disj
  have hJ_map_ne : Ideal.map (algebraMap _ (Polynomial K)) J ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hψ_inj).not.mpr hJ_ne
  -- K[X] is a PID, dim ≤ 1: nonzero prime ≤ prime implies equality
  have hmap_eq : Ideal.map (algebraMap _ (Polynomial K)) J =
      Ideal.map (algebraMap _ (Polynomial K)) J' :=
    have : Ring.DimensionLEOne (Polynomial K) :=
      Ring.DimensionLEOne.principal_ideal_ring _
    (Ring.DimensionLeOne.prime_le_prime_iff_eq hJ_map_ne).mp (Ideal.map_mono hJJ')
  have hJ_sat := IsLocalization.under_map_of_isPrime_disjoint
    M' (Polynomial K) hJ_prime hJ_disj
  have hJ'_sat := IsLocalization.under_map_of_isPrime_disjoint
    M' (Polynomial K) hJ'_prime hJ'_disj
  exact absurd (hJ_sat.symm.trans (hmap_eq ▸ hJ'_sat)) hJJ'_ne

end
