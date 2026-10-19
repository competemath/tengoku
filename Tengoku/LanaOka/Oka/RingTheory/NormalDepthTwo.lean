/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.RingTheory.Ideal.AssociatedPrime.Basic
import Tengoku.Seed.RingTheory.Ideal.KrullsHeightTheorem
import Tengoku.Seed.RingTheory.IntegralClosure.GoingDown
import Tengoku.Seed.RingTheory.Regular.RegularSequence
import Tengoku.Seed.RingTheory.Ideal.GoingUp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Depth two in normal domains

Let `A` be a noetherian integrally closed domain. Every prime `P = (y : x)` associated to a
principal ideal `yA` has height at most one
(`Ideal.height_le_one_of_forall_mem_iff_exists_mul_eq`): with `t = x / y`, either `t P ⊆ P`,
and then `t` is integral, hence in `A`, which is absurd; or `t m ∉ P` for some `m ∈ P`, and then
`P` is minimal over `mA`, so has height at most one by Krull's principal ideal theorem.

Consequently, if no prime of height at most one contains both `g ≠ 0` and `h`, then `[g, h]` is
a weakly regular sequence on `A` (`isWeaklyRegular_pair_of_forall_height_le_one`).

In a noetherian domain, if every prime containing an ideal `J` has height at least two, then `J`
contains `g ≠ 0` and `h` such that no prime of height at most one contains both
(`exists_pair_of_forall_two_le_height`): `h` avoids the finitely many minimal primes of `gA`.

For an integral extension `R ⊆ S`, heights of primes of `S` are at most the heights of their
contractions (`Ideal.height_le_height_comap_of_isIntegral`); with going down they are equal.
-/

open RingTheory.Sequence Pointwise

section Height

/-- Weakly regular sequences are transported by ring isomorphisms. -/
lemma RingTheory.Sequence.IsWeaklyRegular.map_ringEquiv {R S : Type*} [CommRing R]
    [CommRing S] (φ : R ≃+* S) {rs : List R} (h : IsWeaklyRegular R rs) :
    IsWeaklyRegular S (rs.map φ) :=
  (AddEquiv.isWeaklyRegular_congr (e := φ.toAddEquiv) (as := rs) (bs := rs.map φ)
    (List.forall₂_map_right_iff.2 (List.forall₂_same.2 fun r _ x ↦ map_mul φ r x))).1 h

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- In an integral extension, **the height of a prime is at most the height of its
contraction**: contraction is strictly monotone on chains of primes (incomparability). -/
theorem Ideal.height_le_height_comap_of_isIntegral [Algebra.IsIntegral R S] (P : Ideal S)
    [P.IsPrime] : P.height ≤ (P.comap (algebraMap R S)).height := by
  have h1 := PrimeSpectrum.height_eq_orderHeight (⟨P, inferInstance⟩ : PrimeSpectrum S)
  have h2 := PrimeSpectrum.height_eq_orderHeight
    (PrimeSpectrum.comap (algebraMap R S) ⟨P, inferInstance⟩)
  refine h1.le.trans (le_trans ?_ h2.ge)
  refine Order.height_le_height_apply_of_strictMono
    (PrimeSpectrum.comap (algebraMap R S)) (fun p q hpq ↦ ?_) ⟨P, inferInstance⟩
  exact Ideal.IsIntegral.comap_lt_comap (R := R) hpq

/-- With going down, **the height of a prime is at least the height of its contraction**. -/
theorem Ideal.height_comap_le_height [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra.HasGoingDown R S]
    (P : Ideal S) [P.IsPrime] : (P.comap (algebraMap R S)).height ≤ P.height := by
  haveI : P.LiesOver (P.comap (algebraMap R S)) := ⟨rfl⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.comap (algebraMap R S)) P]
  exact le_self_add

end Height

section Normal

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

/-- **Primes associated to principal ideals of a normal domain have height at most one.** If
`P = {a | a x ∈ yA}` is prime, `y ≠ 0`, then `P` has height at most one. -/
theorem Ideal.height_le_one_of_forall_mem_iff_exists_mul_eq {P : Ideal A} [P.IsPrime] {x y : A}
    (hy : y ≠ 0) (hP : ∀ a, a ∈ P ↔ ∃ b, a * x = y * b) : P.height ≤ 1 := by
  let K := FractionRing A
  let t : K := algebraMap A K x / algebraMap A K y
  have hyK : algebraMap A K y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hy
  -- `t P ⊆ A`
  have htP : ∀ m ∈ P, ∃ b, t * algebraMap A K m = algebraMap A K b := by
    intro m hm
    obtain ⟨b, hb⟩ := (hP m).1 hm
    refine ⟨b, ?_⟩
    rw [div_mul_eq_mul_div, div_eq_iff hyK, ← map_mul, ← map_mul, mul_comm x, hb, mul_comm]
  -- `t ∉ A`
  have hyP : y ∈ P := (hP y).2 ⟨x, rfl⟩
  by_cases hcase : ∀ m ∈ P, ∀ b, t * algebraMap A K m = algebraMap A K b → b ∈ P
  · exfalso
    -- `t P ⊆ P`, so `t` is integral, hence `t ∈ A`
    let N : Submodule A K := Submodule.map (Algebra.linearMap A K) P
    have hN : N ≠ ⊥ := by
      intro h
      have : algebraMap A K y ∈ N := Submodule.mem_map_of_mem hyP
      rw [h, Submodule.mem_bot] at this
      exact hyK this
    have hint : IsIntegral A t := by
      refine isIntegral_of_smul_mem_submodule N hN (Submodule.FG.map _
        (IsNoetherian.noetherian P)) t fun n hn ↦ ?_
      obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨b, hb⟩ := htP m hm
      rw [smul_eq_mul, Algebra.linearMap_apply, hb]
      exact Submodule.mem_map_of_mem (hcase m hm b hb)
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have : x = y * a := by
      apply IsFractionRing.injective A K
      rw [map_mul, ha, mul_div_cancel₀ _ hyK]
    have h1 : (1 : A) ∈ P := (hP 1).2 ⟨a, by rw [one_mul, this]⟩
    exact (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one P).2 h1)
  · push Not at hcase
    obtain ⟨m, hm, u, hu, huP⟩ := hcase
    -- `P` is minimal over `mA`
    refine Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {m}) P
      ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem P).2 hm⟩, fun Q hQ hQP ↦ ?_⟩
    intro m' hm'
    obtain ⟨b, hb⟩ := htP m' hm'
    have hmQ : m ∈ Q := (Ideal.span_singleton_le_iff_mem Q).1 hQ.2
    have key : m' * u = b * m := by
      apply IsFractionRing.injective A K
      rw [map_mul, map_mul, ← hu, ← hb]
      ring
    have hmu : m' * u ∈ Q := key ▸ Q.mul_mem_left b hmQ
    exact (hQ.1.mem_or_mem hmu).resolve_right fun h ↦ huP (hQP h)

/-- **Weak regularity of a pair in a normal domain.** If `g ≠ 0` and no prime of height at most
one contains both `g` and `h`, then `[g, h]` is weakly regular on `A`. -/
theorem isWeaklyRegular_pair_of_forall_height_le_one {g h : A} (hg : g ≠ 0)
    (H : ∀ P : Ideal A, P.IsPrime → P.height ≤ 1 → g ∈ P → h ∉ P) :
    IsWeaklyRegular A [g, h] := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_cons_iff]
  refine ⟨IsSMulRegular.of_ne_zero hg, fun x y hxy ↦ ?_, IsWeaklyRegular.nil _ _⟩
  have hmem : ∀ z : A, Submodule.Quotient.mk (p := g • (⊤ : Submodule A A)) z = 0 ↔
      ∃ b, z = g * b := fun z ↦ by
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
    simp [eq_comm]
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hxy' : Submodule.Quotient.mk (p := g • (⊤ : Submodule A A)) (h * (x - y)) = 0 := by
    rw [mul_sub, Submodule.Quotient.mk_sub, sub_eq_zero]
    exact hxy
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub]
  set z := x - y
  by_contra hz
  -- an associated prime of `A ⧸ gA` containing the annihilator of `z`
  obtain ⟨P, hPass, hPle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A
    (Submodule.Quotient.mk (p := g • (⊤ : Submodule A A)) z) hz
  obtain ⟨hPprime, w, hw⟩ := (isAssociatedPrime_iff).1 hPass
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hPmem : ∀ a, a ∈ P ↔ ∃ b, a * w = g * b := fun a ↦ by
    rw [hw, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      smul_eq_mul, hmem]
  have hht := Ideal.height_le_one_of_forall_mem_iff_exists_mul_eq hg hPmem
  have hgP : g ∈ P := (hPmem g).2 ⟨w, rfl⟩
  have hhP : h ∈ P := hPle (by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      smul_eq_mul]
    exact hxy')
  exact H P hPprime hht hgP hhP

end Normal

section Pair

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

/-- **A pair without common primes of height one.** If every prime containing `J` has height at
least two, then `J` contains `g ≠ 0` and `h` such that no prime of height at most one contains
both. -/
theorem exists_pair_of_forall_two_le_height (J : Ideal R)
    (hJ : ∀ P : Ideal R, P.IsPrime → J ≤ P → 2 ≤ P.height) :
    ∃ g ∈ J, ∃ h ∈ J, g ≠ 0 ∧ ∀ P : Ideal R, P.IsPrime → P.height ≤ 1 → g ∈ P → h ∉ P := by
  classical
  -- `J ≠ ⊥`
  obtain ⟨g, hgJ, hg⟩ : ∃ g ∈ J, g ≠ 0 := by
    by_contra! H
    have hJ0 : J ≤ ⊥ := fun x hx ↦ (Submodule.mem_bot R).2 (H x hx)
    have := hJ ⊥ Ideal.isPrime_bot hJ0
    rw [Ideal.height_bot] at this
    exact absurd this (by norm_num)
  -- the minimal primes of `gR` of height at most one
  let F : Finset (Ideal R) := (Ideal.finite_minimalPrimes_of_isNoetherianRing R
    (Ideal.span {g})).toFinset.filter fun P ↦ P.height ≤ 1
  have hF : ∀ P ∈ F, P.IsPrime ∧ P.height ≤ 1 := fun P hP ↦ by
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hP
    exact ⟨hP.1.1.1, hP.2⟩
  have hnot : ¬ ∃ P ∈ F, J ≤ P := by
    rintro ⟨P, hP, hJP⟩
    haveI := (hF P hP).1
    have := (hJ P inferInstance hJP).trans (hF P hP).2
    exact absurd this (by norm_num)
  have havoid : ¬ (J : Set R) ⊆ ⋃ P ∈ (↑F : Set (Ideal R)), (P : Set R) := by
    intro hsub
    exact hnot ((Ideal.subset_union_prime (f := fun P : Ideal R ↦ P) ⊥ ⊥
      fun P hP _ _ ↦ (hF P hP).1).1 hsub)
  obtain ⟨h, hhJ, hh⟩ := Set.not_subset.1 havoid
  refine ⟨g, hgJ, h, hhJ, hg, fun P hP hPh hgP hhP ↦ hh ?_⟩
  -- `P` is minimal over `gR`
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem P).2 hgP)
  have hQeq : Q = P := by
    by_contra hne
    have hlt : Q < P := lt_of_le_of_ne hQP hne
    haveI := hQ.1.1
    have hQ0 : Q ≠ ⊥ := fun h0 ↦ hg (by
      have := (Ideal.span_singleton_le_iff_mem Q).1 hQ.1.2
      rw [h0, Submodule.mem_bot] at this
      exact this)
    have h1 : Q.height ≠ 0 := fun h ↦ hQ0 (Ideal.height_eq_zero_iff_eq_bot.1 h)
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have h3 : (2 : ℕ∞) ≤ P.height :=
      le_trans (by
        have : (1 : ℕ∞) ≤ Q.height := Order.one_le_iff_ne_zero.2 h1
        calc (2 : ℕ∞) = 1 + 1 := by norm_num
          _ ≤ Q.height + 1 := add_le_add_left this 1) h2
    exact absurd (h3.trans hPh) (by norm_num)
  subst hQeq
  refine Set.mem_biUnion (x := Q) ?_ hhP
  rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
  exact ⟨hQ, hPh⟩

end Pair

section Finite

variable {R A : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
  [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra R A]
  [Algebra.IsIntegral R A]

/-- **A regular pair from a finite extension.** Let `R ⊆ A` be a finite injective extension of
noetherian normal domains and `I ⊆ A` an ideal all of whose primes have height at least two.
Then the contraction of `I` contains `p₁, p₂` forming weakly regular sequences on `R` and on
`A`. -/
theorem exists_isWeaklyRegular_pair_of_isIntegral
    (hinj : Function.Injective (algebraMap R A)) (I : Ideal A)
    (hI : ∀ P : Ideal A, P.IsPrime → I ≤ P → 2 ≤ P.height) :
    ∃ p₁ ∈ I.comap (algebraMap R A), ∃ p₂ ∈ I.comap (algebraMap R A),
      IsWeaklyRegular R [p₁, p₂] ∧ IsWeaklyRegular A [algebraMap R A p₁, algebraMap R A p₂] := by
  haveI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).2 hinj
  have hJ : ∀ Q : Ideal R, Q.IsPrime → I.comap (algebraMap R A) ≤ Q → 2 ≤ Q.height := by
    intro Q hQ hIQ
    obtain ⟨P, hIP, hP, rfl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral Q I hIQ
    exact (hI P hP hIP).trans (Ideal.height_le_height_comap_of_isIntegral P)
  obtain ⟨p₁, hp₁, p₂, hp₂, hp0, hpair⟩ := exists_pair_of_forall_two_le_height _ hJ
  refine ⟨p₁, hp₁, p₂, hp₂, isWeaklyRegular_pair_of_forall_height_le_one hp0 hpair,
    isWeaklyRegular_pair_of_forall_height_le_one ((map_ne_zero_iff _ hinj).2 hp0)
      fun P hP hPh h₁ h₂ ↦ ?_⟩
  exact hpair (P.comap (algebraMap R A)) inferInstance
    ((Ideal.height_comap_le_height P).trans hPh) h₁ h₂

end Finite
