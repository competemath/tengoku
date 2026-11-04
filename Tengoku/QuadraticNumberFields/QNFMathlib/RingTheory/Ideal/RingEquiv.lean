/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.Seed.Algebra.GroupWithZero.NonZeroDivisors
import Tengoku.Seed.RingTheory.DedekindDomain.Ideal.Lemmas
import Tengoku.Seed.RingTheory.Ideal.Maps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ideals and Ring Equivalences

Material destined for mathlib.
-/

namespace Ideal

section CommRing

variable {R : Type*} [CommRing R]

/-- A ring equivalence induces a multiplicative equivalence on ideals.-/
def mapRingEquivMulEquiv (σ : R ≃+* R) :
    Ideal R ≃* Ideal R :=
  { σ.idealComapOrderIso.symm.toEquiv with
    map_mul' := Ideal.map_mul σ }

/-- A ring equivalence induces a multiplicative equivalence on non-zero-divisor ideals.-/
noncomputable def mapRingEquivNonZeroDivisorsMulEquiv (σ : R ≃+* R) :
    nonZeroDivisors (Ideal R) ≃* nonZeroDivisors (Ideal R) :=
  ((mapRingEquivMulEquiv σ).submonoidMap (nonZeroDivisors (Ideal R))).trans
    (MulEquiv.submonoidCongr (MulEquivClass.map_nonZeroDivisors (mapRingEquivMulEquiv σ)))

/--
@isnad1 id=eq.0h3v.s12.4c719df870f9 from=translated src=- shape=b75d5f1e vocab=cb103b6f
-/
@[simp]
theorem coe_mapRingEquivNonZeroDivisorsMulEquiv_apply
    (σ : R ≃+* R) (I : nonZeroDivisors (Ideal R)) :
    ((mapRingEquivNonZeroDivisorsMulEquiv σ I : nonZeroDivisors (Ideal R)) : Ideal R) =
      Ideal.map (σ : R →+* R) I.1 :=
  rfl

/-- The image of a non-zero-divisor ideal under a ring equivalence is again a
non-zero-divisor ideal.
@isnad1 id=mem.1h3v.s9.275443450963 from=translated src=- shape=0277109d vocab=453afa02
-/
theorem map_ringEquiv_mem_nonZeroDivisors (σ : R ≃+* R)
    {I : Ideal R} (hI : I ∈ nonZeroDivisors (Ideal R)) :
    Ideal.map (σ : R →+* R) I ∈ nonZeroDivisors (Ideal R) := by
  rw [← MulEquivClass.map_nonZeroDivisors (mapRingEquivMulEquiv σ)]
  exact ⟨I, hI, rfl⟩

/-- Mapping ideals by a ring equivalence is injective.
@isnad1 id=injectiv.0h2v.s7.201f778d4fe0 from=translated src=- shape=2ce2e378 vocab=e2456b0a
-/
theorem map_ringEquiv_injective (σ : R ≃+* R) :
    Function.Injective (fun P : Ideal R => Ideal.map (σ : R →+* R) P) := by
  exact σ.idealComapOrderIso.symm.injective

/-- Mapping a multiset product of ideals by a ring equivalence maps each factor.
@isnad1 id=eq.0h3v.s9.1a95759f1707 from=translated src=- shape=907a8cc3 vocab=d641fcfa
-/
theorem map_ringEquiv_multiset_prod (σ : R ≃+* R) (s : Multiset (Ideal R)) :
    Ideal.map (σ : R →+* R) s.prod =
      (s.map fun P ↦ Ideal.map (σ : R →+* R) P).prod := by
  change (mapRingEquivMulEquiv σ) s.prod =
    (s.map fun P ↦ (mapRingEquivMulEquiv σ) P).prod
  exact (mapRingEquivMulEquiv σ).toMonoidHom.map_multiset_prod s

end CommRing

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- A ring equivalence maps the normalized factorization multiset of a nonzero
Dedekind ideal to the normalized factorization multiset of its image.
@isnad1 id=eq.1h3v.s9.612835b94967 from=translated src=- shape=e1e8492f vocab=f735fc89
-/
theorem normalizedFactors_map_ringEquiv (σ : R ≃+* R)
    {I : Ideal R} (hI : I ≠ ⊥) :
    UniqueFactorizationMonoid.normalizedFactors (Ideal.map (σ : R →+* R) I) =
      (UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P ↦ Ideal.map (σ : R →+* R) P) := by
  rw [show Ideal.map (σ : R →+* R) I =
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P ↦ Ideal.map (σ : R →+* R) P)).prod by
    rw [← Ideal.map_ringEquiv_multiset_prod σ,
      Ideal.prod_normalizedFactors_eq_self hI]]
  apply UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
  intro Q hQ
  rcases Multiset.mem_map.mp hQ with ⟨P, hP, rfl⟩
  exact Ideal.map_prime_of_equiv σ
    (UniqueFactorizationMonoid.prime_of_normalized_factor P hP)
    (UniqueFactorizationMonoid.prime_of_normalized_factor P hP).ne_zero

/-- A ring equivalence preserves normalized-factor multiplicities after applying
the equivalence to the counted factor.
@isnad1 id=eq.1h4v.s9.5beb78be9771 from=translated src=- shape=f451c669 vocab=a56f21c8
-/
theorem normalizedFactors_count_map_ringEquiv (σ : R ≃+* R)
    {P I : Ideal R} (hI : I ≠ ⊥) :
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.map (σ : R →+* R) I)).count
        (Ideal.map (σ : R →+* R) P) =
      (UniqueFactorizationMonoid.normalizedFactors I).count P := by
  rw [Ideal.normalizedFactors_map_ringEquiv σ hI]
  rw [Multiset.count_map_eq_count' _ _ (Ideal.map_ringEquiv_injective σ) P]

end Dedekind

end Ideal
